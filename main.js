/**
 * ioBroker Blustream ACM Adapter
 * Controls Blustream ACM matrix controllers (ACM200/ACM210/ACM500/ACM1000)
 * for audio/video distribution over IP
 *
 * File: main.js - Main adapter file
 */

'use strict';

const utils = require('@iobroker/adapter-core');
const net = require('node:net');
const {
    resolveModel,
    DEFAULT_MODEL,
    MODELS,
    AUDIO_OUTPUT_MODES,
    AUDIO_INPUT_MODES,
    ARC_MODES,
} = require('./lib/models');

/**
 * Device-response banner markers. Matched model-agnostically so the same parser
 * works across ACM200/210/500/1000, whose banners carry different model numbers
 * and (on some models) drop the "IP Control Box" prefix — e.g. both
 * "IP Control Box ACM200 Status Info" and "ACM210 Status Info" must match.
 * NOTE: the field layout inside each block is assumed to match the ACM200; this
 * needs verifying against a real STATUS/detail dump from a non-200 controller.
 */
const BANNER = {
    input: /ACM\d+ Input Info/,
    output: /ACM\d+ Output Info/,
    status: /ACM\d+ Status Info/,
};

/**
 * Receiver states whose value is a transmitter id (as opposed to a mode token).
 * Writes to these are normalised with sanitizeDeviceId() before reaching a
 * command builder — see onStateChange.
 */
const ROUTE_STATES = ['route', 'videoRoute', 'audioRoute', 'irRoute', 'rs232Route', 'usbRoute', 'cecRoute'];

/**
 * Labels for the two refresh buttons, which are easily confused. Held because
 * they are used twice: once when the objects are created and once to push the text
 * onto installs that predate a wording change (setObjectNotExists never updates an
 * object that already exists) — see syncCommandLabels().
 */
const REFRESH_LABELS = {
    'system.commands.refresh': {
        name: 'Refresh Status',
        desc: 'Run a single STATUS poll (routes, names and online state) — the same query used by regular polling. Use refreshAll for per-device details.',
    },
    'system.commands.refreshAll': {
        name: 'Refresh All Device Details',
        desc: 'Query per-device details (firmware, MAC, mode, breakaway routes) for every known transmitter and receiver. Slower than refresh — it sends one command per device.',
    },
};

class BlustreamAcm extends utils.Adapter {
    constructor(options) {
        super({
            ...options,
            name: 'blustream-acm',
        });

        this.on('ready', this.onReady.bind(this));
        this.on('stateChange', this.onStateChange.bind(this));
        this.on('unload', this.onUnload.bind(this));

        // Default settings
        this.model = DEFAULT_MODEL; // Controller model; overridden from config in onReady
        this.modelDef = MODELS[DEFAULT_MODEL]; // Capability/command definition for the model
        this.host = '192.168.0.225'; // Default IP for the ACM controller
        this.port = 23; // Default Telnet port
        this.pollInterval = 30000; // Poll every 30 seconds

        this.pollTimer = null;
        this.reconnectTimer = null;
        this.connected = false;
        this.receiverStates = {};
        this.transmitterStates = {};
        this.connectionInProgress = false;

        // Variables for scheduled refresh
        this.scheduledRefreshTimer = null;

        // New variables for socket-based connection
        this.socket = null;
        this.socketBuffer = '';
        this.heartbeatTimer = null;
        this.heartbeatTimeout = null;
        this.reconnectDelay = 30000; // 30 seconds
        this.commandQueue = [];
        this.processingCommand = false;

        this.timeout = 10000; // default command timeout (ms); overridden from config in onReady
        this.heartbeatInterval = 10000; // Heartbeat every 10 s

        this.collectingTxInfo = false;
        this.txInfoBuffer = '';
        this.collectingRxInfo = false;
        this.rxInfoBuffer = '';
        this.collectingStatus = false;
        this.statusBuffer = '';

        // Last source IP each preview URL was built from, keyed by state id.
        // The URL carries a cache-busting timestamp, so it is only rewritten
        // when the source actually changes (see updatePreviewUrl).
        this.previewUrlSources = {};
    }

    /**
     * Parse, validate and clamp a numeric config value into the inclusive range [min, max].
     * Empty/non-numeric input falls back to `fallback`; out-of-range values are clamped with a warning.
     * Guards timers against negative and >Node-max (2^31-1) values reaching setTimeout/setInterval.
     *
     * @param {string} name - Config key name, used in log messages
     * @param {string|number|undefined|null} raw - Raw value from this.config
     * @param {number} fallback - Default used when raw is empty or not a finite number
     * @param {number} min - Lower bound (inclusive)
     * @param {number} max - Upper bound (inclusive)
     * @returns {number} A finite integer within [min, max]
     */
    validateNumber(name, raw, fallback, min, max) {
        if (raw === undefined || raw === null || raw === '') {
            return fallback;
        }
        const parsed = Number(raw);
        if (!Number.isFinite(parsed)) {
            this.log.warn(`Config "${name}" is not a valid number ("${raw}"); using default ${fallback}`);
            return fallback;
        }
        if (parsed < min) {
            this.log.warn(`Config "${name}" (${parsed}) is below the minimum ${min}; clamping to ${min}`);
            return min;
        }
        if (parsed > max) {
            this.log.warn(`Config "${name}" (${parsed}) exceeds the maximum ${max}; clamping to ${max}`);
            return max;
        }
        return Math.floor(parsed);
    }

    /**
     * Validate and normalise a device ID parsed from a telnet response before it
     * is used to build object IDs. Blustream device IDs are numeric; anything
     * else is rejected so untrusted response data can never inject forbidden
     * characters into the object tree.
     *
     * @param {string} raw - Raw ID token from a parsed response line
     * @returns {string|null} zero-padded 3-digit id, or null if not a valid id
     */
    sanitizeDeviceId(raw) {
        const trimmed = String(raw == null ? '' : raw).trim();
        if (!/^\d+$/.test(trimmed)) {
            return null;
        }
        return trimmed.padStart(3, '0');
    }

    /**
     * Write a preview image URL, but only when the source it points at has changed.
     * The URL carries a cache-busting timestamp, so rebuilding it on every poll would
     * emit a state change every cycle even when nothing was re-routed.
     *
     * @param {string} stateId - Preview URL state, relative to the instance namespace
     * @param {string} sourceIp - IP of the transmitter being previewed; ignored if empty
     * @returns {Promise<void>} resolves once the state has been written (or skipped)
     */
    async updatePreviewUrl(stateId, sourceIp) {
        if (!sourceIp || this.previewUrlSources[stateId] === sourceIp) {
            return;
        }

        const previewUrl = `http://${this.host}/cgi-bin/capture.cgi?hostip=${sourceIp}&capwidth=240&time=${Date.now()}`;
        await this.setState(stateId, previewUrl, true);
        // Cached only after the write succeeded — a failed write must not latch the id out
        this.previewUrlSources[stateId] = sourceIp;
    }

    /**
     * Drop cached preview sources for a device whose objects have just been deleted.
     * Without this, a device that disappears and returns with the same id and the same
     * source would keep its recreated previewUrl state empty forever.
     *
     * @param {string} channel - 'transmitters' or 'receivers'
     * @param {string} deviceId - Device id whose cache entries should be forgotten
     */
    forgetPreviewUrl(channel, deviceId) {
        delete this.previewUrlSources[`${channel}.${deviceId}.previewUrl`];
    }

    /**
     * Initialize the adapter
     */
    async onReady() {
        // Reset the connection indicator at startup
        this.setState('info.connection', false, true);

        // Resolve the controller model from config (falls back to the default)
        const resolved = resolveModel(this.config.model);
        if (!resolved.valid) {
            this.log.warn(`Unknown or missing controller model "${this.config.model}"; falling back to ${resolved.id}`);
        }
        this.model = resolved.id;
        this.modelDef = resolved.def;
        this.log.info(`Controller model: ${this.modelDef.label}`);

        // Get configuration from admin settings (validated & clamped to safe ranges)
        this.host = this.config.host || this.host;
        this.port = this.validateNumber('port', this.config.port, this.port, 1, 65535);
        // Floor of 1000 ms: a multi-line STATUS response cannot realistically arrive faster,
        // and this timeout is what the poll-interval floor below is derived from.
        this.timeout = this.validateNumber('timeout', this.config.timeout, this.timeout, 1000, 60000);
        // A poll cycle must be able to finish (STATUS command + response) before the next one is
        // armed, so the interval floor is derived from the command timeout rather than fixed.
        const pollFloor = Math.max(1000, this.timeout * 2);
        this.pollInterval = this.validateNumber(
            'pollInterval',
            this.config.pollInterval,
            Math.max(this.pollInterval, pollFloor),
            pollFloor,
            3600000,
        );

        this.log.info(`Initializing with host: ${this.host}, port: ${this.port}, timeout: ${this.timeout}ms`);

        // Create root objects using setObjectNotExists instead of createDevice
        await this.setObjectNotExistsAsync('system', {
            type: 'device',
            common: {
                name: 'Blustream ACM System',
            },
            native: {},
        });

        await this.setObjectNotExistsAsync('system.status', {
            type: 'channel',
            common: {
                name: 'System Status',
            },
            native: {},
        });

        await this.setObjectNotExistsAsync('system.commands', {
            type: 'channel',
            common: {
                name: 'System Commands',
            },
            native: {},
        });

        // Add manual refresh buttons and status indicators
        await this.setObjectNotExistsAsync('system.commands.refreshAll', {
            type: 'state',
            common: {
                ...REFRESH_LABELS['system.commands.refreshAll'],
                type: 'boolean',
                role: 'button',
                read: false,
                write: true,
                def: false,
            },
            native: {},
        });

        await this.setObjectNotExistsAsync('system.status.lastFullRefresh', {
            type: 'state',
            common: {
                name: 'Last Full Refresh',
                type: 'string',
                role: 'date',
                read: true,
                write: false,
                def: '',
                desc: 'Timestamp of the last full device details refresh',
            },
            native: {},
        });

        await this.setObjectNotExistsAsync('system.status.fullRefreshRunning', {
            type: 'state',
            common: {
                name: 'Full Refresh Running',
                type: 'boolean',
                role: 'indicator',
                read: true,
                write: false,
                def: false,
                desc: 'Indicates if a full refresh is currently in progress',
            },
            native: {},
        });

        await this.setObjectNotExistsAsync('system.status.nextScheduledRefresh', {
            type: 'state',
            common: {
                name: 'Next Scheduled Refresh',
                type: 'string',
                role: 'date',
                read: true,
                write: false,
                def: '',
                desc: 'Timestamp of the next scheduled full refresh',
            },
            native: {},
        });

        // Create system states using setObjectNotExists
        await this.setObjectNotExistsAsync('system.status.connected', {
            type: 'state',
            common: {
                name: 'Connection Status',
                type: 'boolean',
                role: 'indicator.connected',
                read: true,
                write: false,
                def: false,
            },
            native: {},
        });

        await this.setObjectNotExistsAsync('system.status.lastUpdate', {
            type: 'state',
            common: {
                name: 'Last Update',
                type: 'string',
                role: 'date',
                read: true,
                write: false,
                def: '',
            },
            native: {},
        });

        await this.setObjectNotExistsAsync('system.commands.refresh', {
            type: 'state',
            common: {
                ...REFRESH_LABELS['system.commands.refresh'],
                type: 'boolean',
                role: 'button',
                read: false,
                write: true,
                def: false,
            },
            native: {},
        });

        // Route-to-all-displays commands — write a transmitter ID to trigger
        await this.setObjectNotExistsAsync('system.commands.routeAll', {
            type: 'state',
            common: {
                name: 'Route to All Displays (Audio+Video)',
                type: 'string',
                role: 'text',
                read: true,
                write: true,
                def: '',
                desc: 'Write a transmitter ID to route audio+video to all displays',
            },
            native: {},
        });

        await this.setObjectNotExistsAsync('system.commands.routeAllVideo', {
            type: 'state',
            common: {
                name: 'Route to All Displays (Video Only)',
                type: 'string',
                role: 'text',
                read: true,
                write: true,
                def: '',
                desc: 'Write a transmitter ID to route video only to all displays',
            },
            native: {},
        });

        await this.setObjectNotExistsAsync('system.commands.routeAllAudio', {
            type: 'state',
            common: {
                name: 'Route to All Displays (Audio Only)',
                type: 'string',
                role: 'text',
                read: true,
                write: true,
                def: '',
                desc: 'Write a transmitter ID to route audio only to all displays',
            },
            native: {},
        });

        // Initialize folders for transmitters and receivers
        await this.setObjectNotExistsAsync('transmitters', {
            type: 'device',
            common: {
                name: 'Video Sources (Transmitters)',
            },
            native: {},
        });

        await this.setObjectNotExistsAsync('receivers', {
            type: 'device',
            common: {
                name: 'Displays (Receivers)',
            },
            native: {},
        });

        // Subscribe to states
        this.subscribeStates('system.commands.refresh');
        this.subscribeStates('system.commands.refreshAll');
        this.subscribeStates('system.commands.routeAll');
        this.subscribeStates('system.commands.routeAllVideo');
        this.subscribeStates('system.commands.routeAllAudio');
        this.subscribeStates('receivers.*.route');
        this.subscribeStates('receivers.*.videoRoute');
        this.subscribeStates('receivers.*.audioRoute');
        this.subscribeStates('receivers.*.irRoute');
        this.subscribeStates('receivers.*.rs232Route');
        this.subscribeStates('receivers.*.usbRoute');
        this.subscribeStates('receivers.*.cecRoute');
        this.subscribeStates('receivers.*.power');
        this.subscribeStates('receivers.*.mute');
        this.subscribeStates('receivers.*.audioOutputMode');
        this.subscribeStates('receivers.*.arcMode');
        this.subscribeStates('transmitters.*.audioSource');
        this.subscribeStates('transmitters.*.audioMatrixMode');

        // Remove any states left over from a previous model that the current
        // model does not support (setObjectNotExists never deletes objects).
        await this.reconcileModelStates();

        // Bring the refresh button labels up to date on pre-existing installs
        await this.syncCommandLabels();

        // Start connection to the controller - Use new socket-based connection
        this.connectToACM();

        // Setup scheduled refresh
        this.setupScheduledRefresh();
    }

    /**
     * Handle state changes
     *
     * @param {string} id - State ID
     * @param {object} state - State object
     */
    onStateChange(id, state) {
        if (state && !state.ack) {
            // Handle manual refresh commands
            if (id === `${this.namespace}.system.commands.refresh`) {
                this.log.info('Manual basic refresh triggered');
                this.refreshDeviceStatus();
                return;
            }

            if (id === `${this.namespace}.system.commands.refreshAll`) {
                this.log.info('Manual full refresh triggered');

                // Check if refresh is already running
                this.getStateAsync('system.status.fullRefreshRunning')
                    .then(runningState => {
                        if (runningState && runningState.val === true) {
                            this.log.warn('Full refresh already in progress, ignoring request');
                            return;
                        }

                        // Perform full refresh
                        this.refreshAllDeviceDetails()
                            .then(() => {
                                this.log.info('Manual full refresh completed successfully');
                            })
                            .catch(err => {
                                this.log.error(`Error during manual full refresh: ${err.message}`);
                            });
                    })
                    .catch(err => this.log.warn(`Could not check refresh status: ${err.message}`));
                return;
            }

            // Handle route-to-all-displays commands. The written value is a transmitter id,
            // so it gets the same normalisation as the per-receiver routing states.
            const routeAllTargets = {
                [`${this.namespace}.system.commands.routeAll`]: ['audio+video', tx => this.routeVideoToAll(tx)],
                [`${this.namespace}.system.commands.routeAllVideo`]: ['video', tx => this.routeVideoOnlyToAll(tx)],
                [`${this.namespace}.system.commands.routeAllAudio`]: ['audio', tx => this.routeAudioToAll(tx)],
            };
            if (routeAllTargets[id] && state.val) {
                const [what, run] = routeAllTargets[id];
                const tx = this.sanitizeDeviceId(String(state.val));
                if (!tx) {
                    this.log.warn(`Ignoring routeAll write "${state.val}": not a numeric transmitter id`);
                    return;
                }
                this.log.info(`Routing transmitter ${tx} (${what}) to all displays`);
                run(tx);
                return;
            }

            // Handle receiver control changes
            if (id.startsWith(`${this.namespace}.receivers.`)) {
                const localId = id.slice(this.namespace.length + 1); // e.g. 'receivers.001.route'
                const parts = localId.split('.');
                const receiverId = parts[1];
                const stateName = parts[2];

                if (receiverId) {
                    // Routing states carry a transmitter id written by a user or a script —
                    // normalise it before it reaches a command builder, otherwise a typo is
                    // sent verbatim down the telnet socket (e.g. "abc" -> "OUT001FRabc").
                    const raw = state.val ? String(state.val) : '';
                    const src = ROUTE_STATES.includes(stateName) ? this.sanitizeDeviceId(raw) || '' : raw;
                    if (raw && !src) {
                        this.log.warn(
                            `Ignoring write of "${raw}" to ${stateName} on receiver ${receiverId}: not a numeric transmitter id`,
                        );
                        return;
                    }
                    switch (stateName) {
                        // Routing states carry the source transmitter id; an empty write is ignored.
                        case 'route':
                            if (src) {
                                this.routeVideo(src, receiverId);
                            }
                            break;
                        case 'videoRoute':
                            if (src) {
                                this.routeVideoOnly(src, receiverId);
                            }
                            break;
                        case 'audioRoute':
                            if (src) {
                                this.routeAudioOnly(src, receiverId);
                            }
                            break;
                        case 'irRoute':
                            if (src) {
                                this.routeBreakaway('ir', src, receiverId);
                            }
                            break;
                        case 'rs232Route':
                            if (src) {
                                this.routeBreakaway('rs232', src, receiverId);
                            }
                            break;
                        case 'usbRoute':
                            if (src) {
                                this.routeBreakaway('usb', src, receiverId);
                            }
                            break;
                        case 'cecRoute':
                            if (src) {
                                this.routeBreakaway('cec', src, receiverId);
                            }
                            break;
                        // Boolean control states (false is a valid value, so no src guard).
                        case 'power':
                            this.setOutputPower(receiverId, !!state.val);
                            break;
                        case 'mute':
                            this.setOutputMute(receiverId, !!state.val);
                            break;
                        // Tier 3 — audio matrix / ARC selectors (carry a mode token).
                        case 'audioOutputMode':
                            if (src) {
                                this.setAudioOutputMode(receiverId, src);
                            }
                            break;
                        case 'arcMode':
                            if (src) {
                                this.setArcMode(receiverId, src);
                            }
                            break;
                    }
                }
            }

            // Handle transmitter control changes
            if (id.startsWith(`${this.namespace}.transmitters.`)) {
                const localId = id.slice(this.namespace.length + 1);
                const parts = localId.split('.');
                const txId = parts[1];
                const stateName = parts[2];
                const val = state.val ? String(state.val) : '';

                if (txId && val) {
                    if (stateName === 'audioSource') {
                        this.setTransmitterAudioSource(txId, val);
                    } else if (stateName === 'audioMatrixMode') {
                        this.setAudioInputMode(txId, val);
                    }
                }
            }
        }
    }

    /**
     * Clean up on adapter unload
     *
     * @param {() => void} callback - Called when cleanup is complete
     */
    onUnload(callback) {
        try {
            // Clear timers
            if (this.pollTimer) {
                this.clearTimeout(this.pollTimer);
                this.pollTimer = null;
            }
            if (this.reconnectTimer) {
                this.clearTimeout(this.reconnectTimer);
                this.reconnectTimer = null;
            }
            if (this.heartbeatTimer) {
                this.clearInterval(this.heartbeatTimer);
                this.heartbeatTimer = null;
            }
            if (this.heartbeatTimeout) {
                this.clearTimeout(this.heartbeatTimeout);
                this.heartbeatTimeout = null;
            }
            if (this.scheduledRefreshTimer) {
                this.clearTimeout(this.scheduledRefreshTimer);
                this.scheduledRefreshTimer = null;
            }

            // Clear command queue
            this.commandQueue.forEach(cmd => {
                if (cmd.timer) {
                    this.clearTimeout(cmd.timer);
                }
            });
            this.commandQueue = [];

            // Close socket connection
            if (this.socket) {
                try {
                    this.socket.destroy();
                } catch (e) {
                    this.log.warn(`Error during socket destroy: ${e.message}`);
                }
                this.socket = null;
            }

            this.log.info('Cleaned up everything');
            callback();
        } catch (e) {
            this.log.error(`Error during cleanup: ${e.message}`);
            callback();
        }
    }

    /**
     * Connect to the ACM200 using a direct socket connection
     */
    connectToACM() {
        if (this.connectionInProgress) {
            this.log.info('Connection already in progress, skipping');
            return;
        }

        this.log.info(`Connecting to ${this.modelDef.label} at ${this.host}:${this.port}`);
        this.log.info(`Using socket timeout: ${this.timeout}ms`);

        // Clear any existing connection and timers. Must run BEFORE the in-progress flag
        // is raised, because cleanup() clears that flag (see the note there).
        this.cleanup(false);
        this.connectionInProgress = true;

        try {
            // Create socket connection
            this.socket = new net.Socket();

            // Configure socket with better keepalive settings
            this.socket.setKeepAlive(true, 10000); // Change from 5000 to 10000
            this.socket.setNoDelay(true);

            // Explicitly set timeout and log it
            this.log.debug(`Setting socket timeout to ${this.timeout}ms`);
            this.socket.setTimeout(this.timeout);

            // Add more detailed handlers
            this.socket.on('connect', () => {
                this.log.info(`Socket connected to ${this.modelDef.label}`);
                this.log.debug(`Socket timeout is set to ${this.timeout}ms`);
                this.handleConnect();
            });

            this.socket.on('data', data => {
                // Log data receipt for debugging
                this.log.debug(`Received ${data.length} bytes of data`);
                this.handleData(data);
            });

            this.socket.on('error', err => {
                this.log.error(`Socket error: ${err.message}`);
                this.handleError(err);
            });

            this.socket.on('timeout', () => {
                // Add more context to timeout log
                this.log.warn(`Socket timeout after ${this.timeout}ms - no activity detected`);
                this.log.info(
                    `If the timeout persists, try using a Telnet client to test basic connectivity to ${this.host}:${this.port}`,
                );
                this.handleTimeout();
            });

            this.socket.on('close', hadError => {
                this.log.info(`Socket closed${hadError ? ' due to error' : ''}`);
                this.handleClose(hadError);
            });

            // Connect to the device
            this.socket.connect(this.port, this.host);
        } catch (err) {
            this.log.error(`Error creating socket: ${err.message}`);
            this.connectionInProgress = false;
            this.cleanup(true);
        }
    }

    /**
     * Handle socket connection event
     */
    handleConnect() {
        this.log.info(`Socket connected to ${this.modelDef.label}`);

        // Wait longer before sending test command
        this.setTimeout(() => {
            this.log.debug('Sending test command after connection');
            this.log.debug(`Test command is: STATUS with timeout ${this.timeout}ms`);

            // Send a test command to verify connection
            this.executeCommand('STATUS', this.timeout)
                .then(() => {
                    // Connection confirmed
                    this.log.info('Connection confirmed with test command');
                    this.connected = true;
                    this.connectionInProgress = false;
                    this.setState('info.connection', true, true);
                    this.setState('system.status.connected', true, true);

                    // Disable socket timeout — heartbeat handles liveness detection
                    if (this.socket) {
                        this.socket.setTimeout(0);
                    }

                    // Start heartbeat with more appropriate timing
                    this.startHeartbeat();

                    // Get full device details (including names) on startup
                    this.refreshAllDeviceDetails().catch(err =>
                        this.log.warn(`Initial full refresh failed: ${err.message}`),
                    );

                    // Start regular polling
                    this.startPolling();
                })
                .catch(err => {
                    this.log.warn(`Test command failed: ${err.message}`);
                    this.connected = false;
                    this.connectionInProgress = false;
                    this.cleanup(true);
                });
        }, 5000); // Increase from 2000 to 5000 ms (5 seconds)
    }

    /**
     * Handle socket error
     *
     * @param {Error} err - Error object
     */
    handleError(err) {
        this.log.error(`Socket error: ${err.message}`);
        this.cleanup(true);
    }

    /**
     * Handle socket timeout
     */
    handleTimeout() {
        this.log.warn(`Socket timeout after ${this.timeout}ms`);
        this.cleanup(true);
    }

    /**
     * Handle socket close
     *
     * @param {boolean} hadError - Whether the socket closed due to an error
     */
    handleClose(hadError) {
        if (hadError) {
            this.log.warn('Socket closed due to error');
        } else {
            this.log.info('Socket closed');
        }

        this.cleanup(true);
    }

    /**
     * Start heartbeat monitoring
     */
    startHeartbeat() {
        if (this.heartbeatTimer) {
            this.clearInterval(this.heartbeatTimer);
        }

        // Use the instance heartbeat interval
        const heartbeatInterval = this.heartbeatInterval;

        this.log.info(`Starting heartbeat monitoring (interval: ${heartbeatInterval}ms)`);

        this.heartbeatTimer = this.setInterval(() => {
            if (!this.connected || !this.socket) {
                return;
            }

            // Skip heartbeat STATUS if the command queue is busy — the fact that
            // we're processing commands already proves the connection is alive
            if (this.commandQueue.length > 0 || this.processingCommand) {
                this.log.debug('Skipping heartbeat — command queue is busy (connection is alive)');
                this.resetHeartbeatTimeout();
                return;
            }

            this.log.debug('Sending heartbeat');

            // Set up timeout for heartbeat response
            this.resetHeartbeatTimeout();

            // Use a command that the ACM200 actually supports. Capped at the heartbeat
            // interval so a long configured timeout cannot outlive the watchdog below.
            this.executeCommand('STATUS', Math.min(this.timeout, this.heartbeatInterval))
                .then(response => {
                    this.log.debug(`Heartbeat successful: received ${response ? 'response' : 'no response'}`);
                })
                .catch(err => {
                    this.log.warn(`Heartbeat command failed: ${err.message}`);
                    // The heartbeat timeout will handle reconnection if needed
                });
        }, heartbeatInterval);
    }

    /**
     * Reset the heartbeat timeout
     */
    resetHeartbeatTimeout() {
        // Clear existing timeout
        if (this.heartbeatTimeout) {
            this.clearTimeout(this.heartbeatTimeout);
        }

        // Set new timeout
        this.heartbeatTimeout = this.setTimeout(() => {
            this.log.error('Heartbeat timeout - connection considered dead');
            this.cleanup(true);
        }, this.heartbeatInterval * 1.5); // 1.5 times the interval for some grace period
    }

    /**
     * Execute a command with timeout and response handling
     *
     * @param {string} command - Command to execute
     * @param {number} timeout - Command timeout in ms
     * @returns {Promise} - Resolves with response, rejects on error or timeout
     */
    /**
     * Execute a command with timeout and response handling
     *
     * @param {string} command - Command to execute
     * @param {number} timeout - Command timeout in ms
     * @returns {Promise} - Resolves with response, rejects on error or timeout
     */
    executeCommand(command, timeout = this.timeout) {
        return new Promise((resolve, reject) => {
            if (!this.socket || this.socket.destroyed) {
                return reject(new Error('Socket not connected'));
            }

            const entry = {
                command,
                timeout,
                resolve,
                reject,
                responseReceived: false, // Track if any response was received
                timer: null,
            };

            // Drop this exact entry from the queue. Identity matters: several callers send
            // the same literal ('STATUS' from the heartbeat, the poll and the refresh
            // button), so matching on the command string could remove the wrong one and
            // orphan its promise.
            const removeEntry = () => {
                const idx = this.commandQueue.indexOf(entry);
                if (idx === -1) {
                    return false;
                }
                this.commandQueue.splice(idx, 1);
                return idx === 0;
            };

            const expire = () => {
                // A partial response means the device is still talking — give it more time
                if (entry.responseReceived) {
                    this.log.info(`Command ${command} received partial response but not completed, extending timeout`);
                    entry.timer = this.setTimeout(() => {
                        this.log.warn(`Command still timed out after extension: ${command}`);
                        if (removeEntry()) {
                            this.processingCommand = false;
                        }
                        reject(new Error('Command timed out after extension'));
                        this.processNextCommand();
                    }, timeout * 0.5); // Add 50% more time
                    return;
                }

                this.log.warn(`Command timed out: ${command}`);
                // Only release the in-flight lock if the entry that expired was the one
                // actually being processed (the head of the queue).
                if (removeEntry()) {
                    this.processingCommand = false;
                }
                reject(new Error('Command timed out'));
                this.processNextCommand();
            };

            entry.timer = this.setTimeout(expire, timeout);
            this.commandQueue.push(entry);

            // Process queue if not already processing
            if (!this.processingCommand) {
                this.processNextCommand();
            }
        });
    }

    /**
     * Handle data received from socket
     *
     * @param {Buffer} data - Raw data received
     */
    handleData(data) {
        // Convert buffer to string and add to existing buffer
        const newData = data.toString();
        this.socketBuffer += newData;

        // Log data receipt for debugging (limit output size)
        if (newData.length > 0) {
            const preview = newData.length > 100 ? `${newData.substring(0, 100)}...` : newData;
            this.log.debug(`Received data (${newData.length} bytes): ${preview.replace(/\r\n/g, '\\r\\n')}`);

            // Mark current command as having received some response
            if (this.processingCommand && this.commandQueue.length > 0) {
                this.commandQueue[0].responseReceived = true;
            }
        }

        // Process buffer for complete lines
        let endIndex;
        while ((endIndex = this.socketBuffer.indexOf('\n')) !== -1) {
            const line = this.socketBuffer.substring(0, endIndex).trim();
            this.socketBuffer = this.socketBuffer.substring(endIndex + 1);

            if (line.length > 0) {
                // Process the received line
                this.log.debug(`Processing line: ${line}`);
                this.processResponse(line);
            }
        }

        // Any data receipt means the connection is alive
        this.resetHeartbeatTimeout();
    }

    /**
     * Process the next command in the queue
     */
    processNextCommand() {
        if (this.processingCommand || this.commandQueue.length === 0) {
            return;
        }

        this.processingCommand = true;
        const cmd = this.commandQueue[0];

        this.log.debug(`Executing command: ${cmd.command}`);

        try {
            // Send command with proper line termination
            const commandToSend = cmd.command.endsWith('\r\n') ? cmd.command : `${cmd.command}\r\n`;
            this.socket.write(commandToSend, 'utf8', err => {
                if (err) {
                    // Handle write error
                    this.clearTimeout(cmd.timer);
                    cmd.reject(new Error(`Failed to send command: ${err.message}`));
                    this.commandQueue.shift();
                    this.processingCommand = false;
                    this.processNextCommand();
                }

                // The command has been sent, wait for response
                // Response handling and command completion is done in processResponse
            });
        } catch (err) {
            // Handle any exceptions
            this.clearTimeout(cmd.timer);
            cmd.reject(new Error(`Exception sending command: ${err.message}`));
            this.commandQueue.shift();
            this.processingCommand = false;
            this.processNextCommand();
        }
    }

    /**
     * Process response and complete current command if appropriate
     *
     * @param {string} line - Response line
     */

    processResponse(line) {
        // Log the line for debugging
        this.log.debug(`Processing response line: ${line.substring(0, 50)}...`);

        // Check if we're collecting transmitter info
        if (this.collectingTxInfo) {
            // Add to buffer
            this.txInfoBuffer += `${line}\n`;

            // Check for end of transmitter info response - the exact pattern
            if (
                line.includes('===========') ||
                line.includes('=================') ||
                line.includes('================================================================')
            ) {
                this.log.debug(`End of transmitter info detected, buffer size: ${this.txInfoBuffer.length} bytes`);

                // Make sure the buffer contains transmitter info
                if (BANNER.input.test(this.txInfoBuffer)) {
                    // Process the complete transmitter info
                    try {
                        this.processTransmitterInfo(this.txInfoBuffer);
                    } catch (err) {
                        this.log.error(`Error processing transmitter info: ${err.message}`);
                        this.log.debug(`Transmitter info buffer: ${this.txInfoBuffer.substring(0, 200)}...`);
                    }
                } else {
                    this.log.warn('Received end marker but buffer does not contain transmitter info');
                }

                // Reset collection
                this.collectingTxInfo = false;
                this.txInfoBuffer = '';
            }
            return;
        }

        // Check if we're collecting receiver info
        if (this.collectingRxInfo) {
            // Add to buffer
            this.rxInfoBuffer += `${line}\n`;

            // Check for end of receiver info response
            if (
                line.includes('===========') ||
                line.includes('=================') ||
                line.includes('================================================================')
            ) {
                this.log.debug(`End of receiver info detected, buffer size: ${this.rxInfoBuffer.length} bytes`);

                // Make sure the buffer contains receiver info
                if (BANNER.output.test(this.rxInfoBuffer)) {
                    // Process the complete receiver info
                    try {
                        this.processReceiverInfo(this.rxInfoBuffer);
                    } catch (err) {
                        this.log.error(`Error processing receiver info: ${err.message}`);
                        this.log.debug(`Receiver info buffer: ${this.rxInfoBuffer.substring(0, 200)}...`);
                    }
                } else {
                    this.log.warn('Received end marker but buffer does not contain receiver info');
                }

                // Reset collection
                this.collectingRxInfo = false;
                this.rxInfoBuffer = '';
            }
            return;
        }

        // Check if this is the start of a transmitter info response
        if (BANNER.input.test(line)) {
            this.log.debug('Starting to collect transmitter info');
            this.collectingTxInfo = true;
            this.txInfoBuffer = `${line}\n`;
            return;
        }

        // Check if this is the start of a receiver info response
        if (BANNER.output.test(line)) {
            this.log.debug('Starting to collect receiver info');
            this.collectingRxInfo = true;
            this.rxInfoBuffer = `${line}\n`;
            return;
        }

        // First, handle the response for command processing
        if (this.processingCommand && this.commandQueue.length > 0) {
            const currentCmd = this.commandQueue[0];
            const cmdStr = currentCmd.command.trim();

            // Check if this is a valid response/completion to the current command
            let commandComplete = false;

            // STATUS-type responses end with separator lines
            if (
                line.includes('=================') ||
                line.includes('================================================================') ||
                BANNER.status.test(line)
            ) {
                commandComplete = true;
            } else if (
                // ACM200 action responses: "[SUCCESS]..." or "[ERROR]..."
                line.includes('[SUCCESS]') ||
                line.includes('[ERROR]') ||
                line.includes('Command not found')
            ) {
                commandComplete = true;
            }

            if (commandComplete) {
                this.log.debug(`Completing command: ${cmdStr}`);
                this.clearTimeout(currentCmd.timer);
                currentCmd.resolve(line);
                this.commandQueue.shift();
                this.processingCommand = false;

                // Small delay before next command so the ACM200 can settle
                this.setTimeout(() => this.processNextCommand(), 100);
            }
        }

        // Now process the line for status data extraction
        if (BANNER.status.test(line)) {
            // Begin collecting status info
            this.statusBuffer = `${line}\n`;
            this.collectingStatus = true;
            this.log.debug('Starting to collect status information');
        } else if (this.collectingStatus) {
            // Append to status buffer
            this.statusBuffer += `${line}\n`;

            // Check if we've reached the end of status
            if (
                line.includes('=================') ||
                line.includes('================================================================')
            ) {
                // Process the complete status response
                this.log.debug('Status collection complete, processing status info');
                this.processStatusInfo(this.statusBuffer);
                this.statusBuffer = '';
                this.collectingStatus = false;
            }
        }
    }

    /**
     * Clean up resources and optionally schedule reconnect
     *
     * @param {boolean} reconnect - Whether to schedule a reconnection attempt
     */
    cleanup(reconnect = true) {
        this.connected = false;
        this.processingCommand = false;
        // Must be cleared here, not just on the paths that reach handleConnect(). A socket
        // that fails before 'connect' (host down, ECONNREFUSED, connect-phase timeout) lands
        // in handleError/handleTimeout -> cleanup(), and if the flag stayed set the scheduled
        // reconnect would hit the "already in progress" guard, return without re-arming, and
        // the instance would never retry again.
        this.connectionInProgress = false;
        this.setState('info.connection', false, true);
        this.setState('system.status.connected', false, true);

        // Clear all timers
        if (this.heartbeatTimer) {
            this.clearInterval(this.heartbeatTimer);
            this.heartbeatTimer = null;
        }

        if (this.heartbeatTimeout) {
            this.clearTimeout(this.heartbeatTimeout);
            this.heartbeatTimeout = null;
        }

        if (this.pollTimer) {
            this.clearTimeout(this.pollTimer);
            this.pollTimer = null;
        }

        // Clear command queue and reject any pending commands
        this.commandQueue.forEach(cmd => {
            this.clearTimeout(cmd.timer);
            cmd.reject(new Error('Connection closed'));
        });
        this.commandQueue = [];

        // Close socket
        if (this.socket) {
            try {
                this.socket.destroy();
            } catch (err) {
                this.log.warn(`Error destroying socket: ${err.message}`);
            }
            this.socket = null;
        }

        // Schedule reconnection if needed
        if (reconnect && !this.reconnectTimer) {
            this.log.info(`Will attempt to reconnect in ${this.reconnectDelay / 1000} seconds`);

            this.reconnectTimer = this.setTimeout(() => {
                this.reconnectTimer = null;
                this.connectToACM();
            }, this.reconnectDelay);
        }
    }

    /**
     * Start polling for device status updates
     */
    startPolling() {
        if (this.pollTimer) {
            this.clearTimeout(this.pollTimer);
        }

        this.pollTimer = this.setTimeout(() => {
            // Check if a full refresh is already running before polling
            this.getStateAsync('system.status.fullRefreshRunning')
                .then(state => {
                    const refreshRunning = state && state.val === true;

                    if (this.connected && !refreshRunning) {
                        // Only refresh status if not already doing a full refresh
                        this.log.debug('Executing regular status poll');
                        this.refreshDeviceStatus();
                    } else if (refreshRunning) {
                        this.log.debug('Skipping regular status poll because full refresh is running');
                    }

                    // Restart polling regardless
                    this.startPolling();
                })
                .catch(err => {
                    this.log.warn(`Error checking refresh status: ${err.message}`);

                    // Default to regular polling on error
                    if (this.connected) {
                        this.refreshDeviceStatus();
                    }

                    this.startPolling();
                });
        }, Number(this.pollInterval));
    }

    /**
     * Refresh the device status
     */
    refreshDeviceStatus() {
        if (!this.connected) {
            return;
        }

        // Don't queue a STATUS poll if there are already commands waiting —
        // sending STATUS while the ACM200 is still processing an action command
        // can garble the response stream
        if (this.commandQueue.length > 0 || this.processingCommand) {
            this.log.debug('Skipping status poll — command queue is busy');
            return;
        }

        // Check if a full refresh is running
        this.getStateAsync('system.status.fullRefreshRunning')
            .then(state => {
                const refreshRunning = state && state.val === true;

                if (refreshRunning) {
                    this.log.debug('Skipping device status refresh because full refresh is running');
                    return;
                }

                // Get system status
                this.executeCommand('STATUS').catch(err => {
                    this.log.error(`Error getting STATUS: ${err.message}`);
                });

                // Update timestamp
                this.setState('system.status.lastUpdate', new Date().toISOString(), true);
            })
            .catch(err => {
                this.log.warn(`Error checking refresh status: ${err.message}`);

                // Default behavior on error - try to get status
                this.executeCommand('STATUS').catch(err => {
                    this.log.error(`Error getting STATUS: ${err.message}`);
                });

                this.setState('system.status.lastUpdate', new Date().toISOString(), true);
            });
    }

    /**
     * Set up scheduled refresh of device information
     *
     * @param {boolean} [skipToday] - Always schedule for tomorrow. Set when re-arming
     *   straight after a run, so a slot near the late edge of the randomised window
     *   cannot trigger a second refresh the same night.
     */
    setupScheduledRefresh(skipToday = false) {
        // Clear any existing scheduled refresh
        if (this.scheduledRefreshTimer) {
            this.clearTimeout(this.scheduledRefreshTimer);
            this.scheduledRefreshTimer = null;
        }

        // Calculate time until the next nightly refresh. The slot is nominally 3am but is
        // spread over 02:45–03:15 by a random offset: a fixed timestamp would make every
        // instance on every host hit its controller at the same moment.
        const now = new Date();
        const nextRefresh = new Date(now);

        nextRefresh.setHours(3, 0, 0, 0);
        if (skipToday || now >= nextRefresh) {
            nextRefresh.setDate(nextRefresh.getDate() + 1);
        }

        // 30 minutes wide, centred on 3am: [-15 min, +15 min)
        const offsetMs = Math.floor(Math.random() * 30 * 60 * 1000) - 15 * 60 * 1000;
        nextRefresh.setTime(nextRefresh.getTime() + offsetMs);

        // A negative offset can pull the slot back before "now" — push it out a day
        if (now >= nextRefresh) {
            nextRefresh.setDate(nextRefresh.getDate() + 1);
        }

        // Calculate milliseconds until next refresh
        const msUntilRefresh = nextRefresh.getTime() - now.getTime();

        this.log.info(
            `Scheduled device information refresh set for ${nextRefresh.toLocaleString()} (in ${Math.round(msUntilRefresh / 1000 / 60)} minutes)`,
        );

        // Update next refresh time state
        this.setState('system.status.nextScheduledRefresh', nextRefresh.toISOString(), true);

        // Schedule the refresh
        this.scheduledRefreshTimer = this.setTimeout(() => {
            this.log.info('Running scheduled device information refresh');

            this.refreshAllDeviceDetails()
                .then(() => {
                    this.log.info('Scheduled refresh completed successfully');
                    // Schedule next refresh
                    this.setupScheduledRefresh(true);
                })
                .catch(err => {
                    this.log.error(`Error during scheduled refresh: ${err.message}`);
                    // Still schedule next refresh despite error
                    this.setupScheduledRefresh(true);
                });
        }, msUntilRefresh);
    }

    /**
     * Refresh all device details (full refresh)
     *
     * @returns {Promise} - Promise that resolves when all refreshes are complete
     */
    refreshAllDeviceDetails() {
        return new Promise((resolve, reject) => {
            if (!this.connected) {
                this.log.warn('Cannot refresh device details, not connected');
                return reject(new Error('Not connected'));
            }

            this.setState('system.status.fullRefreshRunning', true, true);

            // First get the system status to discover all devices
            this.executeCommand('STATUS')
                .then(() => {
                    // Wait for STATUS to be processed, then fetch detailed information
                    this.setTimeout(() => {
                        this.fetchDetailedInformation()
                            .then(() => {
                                this.log.info('Full device refresh completed successfully');
                                this.setState('system.status.lastFullRefresh', new Date().toISOString(), true);
                                this.setState('system.status.fullRefreshRunning', false, true);
                                resolve();
                            })
                            .catch(err => {
                                this.log.error(`Error fetching detailed information: ${err.message}`);
                                this.setState('system.status.fullRefreshRunning', false, true);
                                reject(err);
                            });
                    }, 2000); // 2 second delay to allow STATUS processing
                })
                .catch(err => {
                    this.log.error(`Error getting STATUS: ${err.message}`);
                    this.setState('system.status.fullRefreshRunning', false, true);
                    reject(err);
                });
        });
    }

    /**
     * Fetch detailed information for all transmitters and receivers
     *
     * @returns {Promise} - Promise that resolves when all fetches are complete
     */
    fetchDetailedInformation() {
        if (!this.connected) {
            return Promise.reject(new Error('Not connected'));
        }

        this.log.info('Fetching detailed information for all devices');

        return new Promise((resolve, reject) => {
            const fetchPromises = [];
            const queueDelay = 500; // 500ms between commands to avoid flooding the device

            // Queue transmitter detail fetches with delay
            Object.keys(this.transmitterStates).forEach((txId, index) => {
                fetchPromises.push(
                    new Promise(resolve => {
                        this.setTimeout(() => {
                            this.fetchTransmitterDetails(txId)
                                .catch(err => this.log.warn(`Error fetching TX ${txId} details: ${err.message}`))
                                .finally(() => resolve());
                        }, index * queueDelay);
                    }),
                );
            });

            // Queue receiver detail fetches with delay (after transmitters)
            const rxStartDelay = Object.keys(this.transmitterStates).length * queueDelay;
            Object.keys(this.receiverStates).forEach((rxId, index) => {
                fetchPromises.push(
                    new Promise(resolve => {
                        this.setTimeout(
                            () => {
                                this.fetchReceiverDetails(rxId)
                                    .catch(err => this.log.warn(`Error fetching RX ${rxId} details: ${err.message}`))
                                    .finally(() => resolve());
                            },
                            rxStartDelay + index * queueDelay,
                        );
                    }),
                );
            });

            // When all fetches are complete
            Promise.all(fetchPromises)
                .then(() => {
                    this.log.info('Completed fetching detailed information for all devices');
                    resolve();
                })
                .catch(err => {
                    this.log.error(`Error during detailed info fetch: ${err.message}`);
                    reject(err);
                });
        });
    }

    /**
     * Fetch detailed information for a specific transmitter
     *
     * @param {string} id - Transmitter ID (e.g., "001")
     * @returns {Promise} - Promise that resolves when the command is sent
     */
    fetchTransmitterDetails(id) {
        if (!this.connected) {
            this.log.warn(`Cannot fetch transmitter details, not connected`);
            return Promise.reject(new Error('Not connected'));
        }

        // Format the command: IN xxx STATUS
        const command = `IN${id.padStart(3, '0')} STATUS`;

        this.log.debug(`Fetching details for transmitter ${id} with command: ${command}`);

        return this.executeCommand(command);
    }

    /**
     * Fetch detailed information for a specific receiver
     *
     * @param {string} id - Receiver ID (e.g., "001")
     * @returns {Promise} - Promise that resolves when the command is sent
     */
    fetchReceiverDetails(id) {
        if (!this.connected) {
            this.log.warn(`Cannot fetch receiver details, not connected`);
            return Promise.reject(new Error('Not connected'));
        }

        // Format the command: OUT xxx STATUS
        const command = `OUT${id.padStart(3, '0')} STATUS`;

        this.log.debug(`Fetching details for receiver ${id} with command: ${command}`);

        return this.executeCommand(command);
    }

    /**
     * Route video from a transmitter to a receiver
     *
     * @param {string} txId - Transmitter ID
     * @param {string} rxId - Receiver ID
     */
    routeVideo(txId, rxId) {
        if (!this.connected) {
            this.log.warn('Cannot route video, not connected');
            return;
        }

        // Single FR command routes both video and audio together.
        const command = this.modelDef.commands.routeVideoAudio(rxId, txId);

        this.executeCommand(command)
            .then(() => {
                this.log.info(`Successfully routed TX ${txId} (audio+video) to RX ${rxId}`);

                // Update the state so it shows correctly in the UI
                this.setState(`receivers.${rxId}.route`, txId, true);
                // Combined route sets both audio and video to the same source
                this.setState(`receivers.${rxId}.videoRoute`, txId, true);
                this.setState(`receivers.${rxId}.audioRoute`, txId, true);

                // Also update our internal state
                if (this.receiverStates[rxId]) {
                    this.receiverStates[rxId].currentTx = txId;
                    this.receiverStates[rxId].currentVideoTx = txId;
                    this.receiverStates[rxId].currentAudioTx = txId;
                }

                // Update the receiver's preview URL to show the new source
                if (this.transmitterStates[txId]) {
                    this.updatePreviewUrl(`receivers.${rxId}.previewUrl`, this.transmitterStates[txId].ip).catch(err =>
                        this.log.warn(`Could not update preview URL for RX ${rxId}: ${err.message}`),
                    );
                }
            })
            .catch(err => {
                this.log.error(`Error routing video: ${err.message}`);
            });
    }

    /**
     * Route video only from a transmitter to a receiver (audio breakaway)
     *
     * @param {string} txId - Transmitter ID
     * @param {string} rxId - Receiver ID
     */
    routeVideoOnly(txId, rxId) {
        if (!this.connected) {
            this.log.warn('Cannot route video, not connected');
            return;
        }

        const command = this.modelDef.commands.routeVideo(rxId, txId);

        this.executeCommand(command)
            .then(() => {
                this.log.info(`Successfully routed video from TX ${txId} to RX ${rxId}`);
                this.setState(`receivers.${rxId}.videoRoute`, txId, true);

                if (this.receiverStates[rxId]) {
                    this.receiverStates[rxId].currentVideoTx = txId;
                }

                if (this.transmitterStates[txId]) {
                    this.updatePreviewUrl(`receivers.${rxId}.previewUrl`, this.transmitterStates[txId].ip).catch(err =>
                        this.log.warn(`Could not update preview URL for RX ${rxId}: ${err.message}`),
                    );
                }
            })
            .catch(err => {
                this.log.error(`Error routing video only: ${err.message}`);
            });
    }

    /**
     * Route audio only from a transmitter to a receiver (audio breakaway)
     *
     * @param {string} txId - Transmitter ID
     * @param {string} rxId - Receiver ID
     */
    routeAudioOnly(txId, rxId) {
        if (!this.connected) {
            this.log.warn('Cannot route audio, not connected');
            return;
        }

        const command = this.modelDef.commands.routeAudio(rxId, txId);

        this.executeCommand(command)
            .then(() => {
                this.log.info(`Successfully routed audio from TX ${txId} to RX ${rxId}`);
                this.setState(`receivers.${rxId}.audioRoute`, txId, true);

                if (this.receiverStates[rxId]) {
                    this.receiverStates[rxId].currentAudioTx = txId;
                }
            })
            .catch(err => {
                this.log.error(`Error routing audio only: ${err.message}`);
            });
    }

    /**
     * Route a breakaway stream (IR / RS232 / USB / CEC) from a transmitter to a
     * receiver. Only available on models whose capability table defines the
     * matching command (see lib/models.js).
     *
     * @param {'ir'|'rs232'|'usb'|'cec'} kind - Breakaway stream kind
     * @param {string} txId - Transmitter ID (source)
     * @param {string} rxId - Receiver ID (destination)
     */
    routeBreakaway(kind, txId, rxId) {
        const map = {
            ir: { feature: 'routeIR', build: 'routeIR', state: 'irRoute', label: 'IR' },
            rs232: { feature: 'routeRS232', build: 'routeRS232', state: 'rs232Route', label: 'RS232' },
            usb: { feature: 'routeUSB', build: 'routeUSB', state: 'usbRoute', label: 'USB' },
            cec: { feature: 'routeCEC', build: 'routeCEC', state: 'cecRoute', label: 'CEC' },
        };
        const def = map[kind];
        if (!def) {
            return;
        }
        if (!this.connected) {
            this.log.warn(`Cannot route ${def.label}, not connected`);
            return;
        }
        if (!this.modelDef.features[def.feature]) {
            this.log.warn(`${def.label} routing is not supported on ${this.modelDef.label}`);
            return;
        }

        const command = this.modelDef.commands[def.build](rxId, txId);

        this.executeCommand(command)
            .then(() => {
                this.log.info(`Successfully routed ${def.label} from TX ${txId} to RX ${rxId}`);
                this.setState(`receivers.${rxId}.${def.state}`, txId, true);
            })
            .catch(err => {
                this.log.error(`Error routing ${def.label}: ${err.message}`);
            });
    }

    /**
     * Set a receiver's output power on/off. Model-gated (features.outputPower).
     *
     * @param {string} rxId - Receiver ID
     * @param {boolean} on - true = power on, false = power off
     */
    setOutputPower(rxId, on) {
        if (!this.connected) {
            this.log.warn('Cannot set output power, not connected');
            return;
        }
        if (!this.modelDef.features.outputPower) {
            this.log.warn(`Output power control is not supported on ${this.modelDef.label}`);
            return;
        }

        const command = this.modelDef.commands.outputPower(rxId, on);

        this.executeCommand(command)
            .then(() => {
                this.log.info(`Set receiver ${rxId} power ${on ? 'ON' : 'OFF'}`);
                this.setState(`receivers.${rxId}.power`, on, true);
            })
            .catch(err => {
                this.log.error(`Error setting output power: ${err.message}`);
            });
    }

    /**
     * Set a receiver's output mute on/off. Model-gated (features.outputMute).
     *
     * @param {string} rxId - Receiver ID
     * @param {boolean} on - true = muted, false = unmuted
     */
    setOutputMute(rxId, on) {
        if (!this.connected) {
            this.log.warn('Cannot set output mute, not connected');
            return;
        }
        if (!this.modelDef.features.outputMute) {
            this.log.warn(`Output mute control is not supported on ${this.modelDef.label}`);
            return;
        }

        const command = this.modelDef.commands.outputMute(rxId, on);

        this.executeCommand(command)
            .then(() => {
                this.log.info(`Set receiver ${rxId} mute ${on ? 'ON' : 'OFF'}`);
                this.setState(`receivers.${rxId}.mute`, on, true);
            })
            .catch(err => {
                this.log.error(`Error setting output mute: ${err.message}`);
            });
    }

    /**
     * Set audio source for a transmitter
     *
     * @param {string} txId - Transmitter ID
     * @param {string} source - Audio source: HDMI or ANA
     */
    setTransmitterAudioSource(txId, source) {
        if (!this.connected) {
            this.log.warn('Cannot set audio source, not connected');
            return;
        }

        const validSources = ['HDMI', 'ANA'];
        const upperSource = source.toUpperCase();

        if (!validSources.includes(upperSource)) {
            if (upperSource === 'AUTO') {
                // AUTO is reported by the device (and therefore kept in the states map so it
                // displays), but selecting it causes receiver dropout on IP200UHD-TX.
                this.log.warn(
                    `Audio source "Auto" can be reported by the controller but cannot be set from the adapter (it causes receiver dropout). Choose HDMI or Analogue L/R.`,
                );
            } else {
                this.log.error(`Invalid audio source "${source}". Must be one of: ${validSources.join(', ')}`);
            }
            return;
        }

        const command = this.modelDef.commands.setAudioSource(txId, upperSource);

        this.executeCommand(command)
            .then(() => {
                this.log.info(`Successfully set transmitter ${txId} audio source to ${upperSource}`);
                this.setState(`transmitters.${txId}.audioSource`, upperSource, true);

                if (this.transmitterStates[txId]) {
                    this.transmitterStates[txId].audioSource = upperSource;
                }
            })
            .catch(err => {
                this.log.error(`Error setting audio source: ${err.message}`);
            });
    }

    /**
     * Set a receiver's output-side audio matrix path (`OUT ooo AUDxx`).
     * Model-gated (features.audioMatrix).
     *
     * @param {string} rxId - Receiver ID
     * @param {string} mode - Audio path token (key of AUDIO_OUTPUT_MODES)
     */
    setAudioOutputMode(rxId, mode) {
        if (!this.connected) {
            this.log.warn('Cannot set audio output path, not connected');
            return;
        }
        if (!this.modelDef.features.audioMatrix) {
            this.log.warn(`Audio matrix is not supported on ${this.modelDef.label}`);
            return;
        }
        const upperMode = String(mode).toUpperCase();
        if (!AUDIO_OUTPUT_MODES[upperMode]) {
            this.log.error(
                `Invalid audio output path "${mode}". Must be one of: ${Object.keys(AUDIO_OUTPUT_MODES).join(', ')}`,
            );
            return;
        }

        const command = this.modelDef.commands.audioOutput(rxId, upperMode);

        this.executeCommand(command)
            .then(() => {
                this.log.info(`Set receiver ${rxId} audio output path to ${upperMode}`);
                this.setState(`receivers.${rxId}.audioOutputMode`, upperMode, true);
            })
            .catch(err => {
                this.log.error(`Error setting audio output path: ${err.message}`);
            });
    }

    /**
     * Set a receiver's ARC mode (`OUT ooo ARC xxx`). Model-gated (features.arc).
     *
     * @param {string} rxId - Receiver ID
     * @param {string} mode - ARC mode token (key of ARC_MODES)
     */
    setArcMode(rxId, mode) {
        if (!this.connected) {
            this.log.warn('Cannot set ARC mode, not connected');
            return;
        }
        if (!this.modelDef.features.arc) {
            this.log.warn(`ARC is not supported on ${this.modelDef.label}`);
            return;
        }
        const upperMode = String(mode).toUpperCase();
        if (!ARC_MODES[upperMode]) {
            this.log.error(`Invalid ARC mode "${mode}". Must be one of: ${Object.keys(ARC_MODES).join(', ')}`);
            return;
        }

        const command = this.modelDef.commands.arc(rxId, upperMode);

        this.executeCommand(command)
            .then(() => {
                this.log.info(`Set receiver ${rxId} ARC mode to ${upperMode}`);
                this.setState(`receivers.${rxId}.arcMode`, upperMode, true);
            })
            .catch(err => {
                this.log.error(`Error setting ARC mode: ${err.message}`);
            });
    }

    /**
     * Set a transmitter's input-side audio matrix path (`IN iii AUDxx`).
     * Model-gated (features.audioMatrix).
     *
     * @param {string} txId - Transmitter ID
     * @param {string} mode - Audio path token (key of AUDIO_INPUT_MODES)
     */
    setAudioInputMode(txId, mode) {
        if (!this.connected) {
            this.log.warn('Cannot set audio matrix path, not connected');
            return;
        }
        if (!this.modelDef.features.audioMatrix) {
            this.log.warn(`Audio matrix is not supported on ${this.modelDef.label}`);
            return;
        }
        const upperMode = String(mode).toUpperCase();
        if (!AUDIO_INPUT_MODES[upperMode]) {
            this.log.error(
                `Invalid audio matrix path "${mode}". Must be one of: ${Object.keys(AUDIO_INPUT_MODES).join(', ')}`,
            );
            return;
        }

        const command = this.modelDef.commands.audioInput(txId, upperMode);

        this.executeCommand(command)
            .then(() => {
                this.log.info(`Set transmitter ${txId} audio matrix path to ${upperMode}`);
                this.setState(`transmitters.${txId}.audioMatrixMode`, upperMode, true);
            })
            .catch(err => {
                this.log.error(`Error setting audio matrix path: ${err.message}`);
            });
    }

    /**
     * Process system status information
     *
     * @param {string} data - Status data
     */
    processStatusInfo(data) {
        // Update system information
        this.setState('system.status.lastUpdate', new Date().toISOString(), true);

        // Extract firmware version
        const fwMatch = data.match(/FW Version: ([\d.]+)/);
        if (fwMatch) {
            this.setObjectNotExistsAsync('system.status.firmwareVersion', {
                type: 'state',
                common: {
                    name: 'Firmware Version',
                    type: 'string',
                    role: 'text',
                    read: true,
                    write: false,
                    def: '',
                },
                native: {},
            })
                .then(() => {
                    this.setState('system.status.firmwareVersion', fwMatch[1], true);
                })
                .catch(err => this.log.warn(`Could not store firmware version: ${err.message}`));
        }

        // Try to parse transmitters and receivers regardless of header format
        try {
            this.parseTransmitters(data);
        } catch (err) {
            this.log.error(`Error parsing transmitters: ${err.message}`);
        }

        try {
            this.parseReceivers(data);
        } catch (err) {
            this.log.error(`Error parsing receivers: ${err.message}`);
        }

        // Clean up stale devices that are no longer reported by the ACM200
        this.removeStaleDevices().catch(err => {
            this.log.warn(`Error cleaning up stale devices: ${err.message}`);
        });
    }

    /**
     * Remove transmitter/receiver objects from ioBroker that are no longer
     * reported by the ACM200 STATUS response.
     */
    async removeStaleDevices() {
        // Only run cleanup once we have discovered at least one device of each type
        // to avoid wiping everything on a malformed STATUS response
        const knownTxIds = Object.keys(this.transmitterStates);
        const knownRxIds = Object.keys(this.receiverStates);

        if (knownTxIds.length === 0 && knownRxIds.length === 0) {
            return;
        }

        // --- Transmitters ---
        try {
            const txChannels = await this.getChannelsOfAsync('transmitters');
            if (txChannels) {
                for (const obj of txChannels) {
                    // obj._id is e.g. "blustream-acm.0.transmitters.007"
                    const idParts = obj._id.split('.');
                    const deviceId = idParts[idParts.length - 1];

                    if (!this.transmitterStates[deviceId]) {
                        this.log.info(`Removing stale transmitter ${deviceId} (no longer reported by controller)`);
                        await this.deleteChannelAsync('transmitters', deviceId);
                        this.forgetPreviewUrl('transmitters', deviceId);
                    }
                }
            }
        } catch (err) {
            this.log.warn(`Error enumerating transmitter channels: ${err.message}`);
        }

        // --- Receivers ---
        try {
            const rxChannels = await this.getChannelsOfAsync('receivers');
            if (rxChannels) {
                for (const obj of rxChannels) {
                    const idParts = obj._id.split('.');
                    const deviceId = idParts[idParts.length - 1];

                    if (!this.receiverStates[deviceId]) {
                        this.log.info(`Removing stale receiver ${deviceId} (no longer reported by controller)`);
                        await this.deleteChannelAsync('receivers', deviceId);
                        this.forgetPreviewUrl('receivers', deviceId);
                    }
                }
            }
        } catch (err) {
            this.log.warn(`Error enumerating receiver channels: ${err.message}`);
        }
    }

    parseTransmitters(data) {
        const lines = data.split('\n');

        // Look for the line containing transmitter headers, with flexible spacing
        const startIdx = lines.findIndex(line => {
            // Match with flexible spacing between words
            return line.match(/In\s+Net\s+Sig/i) || line.match(/In\s+EDID\s+IP/i);
        });

        if (startIdx === -1) {
            this.log.warn('Status response is missing transmitter header');
            return;
        }

        // Log the header for debugging
        this.log.debug(`Found transmitter header: ${lines[startIdx]}`);

        let i = startIdx + 1;
        let parsedCount = 0;

        while (i < lines.length) {
            const line = lines[i].trim();

            // Stop if we reach the output section or end of data
            if (
                line.startsWith('Out') ||
                line.startsWith('LAN') ||
                line === '' ||
                line.includes('=======') ||
                line.includes('Output')
            ) {
                break;
            }

            // The first field must be a number (transmitter ID)
            if (/^\d+\s/.test(line)) {
                // Split by multiple spaces
                const parts = line.split(/\s+/);

                // Only process if we have at least the basic parts (ID, plus status fields)
                if (parts.length >= 3) {
                    const id = parts[0].padStart(3, '0');

                    // Extract fields based on the header format
                    // Assuming format: "In Net Sig Ver EDID MCast Name" from your example

                    let status = false;
                    let edid = '';
                    let ip = '';
                    let model = '';
                    let name = '';
                    let audioSource = '';

                    // Check header format to determine which positions to use
                    if (lines[startIdx].includes('Net') && lines[startIdx].includes('Sig')) {
                        // Format from your example: "In Net Sig Ver EDID MCast Name"
                        status = parts[1] === 'On' && parts[2] === 'On'; // Net and Sig both On

                        if (parts.length >= 5) {
                            edid = parts[4];
                        }

                        // Name is everything after the 6th field
                        if (parts.length >= 7) {
                            name = parts.slice(6).join(' ');
                        }
                    } else if (lines[startIdx].includes('EDID') && lines[startIdx].includes('IP')) {
                        // Format: "In EDID IP NET/Sig Model AudioSource"
                        // Example: 007  CP018  169.254.003.007  On /On  IP200  ANA
                        edid = parts[1];
                        ip = parts[2];

                        // Status is "On /On" format - may be split into two parts by whitespace
                        let statusEndIdx = 3;
                        if (parts[3]) {
                            if (parts[3].includes('/')) {
                                // Single part like "On/Off"
                                status = parts[3].includes('On');
                                statusEndIdx = 4;
                            } else if (parts.length > 4 && parts[4] && parts[4].startsWith('/')) {
                                // Split into two parts like "On" "/On"
                                status = parts[3] === 'On' || parts[4].includes('On');
                                statusEndIdx = 5;
                            } else {
                                status = parts[3].includes('On');
                                statusEndIdx = 4;
                            }
                        }

                        // Extract model if available (next field after status)
                        if (parts.length > statusEndIdx && parts[statusEndIdx]) {
                            model = parts[statusEndIdx];
                        }

                        // Extract audio source if available (field after model)
                        // Normalise to uppercase to match command values (HDMI, ANA, AUTO)
                        if (parts.length > statusEndIdx + 1 && parts[statusEndIdx + 1]) {
                            const rawAudio = parts[statusEndIdx + 1].toUpperCase();
                            if (rawAudio === 'AUTO' || rawAudio === 'AUTOMATIC') {
                                audioSource = 'AUTO';
                            } else if (rawAudio === 'HDMI') {
                                audioSource = 'HDMI';
                            } else if (rawAudio.startsWith('ANA')) {
                                audioSource = 'ANA';
                            } else {
                                audioSource = rawAudio;
                            }
                        }
                    }

                    // Create or update transmitter
                    this.createTransmitter(id, ip, edid, status, name, model, audioSource).catch(err =>
                        this.log.warn(`Could not update transmitter ${id}: ${err.message}`),
                    );
                    parsedCount++;

                    this.log.debug(
                        `Parsed transmitter ${id}: status=${status}, edid=${edid}, ip=${ip}, model=${model}, name=${name}, audioSource=${audioSource}`,
                    );
                }
            }

            i++;
        }

        this.log.debug(`Parsed ${parsedCount} transmitters from status response`);
    }

    /**
     * Parse receiver information from status response
     *
     * @param {string} data - Status data
     */
    parseReceivers(data) {
        const lines = data.split('\n');

        // Look for the line containing receiver headers, with flexible spacing
        const startIdx = lines.findIndex(line => {
            // Match with flexible spacing between words
            return line.match(/Out\s+FromIn\s+IP\s+NET\/HDMI/i);
        });

        if (startIdx === -1) {
            this.log.warn('Status response is missing receiver header');
            return;
        }

        let i = startIdx + 1;
        let parsedCount = 0;

        while (i < lines.length) {
            const line = lines[i].trim();

            // Stop if we reach the LAN section or end of data
            if (line.startsWith('LAN') || line === '') {
                break;
            }

            // The first field must be a number (receiver ID)
            if (/^\d+\s/.test(line)) {
                // Split by multiple spaces
                const parts = line.split(/\s+/);

                // Only process if we have at least the basic parts
                if (parts.length >= 5) {
                    const id = parts[0].padStart(3, '0');
                    const currentTx = parts[1].padStart(3, '0');
                    const ip = parts[2];

                    // Status is "On/Off" (single part) or "On /On" (split into two parts)
                    let status = false;
                    let statusEndIdx = 3;
                    if (parts[3]) {
                        if (parts[3].includes('/')) {
                            status = parts[3].startsWith('On');
                            statusEndIdx = 4;
                        } else if (parts.length > 4 && parts[4] && parts[4].startsWith('/')) {
                            status = parts[3] === 'On';
                            statusEndIdx = 5;
                        } else {
                            status = parts[3].startsWith('On');
                            statusEndIdx = 4;
                        }
                    }

                    const resolution = parts[statusEndIdx] || '';

                    // Mode (MX = Matrix, VW = Video Wall)
                    const mode = parts[statusEndIdx + 1] || '';

                    // Try to extract model if available
                    const model = parts[statusEndIdx + 2] || '';

                    // Create or update receiver
                    this.createReceiver(id, ip, currentTx, status, resolution, undefined, mode, model).catch(err =>
                        this.log.warn(`Could not update receiver ${id}: ${err.message}`),
                    );
                    parsedCount++;
                }
            }

            i++;
        }

        this.log.debug(`Parsed ${parsedCount} receivers from status response`);
    }

    /**
     * Process transmitter information
     *
     * @param {string} data - Transmitter data
     */
    processTransmitterInfo(data) {
        this.log.debug(`Processing transmitter info data, length: ${data.length} bytes`);

        // Split into lines for easier processing
        const lines = data
            .split('\n')
            .map(line => line.trim())
            .filter(line => line.length > 0);

        // Find the line with the transmitter ID and data
        let dataLine = '';

        for (let i = 0; i < lines.length; i++) {
            const line = lines[i];
            // Look for a line that starts with digits
            if (/^\d+\s+/.test(line)) {
                dataLine = line;
                break;
            }
        }

        if (!dataLine) {
            this.log.warn('Could not find transmitter data line');
            return;
        }

        this.log.info(`Found data line: "${dataLine}"`);

        // Simple, direct approach - split by whitespace and count fields
        const parts = dataLine.split(/\s+/);

        // We know the format is:
        // [0]    [1]     [2]    [3]     [4]    [5]      [6+]
        // 001    On      On     A7.4.1  DF003  On       Screen Cloud A

        if (parts.length < 7) {
            this.log.warn(`Data line has too few parts: ${parts.length}`);
            return;
        }

        const id = this.sanitizeDeviceId(parts[0]);
        if (!id) {
            this.log.warn(`Ignoring transmitter info with invalid ID "${parts[0]}"`);
            return;
        }
        const netStatus = parts[1] === 'On';
        const sigStatus = parts[2] === 'On';
        const version = parts[3];
        const edid = parts[4];

        // Everything from index 6 onwards is the name
        const name = parts.slice(6).join(' ');

        // Status is both net and sig being on
        const status = netStatus && sigStatus;

        // Find IP address
        let ip = '';
        for (let i = 0; i < lines.length; i++) {
            if (lines[i].includes('.')) {
                const ipMatch = lines[i].match(/(\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3})/);
                if (ipMatch) {
                    ip = ipMatch[1];
                    break;
                }
            }
        }

        // Find MAC address
        let mac = '';
        for (let i = 0; i < lines.length; i++) {
            const macMatch = lines[i].match(
                /([0-9A-Fa-f]{2}:[0-9A-Fa-f]{2}:[0-9A-Fa-f]{2}:[0-9A-Fa-f]{2}:[0-9A-Fa-f]{2}:[0-9A-Fa-f]{2})/,
            );
            if (macMatch) {
                mac = macMatch[0];
                break;
            }
        }

        this.log.debug(
            `Extracted data for TX ${id}: name="${name}" ip=${ip} status=${status} edid=${edid} version=${version} mac=${mac}`,
        );

        // Create all objects first to avoid warnings
        this.ensureTransmitterObjects(id)
            .then(() => {
                // Update all states
                this.setState(`transmitters.${id}.id`, id, true);
                this.setState(`transmitters.${id}.name`, name, true);
                this.setState(`transmitters.${id}.ip`, ip, true);
                this.setState(`transmitters.${id}.connected`, status, true);
                this.setState(`transmitters.${id}.edid`, edid, true);
                this.setState(`transmitters.${id}.version`, version, true);
                this.setState(`transmitters.${id}.mac`, mac, true);

                // Update channel name
                this.extendObject(`transmitters.${id}`, {
                    common: {
                        name: name || `Transmitter ${id}`,
                    },
                }).catch(err => this.log.warn(`Could not rename transmitter ${id}: ${err.message}`));
            })
            .catch(err => {
                this.log.error(`Error processing transmitter ${id}: ${err.message}`);
            });
    }

    /**
     * Ensure all transmitter objects exist
     *
     * @param {string} id - Transmitter ID
     * @returns {Promise} - Promise that resolves when all objects are created
     */
    async ensureTransmitterObjects(id) {
        const prefix = `transmitters.${id}`;

        // Create main channel
        await this.setObjectNotExists(prefix, {
            type: 'channel',
            common: {
                name: `Transmitter ${id}`,
            },
            native: {},
        });

        // Create all states
        const states = [
            { id: 'id', name: 'Transmitter ID', type: 'string', role: 'text' },
            { id: 'name', name: 'Transmitter Name', type: 'string', role: 'info.name' },
            { id: 'ip', name: 'IP Address', type: 'string', role: 'info.ip' },
            { id: 'connected', name: 'Connected', type: 'boolean', role: 'indicator.reachable' },
            { id: 'edid', name: 'EDID Setting', type: 'string', role: 'text' },
            {
                id: 'audioSource',
                name: 'Audio Source',
                type: 'string',
                role: 'text',
                write: true,
                states: { AUTO: 'Auto', HDMI: 'HDMI', ANA: 'Analogue L/R' },
            },
            // Tier 3 — audio matrix (input side)
            {
                id: 'audioMatrixMode',
                name: 'Audio Matrix Path',
                type: 'string',
                role: 'text',
                write: true,
                feature: 'audioMatrix',
                states: AUDIO_INPUT_MODES,
            },
            { id: 'version', name: 'Firmware Version', type: 'string', role: 'info.firmware' },
            { id: 'mac', name: 'MAC Address', type: 'string', role: 'info.mac' },
            { id: 'model', name: 'Product Model', type: 'string', role: 'info.model' },
            { id: 'previewUrl', name: 'Preview Image URL', type: 'string', role: 'url' },
        ];

        for (const state of states) {
            if (state.feature && !this.modelDef.features[state.feature]) {
                continue;
            }
            const common = {
                name: state.name,
                type: state.type,
                role: state.role,
                read: true,
                write: state.write || false,
                def: state.type === 'boolean' ? false : state.type === 'number' ? 0 : '',
            };
            if (state.states) {
                common.states = state.states;
            }
            await this.setObjectNotExists(`${prefix}.${state.id}`, {
                type: 'state',
                common,
                native: {},
            });
        }
    }

    /**
     * Push the current name/description onto the two refresh command objects.
     * `setObjectNotExists` leaves an existing object untouched, so installs created
     * before a wording change would keep the old (in this case actively misleading)
     * label forever. Only the text is written; role/type/def stay as created.
     *
     * @returns {Promise<void>} resolves once both objects have been checked
     */
    async syncCommandLabels() {
        for (const [id, labels] of Object.entries(REFRESH_LABELS)) {
            try {
                const obj = await this.getObjectAsync(id);
                if (!obj || (obj.common.name === labels.name && obj.common.desc === labels.desc)) {
                    continue;
                }
                await this.extendObjectAsync(id, { common: { ...labels } });
                this.log.debug(`Updated label and description for ${id}`);
            } catch (err) {
                this.log.warn(`Could not update label for ${id}: ${err.message}`);
            }
        }
    }

    /**
     * Remove feature-gated states that the currently-configured model does not
     * support. Needed because `setObjectNotExists` never deletes objects, so a
     * model change (e.g. ACM1000 → ACM500 or → ACM200) would otherwise leave
     * orphaned states behind.
     *
     * The maps below must stay in exact sync with the feature-gated entries in
     * `ensureReceiverObjects` / `ensureTransmitterObjects` — every listed leaf is
     * a state the adapter actually creates, and its value is the feature flag
     * that guards it.
     *
     * @returns {Promise<void>} resolves once pruning is complete
     */
    async reconcileModelStates() {
        const feat = this.modelDef.features;
        const gated = {
            receivers: {
                irRoute: 'routeIR',
                rs232Route: 'routeRS232',
                usbRoute: 'routeUSB',
                cecRoute: 'routeCEC',
                power: 'outputPower',
                mute: 'outputMute',
                audioOutputMode: 'audioMatrix',
                arcMode: 'arc',
            },
            transmitters: {
                audioMatrixMode: 'audioMatrix',
            },
        };

        for (const [deviceType, leaves] of Object.entries(gated)) {
            let objs;
            try {
                objs = await this.getForeignObjectsAsync(`${this.namespace}.${deviceType}.*`, 'state');
            } catch (err) {
                this.log.warn(`Could not enumerate ${deviceType} states for model reconciliation: ${err.message}`);
                continue;
            }
            for (const fullId of Object.keys(objs)) {
                const leaf = fullId.split('.').pop();
                const feature = leaves[leaf];
                if (feature && !feat[feature]) {
                    try {
                        await this.delForeignObjectAsync(fullId);
                        this.log.info(`Removed state ${fullId}: not supported by model ${this.modelDef.label}`);
                    } catch (err) {
                        this.log.warn(`Could not remove state ${fullId}: ${err.message}`);
                    }
                }
            }
        }
    }

    /**
     * Process receiver information
     *
     * @param {string} data - Receiver data
     */
    processReceiverInfo(data) {
        this.log.debug(`Processing receiver info data, length: ${data.length} bytes`);

        // Verify this is a receiver info response
        if (!BANNER.output.test(data)) {
            this.log.warn('Not a valid receiver info response');
            return;
        }

        // Split into lines for easier processing - keep all lines
        const lines = data.split('\n');

        // Log the first few lines for debugging
        for (let i = 0; i < Math.min(10, lines.length); i++) {
            this.log.debug(`Line ${i}: "${lines[i].trim()}"`);
        }

        // Find the header line and the data line
        let headerLine = '';
        let dataLine = '';

        for (let i = 0; i < lines.length; i++) {
            const trimmed = lines[i].trim();

            // Find the header line that contains "Out Net HPD Ver"
            if (trimmed.startsWith('Out') && trimmed.includes('Net') && trimmed.includes('HPD')) {
                headerLine = trimmed;
                // The next line should be the data line
                if (i + 1 < lines.length) {
                    dataLine = lines[i + 1].trim();
                    break;
                }
            }
        }

        if (!headerLine || !dataLine) {
            this.log.warn('Could not find header or data line');
            this.log.warn(`Total lines: ${lines.length}`);
            return;
        }

        this.log.debug(`Header line: "${headerLine}"`);
        this.log.debug(`Data line: "${dataLine}"`);

        // Split the data line by whitespace
        const parts = dataLine.split(/\s+/);

        // We need at least the ID
        if (parts.length < 1) {
            this.log.warn(`Data line has too few parts: ${parts.length}`);
            return;
        }

        const id = this.sanitizeDeviceId(parts[0]);
        if (!id) {
            this.log.warn(`Ignoring receiver info with invalid ID "${parts[0]}"`);
            return;
        }
        this.log.debug(`Found receiver ID: ${id}`);

        // Extract other fields if available
        let netStatus = false;
        let hpdStatus = false;
        let version = '';
        let mode = '';
        let resolution = '';
        let name = '';

        if (parts.length >= 2) {
            netStatus = parts[1] === 'On';
        }

        if (parts.length >= 3) {
            hpdStatus = parts[2] === 'On';
        }

        if (parts.length >= 4) {
            version = parts[3];
        }

        if (parts.length >= 5) {
            mode = parts[4];
        }

        if (parts.length >= 6) {
            resolution = parts[5];
        }

        // Name is everything from position 7 onwards
        if (parts.length >= 8) {
            name = parts.slice(7).join(' ');
        }

        // Status is both net and hpd being on
        const status = netStatus && hpdStatus;

        // Find the current source (transmitter ID)
        let currentTx = '';
        for (let i = 0; i < lines.length; i++) {
            const line = lines[i].trim();
            if (line.includes('Fr') && line.includes('Vid/Aud')) {
                // The next line should contain the source
                if (i + 1 < lines.length) {
                    const srcLine = lines[i + 1].trim();
                    const srcParts = srcLine.split(/\s+/);
                    // Find the first 3-digit number
                    for (const part of srcParts) {
                        if (/^\d{3}$/.test(part)) {
                            currentTx = part;
                            this.log.debug(`Found source TX: ${currentTx}`);
                            break;
                        }
                    }
                }
                break;
            }
        }

        // Find IP address
        let ip = '';
        for (let i = 0; i < lines.length; i++) {
            const line = lines[i].trim();
            if (line.includes('.') && line.match(/\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}/)) {
                const ipMatch = line.match(/(\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3})/);
                if (ipMatch) {
                    ip = ipMatch[1];
                    this.log.debug(`Found IP: ${ip}`);
                    break;
                }
            }
        }

        // Find MAC address
        let mac = '';
        for (let i = 0; i < lines.length; i++) {
            const line = lines[i].trim();
            const macMatch = line.match(
                /([0-9A-Fa-f]{2}:[0-9A-Fa-f]{2}:[0-9A-Fa-f]{2}:[0-9A-Fa-f]{2}:[0-9A-Fa-f]{2}:[0-9A-Fa-f]{2})/,
            );
            if (macMatch) {
                mac = macMatch[0];
                this.log.debug(`Found MAC: ${mac}`);
                break;
            }
        }

        this.log.debug(
            `Extracted data for RX ${id}: name="${name}" ip=${ip} status=${status} tx=${currentTx} ` +
                `resolution=${resolution} mode=${mode} version=${version} mac=${mac}`,
        );

        // Ensure objects exist before updating states
        this.ensureReceiverObjects(id)
            .then(() => {
                // Update all states
                this.setState(`receivers.${id}.id`, id, true);
                this.setState(`receivers.${id}.name`, name, true);
                this.setState(`receivers.${id}.ip`, ip, true);
                this.setState(`receivers.${id}.connected`, status, true);

                if (currentTx) {
                    this.setState(`receivers.${id}.route`, currentTx, true);
                }

                this.setState(`receivers.${id}.resolution`, resolution, true);
                this.setState(`receivers.${id}.mode`, mode, true);
                this.setState(`receivers.${id}.version`, version, true);
                this.setState(`receivers.${id}.mac`, mac, true);

                // For preview URL, we need the source transmitter's IP
                if (currentTx && this.transmitterStates[currentTx]) {
                    this.updatePreviewUrl(`receivers.${id}.previewUrl`, this.transmitterStates[currentTx].ip).catch(
                        err => this.log.warn(`Could not update preview URL for RX ${id}: ${err.message}`),
                    );
                }

                // Update channel name
                this.extendObject(`receivers.${id}`, {
                    common: {
                        name: name || `Receiver ${id}`,
                    },
                }).catch(err => this.log.warn(`Could not rename receiver ${id}: ${err.message}`));
            })
            .catch(err => {
                this.log.error(`Error processing receiver ${id}: ${err.message}`);
            });
    }

    /**
     * Ensure all receiver objects exist
     *
     * @param {string} id - Receiver ID
     * @returns {Promise} - Promise that resolves when all objects are created
     */
    async ensureReceiverObjects(id) {
        const prefix = `receivers.${id}`;

        // Create main channel
        await this.setObjectNotExists(prefix, {
            type: 'channel',
            common: {
                name: `Receiver ${id}`,
            },
            native: {},
        });

        // Create all states. Entries with a `feature` are only created when the
        // active model supports that capability (see lib/models.js).
        const states = [
            { id: 'id', name: 'Receiver ID', type: 'string', role: 'text' },
            { id: 'name', name: 'Receiver Name', type: 'string', role: 'info.name' },
            { id: 'ip', name: 'IP Address', type: 'string', role: 'info.ip' },
            { id: 'connected', name: 'Connected', type: 'boolean', role: 'indicator.reachable' },
            { id: 'route', name: 'Current Source', type: 'string', role: 'text', write: true },
            { id: 'videoRoute', name: 'Video Source', type: 'string', role: 'text', write: true },
            { id: 'audioRoute', name: 'Audio Source', type: 'string', role: 'text', write: true },
            // Tier 1 — breakaway routing (write the source TX id)
            { id: 'irRoute', name: 'IR Source', type: 'string', role: 'text', write: true, feature: 'routeIR' },
            {
                id: 'rs232Route',
                name: 'RS232 Source',
                type: 'string',
                role: 'text',
                write: true,
                feature: 'routeRS232',
            },
            { id: 'usbRoute', name: 'USB Source', type: 'string', role: 'text', write: true, feature: 'routeUSB' },
            { id: 'cecRoute', name: 'CEC Source', type: 'string', role: 'text', write: true, feature: 'routeCEC' },
            // Tier 2 — per-output control
            {
                id: 'power',
                name: 'Output Power',
                type: 'boolean',
                role: 'switch.power',
                write: true,
                feature: 'outputPower',
            },
            { id: 'mute', name: 'Output Mute', type: 'boolean', role: 'switch', write: true, feature: 'outputMute' },
            // Tier 3 — audio matrix + ARC (output side)
            {
                id: 'audioOutputMode',
                name: 'Audio Output Path',
                type: 'string',
                role: 'text',
                write: true,
                feature: 'audioMatrix',
                states: AUDIO_OUTPUT_MODES,
            },
            {
                id: 'arcMode',
                name: 'ARC Mode',
                type: 'string',
                role: 'text',
                write: true,
                feature: 'arc',
                states: ARC_MODES,
            },
            { id: 'resolution', name: 'Output Resolution', type: 'string', role: 'text' },
            {
                id: 'mode',
                name: 'Operation Mode',
                type: 'string',
                role: 'text',
                states: { MX: 'Matrix', VW: 'Video Wall' },
            },
            { id: 'version', name: 'Firmware Version', type: 'string', role: 'info.firmware' },
            { id: 'mac', name: 'MAC Address', type: 'string', role: 'info.mac' },
            { id: 'model', name: 'Product Model', type: 'string', role: 'info.model' },
            { id: 'previewUrl', name: 'Preview Image URL', type: 'string', role: 'url' },
        ];

        for (const state of states) {
            if (state.feature && !this.modelDef.features[state.feature]) {
                continue;
            }
            const common = {
                name: state.name,
                type: state.type,
                role: state.role,
                read: true,
                write: state.write || false,
                def: state.type === 'boolean' ? false : state.type === 'number' ? 0 : '',
            };
            if (state.states) {
                common.states = state.states;
            }
            await this.setObjectNotExists(`${prefix}.${state.id}`, {
                type: 'state',
                common,
                native: {},
            });
        }
    }

    /**
     * Create or update a transmitter object using setObjectNotExists
     *
     * @param {string} id - Transmitter ID
     * @param {string} ip - IP address
     * @param {string} edid - EDID setting
     * @param {boolean|string} status - Connection status
     * @param {string} name - Optional name
     * @param {string} model - Optional model information
     * @param {string} audioSource - Optional audio source (HDMI/ANA/AUTO)
     */
    async createTransmitter(id, ip, edid, status, name, model, audioSource) {
        const txId = `transmitters.${id}`;
        let statusBool = false;

        if (typeof status === 'string') {
            statusBool = status.includes('On');
        } else {
            statusBool = !!status;
        }

        // Ensure all objects exist (single source of truth: ensureTransmitterObjects)
        await this.ensureTransmitterObjects(id);

        // Save the transmitter info to our internal state
        if (!this.transmitterStates[id]) {
            this.transmitterStates[id] = {
                id,
                ip,
                status: statusBool,
                edid,
                model: model || '',
                name: name || `Transmitter ${id}`,
            };
        }

        // Update state values
        await this.setState(`${txId}.id`, id, true);
        await this.setState(`${txId}.ip`, ip, true);
        await this.setState(`${txId}.connected`, statusBool, true);

        if (edid) {
            await this.setState(`${txId}.edid`, edid, true);
        }

        if (model) {
            await this.setState(`${txId}.model`, model, true);
            // Update internal state
            this.transmitterStates[id].model = model;
        }

        if (audioSource) {
            // STATUS is ground truth — always update to reflect the actual device state
            await this.setState(`${txId}.audioSource`, audioSource, true);
            this.transmitterStates[id].audioSource = audioSource;
        }

        if (name) {
            await this.setState(`${txId}.name`, name, true);

            // Also update the channel name if it changed
            await this.extendObjectAsync(txId, {
                common: {
                    name: name,
                },
            });
        }

        // Generate a preview URL - format as provided by user
        await this.updatePreviewUrl(`${txId}.previewUrl`, ip);

        // Update our internal state
        this.transmitterStates[id] = {
            ...this.transmitterStates[id],
            ip,
            status: statusBool,
            edid,
            name: name || this.transmitterStates[id].name,
        };
    }

    /**
     * Create or update a receiver object using setObjectNotExists
     *
     * @param {string} id - Receiver ID
     * @param {string} ip - IP address
     * @param {string} currentTx - Current transmitter ID
     * @param {boolean|string} status - Connection status
     * @param {string} resolution - Output resolution
     * @param {string} name - Optional name
     * @param {string} mode - Optional mode information
     * @param {string} model - Optional model information
     */
    async createReceiver(id, ip, currentTx, status, resolution, name, mode, model) {
        const rxId = `receivers.${id}`;
        let statusBool = false;

        if (typeof status === 'string') {
            statusBool = status.includes('On');
        } else {
            statusBool = !!status;
        }

        // Ensure all objects exist (single source of truth: ensureReceiverObjects)
        await this.ensureReceiverObjects(id);

        // Save the receiver info to our internal state
        if (!this.receiverStates[id]) {
            this.receiverStates[id] = {
                id,
                ip,
                status: statusBool,
                currentTx,
                resolution,
                mode: mode || '',
                model: model || '',
                name: name || `Receiver ${id}`,
            };
        }

        // Update state values
        await this.setState(`${rxId}.id`, id, true);
        await this.setState(`${rxId}.ip`, ip, true);
        await this.setState(`${rxId}.connected`, statusBool, true);
        await this.setState(`${rxId}.route`, currentTx, true);
        // STATUS only reports one FromIn value — keep video/audio route states in sync
        await this.setState(`${rxId}.videoRoute`, currentTx, true);
        await this.setState(`${rxId}.audioRoute`, currentTx, true);

        if (resolution) {
            await this.setState(`${rxId}.resolution`, resolution, true);
        }

        if (mode) {
            await this.setState(`${rxId}.mode`, mode, true);
            // Update internal state
            this.receiverStates[id].mode = mode;
        }

        if (model) {
            await this.setState(`${rxId}.model`, model, true);
            // Update internal state
            this.receiverStates[id].model = model;
        }

        if (name) {
            await this.setState(`${rxId}.name`, name, true);

            // Also update the channel name if it changed
            await this.extendObjectAsync(rxId, {
                common: {
                    name: name,
                },
            });
        }

        // For Receiver preview, we need to use the connected transmitter's IP
        let sourceIp = '';
        if (this.transmitterStates[currentTx]) {
            sourceIp = this.transmitterStates[currentTx].ip;
        }

        // Generate a preview URL - only if we have a source IP
        await this.updatePreviewUrl(`${rxId}.previewUrl`, sourceIp);

        // Update our internal state
        this.receiverStates[id] = {
            ...this.receiverStates[id],
            ip,
            status: statusBool,
            currentTx,
            currentVideoTx: currentTx,
            currentAudioTx: currentTx,
            resolution,
            name: name || this.receiverStates[id].name,
        };
    }

    /**
     * Route video from a transmitter to all receivers
     *
     * @param {string} txId - Transmitter ID
     */
    routeVideoToAll(txId) {
        if (!this.connected) {
            this.log.warn('Cannot route video, not connected');
            return;
        }

        // Single FR command routes both video and audio together to all outputs (ooo=000).
        const command = this.modelDef.commands.routeVideoAudio('000', txId);

        this.executeCommand(command)
            .then(() => {
                this.log.info(`Successfully routed TX ${txId} (audio+video) to all receivers`);

                // Get source IP for preview URLs
                let sourceIp = '';
                if (this.transmitterStates[txId]) {
                    sourceIp = this.transmitterStates[txId].ip;
                }

                // Update all receiver states
                for (const rxId in this.receiverStates) {
                    this.setState(`receivers.${rxId}.route`, txId, true);
                    this.setState(`receivers.${rxId}.videoRoute`, txId, true);
                    this.setState(`receivers.${rxId}.audioRoute`, txId, true);
                    this.receiverStates[rxId].currentTx = txId;
                    this.receiverStates[rxId].currentVideoTx = txId;
                    this.receiverStates[rxId].currentAudioTx = txId;

                    // Update preview URL if we have a source IP
                    this.updatePreviewUrl(`receivers.${rxId}.previewUrl`, sourceIp).catch(err =>
                        this.log.warn(`Could not update preview URL for RX ${rxId}: ${err.message}`),
                    );
                }
            })
            .catch(err => {
                this.log.error(`Error routing video to all: ${err.message}`);
            });
    }

    /**
     * Route video only from a transmitter to all receivers
     *
     * @param {string} txId - Transmitter ID
     */
    routeVideoOnlyToAll(txId) {
        if (!this.connected) {
            this.log.warn('Cannot route video, not connected');
            return;
        }

        // ooo=000 selects all output ports (video only)
        const command = this.modelDef.commands.routeVideo('000', txId);

        this.executeCommand(command)
            .then(() => {
                this.log.info(`Successfully routed video from TX ${txId} to all receivers`);

                for (const rxId in this.receiverStates) {
                    this.setState(`receivers.${rxId}.videoRoute`, txId, true);
                    this.receiverStates[rxId].currentVideoTx = txId;

                    if (this.transmitterStates[txId]) {
                        this.updatePreviewUrl(`receivers.${rxId}.previewUrl`, this.transmitterStates[txId].ip).catch(
                            err => this.log.warn(`Could not update preview URL for RX ${rxId}: ${err.message}`),
                        );
                    }
                }
            })
            .catch(err => {
                this.log.error(`Error routing video to all: ${err.message}`);
            });
    }

    /**
     * Route audio only from a transmitter to all receivers
     *
     * @param {string} txId - Transmitter ID
     */
    routeAudioToAll(txId) {
        if (!this.connected) {
            this.log.warn('Cannot route audio, not connected');
            return;
        }

        // ooo=000 selects all output ports (audio only)
        const command = this.modelDef.commands.routeAudio('000', txId);

        this.executeCommand(command)
            .then(() => {
                this.log.info(`Successfully routed audio from TX ${txId} to all receivers`);

                for (const rxId in this.receiverStates) {
                    this.setState(`receivers.${rxId}.audioRoute`, txId, true);
                    this.receiverStates[rxId].currentAudioTx = txId;
                }
            })
            .catch(err => {
                this.log.error(`Error routing audio to all: ${err.message}`);
            });
    }
}

// @ts-expect-error parent is a valid property on module
if (module.parent) {
    // Export the constructor in compact mode
    module.exports = options => new BlustreamAcm(options);
} else {
    // otherwise start the instance directly
    new BlustreamAcm();
}
