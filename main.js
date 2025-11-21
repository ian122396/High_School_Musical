const express = require('express');
const http = require('http');
const path = require('path');
const fs = require('fs/promises');
const cookie = require('cookie');
const { Server } = require('socket.io');
const { v4: uuidv4 } = require('uuid');
const QRCode = require('qrcode');
const bcrypt = require('bcryptjs');

const PORT = process.env.PORT || 3000;
const DATA_FILE = path.join(__dirname, 'data', 'state.json');
const LOCK_TIMEOUT_MS = 2 * 60 * 1000;
const SESSION_COOKIE_NAME = 'sessionId';
const SESSION_TTL_MS = 12 * 60 * 60 * 1000;
const DEFAULT_ADMIN_USERNAME = process.env.ADMIN_USERNAME || 'admin';
const DEFAULT_ADMIN_PASSWORD = process.env.ADMIN_PASSWORD || 'admin123';
const DEFAULT_SALES_USERNAME = process.env.SALES_USERNAME || 'sales';
const DEFAULT_SALES_PASSWORD = process.env.SALES_PASSWORD || 'sales123';
const PASSWORD_SALT_ROUNDS = 10;

const app = express();
const server = http.createServer(app);
const io = new Server(server);
const JSON_BODY_LIMIT = process.env.JSON_BODY_LIMIT || '12mb';
const MAX_MERCH_IMAGE_BYTES = 10 * 1024 * 1024;
const MERCH_IMAGE_DIR = path.join(__dirname, 'public', 'uploads', 'merch');
const MERCH_IMAGE_URL_PREFIX = '/uploads/merch';
const BACKUP_DIR = path.join(__dirname, 'data', 'backups');
const CHECKIN_LOG_LIMIT = 5000;

app.use(express.json({ limit: JSON_BODY_LIMIT }));

/**
 * @typedef {Object} Seat
 * @property {number} row
 * @property {number} col
 * @property {'disabled'|'available'|'locked'|'sold'} status
 * @property {number|null} price
 * @property {string|null} ticketCode
 * @property {string|null} seatLabel
 * @property {string|null} lockedBy
 * @property {number|null} lockExpiresAt
 * @property {number|null} issuedAt
 */

/**
 * @typedef {Object} Project
 * @property {string} id
 * @property {string} name
 * @property {number} rows
 * @property {number} cols
 * @property {number} createdAt
 * @property {number} updatedAt
 * @property {Record<string, Seat>} seats
 */

/** @type {{
 *  projects: Record<string, Project>,
 *  accounts: Record<string, {username: string, passwordHash: string, role:'admin'|'sales'}>,
 *  merch?: {
 *    products: Record<string, any>,
 *    checkoutModes: Record<string, any>,
 *    orders: Array<any>
 *  }
 * }} */
let state = { projects: {}, accounts: {}, merch: undefined };

/** @type {Map<string, {role:'admin'|'sales', username: string, createdAt: number}>} */
const sessions = new Map();

const seatId = (row, col) => `r${row}-c${col}`;

const PRICE_COLORS = [
  '#2B8A3E',
  '#20639B',
  '#ED553B',
  '#6F42C1',
  '#3CAEA3',
  '#F6AE2D',
  '#FF6B6B',
  '#4C72B0',
  '#9E2B25',
  '#20BF55',
];

const ensureProjectMetadata = (project) => {
  if (!project.priceColorAssignments || typeof project.priceColorAssignments !== 'object') {
    project.priceColorAssignments = {};
  }
  if (!project.seatLabelProgress || typeof project.seatLabelProgress !== 'object') {
    project.seatLabelProgress = {};
  }
};

const ensureMerchState = () => {
  if (!state.merch || typeof state.merch !== 'object') {
    state.merch = { products: {}, checkoutModes: {}, orders: [] };
  }
  if (!state.merch.products || typeof state.merch.products !== 'object') {
    state.merch.products = {};
  }
  if (!state.merch.checkoutModes || typeof state.merch.checkoutModes !== 'object') {
    state.merch.checkoutModes = {};
  }
  if (!Array.isArray(state.merch.orders)) {
    state.merch.orders = [];
  }
  if (!Object.keys(state.merch.checkoutModes).length) {
    const defaultModeId = uuidv4();
    state.merch.checkoutModes[defaultModeId] = {
      id: defaultModeId,
      name: '原价',
      type: 'standard',
      value: 1,
      threshold: null,
      cutAmount: null,
      stackLimit: null,
      description: '按标价结算',
      enabled: true,
      createdAt: Date.now(),
      updatedAt: Date.now(),
    };
  }
};

const ensureMerchImageDir = async () => {
  await fs.mkdir(MERCH_IMAGE_DIR, { recursive: true });
};

const ensureCheckinLogs = () => {
  if (!Array.isArray(state.checkInLogs)) {
    state.checkInLogs = [];
  }
};

const appendCheckinLog = (entry) => {
  ensureCheckinLogs();
  state.checkInLogs.unshift(entry);
  if (state.checkInLogs.length > CHECKIN_LOG_LIMIT) {
    state.checkInLogs.length = CHECKIN_LOG_LIMIT;
  }
};

const ensureSeatCheckinState = (seat) => {
  if (!seat || typeof seat !== 'object') return;
  if (!Object.prototype.hasOwnProperty.call(seat, 'checkedInAt')) {
    seat.checkedInAt = null;
  }
  if (!Object.prototype.hasOwnProperty.call(seat, 'checkedInBy')) {
    seat.checkedInBy = null;
  }
};

const resetSeatCheckin = (seat) => {
  if (!seat) return;
  seat.checkedInAt = null;
  seat.checkedInBy = null;
};

const findSeatByTicketCode = (project, ticketCode) => {
  if (!project || !ticketCode) return null;
  const normalized = String(ticketCode).trim();
  if (!normalized) return null;
  return Object.values(project.seats || {}).find(
    (seat) => seat && typeof seat.ticketNumber === 'string' && seat.ticketNumber.trim() === normalized
  );
};

const buildSeatCheckinPayload = (project, seat) => {
  if (!project || !seat) return null;
  return {
    projectId: project.id,
    projectName: project.name,
    seatId: seatId(seat.row, seat.col),
    row: seat.row,
    col: seat.col,
    seatLabel: seat.seatLabel,
    ticketNumber: seat.ticketNumber,
    price: seat.price,
    status: seat.status,
    issuedAt: seat.issuedAt,
    checkedInAt: seat.checkedInAt,
    checkedInBy: seat.checkedInBy,
  };
};

const computeCheckinStats = (project) => {
  if (!project) return { totalSold: 0, checkedIn: 0 };
  let totalSold = 0;
  let checkedIn = 0;
  Object.values(project.seats || {}).forEach((seat) => {
    if (seat && seat.status === 'sold') {
      totalSold += 1;
      if (seat.checkedInAt) checkedIn += 1;
    }
  });
  return { totalSold, checkedIn };
};

const ensureBackupDir = async () => {
  await fs.mkdir(BACKUP_DIR, { recursive: true });
};

const createStateBackup = async (label = 'backup') => {
  try {
    await ensureBackupDir();
    const timestamp = new Date().toISOString().replace(/[:.]/g, '-');
    const filename = `${timestamp}-${label}.json`;
    const filePath = path.join(BACKUP_DIR, filename);
    await fs.writeFile(filePath, JSON.stringify(state, null, 2), 'utf8');
    return filePath;
  } catch (error) {
    console.error('Failed to create state backup:', error);
    return null;
  }
};

const getExtensionFromMime = (mime) => {
  if (!mime) return '.jpg';
  if (mime.includes('png')) return '.png';
  if (mime.includes('gif')) return '.gif';
  if (mime.includes('webp')) return '.webp';
  if (mime.includes('bmp')) return '.bmp';
  return '.jpg';
};

const deleteMerchImageFile = async (imagePath) => {
  if (!imagePath || typeof imagePath !== 'string') return;
  if (!imagePath.startsWith(MERCH_IMAGE_URL_PREFIX)) return;
  const relativePath = imagePath.replace(/^\//, '');
  const normalizedRelativePath = path.normalize(relativePath);
  if (normalizedRelativePath.startsWith('..')) return;
  const absolutePath = path.join(__dirname, 'public', normalizedRelativePath);
  if (!absolutePath.startsWith(path.join(__dirname, 'public'))) return;
  await fs.unlink(absolutePath).catch(() => {});
};

const saveMerchImageFromDataUrl = async (dataUrl, previousPath = null) => {
  if (!dataUrl || typeof dataUrl !== 'string') return null;
  if (!dataUrl.startsWith('data:')) {
    return dataUrl;
  }
  const match = dataUrl.match(/^data:(image\/[a-zA-Z0-9+.+-]+);base64,(.+)$/);
  if (!match) {
    throw new Error('图片格式无效，请上传常见的图片文件。');
  }
  const mime = match[1].toLowerCase();
  const base64 = match[2];
  const buffer = Buffer.from(base64, 'base64');
  if (buffer.length > MAX_MERCH_IMAGE_BYTES) {
    throw new Error('图片体积过大，请压缩至 10MB 以内后再试。');
  }
  await ensureMerchImageDir();
  const ext = getExtensionFromMime(mime);
  const filename = `${uuidv4()}${ext}`;
  const fullPath = path.join(MERCH_IMAGE_DIR, filename);
  await fs.writeFile(fullPath, buffer);
  if (previousPath && previousPath !== `${MERCH_IMAGE_URL_PREFIX}/${filename}`) {
    await deleteMerchImageFile(previousPath);
  }
  return `${MERCH_IMAGE_URL_PREFIX}/${filename}`;
};

const normalizePriceKey = (price) => (price == null ? null : String(Number(price)));

const getNextPriceColor = (project) => {
  ensureProjectMetadata(project);
  const used = new Set(Object.values(project.priceColorAssignments));
  for (const color of PRICE_COLORS) {
    if (!used.has(color)) return color;
  }
  return PRICE_COLORS[used.size % PRICE_COLORS.length];
};

const ensurePriceColorAssignment = (project, price) => {
  const key = normalizePriceKey(price);
  if (key == null) return null;
  ensureProjectMetadata(project);
  if (!project.priceColorAssignments[key]) {
    project.priceColorAssignments[key] = getNextPriceColor(project);
  }
  return project.priceColorAssignments[key];
};

const refreshPriceAssignments = (project) => {
  ensureProjectMetadata(project);
  Object.values(project.seats).forEach((seat) => {
    if (seat && seat.status !== 'disabled' && seat.price != null) {
      ensurePriceColorAssignment(project, seat.price);
    }
  });
};

const getProductImageSource = (product) => {
  if (!product) return null;
  if (product.imagePath) return product.imagePath;
  if (typeof product.imageData === 'string' && product.imageData.startsWith('data:')) {
    return product.imageData;
  }
  if (typeof product.imageData === 'string' && product.imageData.startsWith(MERCH_IMAGE_URL_PREFIX)) {
    return product.imageData;
  }
  return null;
};

const serializeProduct = (product) => ({
  id: product.id,
  name: product.name,
  price: product.price,
  stock: product.stock,
  description: product.description || '',
  imageData: getProductImageSource(product),
  enabled: product.enabled !== false,
  createdAt: product.createdAt,
  updatedAt: product.updatedAt,
});

const serializeCheckoutMode = (mode) => ({
  id: mode.id,
  name: mode.name,
  type: mode.type,
  value: mode.value,
  threshold: mode.threshold ?? null,
  cutAmount: mode.cutAmount ?? null,
  stackLimit: mode.stackLimit ?? null,
  description: mode.description || '',
  enabled: mode.enabled !== false,
  createdAt: mode.createdAt,
  updatedAt: mode.updatedAt,
});

const normalizeCheckoutModePayload = (payload = {}, existing = null) => {
  const base = existing
    ? {
        name: existing.name,
        type: existing.type,
        value: existing.value,
        threshold: existing.threshold ?? null,
        cutAmount: existing.cutAmount ?? null,
        stackLimit: existing.stackLimit ?? null,
        description: existing.description || '',
        enabled: existing.enabled !== false,
      }
    : {
        name: '',
        type: 'standard',
        value: 1,
        threshold: null,
        cutAmount: null,
        stackLimit: null,
        description: '',
        enabled: true,
      };

  if (payload.name && typeof payload.name === 'string') {
    base.name = payload.name.trim();
  }
  if (payload.description !== undefined) {
    base.description = typeof payload.description === 'string' ? payload.description.trim() : '';
  }
  if (payload.enabled !== undefined) {
    base.enabled = Boolean(payload.enabled);
  }

  if (payload.type && ['standard', 'discount', 'fullcut'].includes(payload.type)) {
    base.type = payload.type;
  }

  if (base.type === 'standard') {
    base.value = 1;
    base.threshold = null;
    base.cutAmount = null;
    base.stackLimit = null;
  } else if (base.type === 'discount') {
    const raw = payload.value ?? payload.discountRate ?? base.value;
    const numeric = Number(raw);
    if (!Number.isFinite(numeric) || numeric <= 0) {
      throw new Error('请输入有效的折扣比例');
    }
    base.value = numeric > 1 ? numeric / 10 : numeric;
    if (base.value <= 0 || base.value > 1) {
      throw new Error('折扣需介于 0-1（或 0-10 折）之间');
    }
    base.threshold = null;
    base.cutAmount = null;
    base.stackLimit = null;
  } else if (base.type === 'fullcut') {
    const threshold = Number(payload.threshold ?? base.threshold);
    const cutAmount = Number(payload.cutAmount ?? base.cutAmount);
    let stackLimit =
      payload.stackLimit === 'unlimited'
        ? 'unlimited'
        : Number(payload.stackLimit ?? base.stackLimit ?? 1);
    if (!Number.isFinite(threshold) || threshold <= 0) {
      throw new Error('满减门槛必须为正数');
    }
    if (!Number.isFinite(cutAmount) || cutAmount <= 0) {
      throw new Error('满减优惠金额必须为正数');
    }
    if (stackLimit === 0) {
      stackLimit = 'unlimited';
    }
    if (stackLimit !== 'unlimited' && (!Number.isFinite(stackLimit) || stackLimit <= 0)) {
      throw new Error('可叠加次数必须大于 0，或设置为无限叠加');
    }
    base.threshold = threshold;
    base.cutAmount = cutAmount;
    base.stackLimit = stackLimit === 'unlimited' ? null : Math.floor(stackLimit);
    base.value = 1;
  }

  return base;
};

const getRowProgress = (project, row) => {
  ensureProjectMetadata(project);
  const key = String(row);
  if (!project.seatLabelProgress[key]) {
    project.seatLabelProgress[key] = { leftNext: 1, rightNext: 2 };
  }
  return project.seatLabelProgress[key];
};

const parseSeatNumber = (seatLabel) => {
  if (!seatLabel) return null;
  const match = seatLabel.match(/^(\d+)排(\d+)号$/);
  if (!match) return null;
  return Number(match[2]);
};

const applyCheckoutModeToTotal = (mode, total) => {
  if (!mode || mode.enabled === false) {
    return { totalAfter: total, discount: 0 };
  }
  if (mode.type === 'discount' || mode.type === 'percentage') {
    const multiplier = Math.min(1, Math.max(0, Number(mode.value) || 1));
    const totalAfter = Math.max(0, Math.round(total * multiplier * 100) / 100);
    return { totalAfter, discount: Math.round((total - totalAfter) * 100) / 100 };
  }
  if (mode.type === 'fullcut') {
    const threshold = Math.max(0, Number(mode.threshold) || 0);
    const cutAmount = Math.max(0, Number(mode.cutAmount) || 0);
    const stackLimit = Number.isFinite(Number(mode.stackLimit))
      ? Math.max(1, Math.floor(Number(mode.stackLimit)))
      : null;
    if (!threshold || !cutAmount) {
      return { totalAfter: total, discount: 0 };
    }
    const possibleStacks = Math.floor(total / threshold);
    const stacks = stackLimit ? Math.min(possibleStacks, stackLimit) : possibleStacks;
    const discount = Math.max(0, Math.min(total, stacks * cutAmount));
    return { totalAfter: total - discount, discount };
  }
  return { totalAfter: total, discount: 0 };
};

const normalizeUsername = (username = '') => username.trim().toLowerCase();

const hashPassword = async (plain) => bcrypt.hash(String(plain), PASSWORD_SALT_ROUNDS);

const verifyPassword = async (plain, hash) => bcrypt.compare(String(plain), hash);

const ensureAccount = async (username, password, role, { overridePassword = false } = {}) => {
  if (!username || !password) return null;
  const key = normalizeUsername(username);
  const existing = state.accounts[key];
  if (existing && !overridePassword) {
    if (existing.role !== role) {
      existing.role = role;
      existing.updatedAt = Date.now();
    }
    return existing;
  }
  const passwordHash = await hashPassword(password);
  const account = {
    username: username.trim(),
    passwordHash,
    role,
    createdAt: existing?.createdAt || Date.now(),
    updatedAt: Date.now(),
  };
  state.accounts[key] = account;
  return account;
};

const getAccount = (username) => state.accounts[normalizeUsername(username)] || null;

const removeAccount = (username) => {
  const key = normalizeUsername(username);
  if (state.accounts[key]) {
    delete state.accounts[key];
    return true;
  }
  return false;
};

const countAccountsByRole = (role) =>
  Object.values(state.accounts).filter((account) => account.role === role).length;

const ensureDefaultAccounts = async () => {
  if (!state.accounts || typeof state.accounts !== 'object') {
    state.accounts = {};
  }
  const accountsArray = Object.values(state.accounts);
  const hasAdmin = accountsArray.some((account) => account.role === 'admin');
  if (!hasAdmin) {
    await ensureAccount(DEFAULT_ADMIN_USERNAME, DEFAULT_ADMIN_PASSWORD, 'admin');
  } else if (!state.accounts[normalizeUsername(DEFAULT_ADMIN_USERNAME)]) {
    await ensureAccount(DEFAULT_ADMIN_USERNAME, DEFAULT_ADMIN_PASSWORD, 'admin');
  }

  const hasSales = accountsArray.some((account) => account.role === 'sales');
  if (!hasSales && DEFAULT_SALES_PASSWORD) {
    await ensureAccount(DEFAULT_SALES_USERNAME, DEFAULT_SALES_PASSWORD, 'sales');
  }
};

const ensureDataFile = async () => {
  try {
    await fs.access(DATA_FILE);
  } catch {
    await fs.mkdir(path.dirname(DATA_FILE), { recursive: true });
    await fs.writeFile(DATA_FILE, JSON.stringify(state, null, 2), 'utf8');
  }
};

const migrateLegacyState = (raw) => {
  if (!raw || typeof raw !== 'object') return null;
  if (raw.projects) return raw;
  const { rows, cols, seats } = raw;
  if (!Number.isInteger(rows) || !Number.isInteger(cols) || rows <= 0 || cols <= 0) {
    return null;
  }
  const projectId = uuidv4();
  return {
    projects: {
      [projectId]: {
        id: projectId,
        name: '默认项目',
        rows,
        cols,
        createdAt: Date.now(),
        updatedAt: Date.now(),
        seats: seats || {},
      },
    },
  };
};

const loadState = async () => {
  try {
    const raw = await fs.readFile(DATA_FILE, 'utf8');
    const parsed = JSON.parse(raw);
    if (parsed && typeof parsed === 'object') {
      const migrated = migrateLegacyState(parsed) || parsed;
      const projects = migrated.projects && typeof migrated.projects === 'object' ? migrated.projects : {};
      const accounts = migrated.accounts && typeof migrated.accounts === 'object' ? migrated.accounts : {};
      state = {
        projects,
        accounts,
        merch: migrated.merch || undefined,
      };
    }
  } catch (error) {
    console.warn('Failed to load state file, using defaults.', error);
  }
  ensureMerchState();
};

const saveState = async () => {
  await fs.writeFile(DATA_FILE, JSON.stringify(state, null, 2), 'utf8');
};

const createEmptyProject = ({ name, rows, cols }) => {
  const id = uuidv4();
  const createdAt = Date.now();
  const seats = {};
  for (let row = 0; row < rows; row += 1) {
    for (let col = 0; col < cols; col += 1) {
      seats[seatId(row, col)] = {
        row,
        col,
        status: 'disabled',
        price: null,
        ticketCode: null,
        seatLabel: null,
        lockedBy: null,
        lockExpiresAt: null,
        issuedAt: null,
        checkedInAt: null,
        checkedInBy: null,
      };
    }
  }
  return {
    id,
    name,
    rows,
    cols,
    createdAt,
    updatedAt: createdAt,
    seats,
    ticketing: {
      mode: 'random',
      sequence: null,
    },
    priceColorAssignments: {},
    seatLabelProgress: {},
  };
};

const generateTicketCode = (projectId, row, col) => {
  const prettyRow = String(row + 1).padStart(2, '0');
  const prettyCol = String(col + 1).padStart(2, '0');
  return `P${projectId.slice(0, 4).toUpperCase()}-${prettyRow}${prettyCol}-${uuidv4()
    .slice(0, 8)
    .toUpperCase()}`;
};

const assignSeatLabels = (project, targetRows = null) => {
  ensureProjectMetadata(project);
  const { rows, cols, seats } = project;
  let rowFilter = null;
  if (targetRows != null) {
    const candidates =
      targetRows instanceof Set
        ? [...targetRows]
        : Array.isArray(targetRows)
        ? targetRows
        : [targetRows];
    rowFilter = new Set();
    candidates.forEach((value) => {
      const index = Number(value);
      if (Number.isInteger(index) && index >= 0 && index < rows) {
        rowFilter.add(index);
      }
    });
    if (rowFilter.size === 0) {
      rowFilter = null;
    }
  }
  const centerLeftIndex = Math.floor((cols - 1) / 2);
  const centerRightIndex = centerLeftIndex + 1;

  for (let row = 0; row < rows; row += 1) {
    if (rowFilter && !rowFilter.has(row)) continue;
    const leftSeats = [];
    const rightSeats = [];

    for (let col = 0; col < cols; col += 1) {
      const id = seatId(row, col);
      const seat = seats[id];
      if (!seat) continue;
      ensureSeatCheckinState(seat);

      if (seat.status === 'disabled') {
        seat.seatLabel = null;
        continue;
      }

      if (col <= centerLeftIndex) {
        leftSeats.push({ seat, col });
      } else {
        rightSeats.push({ seat, col });
      }
    }

    leftSeats
      .sort((a, b) => {
        const distA = centerLeftIndex - a.col;
        const distB = centerLeftIndex - b.col;
        if (distA !== distB) return distA - distB;
        return b.col - a.col;
      })
      .forEach((entry, index) => {
        const labelNumber = 1 + index * 2;
        entry.seat.seatLabel = `${row + 1}排${labelNumber}号`;
      });

    rightSeats
      .sort((a, b) => {
        const distA = a.col - centerRightIndex;
        const distB = b.col - centerRightIndex;
        if (distA !== distB) return distA - distB;
        return a.col - b.col;
      })
      .forEach((entry, index) => {
        const labelNumber = 2 + index * 2;
        entry.seat.seatLabel = `${row + 1}排${labelNumber}号`;
      });

    const progress = getRowProgress(project, row);
    progress.leftNext = leftSeats.length > 0 ? leftSeats.length * 2 + 1 : 1;
    if (progress.leftNext % 2 === 0) progress.leftNext += 1;
    progress.rightNext = rightSeats.length > 0 ? rightSeats.length * 2 + 2 : 2;
    if (progress.rightNext % 2 !== 0) progress.rightNext += 1;
  }
};

const sanitizeSeatsUpdate = (project, updates = []) => {
  const { rows, cols } = project;
  const normalized = {};
  updates.forEach((seat) => {
    if (
      !seat ||
      typeof seat !== 'object' ||
      !Number.isInteger(seat.row) ||
      !Number.isInteger(seat.col)
    ) {
      return;
    }
    if (seat.row < 0 || seat.col < 0 || seat.row >= rows || seat.col >= cols) {
      return;
    }
    const allowedStatuses = ['disabled', 'available', 'locked', 'sold'];
    const status = allowedStatuses.includes(seat.status) ? seat.status : 'disabled';
    const price =
      typeof seat.price === 'number' && Number.isFinite(seat.price) && seat.price >= 0
        ? seat.price
        : null;
    const ticketNumber = typeof seat.ticketNumber === 'string' ? seat.ticketNumber.trim() || null : null;
    normalized[seatId(seat.row, seat.col)] = {
      row: seat.row,
      col: seat.col,
      status,
      price,
      ticketNumber,
    };
  });
  return normalized;
};

const ensureProjectTicketing = (project) => {
  if (!project.ticketing || typeof project.ticketing !== 'object') {
    project.ticketing = { mode: 'random', sequence: null };
  }
  if (!project.ticketing.mode) {
    project.ticketing.mode = 'random';
  }
  if (project.ticketing.mode !== 'sequence') {
    project.ticketing.sequence = null;
  } else {
    project.ticketing.sequence = {
      template: project.ticketing.sequence?.template || null,
      width: project.ticketing.sequence?.width || 0,
      startValue: project.ticketing.sequence?.startValue || 1,
      nextValue:
        typeof project.ticketing.sequence?.nextValue === 'number'
          ? project.ticketing.sequence.nextValue
          : (project.ticketing.sequence?.startValue || 1) - 1,
      maxValue: project.ticketing.sequence?.maxValue || 0,
      prefix: project.ticketing.sequence?.prefix || '',
    };
  }
};

const prepareSequenceState = (project) => {
  ensureProjectTicketing(project);
  if (project.ticketing.mode !== 'sequence') return null;
  const sequence = project.ticketing.sequence;
  if (!sequence || !sequence.template) return null;
  const match = sequence.template.match(/(X+)$/);
  if (!match) return null;
  const width = match[1].length;
  const prefix = sequence.template.slice(0, -width);
  const startValue = parseInt(String(sequence.startValue ?? '1'), 10);
  if (Number.isNaN(startValue)) return null;
  const maxValue = 10 ** width - 1;
  sequence.width = width;
  sequence.prefix = prefix;
  sequence.startValue = startValue;
  sequence.startString = String(sequence.startValue).padStart(width, '0');
  sequence.maxValue = maxValue;
  if (typeof sequence.nextValue !== 'number' || sequence.nextValue < startValue - 1) {
    sequence.nextValue = startValue - 1;
  }
  return sequence;
};

const formatSequenceTicketNumber = (sequence, value) => {
  if (!sequence) return null;
  const digits = String(value).padStart(sequence.width, '0');
  if (digits.length > sequence.width) return null;
  return `${sequence.prefix}${digits}`;
};

const deriveSequenceValue = (sequence, ticketNumber) => {
  if (!sequence || !ticketNumber) return null;
  if (!ticketNumber.startsWith(sequence.prefix)) return null;
  const digits = ticketNumber.slice(sequence.prefix.length);
  if (!/^\d+$/.test(digits) || digits.length !== sequence.width) return null;
  const value = parseInt(digits, 10);
  if (Number.isNaN(value)) return null;
  return value;
};

const assignTicketNumberToSeat = (project, seat, { force = false } = {}) => {
  ensureProjectTicketing(project);
  if (!seat) return;
  if (seat.status === 'disabled') {
    seat.ticketNumber = null;
    seat.ticketCode = null;
    seat.ticketSequenceValue = null;
    return;
  }
  if (!force && seat.ticketNumber) {
    seat.ticketCode = seat.ticketNumber;
    return;
  }
  if (project.ticketing.mode === 'sequence') {
    const sequence = prepareSequenceState(project);
    if (!sequence) {
      const ticketNumber = generateTicketCode(project.id, seat.row, seat.col);
      seat.ticketNumber = ticketNumber;
      seat.ticketCode = ticketNumber;
      seat.ticketSequenceValue = null;
      return;
    }
    const nextValue = sequence.nextValue + 1;
    if (nextValue > sequence.maxValue) {
      throw new Error('票号流水已超出范围');
    }
    sequence.nextValue = nextValue;
    const ticketNumber = formatSequenceTicketNumber(sequence, nextValue);
    seat.ticketNumber = ticketNumber;
    seat.ticketCode = ticketNumber;
    seat.ticketSequenceValue = nextValue;
  } else {
    const ticketNumber = generateTicketCode(project.id, seat.row, seat.col);
    seat.ticketNumber = ticketNumber;
    seat.ticketCode = ticketNumber;
    seat.ticketSequenceValue = null;
  }
};

const ensureSeatTicketNumbers = (project, { force = false } = {}) => {
  ensureProjectTicketing(project);
  const seats = Object.values(project.seats || {}).sort((a, b) => {
    if (a.row !== b.row) return a.row - b.row;
    const numA = parseSeatNumber(a.seatLabel) ?? a.col + 1;
    const numB = parseSeatNumber(b.seatLabel) ?? b.col + 1;
    return numA - numB;
  });
  const sequence = prepareSequenceState(project);
  if (sequence && force) {
    sequence.nextValue = sequence.startValue - 1;
  }
  if (sequence) {
    const activeSeatCount = seats.filter((seat) => seat.status !== 'disabled').length;
    const potentialMax = sequence.startValue - 1 + activeSeatCount;
    if (potentialMax > sequence.maxValue) {
      throw new Error('可用流水号不足以覆盖启用座位数量');
    }
  }
  seats.forEach((seat) => {
    if (sequence) {
      if (seat.ticketNumber && !seat.ticketSequenceValue) {
        const derived = deriveSequenceValue(sequence, seat.ticketNumber);
        if (derived !== null) {
          seat.ticketSequenceValue = derived;
        }
      }
      if (!force && seat.ticketSequenceValue) {
        if (seat.ticketSequenceValue > sequence.nextValue) {
          sequence.nextValue = seat.ticketSequenceValue;
        }
        if (seat.ticketNumber && seat.status !== 'disabled') {
          seat.ticketCode = seat.ticketNumber;
          return;
        }
      }
    }
    if (!force && seat.ticketNumber && seat.status !== 'disabled') {
      seat.ticketCode = seat.ticketNumber;
      return;
    }
    assignTicketNumberToSeat(project, seat, { force });
  });
};

const regenerateSeatTicketNumbers = (project, config = null) => {
  if (config && config.mode === 'sequence') {
    const { template, startValue } = config.sequence || {};
    const match = template && template.match(/(X+)$/);
    if (!match) {
      throw new Error('票号模板必须以连续的 X 结尾');
    }
    const width = match[1].length;
    if (!startValue || String(startValue).length !== width) {
      throw new Error('流水码起始长度需与模板中 X 的数量一致');
    }
    const numericStart = parseInt(String(startValue), 10);
    if (Number.isNaN(numericStart)) {
      throw new Error('流水码起始必须是数字');
    }
    project.ticketing = {
      mode: 'sequence',
      sequence: {
        template,
        width,
        startValue: numericStart,
        nextValue: numericStart - 1,
        maxValue: 10 ** width - 1,
        prefix: template.slice(0, -width),
        startString: String(startValue).padStart(width, '0'),
      },
    };
  } else if (config && config.mode === 'random') {
    project.ticketing = { mode: 'random', sequence: null };
  }
  ensureSeatTicketNumbers(project, { force: true });
};

const releaseSeatLock = (seat) => {
  seat.lockedBy = null;
  seat.lockExpiresAt = null;
  if (seat.status === 'locked') {
    seat.status = 'available';
  }
};

const enforceLockTimeouts = () => {
  const now = Date.now();
  let changedProjects = new Set();
  Object.values(state.projects).forEach((project) => {
    let changed = false;
    Object.values(project.seats).forEach((seat) => {
      if (seat.lockExpiresAt && seat.lockExpiresAt <= now) {
        releaseSeatLock(seat);
        changed = true;
      }
    });
    if (changed) {
      project.updatedAt = Date.now();
      changedProjects.add(project.id);
    }
  });
  if (changedProjects.size > 0) {
    saveState().catch((err) => console.error('Failed to persist state after lock timeout', err));
    changedProjects.forEach((projectId) => broadcastProject(projectId));
  }
};

setInterval(enforceLockTimeouts, 5 * 1000);

const parseSession = (req) => {
  try {
    const cookies = cookie.parse(req.headers.cookie || '');
    const sessionId = cookies[SESSION_COOKIE_NAME];
    if (!sessionId) return null;
    const session = sessions.get(sessionId);
    if (!session) return null;
    if (Date.now() - session.createdAt > SESSION_TTL_MS) {
      sessions.delete(sessionId);
      return null;
    }
    return { ...session, sessionId };
  } catch {
    return null;
  }
};

const setSessionCookie = (res, sessionId) => {
  const cookieValue = cookie.serialize(SESSION_COOKIE_NAME, sessionId, {
    httpOnly: true,
    sameSite: 'lax',
    maxAge: SESSION_TTL_MS / 1000,
    path: '/',
  });
  res.setHeader('Set-Cookie', cookieValue);
};

const clearSessionCookie = (res) => {
  const cookieValue = cookie.serialize(SESSION_COOKIE_NAME, '', {
    httpOnly: true,
    sameSite: 'lax',
    expires: new Date(0),
    path: '/',
  });
  res.setHeader('Set-Cookie', cookieValue);
};

const requireRole = (role) => (req, res, next) => {
  const session = parseSession(req);
  if (!session) {
    return res.status(401).json({ error: '未登录' });
  }
  if (role === 'admin' && session.role !== 'admin') {
    return res.status(403).json({ error: '无权限' });
  }
  req.session = session;
  return next();
};

const requireAnyRole = (req, res, next) => {
  const session = parseSession(req);
  if (!session) {
    return res.status(401).json({ error: '未登录' });
  }
  req.session = session;
  next();
};

const guardPage = (role) => (req, res, next) => {
  const session = parseSession(req);
  if (!session) {
    return res.redirect(`/login.html?role=${role}`);
  }
  if (role === 'admin' && session.role !== 'admin') {
    return res.redirect('/login.html?role=admin');
  }
  if (role === 'sales' && !['sales', 'admin'].includes(session.role)) {
    return res.redirect('/login.html?role=sales');
  }
  next();
};

app.get('/admin.html', guardPage('admin'), (req, res) => {
  res.sendFile(path.join(__dirname, 'public', 'admin.html'));
});

app.get('/sales.html', guardPage('sales'), (req, res) => {
  res.sendFile(path.join(__dirname, 'public', 'sales.html'));
});

app.use(express.static(path.join(__dirname, 'public')));

app.get('/api/auth/session', (req, res) => {
  const session = parseSession(req);
  if (!session) {
    return res.json({ authenticated: false, role: null, username: null });
  }
  return res.json({ authenticated: true, role: session.role, username: session.username });
});

app.post('/api/auth/login', async (req, res) => {
  const { username, password } = req.body || {};
  if (!username || !password) {
    return res.status(400).json({ error: '请输入用户名与密码' });
  }
  const account = getAccount(username);
  if (!account) {
    return res.status(401).json({ error: '用户名或密码错误' });
  }
  const verified = await verifyPassword(password, account.passwordHash).catch(() => false);
  if (!verified) {
    return res.status(401).json({ error: '用户名或密码错误' });
  }
  const sessionId = uuidv4();
  sessions.set(sessionId, {
    role: account.role,
    username: account.username,
    createdAt: Date.now(),
  });
  setSessionCookie(res, sessionId);
  return res.json({ ok: true, role: account.role, username: account.username });
});

app.post('/api/auth/logout', requireAnyRole, (req, res) => {
  if (req.session) {
    sessions.delete(req.session.sessionId);
  }
  clearSessionCookie(res);
  res.json({ ok: true });
});

app.get('/api/accounts', requireRole('admin'), (_req, res) => {
  const accounts = Object.values(state.accounts)
    .map(({ username, role, createdAt, updatedAt }) => ({ username, role, createdAt, updatedAt }))
    .sort((a, b) => {
      if (a.role === b.role) {
        return a.username.localeCompare(b.username);
      }
      return a.role.localeCompare(b.role);
    });
  res.json({ accounts });
});

app.post('/api/accounts', requireRole('admin'), async (req, res) => {
  const { username, password, role } = req.body || {};
  if (!username || typeof username !== 'string' || !password || typeof password !== 'string') {
    return res.status(400).json({ error: '用户名与密码不能为空' });
  }
  if (!['admin', 'sales'].includes(role)) {
    return res.status(400).json({ error: '角色无效' });
  }
  if (state.accounts[normalizeUsername(username)]) {
    return res.status(409).json({ error: '该用户名已存在' });
  }
  await ensureAccount(username, password, role, { overridePassword: true });
  await saveState();
  broadcastAdminUpdate();
  res.json({ ok: true });
});

app.get('/api/merch/products', requireAnyRole, (_req, res) => {
  ensureMerchState();
  const products = Object.values(state.merch.products).map(serializeProduct);
  res.json({ products });
});

app.post('/api/merch/products', requireRole('admin'), async (req, res) => {
  ensureMerchState();
  const { name, price, stock, description, imageData, enabled = true } = req.body || {};
  if (!name || typeof name !== 'string') {
    return res.status(400).json({ error: '请输入商品名称' });
  }
  const numericPrice = Number(price);
  if (!Number.isFinite(numericPrice) || numericPrice < 0) {
    return res.status(400).json({ error: '价格必须为非负数字' });
  }
  const numericStock = Number.isFinite(Number(stock)) ? Math.max(0, Math.floor(Number(stock))) : 0;
  if (numericStock < 0) {
    return res.status(400).json({ error: '库存数量无效' });
  }
  const id = uuidv4();
  let imagePath = null;
  if (imageData) {
    try {
      imagePath = await saveMerchImageFromDataUrl(imageData);
    } catch (error) {
      return res.status(400).json({ error: error.message });
    }
  }
  const product = {
    id,
    name: name.trim(),
    price: Math.round(numericPrice * 100) / 100,
    stock: numericStock,
    description: typeof description === 'string' ? description.trim() : '',
    imageData: null,
    imagePath,
    enabled: Boolean(enabled),
    createdAt: Date.now(),
    updatedAt: Date.now(),
  };
  state.merch.products[id] = product;
  await saveState();
  res.json({ product: serializeProduct(product) });
});

app.put('/api/merch/products/:productId', requireRole('admin'), async (req, res) => {
  ensureMerchState();
  const product = state.merch.products[req.params.productId];
  if (!product) {
    return res.status(404).json({ error: '商品不存在' });
  }
  const payload = req.body || {};
  if (payload.name && typeof payload.name === 'string') {
    product.name = payload.name.trim();
  }
  if (payload.price !== undefined) {
    const numericPrice = Number(payload.price);
    if (!Number.isFinite(numericPrice) || numericPrice < 0) {
      return res.status(400).json({ error: '价格必须为非负数字' });
    }
    product.price = Math.round(numericPrice * 100) / 100;
  }
  if (payload.stock !== undefined) {
    const numericStock = Number.isFinite(Number(payload.stock))
      ? Math.max(0, Math.floor(Number(payload.stock)))
      : null;
    if (numericStock === null) {
      return res.status(400).json({ error: '库存数量无效' });
    }
    product.stock = numericStock;
  }
  if (payload.description !== undefined) {
    product.description = typeof payload.description === 'string' ? payload.description.trim() : '';
  }
  if (payload.imageData !== undefined) {
    if (payload.imageData) {
      try {
        const newPath = await saveMerchImageFromDataUrl(payload.imageData, product.imagePath);
        product.imagePath = newPath;
        product.imageData = null;
      } catch (error) {
        return res.status(400).json({ error: error.message });
      }
    } else {
      await deleteMerchImageFile(product.imagePath);
      product.imagePath = null;
      product.imageData = null;
    }
  }
  if (payload.enabled !== undefined) {
    product.enabled = Boolean(payload.enabled);
  }
  product.updatedAt = Date.now();
  await saveState();
  res.json({ product: serializeProduct(product) });
});

app.delete('/api/merch/products/:productId', requireRole('admin'), async (req, res) => {
  ensureMerchState();
  const product = state.merch.products[req.params.productId];
  if (!product) {
    return res.status(404).json({ error: '商品不存在' });
  }
  createStateBackup(`delete-product-${product.id}`).catch(() => {});
  await deleteMerchImageFile(product.imagePath);
  delete state.merch.products[req.params.productId];
  await saveState();
  res.json({ ok: true });
});

app.get('/api/merch/modes', requireAnyRole, (_req, res) => {
  ensureMerchState();
  const modes = Object.values(state.merch.checkoutModes).map(serializeCheckoutMode);
  res.json({ modes });
});

app.post('/api/merch/modes', requireRole('admin'), async (req, res) => {
  ensureMerchState();
  const { name } = req.body || {};
  if (!name || typeof name !== 'string') {
    return res.status(400).json({ error: '请输入结账模式名称' });
  }
  let definitions;
  try {
    definitions = normalizeCheckoutModePayload(req.body);
  } catch (error) {
    return res.status(400).json({ error: error.message });
  }
  const id = uuidv4();
  const mode = {
    id,
    ...definitions,
    createdAt: Date.now(),
    updatedAt: Date.now(),
  };
  state.merch.checkoutModes[id] = mode;
  await saveState();
  res.json({ mode: serializeCheckoutMode(mode) });
});

app.put('/api/merch/modes/:modeId', requireRole('admin'), async (req, res) => {
  ensureMerchState();
  const mode = state.merch.checkoutModes[req.params.modeId];
  if (!mode) {
    return res.status(404).json({ error: '结账模式不存在' });
  }
  let updated;
  try {
    updated = normalizeCheckoutModePayload(req.body, mode);
  } catch (error) {
    return res.status(400).json({ error: error.message });
  }
  Object.assign(mode, updated, { updatedAt: Date.now() });
  await saveState();
  res.json({ mode: serializeCheckoutMode(mode) });
});

app.delete('/api/merch/modes/:modeId', requireRole('admin'), async (req, res) => {
  ensureMerchState();
  const mode = state.merch.checkoutModes[req.params.modeId];
  if (!mode) {
    return res.status(404).json({ error: '结账模式不存在' });
  }
  createStateBackup(`delete-mode-${mode.id}`).catch(() => {});
  delete state.merch.checkoutModes[req.params.modeId];
  if (!Object.keys(state.merch.checkoutModes).length) {
    await ensureMerchState();
  }
  await saveState();
  res.json({ ok: true });
});

app.get('/api/merch/orders', requireRole('admin'), (req, res) => {
  ensureMerchState();
  const { since, until } = req.query || {};
  const parsedSince = since ? Number(since) : null;
  const parsedUntil = until ? Number(until) : null;
  const orders = state.merch.orders
    .filter((order) => {
      if (parsedSince && order.createdAt < parsedSince) return false;
      if (parsedUntil && order.createdAt > parsedUntil) return false;
      return true;
    })
    .sort((a, b) => b.createdAt - a.createdAt)
    .slice(0, 500);
  res.json({ orders });
});

const requireSalesOrAdmin = (req, res, next) => {
  const session = parseSession(req);
  if (!session) {
    return res.status(401).json({ error: '未登录' });
  }
  if (!['sales', 'admin'].includes(session.role)) {
    return res.status(403).json({ error: '无权限' });
  }
  req.session = session;
  return next();
};

const resolveCheckoutMode = (checkoutModeId) => {
  if (!checkoutModeId) return null;
  const mode = state.merch.checkoutModes[checkoutModeId];
  return mode && mode.enabled !== false ? mode : null;
};

const normalizeOrderItems = (items = []) => {
  if (!Array.isArray(items) || !items.length) {
    throw new Error('请至少添加一条商品记录');
  }
  return items.map((item, index) => {
    if (!item || typeof item !== 'object') {
      throw new Error(`第 ${index + 1} 条商品数据无效`);
    }
    const name = (item.name || item.productName || '').trim();
    if (!name) {
      throw new Error(`第 ${index + 1} 条商品缺少名称`);
    }
    const unitPrice = Number(item.unitPrice ?? item.price);
    if (!Number.isFinite(unitPrice) || unitPrice < 0) {
      throw new Error(`第 ${index + 1} 条商品单价无效`);
    }
    const quantity = Math.max(1, Math.floor(Number(item.quantity) || 0));
    const subtotal = Math.round(unitPrice * quantity * 100) / 100;
    return {
      productId: item.productId || null,
      name,
      quantity,
      unitPrice: Math.round(unitPrice * 100) / 100,
      subtotal,
    };
  });
};

app.post('/api/merch/orders', requireSalesOrAdmin, async (req, res) => {
  ensureMerchState();
  const { items, checkoutModeId, note } = req.body || {};
  if (!Array.isArray(items) || !items.length) {
    return res.status(400).json({ error: '请选择至少一件商品' });
  }
  const parsedItems = [];
  for (const entry of items) {
    if (!entry || typeof entry !== 'object') continue;
    const product = state.merch.products[entry.productId];
    if (!product || product.enabled === false) {
      return res.status(400).json({ error: '存在无效商品' });
    }
    const quantity = Math.max(1, Math.floor(Number(entry.quantity) || 0));
    if (product.stock < quantity) {
      return res.status(400).json({ error: `商品「${product.name}」库存不足` });
    }
    parsedItems.push({ product, quantity });
  }
  if (!parsedItems.length) {
    return res.status(400).json({ error: '未找到有效商品' });
  }

  const mode = checkoutModeId ? state.merch.checkoutModes[checkoutModeId] : null;
  if (checkoutModeId && !mode) {
    return res.status(400).json({ error: '结账模式不存在' });
  }

  let totalBefore = 0;
  const orderItems = parsedItems.map(({ product, quantity }) => {
    const subtotal = Math.round(product.price * quantity * 100) / 100;
    totalBefore += subtotal;
    return {
      productId: product.id,
      name: product.name,
      quantity,
      unitPrice: product.price,
      subtotal,
    };
  });
  totalBefore = Math.round(totalBefore * 100) / 100;
  const { totalAfter, discount } = applyCheckoutModeToTotal(mode, totalBefore);

  parsedItems.forEach(({ product, quantity }) => {
    product.stock -= quantity;
    if (product.stock < 0) product.stock = 0;
    product.updatedAt = Date.now();
  });

  const order = {
    id: uuidv4(),
    items: orderItems,
    checkoutModeId: mode ? mode.id : null,
    checkoutModeName: mode ? mode.name : '原价',
    discount,
    totalBefore,
    totalAfter: Math.round(totalAfter * 100) / 100,
    handledBy: req.session?.username || 'unknown',
    note: typeof note === 'string' ? note.trim() : '',
    createdAt: Date.now(),
  };
  state.merch.orders.unshift(order);
  state.merch.orders = state.merch.orders.slice(0, 2000);
  await saveState();
  res.json({ order });
});

app.post('/api/merch/orders/manual', requireRole('admin'), async (req, res) => {
  ensureMerchState();
  let orderItems;
  try {
    orderItems = normalizeOrderItems(req.body?.items);
  } catch (error) {
    return res.status(400).json({ error: error.message });
  }
  const mode = resolveCheckoutMode(req.body?.checkoutModeId);
  const totalBefore =
    Math.round(orderItems.reduce((sum, item) => sum + item.subtotal, 0) * 100) / 100;
  const { totalAfter, discount } = applyCheckoutModeToTotal(mode, totalBefore);
  const handledBy =
    typeof req.body?.handledBy === 'string' && req.body.handledBy.trim()
      ? req.body.handledBy.trim()
      : req.session?.username || 'admin';
  const order = {
    id: uuidv4(),
    items: orderItems,
    checkoutModeId: mode ? mode.id : null,
    checkoutModeName: mode ? mode.name : '原价',
    discount,
    totalBefore,
    totalAfter: Math.round(totalAfter * 100) / 100,
    handledBy,
    note: typeof req.body?.note === 'string' ? req.body.note.trim() : '',
    createdAt: Number(req.body?.createdAt) || Date.now(),
    manual: true,
  };
  state.merch.orders.unshift(order);
  state.merch.orders = state.merch.orders.slice(0, 2000);
  await saveState();
  res.json({ order });
});

app.put('/api/merch/orders/:orderId', requireRole('admin'), async (req, res) => {
  ensureMerchState();
  const index = state.merch.orders.findIndex((order) => order.id === req.params.orderId);
  if (index === -1) {
    return res.status(404).json({ error: '记录不存在' });
  }
  const existing = state.merch.orders[index];
  let updatedItems = existing.items;
  if (req.body?.items) {
    try {
      updatedItems = normalizeOrderItems(req.body.items);
    } catch (error) {
      return res.status(400).json({ error: error.message });
    }
  }
  const mode = resolveCheckoutMode(req.body?.checkoutModeId ?? existing.checkoutModeId);
  const totalBefore =
    Math.round(updatedItems.reduce((sum, item) => sum + item.subtotal, 0) * 100) / 100;
  const { totalAfter, discount } = applyCheckoutModeToTotal(mode, totalBefore);
  const updatedOrder = {
    ...existing,
    items: updatedItems,
    checkoutModeId: mode ? mode.id : null,
    checkoutModeName: mode ? mode.name : '原价',
    discount,
    totalBefore,
    totalAfter: Math.round(totalAfter * 100) / 100,
    note:
      req.body?.note !== undefined ? (typeof req.body.note === 'string' ? req.body.note.trim() : '') : existing.note,
    handledBy:
      req.body?.handledBy !== undefined
        ? (typeof req.body.handledBy === 'string' ? req.body.handledBy.trim() : existing.handledBy)
        : existing.handledBy,
    createdAt:
      req.body?.createdAt !== undefined && Number.isFinite(Number(req.body.createdAt))
        ? Number(req.body.createdAt)
        : existing.createdAt,
    manual: existing.manual || Boolean(req.body?.manual),
  };
  state.merch.orders[index] = updatedOrder;
  await saveState();
  res.json({ order: updatedOrder });
});

app.delete('/api/merch/orders/:orderId', requireRole('admin'), async (req, res) => {
  ensureMerchState();
  const index = state.merch.orders.findIndex((order) => order.id === req.params.orderId);
  if (index === -1) {
    return res.status(404).json({ error: '记录不存在' });
  }
  createStateBackup(`delete-order-${req.params.orderId}`).catch(() => {});
  state.merch.orders.splice(index, 1);
  await saveState();
  res.json({ ok: true });
});

app.get('/api/merch/orders/export', requireRole('admin'), (req, res) => {
  ensureMerchState();
  res.json({ orders: state.merch.orders });
});

app.post('/api/merch/orders/import', requireRole('admin'), async (req, res) => {
  ensureMerchState();
  const { orders, mode = 'replace' } = req.body || {};
  if (!Array.isArray(orders)) {
    return res.status(400).json({ error: '导入数据格式无效' });
  }
  const normalizedOrders = [];
  try {
    orders.forEach((entry) => {
      const items = normalizeOrderItems(entry.items || []);
      const modeInstance = resolveCheckoutMode(entry.checkoutModeId);
      const totalBefore = Math.round(items.reduce((sum, item) => sum + item.subtotal, 0) * 100) / 100;
      const result = applyCheckoutModeToTotal(modeInstance, totalBefore);
      normalizedOrders.push({
        id: entry.id && typeof entry.id === 'string' ? entry.id : uuidv4(),
        items,
        checkoutModeId: modeInstance ? modeInstance.id : null,
        checkoutModeName: modeInstance ? modeInstance.name : '原价',
        discount: result.discount,
        totalBefore,
        totalAfter: Math.round(result.totalAfter * 100) / 100,
        handledBy: entry.handledBy || 'imported',
        note: typeof entry.note === 'string' ? entry.note.trim() : '',
        createdAt: Number(entry.createdAt) || Date.now(),
        manual: Boolean(entry.manual),
      });
    });
  } catch (error) {
    return res.status(400).json({ error: error.message });
  }
  createStateBackup('import-orders').catch(() => {});
  if (mode === 'append') {
    state.merch.orders = [...normalizedOrders, ...state.merch.orders].slice(0, 2000);
  } else {
    state.merch.orders = normalizedOrders.slice(0, 2000);
  }
  await saveState();
  res.json({ count: normalizedOrders.length });
});

app.post('/api/merch/orders/clear', requireRole('admin'), async (req, res) => {
  ensureMerchState();
  if (!state.merch.orders.length) {
    return res.json({ ok: true, cleared: 0 });
  }
  createStateBackup('clear-orders').catch(() => {});
  const cleared = state.merch.orders.length;
  state.merch.orders = [];
  await saveState();
  res.json({ ok: true, cleared });
});

app.post('/api/checkins/seat', requireRole('admin'), async (req, res) => {
  const { ticketNumber, action } = req.body || {};
  if (!ticketNumber || typeof ticketNumber !== 'string') {
    return res.status(400).json({ error: '请输入票号' });
  }
  const normalized = ticketNumber.trim();
  let foundSeat = null;
  let foundProject = null;
  Object.values(state.projects).some((project) => {
    const seat = findSeatByTicketCode(project, normalized);
    if (seat) {
      foundSeat = seat;
      foundProject = project;
      return true;
    }
    return false;
  });
  if (!foundSeat || !foundProject) {
    return res.status(404).json({ error: '未找到该票号' });
  }
  ensureSeatCheckinState(foundSeat);
  if (action === 'clear') {
    resetSeatCheckin(foundSeat);
    appendCheckinLog({
      id: uuidv4(),
      ...buildSeatCheckinPayload(foundProject, foundSeat),
      status: 'cleared',
      message: '管理端清除检票状态',
      handledBy: req.session?.username || 'admin',
      createdAt: Date.now(),
    });
    await saveState();
    broadcastProject(foundProject.id);
    return res.json({ ok: true, seat: buildSeatCheckinPayload(foundProject, foundSeat) });
  }
  // action === 'checked'
  foundSeat.checkedInAt = Date.now();
  foundSeat.checkedInBy = req.session?.username || 'admin';
  appendCheckinLog({
    id: uuidv4(),
    ...buildSeatCheckinPayload(foundProject, foundSeat),
    status: 'override',
    message: '管理端标记为已检',
    handledBy: foundSeat.checkedInBy,
    createdAt: foundSeat.checkedInAt,
  });
  await saveState();
  broadcastProject(foundProject.id);
  res.json({ ok: true, seat: buildSeatCheckinPayload(foundProject, foundSeat) });
});

app.patch('/api/accounts/:username', requireRole('admin'), async (req, res) => {
  const targetUsername = req.params.username;
  const account = getAccount(targetUsername);
  if (!account) {
    return res.status(404).json({ error: '账号不存在' });
  }
  const { password, role } = req.body || {};
  if (role && !['admin', 'sales'].includes(role)) {
    return res.status(400).json({ error: '角色无效' });
  }
  if (role && role !== account.role) {
    if (account.role === 'admin' && role !== 'admin' && countAccountsByRole('admin') <= 1) {
      return res.status(400).json({ error: '至少需要保留一个管理员账号' });
    }
    account.role = role;
  }
  if (password) {
    account.passwordHash = await hashPassword(password);
  }
  account.updatedAt = Date.now();
  state.accounts[normalizeUsername(account.username)] = account;
  await saveState();
  broadcastAdminUpdate();
  res.json({ ok: true });
});

app.delete('/api/accounts/:username', requireRole('admin'), (req, res) => {
  const targetUsername = req.params.username;
  const account = getAccount(targetUsername);
  if (!account) {
    return res.status(404).json({ error: '账号不存在' });
  }
  if (account.role === 'admin' && countAccountsByRole('admin') <= 1) {
    return res.status(400).json({ error: '至少需要保留一个管理员账号' });
  }
  const currentSession = parseSession(req);
  if (currentSession && normalizeUsername(currentSession.username) === normalizeUsername(targetUsername)) {
    return res.status(400).json({ error: '无法删除当前登录账号' });
  }
  createStateBackup(`delete-account-${normalizeUsername(targetUsername)}`).catch(() => {});
  removeAccount(targetUsername);
  saveState().catch((err) => console.error('Failed to save state after delete account', err));
  broadcastAdminUpdate();
  res.json({ ok: true });
});

app.get('/api/projects', requireAnyRole, (_req, res) => {
  const projects = Object.values(state.projects).map((project) => ({
    id: project.id,
    name: project.name,
    rows: project.rows,
    cols: project.cols,
    createdAt: project.createdAt,
    updatedAt: project.updatedAt,
    availableSeats: Object.values(project.seats).filter((seat) => seat.status === 'available')
      .length,
  }));
  res.json({ projects });
});

app.post('/api/projects', requireRole('admin'), (req, res) => {
  const { name, rows, cols, ticketing } = req.body || {};
  if (!name || typeof name !== 'string' || !name.trim()) {
    return res.status(400).json({ error: '请输入项目名称' });
  }
  if (!Number.isInteger(rows) || !Number.isInteger(cols) || rows <= 0 || cols <= 0) {
    return res.status(400).json({ error: '行列数必须为正整数' });
  }
  if (rows > 200 || cols > 200) {
    return res.status(400).json({ error: '行列数过大，建议控制在 200 以内' });
  }
  const project = createEmptyProject({ name: name.trim(), rows, cols });
  try {
    if (ticketing) {
      regenerateSeatTicketNumbers(project, ticketing);
    } else {
      ensureSeatTicketNumbers(project, { force: true });
    }
  } catch (error) {
    return res.status(400).json({ error: error.message });
  }
  assignSeatLabels(project);
  state.projects[project.id] = project;
  saveState().catch((err) => console.error('Failed to save state after create project', err));
  broadcastProject(project.id);
  res.json({ project });
});

app.delete('/api/projects/:projectId', requireRole('admin'), (req, res) => {
  const { projectId } = req.params;
  if (!state.projects[projectId]) {
    return res.status(404).json({ error: '项目不存在' });
  }
  createStateBackup(`delete-project-${projectId}`).catch(() => {});
  delete state.projects[projectId];
  saveState().catch((err) => console.error('Failed to save state after delete project', err));
  res.json({ ok: true });
});

const serializeProject = (project) => {
  ensureProjectTicketing(project);
  return {
    id: project.id,
    name: project.name,
    rows: project.rows,
    cols: project.cols,
    createdAt: project.createdAt,
    updatedAt: project.updatedAt,
    seats: project.seats,
    ticketing: project.ticketing,
    priceColorAssignments: project.priceColorAssignments,
    seatLabelProgress: project.seatLabelProgress,
  };
};

function broadcastProject(projectId) {
  const project = state.projects[projectId];
  if (!project) return;
  io.to(`project:${projectId}`).emit('project:update', {
    projectId,
    project: serializeProject(project),
  });
}

const listAccountsForClient = () =>
  Object.values(state.accounts)
    .map(({ username, role, createdAt, updatedAt }) => ({ username, role, createdAt, updatedAt }))
    .sort((a, b) => {
      if (a.role === b.role) {
        return a.username.localeCompare(b.username);
      }
      return a.role.localeCompare(b.role);
    });

const broadcastAdminUpdate = () => {
  io.emit('admin:accounts:update', { accounts: listAccountsForClient() });
};

app.get('/api/projects/:projectId', requireAnyRole, (req, res) => {
  const project = state.projects[req.params.projectId];
  if (!project) {
    return res.status(404).json({ error: '项目不存在' });
  }
  res.json({ project: serializeProject(project) });
});

app.get('/api/projects/:projectId/export', requireRole('admin'), (req, res) => {
  const project = state.projects[req.params.projectId];
  if (!project) {
    return res.status(404).json({ error: '项目不存在' });
  }
  res.json({ project: serializeProject(project) });
});

app.get('/api/projects/:projectId/checkin/stats', requireSalesOrAdmin, (req, res) => {
  const project = state.projects[req.params.projectId];
  if (!project) {
    return res.status(404).json({ error: '项目不存在' });
  }
  const stats = computeCheckinStats(project);
  res.json({ stats });
});

app.post('/api/projects/:projectId/checkin', requireSalesOrAdmin, async (req, res) => {
  const project = state.projects[req.params.projectId];
  if (!project) {
    return res.status(404).json({ error: '项目不存在' });
  }
  const ticketCode = typeof req.body?.ticketCode === 'string' ? req.body.ticketCode.trim() : '';
  const scannerId = typeof req.body?.scannerId === 'string' ? req.body.scannerId : '';
  if (!ticketCode) {
    return res.status(400).json({ error: '请提供票号' });
  }
  let seat = findSeatByTicketCode(project, ticketCode);
  if (!seat) {
    return res.status(404).json({ error: '未找到该票号' });
  }
  ensureSeatCheckinState(seat);
  const payload = buildSeatCheckinPayload(project, seat);
  if (seat.status !== 'sold') {
    return res.status(400).json({ error: '票未售出或已作废', seat: payload });
  }
  if (seat.checkedInAt) {
    return res.status(409).json({
      error: '已检票',
      seat: payload,
      checkedInAt: seat.checkedInAt,
      checkedInBy: seat.checkedInBy,
    });
  }
  seat.checkedInAt = Date.now();
  seat.checkedInBy = req.session?.username || scannerId || 'unknown';
  project.updatedAt = Date.now();
  const updatedPayload = buildSeatCheckinPayload(project, seat);
  appendCheckinLog({
    id: uuidv4(),
    ...updatedPayload,
    status: 'success',
    message: '检票成功',
    handledBy: updatedPayload.checkedInBy,
    createdAt: seat.checkedInAt,
  });
  await saveState();
  broadcastProject(project.id);
  const stats = computeCheckinStats(project);
  res.json({ ok: true, seat: updatedPayload, stats });
});

app.get('/api/checkins', requireRole('admin'), (req, res) => {
  ensureCheckinLogs();
  const { projectId, limit = 500 } = req.query || {};
  const lim = Math.min(2000, Math.max(1, Number(limit) || 500));
  const logs = state.checkInLogs
    .filter((log) => (!projectId ? true : log.projectId === projectId))
    .slice(0, lim);
  res.json({ logs });
});

app.post('/api/projects/:projectId/import', requireRole('admin'), async (req, res) => {
  const project = state.projects[req.params.projectId];
  if (!project) {
    return res.status(404).json({ error: '项目不存在' });
  }
  ensureProjectMetadata(project);
  const payload = (req.body && (req.body.project || req.body)) || {};
  if (!payload || typeof payload !== 'object') {
    return res.status(400).json({ error: '导入数据无效' });
  }
  if (
    (payload.rows && payload.rows !== project.rows) ||
    (payload.cols && payload.cols !== project.cols)
  ) {
    return res.status(400).json({ error: '导入数据的行列数与现有项目不一致' });
  }
  if (payload.name && typeof payload.name === 'string' && payload.name.trim()) {
    project.name = payload.name.trim();
  }
  const incomingSeats = payload.seats && typeof payload.seats === 'object' ? payload.seats : null;
  if (!incomingSeats) {
    return res.status(400).json({ error: '导入数据缺少座位信息' });
  }
  const allowedStatuses = ['disabled', 'available', 'locked', 'sold'];
  Object.entries(project.seats).forEach(([id, seat]) => {
    ensureSeatCheckinState(seat);
    const incoming = incomingSeats[id];
    if (!incoming || typeof incoming !== 'object') {
      seat.status = 'disabled';
      seat.price = null;
      seat.ticketNumber = null;
      seat.ticketCode = null;
      seat.ticketSequenceValue = null;
      seat.seatLabel = null;
      seat.lockedBy = null;
      seat.lockExpiresAt = null;
      seat.issuedAt = null;
      resetSeatCheckin(seat);
      return;
    }
    const status = allowedStatuses.includes(incoming.status) ? incoming.status : 'disabled';
    seat.status = status;
    const incomingPrice = incoming.price;
    if (status === 'disabled') {
      seat.price = null;
    } else if (typeof incomingPrice === 'number' && Number.isFinite(incomingPrice)) {
      seat.price = incomingPrice;
      ensurePriceColorAssignment(project, seat.price);
    } else {
      seat.price = null;
    }
    const ticketNumber = typeof incoming.ticketNumber === 'string' ? incoming.ticketNumber.trim() : '';
    seat.ticketNumber = ticketNumber || null;
    seat.ticketCode = seat.ticketNumber;
    seat.ticketSequenceValue =
      typeof incoming.ticketSequenceValue === 'number' && Number.isFinite(incoming.ticketSequenceValue)
        ? incoming.ticketSequenceValue
        : null;
    if (status === 'sold') {
      seat.issuedAt = typeof incoming.issuedAt === 'number' ? incoming.issuedAt : Date.now();
    } else {
      seat.issuedAt = null;
    }
    seat.lockedBy = null;
    seat.lockExpiresAt = null;
    const incomingLabel = typeof incoming.seatLabel === 'string' ? incoming.seatLabel.trim() : '';
    seat.seatLabel = incomingLabel || null;
    seat.checkedInAt =
      status === 'sold' && typeof incoming.checkedInAt === 'number' ? incoming.checkedInAt : null;
    seat.checkedInBy =
      status === 'sold' && typeof incoming.checkedInBy === 'string' ? incoming.checkedInBy : null;
  });

  if (payload.ticketing && typeof payload.ticketing === 'object') {
    project.ticketing = payload.ticketing;
  }
  if (payload.priceColorAssignments && typeof payload.priceColorAssignments === 'object') {
    project.priceColorAssignments = { ...payload.priceColorAssignments };
  }
  if (payload.seatLabelProgress && typeof payload.seatLabelProgress === 'object') {
    project.seatLabelProgress = { ...payload.seatLabelProgress };
  }

  ensureProjectMetadata(project);
  ensureProjectTicketing(project);
  refreshPriceAssignments(project);
  assignSeatLabels(project);
  try {
    ensureSeatTicketNumbers(project);
  } catch (error) {
    return res.status(400).json({ error: error.message });
  }
  project.updatedAt = Date.now();
  await saveState();
  broadcastProject(project.id);
  res.json({ project: serializeProject(project) });
});

app.put('/api/projects/:projectId', requireRole('admin'), async (req, res) => {
  const project = state.projects[req.params.projectId];
  if (!project) {
    return res.status(404).json({ error: '项目不存在' });
  }
  ensureProjectMetadata(project);
  const { name, seats: seatUpdates } = req.body || {};
  if (name && typeof name === 'string' && name.trim()) {
    project.name = name.trim();
  }
  if (Array.isArray(seatUpdates)) {
    const normalized = sanitizeSeatsUpdate(project, seatUpdates);
    const affectedRows = new Set();
    Object.entries(normalized).forEach(([id, payload]) => {
      const seat = project.seats[id];
      if (!seat) return;
      if (Number.isInteger(payload.row)) {
        affectedRows.add(payload.row);
      } else if (Number.isInteger(seat.row)) {
        affectedRows.add(seat.row);
      }
      if (payload.ticketNumber !== undefined) {
        const ticketNumber = payload.ticketNumber || null;
        seat.ticketNumber = ticketNumber;
        seat.ticketCode = ticketNumber;
        if (project.ticketing?.mode === 'sequence') {
          const sequence = prepareSequenceState(project);
          const value = deriveSequenceValue(sequence, ticketNumber);
          seat.ticketSequenceValue = value;
          if (sequence && value && value > sequence.nextValue) {
            sequence.nextValue = value;
          }
        } else {
          seat.ticketSequenceValue = null;
        }
      }
      if (payload.status) {
        const status = payload.status;
        if (status === 'available') {
          seat.status = 'available';
          seat.lockedBy = null;
          seat.lockExpiresAt = null;
          seat.issuedAt = null;
          resetSeatCheckin(seat);
          if (seat.price != null) {
            ensurePriceColorAssignment(project, seat.price);
          }
        } else if (status === 'locked') {
          seat.status = 'locked';
          seat.lockedBy = null;
          seat.lockExpiresAt = null;
          resetSeatCheckin(seat);
        } else if (status === 'sold') {
          seat.status = 'sold';
          seat.lockedBy = null;
          seat.lockExpiresAt = null;
          seat.issuedAt = Date.now();
        } else {
          seat.status = 'disabled';
          seat.lockedBy = null;
          seat.lockExpiresAt = null;
          seat.issuedAt = null;
          seat.price = null;
          seat.ticketNumber = null;
          seat.ticketCode = null;
          seat.ticketSequenceValue = null;
          resetSeatCheckin(seat);
        }
      }
      if (payload.price !== undefined) {
        if (seat.status === 'disabled') {
          seat.price = null;
        } else {
          seat.price = payload.price;
          if (seat.price != null) {
            ensurePriceColorAssignment(project, seat.price);
          }
        }
      }
    });
    refreshPriceAssignments(project);
    assignSeatLabels(project, affectedRows);
    try {
      ensureSeatTicketNumbers(project);
    } catch (error) {
      return res.status(400).json({ error: error.message });
    }
  }
  project.updatedAt = Date.now();
  await saveState();
  broadcastProject(project.id);
  res.json({ project: serializeProject(project) });
});

app.post('/api/projects/:projectId/ticketing', requireRole('admin'), async (req, res) => {
  const project = state.projects[req.params.projectId];
  if (!project) {
    return res.status(404).json({ error: '项目不存在' });
  }
  const config = req.body || {};
  try {
    if (!config.mode) {
      regenerateSeatTicketNumbers(project, null);
    } else {
      regenerateSeatTicketNumbers(project, config);
    }
  } catch (error) {
    return res.status(400).json({ error: error.message });
  }
  project.updatedAt = Date.now();
  await saveState();
  broadcastProject(project.id);
  res.json({ project: serializeProject(project) });
});

app.post('/api/projects/:projectId/ticketing/regenerate', requireRole('admin'), async (req, res) => {
  const project = state.projects[req.params.projectId];
  if (!project) {
    return res.status(404).json({ error: '项目不存在' });
  }
  try {
    let config = project.ticketing;
    if (project.ticketing?.mode === 'sequence' && project.ticketing.sequence) {
      const seq = project.ticketing.sequence;
      config = {
        mode: 'sequence',
        sequence: {
          template: seq.template,
          startValue: seq.startString || String(seq.startValue).padStart(seq.width || 0, '0'),
        },
      };
    }
    regenerateSeatTicketNumbers(project, config);
  } catch (error) {
    return res.status(400).json({ error: error.message });
  }
  project.updatedAt = Date.now();
  await saveState();
  broadcastProject(project.id);
  res.json({ project: serializeProject(project) });
});

app.patch('/api/projects/:projectId/seats/:seatId', requireRole('admin'), async (req, res) => {
  const project = state.projects[req.params.projectId];
  if (!project) {
    return res.status(404).json({ error: '项目不存在' });
  }
  const seat = project.seats[req.params.seatId];
  if (!seat) {
    return res.status(404).json({ error: '座位不存在' });
  }
  const { status, price, ticketNumber } = req.body || {};
  if (price !== undefined) {
    if (price === null || price === '') {
      seat.price = null;
    } else if (typeof price === 'number' && Number.isFinite(price) && price >= 0) {
      seat.price = price;
    } else {
      return res.status(400).json({ error: '票价必须为非负数字' });
    }
  }
  if (ticketNumber !== undefined) {
    const normalizedTicket = ticketNumber ? String(ticketNumber).trim() : null;
    seat.ticketNumber = normalizedTicket;
    seat.ticketCode = normalizedTicket;
    if (project.ticketing?.mode === 'sequence') {
      const sequence = prepareSequenceState(project);
      const value = deriveSequenceValue(sequence, normalizedTicket);
      seat.ticketSequenceValue = value;
      if (sequence && value && value > sequence.nextValue) {
        sequence.nextValue = value;
      }
    } else {
      seat.ticketSequenceValue = null;
    }
  }
  if (status) {
    const allowedStatuses = ['available', 'locked', 'sold', 'disabled'];
    if (!allowedStatuses.includes(status)) {
      return res.status(400).json({ error: '无效的座位状态' });
    }
    if (status === 'available') {
      seat.status = 'available';
      seat.lockedBy = null;
      seat.lockExpiresAt = null;
      seat.issuedAt = null;
      resetSeatCheckin(seat);
    } else if (status === 'locked') {
      seat.status = 'locked';
      seat.lockedBy = null;
      seat.lockExpiresAt = null;
      resetSeatCheckin(seat);
    } else if (status === 'sold') {
      seat.status = 'sold';
      seat.lockedBy = null;
      seat.lockExpiresAt = null;
      seat.issuedAt = Date.now();
    } else if (status === 'disabled') {
      seat.status = 'disabled';
      seat.lockedBy = null;
      seat.lockExpiresAt = null;
      seat.issuedAt = null;
      seat.price = null;
      seat.ticketNumber = null;
      seat.ticketCode = null;
      seat.ticketSequenceValue = null;
      resetSeatCheckin(seat);
    }
  }
  assignSeatLabels(project);
  try {
    ensureSeatTicketNumbers(project);
  } catch (error) {
    return res.status(400).json({ error: error.message });
  }
  project.updatedAt = Date.now();
  await saveState();
  broadcastProject(project.id);
  res.json({ ok: true, seat });
});

app.use((err, req, res, next) => {
  if (err && err.type === 'entity.too.large') {
    return res.status(413).json({ error: '请求体过大，请压缩图片或拆分内容后再试。' });
  }
  console.error('Unhandled request error:', err);
  return res.status(500).json({ error: '服务器繁忙，请稍后再试。' });
});

io.use((socket, next) => {
  try {
    const cookies = cookie.parse(socket.handshake.headers.cookie || '');
    const sessionId = cookies[SESSION_COOKIE_NAME];
    if (!sessionId) {
      return next(new Error('未登录'));
    }
    const session = sessions.get(sessionId);
    if (!session) {
      return next(new Error('会话已失效'));
    }
    if (Date.now() - session.createdAt > SESSION_TTL_MS) {
      sessions.delete(sessionId);
      return next(new Error('会话已过期'));
    }
    socket.data.session = { ...session, sessionId };
    return next();
  } catch (error) {
    return next(error);
  }
});

io.on('connection', (socket) => {
  socket.data.currentProjectId = null;

  if (socket.data.session?.role === 'admin') {
    socket.emit('admin:accounts:update', { accounts: listAccountsForClient() });
  }

  socket.on('project:join', ({ projectId }, ack = () => {}) => {
    const project = state.projects[projectId];
    if (!project) {
      return ack({ ok: false, message: '项目不存在' });
    }
    if (socket.data.currentProjectId) {
      socket.leave(`project:${socket.data.currentProjectId}`);
    }
    socket.join(`project:${projectId}`);
    socket.data.currentProjectId = projectId;
    return ack({ ok: true, project: serializeProject(project) });
  });

  socket.on('lock-seat', async ({ projectId, seatId: requestedId }, ack = () => {}) => {
    const project = state.projects[projectId];
    if (!project) {
      return ack({ ok: false, message: '项目不存在' });
    }
    const seat = project.seats[requestedId];
    if (!seat) {
      return ack({ ok: false, message: '座位不存在' });
    }
    if (seat.status === 'sold') {
      return ack({ ok: false, message: '座位已签发' });
    }
    if (seat.status === 'disabled') {
      return ack({ ok: false, message: '座位未启用' });
    }
    if (!seat.ticketNumber) {
      try {
        assignTicketNumberToSeat(project, seat, { force: true });
      } catch (error) {
        return ack({ ok: false, message: error.message });
      }
    }
    if (seat.status === 'locked' && seat.lockedBy && seat.lockedBy !== socket.id) {
      return ack({ ok: false, message: '座位已被其他终端锁定' });
    }
    seat.status = 'locked';
    seat.lockedBy = socket.id;
    seat.lockExpiresAt = Date.now() + LOCK_TIMEOUT_MS;
    project.updatedAt = Date.now();
    await saveState();
    broadcastProject(project.id);
    return ack({ ok: true });
  });

  socket.on('unlock-seat', async ({ projectId, seatId: requestedId }, ack = () => {}) => {
    const project = state.projects[projectId];
    if (!project) {
      return ack({ ok: false, message: '项目不存在' });
    }
    const seat = project.seats[requestedId];
    if (!seat) {
      return ack({ ok: false, message: '座位不存在' });
    }
    if (seat.lockedBy !== socket.id) {
      return ack({ ok: false, message: '没有权限释放该座位' });
    }
    if (seat.status === 'sold') {
      return ack({ ok: false, message: '座位已经签发' });
    }
    releaseSeatLock(seat);
    project.updatedAt = Date.now();
    await saveState();
    broadcastProject(project.id);
    return ack({ ok: true });
  });

  socket.on('seat:issue', async ({ projectId, seatId: requestedId, ticketCode }, ack = () => {}) => {
    const project = state.projects[projectId];
    if (!project) {
      return ack({ ok: false, message: '项目不存在' });
    }
    const seat = project.seats[requestedId];
    if (!seat) {
      return ack({ ok: false, message: '座位不存在' });
    }
    if (!ticketCode || ticketCode !== seat.ticketCode) {
      return ack({ ok: false, message: '票码不匹配' });
    }
    if (seat.lockedBy !== socket.id) {
      return ack({ ok: false, message: '当前终端未锁定该座位' });
    }
    seat.status = 'sold';
    seat.lockedBy = null;
    seat.lockExpiresAt = null;
    seat.issuedAt = Date.now();
    if (!seat.seatLabel) {
      assignSeatLabels(project, new Set([seat.row]));
    }
    project.updatedAt = Date.now();
    await saveState();
    broadcastProject(project.id);
    return ack({ ok: true });
  });

  socket.on('request-ticket-code', async ({ projectId, seatId: requestedId }, ack = () => {}) => {
    const project = state.projects[projectId];
    if (!project) {
      return ack({ ok: false, message: '项目不存在' });
    }
    const seat = project.seats[requestedId];
    if (!seat) {
      return ack({ ok: false, message: '座位不存在' });
    }
    if (!seat.ticketNumber) {
      try {
        assignTicketNumberToSeat(project, seat, { force: true });
      } catch (error) {
        return ack({ ok: false, message: error.message });
      }
      project.updatedAt = Date.now();
      await saveState();
    }
    const qrDataUrl = await QRCode.toDataURL(seat.ticketCode || seat.ticketNumber, {
      width: 256,
      margin: 1,
    }).catch(
      () => null
    );
    return ack({ ok: true, ticketCode: seat.ticketCode || seat.ticketNumber, qrDataUrl });
  });

  socket.on('disconnect', async () => {
    const { id } = socket;
    const touchedProjects = new Set();
    Object.values(state.projects).forEach((project) => {
      let changed = false;
      Object.values(project.seats).forEach((seat) => {
        if (seat.lockedBy === id && seat.status !== 'sold') {
          releaseSeatLock(seat);
          changed = true;
        }
      });
      if (changed) {
        project.updatedAt = Date.now();
        touchedProjects.add(project.id);
      }
    });
    if (touchedProjects.size > 0) {
      await saveState();
      touchedProjects.forEach((projectId) => broadcastProject(projectId));
    }
  });
});

(async () => {
  await ensureDataFile();
  await ensureMerchImageDir();
  await loadState();
  await ensureDefaultAccounts();
  Object.values(state.projects).forEach((project) => {
    try {
      ensureProjectMetadata(project);
      ensureProjectTicketing(project);
      refreshPriceAssignments(project);
      Object.values(project.seats || {}).forEach((seat) => ensureSeatCheckinState(seat));
      assignSeatLabels(project);
      ensureSeatTicketNumbers(project);
    } catch (error) {
      console.error(`Failed to normalize project ${project.id}:`, error.message);
    }
  });
  ensureCheckinLogs();
  await saveState();
  server.listen(PORT, () => {
    console.log(`Server listening on http://localhost:${PORT}`);
  });
})();
