const express = require("express")
const crypto = require("crypto")
const compression = require("compression")
const cors = require("cors")
const http = require("http")
const https = require("https")
const WebSocket = require("ws")
const { spawn, execSync } = require("child_process")
const fs = require("fs")
const multer = require("multer")

const app = express()
const httpServer = http.createServer(app)

app.use(compression())
app.use(cors())
app.use(express.json({ limit: "10mb" }))
app.use(express.static("public"))

const PORT = process.env.PORT || 3000
const OWNER_TOKEN = process.env.OWNER_TOKEN
const GITHUB_TOKEN = process.env.GITHUB_TOKEN
const GITHUB_REPO = process.env.GITHUB_REPO
const GITHUB_BRANCH = process.env.GITHUB_BRANCH || "main"
const ENCRYPTION_KEY = process.env.ENCRYPTION_KEY || ""

if (!OWNER_TOKEN) throw "missing OWNER_TOKEN"
if (!GITHUB_TOKEN || !GITHUB_REPO) throw "missing GITHUB config"

try {
    execSync("python3 -m pip install --user discord.py aiohttp", { stdio: "ignore" })
} catch (e) {}

const DB_PATH = "db.json"
const DB_BACKUP_PATH = "db.backup.json"
const BOT_DB_PATH = "db_bots.json"
const BOT_DB_BACKUP_PATH = "db_bots.backup.json"
const MAX_CHAT_MESSAGES = 300
const MAX_BOT_LOGS = 500
const MAX_MONITOR_HISTORY = 60
const BOT_LIMIT_USER = 1
const BOT_MAX_RESTARTS = 5
const BOT_RESTART_DELAY = 15000

let fileSha = {}
let DB = { apis: {}, users: {}, sessions: {}, bots: {}, monitors: {} }
let chatMessages = []
const chatClients = new Map()
const activeProcesses = new Map()

const globalDefaults = {
    ttl: 60000, prefix: "", suffix: "", encode: null,
    removeDuplicate: false, maxJobsPerBoss: 0, maxTotalJobs: 0,
    enabled: true, privateMode: false, whitelistIPs: [],
    jobSort: "desc", customFields: null, webhookCustom: null
}

function encrypt(text) {
    if (!ENCRYPTION_KEY) return text
    const key = crypto.createHash("sha256").update(ENCRYPTION_KEY).digest()
    const iv = crypto.randomBytes(16)
    const cipher = crypto.createCipheriv("aes-256-cbc", key, iv)
    let enc = cipher.update(text, "utf8", "base64")
    enc += cipher.final("base64")
    return iv.toString("base64") + ":" + enc
}

function decrypt(text) {
    if (!ENCRYPTION_KEY) return text
    const parts = text.split(":")
    if (parts.length !== 2) return text
    try {
        const key = crypto.createHash("sha256").update(ENCRYPTION_KEY).digest()
        const iv = Buffer.from(parts[0], "base64")
        const decipher = crypto.createDecipheriv("aes-256-cbc", key, iv)
        let dec = decipher.update(parts[1], "base64", "utf8")
        dec += decipher.final("utf8")
        return dec
    } catch (e) {
        return null
    }
}

async function fetchFileFromGithub(filePath) {
    const url = `https://api.github.com/repos/${GITHUB_REPO}/contents/${filePath}?ref=${GITHUB_BRANCH}`
    const res = await fetch(url, { headers: { Authorization: `token ${GITHUB_TOKEN}`, Accept: "application/vnd.github.v3+json" } })
    if (!res.ok) return null
    const data = await res.json()
    fileSha[filePath] = data.sha
    return decrypt(Buffer.from(data.content, "base64").toString("utf8"))
}

async function getFileShaFromGithub(filePath) {
    try {
        const url = `https://api.github.com/repos/${GITHUB_REPO}/contents/${filePath}?ref=${GITHUB_BRANCH}`
        const res = await fetch(url, { headers: { Authorization: `token ${GITHUB_TOKEN}`, Accept: "application/vnd.github.v3+json" } })
        if (!res.ok) return null
        const data = await res.json()
        fileSha[filePath] = data.sha
        return data.sha
    } catch { return null }
}

async function initEmptyRepo() {
    const baseUrl = `https://api.github.com/repos/${GITHUB_REPO}`
    const headers = {
        Authorization: `token ${GITHUB_TOKEN}`,
        Accept: "application/vnd.github.v3+json",
        "Content-Type": "application/json"
    }
    const treeRes = await fetch(`${baseUrl}/git/trees`, { method: "POST", headers, body: JSON.stringify({ tree: [] }) })
    if (!treeRes.ok) throw new Error("init tree failed")
    const treeData = await treeRes.json()
    const commitRes = await fetch(`${baseUrl}/git/commits`, { method: "POST", headers, body: JSON.stringify({ message: "init", tree: treeData.sha, parents: [] }) })
    if (!commitRes.ok) throw new Error("init commit failed")
    const commitData = await commitRes.json()
    const refRes = await fetch(`${baseUrl}/git/refs`, { method: "POST", headers, body: JSON.stringify({ ref: `refs/heads/${GITHUB_BRANCH}`, sha: commitData.sha }) })
    if (!refRes.ok) throw new Error("init branch failed")
}

async function pushFileToGithub(filePath, content, retry = true) {
    const branchCheckUrl = `https://api.github.com/repos/${GITHUB_REPO}/git/refs/heads/${GITHUB_BRANCH}`
    let branchCheck = await fetch(branchCheckUrl, { headers: { Authorization: `token ${GITHUB_TOKEN}`, Accept: "application/vnd.github.v3+json" } })
    if (!branchCheck.ok && branchCheck.status === 404) {
        await initEmptyRepo()
        await new Promise(r => setTimeout(r, 1000))
    }

    const encrypted = encrypt(content)
    const encoded = Buffer.from(encrypted).toString("base64")
    const ghUrl = `https://api.github.com/repos/${GITHUB_REPO}/contents/${filePath}`
    const ghHeaders = { Authorization: `token ${GITHUB_TOKEN}`, Accept: "application/vnd.github.v3+json", "Content-Type": "application/json" }

    let freshSha = await getFileShaFromGithub(filePath)
    const body = { message: `update ${filePath}`, content: encoded, branch: GITHUB_BRANCH }
    if (freshSha) body.sha = freshSha

    let res = await fetch(ghUrl, { method: "PUT", headers: ghHeaders, body: JSON.stringify(body) })

    if (res.status === 409 && retry) {
        freshSha = await getFileShaFromGithub(filePath)
        if (freshSha) body.sha = freshSha; else delete body.sha
        res = await fetch(ghUrl, { method: "PUT", headers: ghHeaders, body: JSON.stringify(body) })
    }

    if (!res.ok) {
        const errText = await res.text().catch(() => res.statusText)
        throw new Error(`Push failed for ${filePath}: ${res.status} ${errText}`)
    }

    const data = await res.json()
    fileSha[filePath] = data.content.sha
}

function validateDB(data) { return data && typeof data === "object" && data.apis && data.users }

function mergeDB(data) {
    if (!validateDB(data)) return false
    DB.apis = data.apis || {}
    DB.users = data.users || {}
    DB.sessions = data.sessions || {}
    DB.monitors = data.monitors || {}
    if (data.bots) DB.bots = data.bots
    else DB.bots = DB.bots || {}
    return true
}

const LOCAL_DB_PATH = "/tmp/db_local.json"

function saveLocalDB(data) {
    try { fs.writeFileSync(LOCAL_DB_PATH, data, "utf8") } catch (e) {}
}

function loadLocalDB() {
    try {
        if (fs.existsSync(LOCAL_DB_PATH)) {
            const raw = fs.readFileSync(LOCAL_DB_PATH, "utf8")
            if (raw && mergeDB(JSON.parse(raw))) return true
        }
    } catch (e) {}
    return false
}

async function loadDB() {
    try {
        let raw = await fetchFileFromGithub(DB_PATH)
        if (raw) {
            const mainData = JSON.parse(raw)
            mergeDB(mainData)
            const rawBots = await fetchFileFromGithub(BOT_DB_PATH)
            if (rawBots) {
                const botsData = JSON.parse(rawBots)
                DB.bots = botsData.bots || {}
            } else {
                const rawBotsBackup = await fetchFileFromGithub(BOT_DB_BACKUP_PATH)
                if (rawBotsBackup) {
                    const botsData = JSON.parse(rawBotsBackup)
                    DB.bots = botsData.bots || {}
                }
            }
            return true
        }
        raw = await fetchFileFromGithub(DB_BACKUP_PATH)
        if (raw) {
            const mainData = JSON.parse(raw)
            mergeDB(mainData)
            return true
        }
    } catch (e) {}
    if (loadLocalDB()) return true
    return false
}

let writeQueue = Promise.resolve()
let pendingWrite = false

async function writeDB() {
    const mainData = JSON.stringify({ apis: DB.apis, users: DB.users, sessions: DB.sessions, monitors: DB.monitors })
    const botsData = JSON.stringify({ bots: DB.bots })
    saveLocalDB(JSON.stringify(DB))
    try {
        await pushFileToGithub(DB_BACKUP_PATH, mainData)
        await pushFileToGithub(DB_PATH, mainData)
        await pushFileToGithub(BOT_DB_BACKUP_PATH, botsData)
        await pushFileToGithub(BOT_DB_PATH, botsData)
    } catch (e) {
        console.error("GitHub push failed:", e.message)
    }
}

let saveTimeout = null
function saveDB() {
    if (saveTimeout) clearTimeout(saveTimeout)
    return new Promise((resolve) => {
        saveTimeout = setTimeout(() => {
            if (pendingWrite) { resolve(); return }
            pendingWrite = true
            writeQueue = writeQueue.then(() => writeDB()).finally(() => {
                pendingWrite = false
                resolve()
            })
        }, 300)
    })
}

const genToken = () => crypto.randomBytes(32).toString("hex")
const genID = () => crypto.randomBytes(6).toString("hex")
const now = () => Date.now()
const toBool = v => typeof v === "boolean" ? v : (typeof v === "string" ? v.toLowerCase() === "true" || v === "1" : !!v)
const getIP = r => (r.headers["x-forwarded-for"] || "").split(",")[0].trim() || r.socket.remoteAddress
const genGuest = ip => "Khach" + (ip.replace(/\D/g, "").slice(-5) || Math.floor(Math.random() * 99999))
const getSession = r => DB.sessions[r.headers.authorization]
const getUser = r => getSession(r)?.user
const getRole = r => {
    const s = getSession(r)
    if (!s) return "guest"
    if (s.role === "OWNER") return "owner"
    const u = DB.users[s.user]
    return (u && u.role) ? u.role : "member"
}
const isOwner = r => getRole(r) === "owner"
const isAdminOrOwner = r => { const role = getRole(r); return role === "owner" || role === "admin" }
const parseEncode = txt => { try { return JSON.parse(txt) } catch { return null } }
const encode = (txt, map) => { if (!map) return String(txt); return String(txt).split("").map(c => map[c] || c).join("") }

function injectWebhookData(template, data) {
    if (!template) return null
    try {
        let str = typeof template === "string" ? template : JSON.stringify(template)
        str = str.replace(/\{\{job\}\}/g, String(data.job || "")).replace(/\{\{boss\}\}/g, String(data.boss || "")).replace(/\{\{players\}\}/g, String(data.players || 0)).replace(/\{\{sea\}\}/g, String(data.sea || 0)).replace(/\{\{time\}\}/g, new Date().toISOString())
        return JSON.parse(str)
    } catch { return null }
}

const sendWebhook = async (url, data, custom) => {
    try {
        const payload = custom
            ? (injectWebhookData(custom, data) || { content: `Job: ${data.job} | Boss: ${data.boss} | Players: ${data.players} | Sea: ${data.sea}` })
            : { embeds: [{ title: "New Job Added", color: 65280, fields: [{ name: "Boss", value: String(data.boss), inline: true }, { name: "Players", value: String(data.players), inline: true }, { name: "Sea", value: String(data.sea), inline: true }, { name: "JobId", value: String(data.job).slice(0, 1000) }], timestamp: new Date().toISOString() }] }
        await fetch(url, { method: "POST", headers: { "Content-Type": "application/json" }, body: JSON.stringify(payload), signal: AbortSignal.timeout(8000) })
    } catch {}
}

const applyJobLimits = api => {
    if (api.maxTotalJobs > 0) {
        let total = 0
        for (let b in api.jobs) total += api.jobs[b].length
        while (total > api.maxTotalJobs) {
            let oldestBoss = null, oldestTime = Infinity
            for (let b in api.jobs) { if (api.jobs[b].length && api.jobs[b][0].t < oldestTime) { oldestTime = api.jobs[b][0].t; oldestBoss = b } }
            if (oldestBoss) { api.jobs[oldestBoss].shift(); total--; if (!api.jobs[oldestBoss].length) delete api.jobs[oldestBoss] }
            else break
        }
    }
    if (api.maxJobsPerBoss > 0) { for (let b in api.jobs) while (api.jobs[b].length > api.maxJobsPerBoss) api.jobs[b].shift() }
}

const cleanExpiredJobs = api => {
    const t = now()
    Object.keys(api.jobs).forEach(boss => { api.jobs[boss] = api.jobs[boss].filter(j => t - j.t < api.ttl); if (!api.jobs[boss].length) delete api.jobs[boss] })
}

async function checkMonitor(m) {
    const old = m.lastStatus
    const start = now()
    try {
        await new Promise((resolve, reject) => {
            const lib = m.url.startsWith("https") ? https : http
            const req = lib.request(m.url, { method: "GET", timeout: 15000 }, res => { m.lastCode = res.statusCode; res.resume(); resolve() })
            req.on("error", reject)
            req.on("timeout", () => { req.destroy(); reject(new Error("timeout")) })
            req.end()
        })
        m.totalChecks = (m.totalChecks || 0) + 1
        m.goodChecks = (m.goodChecks || 0) + 1
        m.uptime = ((m.goodChecks / m.totalChecks) * 100).toFixed(2)
        m.lastPing = now() - start
        m.lastStatus = "online"; m.lastError = null; m.lastCheck = now(); m.retry = 0
        m.history = m.history || []
        m.history.push({ t: now(), s: "on", p: m.lastPing })
        if (m.history.length > MAX_MONITOR_HISTORY) m.history.shift()
        if (old !== "online" && m.webhook) sendMonitorWebhook(m, "up")
    } catch (err) {
        m.retry = (m.retry || 0) + 1
        if (m.retry < 3) return
        m.totalChecks = (m.totalChecks || 0) + 1
        m.uptime = (((m.goodChecks || 0) / m.totalChecks) * 100).toFixed(2)
        m.lastStatus = "offline"; m.lastError = err.message || String(err); m.lastCheck = now()
        m.history = m.history || []
        m.history.push({ t: now(), s: "off", p: 0 })
        if (m.history.length > MAX_MONITOR_HISTORY) m.history.shift()
        if (old !== "offline" && m.webhook) sendMonitorWebhook(m, "down")
    }
    saveDB()
}

async function sendMonitorWebhook(m, type) {
    try {
        await fetch(m.webhook, {
            method: "POST", headers: { "Content-Type": "application/json" },
            body: JSON.stringify({ embeds: [{ title: type === "up" ? "🟢 Online" : "🔴 Offline", color: type === "up" ? 65280 : 16711680, fields: [{ name: "Name", value: m.name, inline: true }, { name: "URL", value: m.url, inline: true }, { name: "Uptime", value: m.uptime + "%", inline: true }, { name: "Ping", value: (m.lastPing || 0) + "ms", inline: true }], timestamp: new Date().toISOString() }] }),
            signal: AbortSignal.timeout(8000)
        })
    } catch {}
}

function spawnBot(bot) {
    if (activeProcesses.has(bot.id)) return
    const code = Buffer.from(bot.code, "base64").toString("utf8")
    const tmpFile = `/tmp/bot_${bot.id}.py`
    fs.writeFileSync(tmpFile, code)
    const child = spawn("python3", [tmpFile], { env: { ...process.env, ...bot.env } })
    bot.pid = child.pid; bot.status = "running"; bot.updated_at = now()
    activeProcesses.set(bot.id, child)
    const appendLog = data => {
        const lines = String(data).split("\n").filter(Boolean)
        bot.logs.push(...lines)
        if (bot.logs.length > MAX_BOT_LOGS) bot.logs.splice(0, bot.logs.length - MAX_BOT_LOGS)
        saveDB()
    }
    child.stdout.on("data", appendLog)
    child.stderr.on("data", data => appendLog("[ERR] " + data))
    child.on("close", (exitCode, signal) => {
        activeProcesses.delete(bot.id)
        bot.pid = null; bot.updated_at = now()
        bot.logs.push(`[EXIT] code=${exitCode} signal=${signal}`)
        const currentBot = DB.bots[bot.id]
        if (!currentBot) { try { fs.unlinkSync(tmpFile) } catch {} return }
        if (currentBot.autoRestart && (currentBot.restartCount || 0) < BOT_MAX_RESTARTS) {
            currentBot.status = "restarting"
            currentBot.restartCount = (currentBot.restartCount || 0) + 1
            currentBot.logs.push(`[AUTO-RESTART] lan ${currentBot.restartCount}/${BOT_MAX_RESTARTS} sau ${BOT_RESTART_DELAY / 1000}s...`)
            saveDB()
            setTimeout(() => {
                const b = DB.bots[bot.id]
                if (b && b.autoRestart && b.status === "restarting") {
                    b.logs.push(`[RESTART] bat lai...`)
                    spawnBot(b)
                    saveDB()
                }
            }, BOT_RESTART_DELAY)
        } else {
            currentBot.status = "stopped"
            if (currentBot.autoRestart && (currentBot.restartCount || 0) >= BOT_MAX_RESTARTS) {
                currentBot.logs.push(`[STOP] Da restart ${BOT_MAX_RESTARTS} lan, dung lai.`)
                currentBot.autoRestart = false
            }
            saveDB()
        }
        try { fs.unlinkSync(tmpFile) } catch {}
    })
    child.on("error", err => { bot.status = "error"; bot.logs.push("[ERROR] " + err.message); activeProcesses.delete(bot.id); saveDB() })
}

setInterval(() => {
    Object.values(DB.apis).forEach(api => { cleanExpiredJobs(api); applyJobLimits(api) })
    Object.values(DB.monitors).forEach(m => { if (now() - (m.lastCheck || 0) >= (m.interval || 60000)) checkMonitor(m) })
    saveDB()
}, 15000)

setInterval(() => writeDB(), 450000)

process.on("SIGTERM", async () => { await writeDB(); process.exit(0) })
process.on("SIGINT", async () => { await writeDB(); process.exit(0) })
process.on("uncaughtException", async err => { await writeDB() })

const upload = multer({ dest: "/tmp/bot_uploads/", limits: { fileSize: 5 * 1024 * 1024 } })

app.post("/register", async (req, res) => {
    let { user, pass } = req.body
    if (!user || !pass) return res.json({ err: "thieu user/pass" })
    if (pass.length < 8) return res.json({ err: "mat khau it nhat 8 ky tu" })
    if (/\s/.test(user)) return res.json({ err: "ten khong duoc chua khoang trang" })
    if (DB.users[user]) return res.json({ err: "tai khoan da ton tai" })
    const isFirst = Object.keys(DB.users).length === 0
    DB.users[user] = { pass, createdAt: now(), role: isFirst ? "owner" : "member", avatar: "" }
    await saveDB(); res.json({ ok: 1 })
})

app.post("/login", async (req, res) => {
    let { user, pass } = req.body
    if (pass === OWNER_TOKEN) {
        let token = genToken()
        if (!DB.users[user]) DB.users[user] = { pass: null, createdAt: now(), role: "owner", avatar: "" }
        DB.sessions[token] = { user, role: "OWNER" }
        await saveDB(); return res.json({ token, role: "owner" })
    }
    let u = DB.users[user]
    if (!u || u.pass !== pass) return res.json({ err: "sai thong tin" })
    let token = genToken()
    DB.sessions[token] = { user, role: "user" }
    await saveDB(); res.json({ token, role: u.role || "member" })
})

app.post("/logout", async (req, res) => {
    const token = req.headers.authorization
    if (token && DB.sessions[token]) { delete DB.sessions[token]; await saveDB(); res.json({ ok: 1 }) }
    else res.json({ err: "khong co phien" })
})

app.get("/me", (req, res) => {
    let s = getSession(req)
    if (s) { const u = DB.users[s.user]; return res.json({ user: s.user, role: getRole(req), avatar: u?.avatar || "" }) }
    res.json({ guest: genGuest(getIP(req)), role: "guest", avatar: "" })
})

app.post("/set-avatar", async (req, res) => {
    let user = getUser(req)
    if (!user) return res.json({ err: "dang nhap di" })
    const { avatar } = req.body
    if (typeof avatar !== "string" || avatar.length > 300) return res.json({ err: "avatar khong hop le" })
    DB.users[user] = DB.users[user] || { pass: null, createdAt: now(), role: "member", avatar: "" }
    DB.users[user].avatar = avatar
    await saveDB(); res.json({ ok: 1, avatar })
})

app.post("/change-password", async (req, res) => {
    let user = getUser(req)
    if (!user) return res.json({ err: "dang nhap di" })
    const { oldPass, newPass } = req.body
    const u = DB.users[user]
    if (!u) return res.json({ err: "khong tim thay" })
    if (u.pass && u.pass !== oldPass) return res.json({ err: "sai mat khau hien tai" })
    if (!newPass || newPass.length < 8) return res.json({ err: "mat khau moi qua ngan" })
    u.pass = newPass; await saveDB(); res.json({ ok: 1 })
})

app.get("/user/:username", (req, res) => {
    const u = DB.users[req.params.username]
    if (!u) return res.json({ err: "khong tim thay" })
    res.json({ username: req.params.username, avatar: u.avatar || "", role: u.role || "member" })
})

app.post("/create", async (req, res) => {
    let user = getUser(req)
    if (!user) return res.json({ err: "dang nhap di" })
    let { name, displayName, webhook, privateMode, viewIP, whitelistIPs } = req.body
    if (!name) return res.json({ err: "thieu ten API" })
    if (/[^\w]/.test(name)) return res.json({ err: "ten API chi duoc chua chu, so, _" })
    let id = genID()
    DB.apis[id] = { id, name, displayName: displayName || name, owner: user, jobs: {}, webhook: webhook || "", webhookCustom: globalDefaults.webhookCustom, encode: globalDefaults.encode, prefix: globalDefaults.prefix, suffix: globalDefaults.suffix, ttl: globalDefaults.ttl, removeDuplicate: globalDefaults.removeDuplicate, maxJobsPerBoss: globalDefaults.maxJobsPerBoss, maxTotalJobs: globalDefaults.maxTotalJobs, enabled: true, privateMode: privateMode !== undefined ? toBool(privateMode) : globalDefaults.privateMode, viewIP: viewIP || "", whitelistIPs: whitelistIPs || [...(globalDefaults.whitelistIPs || [])], jobSort: globalDefaults.jobSort, customFields: globalDefaults.customFields ? [...globalDefaults.customFields] : null, apiKey: genToken() }
    await saveDB(); res.json({ ok: 1, id, apiKey: DB.apis[id].apiKey, link: `/api/${id}/all` })
})

app.get("/my", (req, res) => {
    let user = getUser(req)
    if (!user) return res.json([])
    const apis = isAdminOrOwner(req) ? Object.values(DB.apis) : Object.values(DB.apis).filter(a => a.owner === user)
    res.json(apis.map(api => {
        const bossCounts = {}; let total = 0
        for (let b in api.jobs) { bossCounts[b] = api.jobs[b].length; total += api.jobs[b].length }
        return { id: api.id, displayName: api.displayName, name: api.name, owner: api.owner, totalJobs: total, bosses: bossCounts, enabled: api.enabled, privateMode: api.privateMode, ttl: api.ttl, webhook: !!api.webhook, encode: !!api.encode, prefix: api.prefix || "", suffix: api.suffix || "", removeDuplicate: !!api.removeDuplicate, jobSort: api.jobSort, maxJobsPerBoss: api.maxJobsPerBoss, maxTotalJobs: api.maxTotalJobs, whitelistIPs: api.whitelistIPs || [], customFields: api.customFields || null, viewIP: api.viewIP || "", apiKey: api.apiKey }
    }))
})

app.post("/push", async (req, res) => {
    let { id, apiKey, job, players, sea, boss } = req.body
    let api = DB.apis[id]
    if (!api) return res.json({ err: "api khong ton tai" })
    if (!api.enabled) return res.json({ err: "api dang bi tat" })
    if (api.apiKey !== apiKey) return res.json({ err: "sai key" })
    if (!job) return res.json({ err: "thieu job" })
    if (!boss) return res.json({ err: "thieu boss" })
    boss = String(boss).toLowerCase().trim()
    let finalJob = encode(job, api.encode)
    if (api.prefix) finalJob = api.prefix + finalJob
    if (api.suffix) finalJob = finalJob + api.suffix
    if (!api.jobs[boss]) api.jobs[boss] = []
    if (toBool(api.removeDuplicate)) {
        let ex = api.jobs[boss].find(j => j.job === finalJob)
        if (ex) { ex.players = Number(players) || 0; ex.sea = Number(sea) || 0; ex.t = now(); applyJobLimits(api); await saveDB(); return res.json({ ok: 1, update: true }) }
    }
    let data = { job: finalJob, players: Number(players) || 0, sea: Number(sea) || 0, boss, t: now() }
    api.jobs[boss].push(data); applyJobLimits(api)
    if (api.webhook) sendWebhook(api.webhook, data, api.webhookCustom)
    await saveDB(); res.json({ ok: 1 })
})

app.post("/push/bulk", async (req, res) => {
    let { id, apiKey, jobs } = req.body
    let api = DB.apis[id]
    if (!api) return res.json({ err: "api khong ton tai" })
    if (!api.enabled) return res.json({ err: "api dang bi tat" })
    if (api.apiKey !== apiKey) return res.json({ err: "sai key" })
    if (!Array.isArray(jobs) || !jobs.length) return res.json({ err: "mang jobs rong" })
    let added = 0, dup = toBool(api.removeDuplicate)
    for (let item of jobs) {
        let { job, players, sea, boss } = item
        if (!job || !boss) continue
        boss = String(boss).toLowerCase().trim()
        let finalJob = encode(job, api.encode)
        if (api.prefix) finalJob = api.prefix + finalJob
        if (api.suffix) finalJob = finalJob + api.suffix
        if (!api.jobs[boss]) api.jobs[boss] = []
        if (dup) { let ex = api.jobs[boss].find(j => j.job === finalJob); if (ex) { ex.players = Number(players) || 0; ex.sea = Number(sea) || 0; ex.t = now(); added++; continue } }
        api.jobs[boss].push({ job: finalJob, players: Number(players) || 0, sea: Number(sea) || 0, boss, t: now() })
        added++
        if (api.webhook) sendWebhook(api.webhook, { job: finalJob, players, sea, boss }, api.webhookCustom)
    }
    applyJobLimits(api); await saveDB(); res.json({ ok: 1, added })
})

const checkView = (req, api) => {
    if (!api.privateMode) return true
    const ip = getIP(req)
    if (api.viewIP && api.viewIP === ip) return true
    if (api.whitelistIPs && api.whitelistIPs.includes(ip)) return true
    return false
}

const filterJobFields = (job, fields) => {
    if (!fields || !fields.length) return job
    const f = {}
    fields.forEach(k => { if (Object.prototype.hasOwnProperty.call(job, k)) f[k] = job[k] })
    return f
}

app.get("/api/:id/stats", (req, res) => {
    let api = DB.apis[req.params.id]
    if (!api) return res.json({ err: "api khong ton tai" })
    if (!isAdminOrOwner(req) && api.owner !== getUser(req)) return res.json({ err: "khong co quyen" })
    cleanExpiredJobs(api); applyJobLimits(api)
    const bossCounts = {}; let total = 0
    for (let b in api.jobs) { bossCounts[b] = api.jobs[b].length; total += api.jobs[b].length }
    res.json({ id: api.id, displayName: api.displayName, totalJobs: total, maxJobsPerBoss: api.maxJobsPerBoss, maxTotalJobs: api.maxTotalJobs, bosses: bossCounts, enabled: api.enabled, ttl: api.ttl, privateMode: api.privateMode, removeDuplicate: !!api.removeDuplicate })
})

app.get("/api/:id/:boss?", (req, res) => {
    let api = DB.apis[req.params.id]
    if (!api) return res.json([])
    if (!checkView(req, api)) return res.json({ err: "thieu IP duoc phep" })
    cleanExpiredJobs(api); applyJobLimits(api)
    let boss = (req.params.boss || "all").toLowerCase()
    let sortOrder = (req.query.sort || api.jobSort || "desc") === "asc" ? 1 : -1
    let page = Math.max(1, parseInt(req.query.page) || 1)
    let limit = Math.min(500, Math.max(1, parseInt(req.query.limit) || 50))
    let group = req.query.group === "true"
    if (boss === "stats") return res.json({ err: "dung /api/:id/stats" })
    const resp = { api: { id: api.id, name: api.displayName, owner: api.owner, ttl: api.ttl, encode: !!api.encode, totalJobs: 0 }, jobs: group ? {} : [] }
    if (boss !== "all") {
        let jobs = (api.jobs[boss] || []).sort((a, b) => sortOrder * (b.t - a.t))
        resp.api.totalJobs = jobs.length
        const sliced = jobs.slice((page - 1) * limit, page * limit).map(j => filterJobFields(j, api.customFields))
        if (group) resp.jobs[boss] = sliced; else resp.jobs = sliced
        resp.page = page; resp.totalPages = Math.ceil(jobs.length / limit)
    } else {
        if (group) {
            let total = 0
            for (let b in api.jobs) { resp.jobs[b] = [...api.jobs[b]].sort((a, bb) => sortOrder * (bb.t - a.t)).map(j => filterJobFields(j, api.customFields)); total += api.jobs[b].length }
            resp.api.totalJobs = total
        } else {
            let all = [], total = 0
            for (let b in api.jobs) { total += api.jobs[b].length; all.push(...api.jobs[b].map(j => ({ ...j, boss: b }))) }
            all.sort((a, b) => sortOrder * (b.t - a.t))
            resp.api.totalJobs = total; resp.jobs = all.slice((page - 1) * limit, page * limit).map(j => filterJobFields(j, api.customFields))
            resp.page = page; resp.totalPages = Math.ceil(total / limit)
        }
    }
    res.json(resp)
})

app.delete("/api/:id/job", async (req, res) => {
    let user = getUser(req), api = DB.apis[req.params.id]
    if (!api) return res.json({ err: "api khong ton tai" })
    if (!isAdminOrOwner(req) && api.owner !== user) return res.json({ err: "khong co quyen" })
    let { boss, job, index } = req.body
    if (!boss) return res.json({ err: "thieu boss" })
    boss = boss.toLowerCase()
    if (!api.jobs[boss]) return res.json({ err: "boss khong co job" })
    if (index !== undefined) {
        let i = parseInt(index)
        if (isNaN(i) || i < 0 || i >= api.jobs[boss].length) return res.json({ err: "index khong hop le" })
        api.jobs[boss].splice(i, 1); if (!api.jobs[boss].length) delete api.jobs[boss]
        await saveDB(); return res.json({ ok: 1 })
    }
    if (job) {
        const before = api.jobs[boss].length
        api.jobs[boss] = api.jobs[boss].filter(j => j.job !== job)
        if (!api.jobs[boss].length) delete api.jobs[boss]
        if ((api.jobs[boss]?.length ?? 0) === before) return res.json({ err: "khong tim thay job" })
        await saveDB(); return res.json({ ok: 1 })
    }
    res.json({ err: "can job hoac index" })
})

app.delete("/api/:id/clear", async (req, res) => {
    let user = getUser(req), api = DB.apis[req.params.id]
    if (!api) return res.json({ err: "api khong ton tai" })
    if (!isAdminOrOwner(req) && api.owner !== user) return res.json({ err: "khong co quyen" })
    let { boss } = req.body
    if (boss) delete api.jobs[boss.toLowerCase()]; else api.jobs = {}
    await saveDB(); res.json({ ok: 1 })
})

app.delete("/api/:id", async (req, res) => {
    let user = getUser(req), api = DB.apis[req.params.id]
    if (!api) return res.json({ err: "api khong ton tai" })
    if (!isAdminOrOwner(req) && api.owner !== user) return res.json({ err: "khong co quyen" })
    delete DB.apis[req.params.id]; await saveDB(); res.json({ ok: 1 })
})

app.post("/settings", async (req, res) => {
    let user = getUser(req)
    let { id, encodeText, ttl, webhook, displayName, privateMode, viewIP, removeDuplicate, prefix, suffix, maxJobsPerBoss, maxTotalJobs, enabled, whitelistIPs, jobSort, customFields, webhookCustom } = req.body
    let api = DB.apis[id]
    if (!api) return res.json({ err: "api khong ton tai" })
    if (!isAdminOrOwner(req) && api.owner !== user) return res.json({ err: "khong co quyen" })
    if (encodeText !== undefined) api.encode = parseEncode(encodeText)
    if (ttl !== undefined) api.ttl = Number(ttl)
    if (webhook !== undefined) api.webhook = webhook
    if (displayName !== undefined) api.displayName = displayName
    if (privateMode !== undefined) api.privateMode = toBool(privateMode)
    if (viewIP !== undefined) api.viewIP = viewIP
    if (removeDuplicate !== undefined) api.removeDuplicate = toBool(removeDuplicate)
    if (prefix !== undefined) api.prefix = String(prefix)
    if (suffix !== undefined) api.suffix = String(suffix)
    if (maxJobsPerBoss !== undefined) api.maxJobsPerBoss = Number(maxJobsPerBoss)
    if (maxTotalJobs !== undefined) api.maxTotalJobs = Number(maxTotalJobs)
    if (enabled !== undefined) api.enabled = toBool(enabled)
    if (whitelistIPs !== undefined) api.whitelistIPs = Array.isArray(whitelistIPs) ? whitelistIPs : []
    if (jobSort !== undefined && ["asc", "desc"].includes(jobSort)) api.jobSort = jobSort
    if (customFields !== undefined) api.customFields = Array.isArray(customFields) ? customFields : null
    if (webhookCustom !== undefined) api.webhookCustom = webhookCustom
    applyJobLimits(api); await saveDB(); res.json({ ok: 1 })
})

app.put("/api/:id/rename", async (req, res) => {
    let user = getUser(req), api = DB.apis[req.params.id]
    if (!api) return res.json({ err: "api khong ton tai" })
    if (!isAdminOrOwner(req) && api.owner !== user) return res.json({ err: "khong co quyen" })
    const { displayName } = req.body
    if (displayName !== undefined) {
        if (typeof displayName !== "string" || !displayName.trim()) return res.json({ err: "ten hien thi khong hop le" })
        api.displayName = displayName.trim()
        await saveDB()
        return res.json({ ok: 1, displayName: api.displayName })
    }
    res.json({ err: "thieu displayName" })
})

app.get("/owner", (req, res) => {
    if (!isAdminOrOwner(req)) return res.json({ err: "khong phai admin hoac owner" })
    res.json(DB)
})

app.post("/owner/edit", async (req, res) => {
    if (!isOwner(req)) return res.json({ err: "khong phai owner" })
    let { id, encodeText, ttl, webhook, displayName, privateMode, viewIP, removeDuplicate, prefix, suffix, maxJobsPerBoss, maxTotalJobs, enabled, whitelistIPs, jobSort, customFields, webhookCustom } = req.body
    let api = DB.apis[id]
    if (!api) return res.json({ err: "api khong ton tai" })
    if (encodeText !== undefined) api.encode = parseEncode(encodeText)
    if (ttl !== undefined) api.ttl = Number(ttl)
    if (webhook !== undefined) api.webhook = webhook
    if (displayName !== undefined) api.displayName = displayName
    if (privateMode !== undefined) api.privateMode = toBool(privateMode)
    if (viewIP !== undefined) api.viewIP = viewIP
    if (removeDuplicate !== undefined) api.removeDuplicate = toBool(removeDuplicate)
    if (prefix !== undefined) api.prefix = String(prefix)
    if (suffix !== undefined) api.suffix = String(suffix)
    if (maxJobsPerBoss !== undefined) api.maxJobsPerBoss = Number(maxJobsPerBoss)
    if (maxTotalJobs !== undefined) api.maxTotalJobs = Number(maxTotalJobs)
    if (enabled !== undefined) api.enabled = toBool(enabled)
    if (whitelistIPs !== undefined) api.whitelistIPs = Array.isArray(whitelistIPs) ? whitelistIPs : []
    if (jobSort !== undefined && ["asc", "desc"].includes(jobSort)) api.jobSort = jobSort
    if (customFields !== undefined) api.customFields = Array.isArray(customFields) ? customFields : null
    if (webhookCustom !== undefined) api.webhookCustom = webhookCustom
    applyJobLimits(api); await saveDB(); res.json({ ok: 1 })
})

app.get("/owner/stats", (req, res) => {
    if (!isOwner(req)) return res.json({ err: "khong phai owner" })
    let totalJobs = 0
    Object.values(DB.apis).forEach(api => Object.values(api.jobs).forEach(arr => totalJobs += arr.length))
    res.json({ totalApis: Object.keys(DB.apis).length, totalJobs, totalUsers: Object.keys(DB.users).length, activeSessions: Object.keys(DB.sessions).length, totalBots: Object.keys(DB.bots).length, runningBots: Object.values(DB.bots).filter(b => b.status === "running").length, totalMonitors: Object.keys(DB.monitors).length, onlineMonitors: Object.values(DB.monitors).filter(m => m.lastStatus === "online").length })
})

app.post("/owner/global-settings", async (req, res) => {
    if (!isOwner(req)) return res.json({ err: "khong phai owner" })
    let { ttl, prefix, suffix, encodeText, removeDuplicate, maxJobsPerBoss, maxTotalJobs, enabled, privateMode, whitelistIPs, jobSort, customFields, webhookCustom } = req.body
    if (ttl !== undefined) globalDefaults.ttl = Number(ttl)
    if (prefix !== undefined) globalDefaults.prefix = String(prefix)
    if (suffix !== undefined) globalDefaults.suffix = String(suffix)
    if (encodeText !== undefined) globalDefaults.encode = parseEncode(encodeText)
    if (removeDuplicate !== undefined) globalDefaults.removeDuplicate = toBool(removeDuplicate)
    if (maxJobsPerBoss !== undefined) globalDefaults.maxJobsPerBoss = Number(maxJobsPerBoss)
    if (maxTotalJobs !== undefined) globalDefaults.maxTotalJobs = Number(maxTotalJobs)
    if (enabled !== undefined) globalDefaults.enabled = toBool(enabled)
    if (privateMode !== undefined) globalDefaults.privateMode = toBool(privateMode)
    if (whitelistIPs !== undefined) globalDefaults.whitelistIPs = Array.isArray(whitelistIPs) ? whitelistIPs : []
    if (jobSort !== undefined && ["asc", "desc"].includes(jobSort)) globalDefaults.jobSort = jobSort
    if (customFields !== undefined) globalDefaults.customFields = Array.isArray(customFields) ? customFields : null
    if (webhookCustom !== undefined) globalDefaults.webhookCustom = webhookCustom
    await saveDB(); res.json({ ok: 1, globalDefaults })
})

app.get("/owner/global-settings", (req, res) => {
    if (!isOwner(req)) return res.json({ err: "khong phai owner" })
    res.json(globalDefaults)
})

app.post("/owner/reset-api-key", async (req, res) => {
    if (!isOwner(req)) return res.json({ err: "khong phai owner" })
    let api = DB.apis[req.body.id]
    if (!api) return res.json({ err: "api khong ton tai" })
    api.apiKey = genToken(); await saveDB(); res.json({ ok: 1, apiKey: api.apiKey })
})

app.post("/owner/change-owner", async (req, res) => {
    if (!isOwner(req)) return res.json({ err: "khong phai owner" })
    let { id, newOwner } = req.body
    let api = DB.apis[id]
    if (!api) return res.json({ err: "api khong ton tai" })
    if (!newOwner || !DB.users[newOwner]) return res.json({ err: "nguoi dung khong ton tai" })
    api.owner = newOwner; await saveDB(); res.json({ ok: 1 })
})

app.post("/owner/clean-all-expired", async (req, res) => {
    if (!isAdminOrOwner(req)) return res.json({ err: "khong phai admin hoac owner" })
    Object.values(DB.apis).forEach(api => { cleanExpiredJobs(api); applyJobLimits(api) })
    await saveDB(); res.json({ ok: 1 })
})

app.post("/owner/set-role", async (req, res) => {
    if (!isOwner(req)) return res.json({ err: "khong phai owner" })
    let { user, role } = req.body
    if (!user || !role || !DB.users[user]) return res.json({ err: "thieu thong tin hoac user khong ton tai" })
    if (!["member", "admin"].includes(role)) return res.json({ err: "role khong hop le" })
    DB.users[user].role = role; await saveDB(); res.json({ ok: 1, user, newRole: role })
})

app.get("/admin/users", (req, res) => {
    if (!isAdminOrOwner(req)) return res.json({ err: "khong phai admin hoac owner" })
    res.json(Object.entries(DB.users).map(([username, data]) => ({ username, role: data.role || "member", avatar: data.avatar || "", createdAt: data.createdAt })))
})

app.post("/admin/set-role", async (req, res) => {
    if (!isAdminOrOwner(req)) return res.json({ err: "khong phai admin hoac owner" })
    let { user, role } = req.body
    if (!user || !role || !DB.users[user]) return res.json({ err: "thieu thong tin hoac user khong ton tai" })
    if (!["member", "admin"].includes(role)) return res.json({ err: "role khong hop le" })
    if (DB.users[user].role === "owner") return res.json({ err: "khong the thay doi role cua owner" })
    DB.users[user].role = role; await saveDB(); res.json({ ok: 1, user, newRole: role })
})

app.post("/bot/create", upload.single("file"), async (req, res) => {
    let user = getUser(req)
    if (!user) return res.json({ err: "dang nhap di" })
    let { name, env, autoRestart } = req.body
    if (!name) return res.json({ err: "thieu ten bot" })
    if (!isAdminOrOwner(req)) {
        const existing = Object.values(DB.bots).filter(b => b.owner === user)
        if (existing.length >= BOT_LIMIT_USER) return res.json({ err: `Moi tai khoan chi duoc host ${BOT_LIMIT_USER} bot Discord. Xoa bot cu truoc!` })
    }
    let code = ""
    if (req.file) { code = fs.readFileSync(req.file.path, "utf8"); fs.unlinkSync(req.file.path) }
    else if (req.body.code) { code = req.body.code }
    else { return res.json({ err: "can upload file .py hoac gui code" }) }
    let envObj = {}
    try { envObj = JSON.parse(env || "{}") } catch {}
    const id = genID()
    DB.bots[id] = { id, name, owner: user, code: Buffer.from(code).toString("base64"), env: envObj, status: "stopped", pid: null, logs: [], autoRestart: toBool(autoRestart || false), restartCount: 0, created_at: now(), updated_at: now() }
    await saveDB(); res.json({ ok: 1, id })
})

app.get("/bot/my", (req, res) => {
    let user = getUser(req)
    if (!user) return res.json([])
    res.json(Object.values(DB.bots)
        .filter(b => b.owner === user || isAdminOrOwner(req))
        .map(b => ({ id: b.id, name: b.name, status: b.status, autoRestart: b.autoRestart || false, restartCount: b.restartCount || 0, envKeys: Object.keys(b.env || {}), created_at: b.created_at, updated_at: b.updated_at })))
})

app.post("/bot/:id/start", async (req, res) => {
    let user = getUser(req), bot = DB.bots[req.params.id]
    if (!bot) return res.json({ err: "bot khong ton tai" })
    if (bot.owner !== user && !isAdminOrOwner(req)) return res.json({ err: "khong co quyen" })
    if (bot.status === "running") return res.json({ err: "bot dang chay" })
    bot.logs = []; bot.restartCount = 0; bot.autoRestart = toBool(req.body.autoRestart !== undefined ? req.body.autoRestart : bot.autoRestart)
    spawnBot(bot); await saveDB(); res.json({ ok: 1, pid: bot.pid })
})

app.post("/bot/:id/stop", async (req, res) => {
    let user = getUser(req), bot = DB.bots[req.params.id]
    if (!bot) return res.json({ err: "bot khong ton tai" })
    if (bot.owner !== user && !isAdminOrOwner(req)) return res.json({ err: "khong co quyen" })
    bot.autoRestart = false
    if (bot.status !== "running" && bot.status !== "restarting" || !bot.pid) { bot.status = "stopped"; await saveDB(); return res.json({ ok: 1 }) }
    try {
        const child = activeProcesses.get(bot.id)
        if (child) { child.kill("SIGTERM"); activeProcesses.delete(bot.id) } else process.kill(bot.pid, "SIGTERM")
        bot.status = "stopped"; bot.pid = null; bot.updated_at = now()
        await saveDB(); res.json({ ok: 1 })
    } catch (e) { bot.status = "error"; await saveDB(); res.json({ err: "khong the kill: " + e.message }) }
})

app.delete("/bot/:id", async (req, res) => {
    let user = getUser(req), bot = DB.bots[req.params.id]
    if (!bot) return res.json({ err: "bot khong ton tai" })
    if (bot.owner !== user && !isAdminOrOwner(req)) return res.json({ err: "khong co quyen" })
    bot.autoRestart = false
    if ((bot.status === "running" || bot.status === "restarting") && bot.pid) {
        try { const child = activeProcesses.get(bot.id); if (child) child.kill("SIGKILL"); else process.kill(bot.pid, "SIGKILL"); activeProcesses.delete(bot.id) } catch {}
    }
    delete DB.bots[req.params.id]; await saveDB(); res.json({ ok: 1 })
})

app.get("/bot/:id/logs", (req, res) => {
    let user = getUser(req), bot = DB.bots[req.params.id]
    if (!bot) return res.json({ err: "bot khong ton tai" })
    if (bot.owner !== user && !isAdminOrOwner(req)) return res.json({ err: "khong co quyen" })
    res.json({ logs: bot.logs.slice(-100), status: bot.status, restartCount: bot.restartCount || 0 })
})

app.put("/bot/:id/rename", async (req, res) => {
    let user = getUser(req), bot = DB.bots[req.params.id]
    if (!bot) return res.json({ err: "bot khong ton tai" })
    if (bot.owner !== user && !isAdminOrOwner(req)) return res.json({ err: "khong co quyen" })
    const { name } = req.body
    if (!name || typeof name !== "string" || !name.trim()) return res.json({ err: "ten moi khong hop le" })
    bot.name = name.trim()
    bot.updated_at = now()
    await saveDB()
    res.json({ ok: 1, name: bot.name })
})

app.post("/monitor/create", async (req, res) => {
    let user = getUser(req)
    if (!user) return res.json({ err: "dang nhap di" })
    let { name, url, interval, webhook } = req.body
    if (!name || !url) return res.json({ err: "thieu name hoac url" })
    if (!url.startsWith("http")) return res.json({ err: "url phai bat dau bang http/https" })
    const id = genID()
    DB.monitors[id] = { id, name, url, owner: user, interval: Math.max(30000, Number(interval) || 60000), webhook: webhook || "", lastStatus: "waiting", lastPing: 0, lastCode: 0, lastError: null, lastCheck: 0, totalChecks: 0, goodChecks: 0, uptime: "0.00", retry: 0, history: [], created_at: now() }
    await saveDB()
    checkMonitor(DB.monitors[id])
    res.json({ ok: 1, id })
})

app.get("/monitor/my", (req, res) => {
    let user = getUser(req)
    if (!user) return res.json([])
    res.json(Object.values(DB.monitors).filter(m => m.owner === user || isAdminOrOwner(req)))
})

app.delete("/monitor/:id", async (req, res) => {
    let user = getUser(req), m = DB.monitors[req.params.id]
    if (!m) return res.json({ err: "monitor khong ton tai" })
    if (m.owner !== user && !isAdminOrOwner(req)) return res.json({ err: "khong co quyen" })
    delete DB.monitors[req.params.id]; await saveDB(); res.json({ ok: 1 })
})

app.get("/monitor/:id", (req, res) => {
    const m = DB.monitors[req.params.id]
    if (!m) return res.json({ err: "khong tim thay" })
    res.json(m)
})

app.put("/monitor/:id/rename", async (req, res) => {
    let user = getUser(req), mon = DB.monitors[req.params.id]
    if (!mon) return res.json({ err: "monitor khong ton tai" })
    if (mon.owner !== user && !isAdminOrOwner(req)) return res.json({ err: "khong co quyen" })
    const { name } = req.body
    if (!name || typeof name !== "string" || !name.trim()) return res.json({ err: "ten moi khong hop le" })
    mon.name = name.trim()
    await saveDB()
    res.json({ ok: 1, name: mon.name })
})

const wss = new WebSocket.Server({ server: httpServer, path: "/ws" })

wss.on("connection", (ws, req) => {
    const token = new URL(req.url, `http://${req.headers.host}`).searchParams.get("token") || ""
    const session = DB.sessions[token]
    if (!session) { ws.close(4001, "Unauthorized"); return }
    const username = session.user
    const avatar = DB.users[username]?.avatar || ""
    chatClients.set(ws, { username, avatar })
    ws.send(JSON.stringify({ type: "history", messages: chatMessages.slice(-50) }))
    ws.on("message", raw => {
        let msg
        try { msg = JSON.parse(raw) } catch { return }
        if (msg.type === "msg" && typeof msg.content === "string" && msg.content.trim().length > 0 && msg.content.length <= 500) {
            const chatMsg = { user: username, avatar, content: msg.content.trim(), timestamp: now() }
            chatMessages.push(chatMsg)
            if (chatMessages.length > MAX_CHAT_MESSAGES) chatMessages.shift()
            broadcast({ type: "msg", ...chatMsg })
        }
    })
    ws.on("close", () => chatClients.delete(ws))
    ws.on("error", () => chatClients.delete(ws))
})

function broadcast(payload) {
    const data = JSON.stringify(payload)
    for (const [ws] of chatClients) { try { ws.send(data) } catch {} }
}

;(async () => {
    if (!fs.existsSync("/tmp/bot_uploads")) fs.mkdirSync("/tmp/bot_uploads", { recursive: true })
    await loadDB()
    httpServer.listen(PORT, () => console.log("Server running on port " + PORT))
})()
