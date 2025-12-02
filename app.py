from flask import (
    Flask, render_template, request, redirect,
    url_for, session, flash, g, make_response
)
from werkzeug.security import generate_password_hash, check_password_hash
from functools import wraps
import sqlite3
import datetime


# =========================================================
# Westgard / Stats Helpers (ของเดิมคุณ)
# =========================================================
def _sign(x: float) -> int:
    if x > 0:
        return 1
    if x < 0:
        return -1
    return 0


def _fallback_sd(values, mean):
    """กันเคส SD=0 เพื่อให้คำนวณ rule ได้ (ข้อมูลน้อย/ค่าซ้ำกันหมด)"""
    if not values:
        return 1.0
    vmin, vmax = min(values), max(values)
    spread = vmax - vmin
    if spread > 0:
        return spread / 4.0  # สมมติ range ~ 4SD (±2SD)
    if mean != 0:
        return abs(mean) * 0.05
    return 1.0


def _mean_sd(values):
    import statistics
    mean = statistics.fmean(values)
    sd = statistics.pstdev(values) if len(values) > 1 else 0.0
    if not sd or sd == 0:
        sd = _fallback_sd(values, mean)
    return mean, sd


def build_level_stats(points):
    """
    points: list[dict] ต้องมี keys: level, value
    คืนค่า dict: { "Level 0": {"mean":..., "sd":...}, ... }
    """
    from collections import defaultdict
    grp = defaultdict(list)
    for p in points:
        if p.get("value") is not None:
            grp[p["level"]].append(p["value"])

    stats = {}
    for lvl, vals in grp.items():
        if vals:
            m, s = _mean_sd(vals)
            stats[lvl] = {"mean": m, "sd": s}
    return stats


def apply_run_r4s(points_all, level_stats):
    """
    R-4s (within-run):
      ใน run เดียวกัน (dept + date) ถ้ามีอย่างน้อย 1 level ที่ z >= +2
      และอย่างน้อย 1 level ที่ z <= -2  => R-4s
    mark เฉพาะจุดที่เป็นตัว trigger (abs(z)>=2) ใน run นั้น
    คืน set ของ ids ที่โดน R-4s
    """
    from collections import defaultdict

    enriched = []
    for p in points_all:
        lvl = p["level"]
        v = p.get("value")
        st = level_stats.get(lvl)
        if not st or v is None:
            z = 0.0
        else:
            z = (v - st["mean"]) / st["sd"] if st["sd"] else 0.0
        ep = dict(p)
        ep["z_run"] = z
        enriched.append(ep)

    runs = defaultdict(list)
    for ep in enriched:
        runs[(ep["dept"], ep["date"])].append(ep)

    bad_ids = set()
    for _, pts in runs.items():
        zs = [pp["z_run"] for pp in pts]
        if any(z >= 2 for z in zs) and any(z <= -2 for z in zs):
            for pp in pts:
                if abs(pp["z_run"]) >= 2:
                    bad_ids.add(pp["id"])

    return bad_ids


def evaluate_westgard_series(points, mean: float, sd: float):
    """
    Westgard แบบ series ตามเวลา (ใน level เดียว):
      1-2s (warning), 1-3s, 2-2s, 4-1s, 10x

    points: list[dict] ต้องมี {"id","value","date"}
    คืน:
      - points_enriched: เพิ่ม z, rules, severity
      - violations: รายการ reject เพื่อโชว์ใต้กราฟ
    """
    pts = [dict(p) for p in points]
    values = [p["value"] for p in pts if p.get("value") is not None]
    if not values:
        for p in pts:
            p["z"] = 0.0
            p["rules"] = []
            p["severity"] = "ok"
        return pts, []

    if not sd or sd == 0:
        sd = _fallback_sd(values, mean)

    z = []
    for p in pts:
        v = p.get("value")
        zi = (v - mean) / sd if (v is not None and sd) else 0.0
        z.append(zi)

    rules_by_idx = [set() for _ in pts]

    # 1-2s / 1-3s
    for i, zi in enumerate(z):
        if abs(zi) >= 3:
            rules_by_idx[i].add("1-3s")
        if abs(zi) >= 2:
            rules_by_idx[i].add("1-2s")  # warning

    # 2-2s
    for i in range(1, len(z)):
        if (abs(z[i]) >= 2) and (abs(z[i - 1]) >= 2) and (_sign(z[i]) == _sign(z[i - 1])) and (_sign(z[i]) != 0):
            rules_by_idx[i].add("2-2s")
            rules_by_idx[i - 1].add("2-2s")

    # 4-1s
    for i in range(3, len(z)):
        window = z[i - 3:i + 1]
        s = _sign(window[0])
        if s != 0 and all(_sign(w) == s and abs(w) >= 1 for w in window):
            for k in range(i - 3, i + 1):
                rules_by_idx[k].add("4-1s")

    # 10x
    for i in range(9, len(z)):
        window = z[i - 9:i + 1]
        s = _sign(window[0])
        if s != 0 and all(_sign(w) == s for w in window):
            for k in range(i - 9, i + 1):
                rules_by_idx[k].add("10x")

    reject_set = {"1-3s", "2-2s", "4-1s", "10x"}
    violations = []

    for i, p in enumerate(pts):
        r = sorted(list(rules_by_idx[i]))
        p["z"] = z[i]
        p["rules"] = r

        if any(rr in reject_set for rr in r):
            p["severity"] = "reject"
            violations.append({
                "id": p.get("id"),
                "index": i + 1,
                "date": p.get("date"),
                "dept": p.get("dept"),
                "level": p.get("level"),
                "value": p.get("value"),
                "z": p.get("z"),
                "rules": r
            })
        elif "1-2s" in r:
            p["severity"] = "warning"
        else:
            p["severity"] = "ok"

    return pts, violations


# =========================================================
# App / Auth / DB
# =========================================================
import os

app = Flask(__name__)
app.secret_key = os.environ.get("SECRET_KEY", "dev-secret-key")
    
def login_required(f):
    @wraps(f)
    def decorated_function(*args, **kwargs):
        if "user_id" not in session:
            flash("กรุณาเข้าสู่ระบบก่อนใช้งาน", "warning")
            return redirect(url_for("login"))
        return f(*args, **kwargs)
    return decorated_function


def is_admin():
    return session.get("username") == "Admin"


def admin_required(f):
    @wraps(f)
    def decorated_function(*args, **kwargs):
        if not is_admin():
            flash("คุณไม่มีสิทธิ์เข้าหน้านี้ (เฉพาะผู้ดูแลระบบ)", "danger")
            return redirect(url_for("qc_form"))
        return f(*args, **kwargs)
    return decorated_function


@app.context_processor
def inject_user_info():
    return {
        "is_admin": is_admin(),
        "current_username": session.get("username"),
    }


def get_db():
    if not hasattr(g, "_database"):
        g._database = sqlite3.connect("chondaen_iqc_bgm.db")
        g._database.row_factory = sqlite3.Row
    return g._database


@app.teardown_appcontext
def close_db(exception=None):
    db = getattr(g, "_database", None)
    if db is not None:
        db.close()


def init_db():
    db = get_db()

    # users (ตัวอย่างพื้นฐาน)
    db.execute(
        """
        CREATE TABLE IF NOT EXISTS users (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            username TEXT UNIQUE NOT NULL,
            password_hash TEXT NOT NULL
        )
        """
    )

    # qc_results (ตัวอย่างพื้นฐาน)
    db.execute(
        """
        CREATE TABLE IF NOT EXISTS qc_results (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            test_name TEXT,
            level TEXT,
            result_date TEXT,
            value REAL,
            user_id INTEGER,
            FOREIGN KEY (user_id) REFERENCES users(id)
        )
        """
    )
    db.commit()


def _norm(s: str) -> str:
    s = (s or "")
    s = s.replace("\r", "").replace("\n", "")
    s = s.replace("\u200b", "").replace("\ufeff", "")  # กัน zero-width/BOM
    return s.strip()


def fetch_user_by_username(db, username: str):
    """รองรับ schema ที่อาจเป็น password_hash หรือ password"""
    try:
        return db.execute(
            "SELECT id, username, password_hash AS pw FROM users WHERE username = ?",
            (username,),
        ).fetchone()
    except Exception:
        return db.execute(
            "SELECT id, username, password AS pw FROM users WHERE username = ?",
            (username,),
        ).fetchone()


def insert_user_fallback(db, username: str, pw_hash: str):
    """รองรับ schema ได้ทั้ง password_hash และ password และ (อาจมี/ไม่มี) is_admin"""
    insert_variants = [
        ("INSERT INTO users (username, password_hash, is_admin) VALUES (?, ?, 0)", (username, pw_hash)),
        ("INSERT INTO users (username, password, is_admin) VALUES (?, ?, 0)", (username, pw_hash)),
        ("INSERT INTO users (username, password_hash) VALUES (?, ?)", (username, pw_hash)),
        ("INSERT INTO users (username, password) VALUES (?, ?)", (username, pw_hash)),
    ]
    last_err = None
    for sql, params in insert_variants:
        try:
            db.execute(sql, params)
            db.commit()
            return True, None
        except Exception as e:
            last_err = e
    return False, last_err


def set_password(db, user_id: int, new_password: str):
    pw_hash = generate_password_hash(new_password)

    variants = [
        ("UPDATE users SET password_hash = ? WHERE id = ?", (pw_hash, user_id)),
        ("UPDATE users SET password = ? WHERE id = ?", (pw_hash, user_id)),
    ]

    last_err = None
    for sql, params in variants:
        try:
            db.execute(sql, params)
            db.commit()
            return True, None
        except Exception as e:
            last_err = e
    return False, last_err


def ensure_admin_user():
    db = get_db()
    row = db.execute("SELECT id FROM users WHERE username = ?", ("Admin",)).fetchone()
    if row is None:
        ok, err = insert_user_fallback(db, "Admin", generate_password_hash("111"))
        if not ok:
            # ถ้า schema แปลกมากจริง ๆ จะได้รู้
            print("Ensure Admin failed:", err)


# =========================================================
# Routes: Index / Login / Logout / Register
# =========================================================
@app.route("/")
def index():
    if "user_id" in session:
        return redirect(url_for("qc_form"))
    return redirect(url_for("login"))


@app.route("/login", methods=["GET", "POST"])
def login():
    if request.method == "POST":
        username = _norm(request.form.get("username"))
        password = _norm(request.form.get("password"))

        db = get_db()
        user = fetch_user_by_username(db, username)

        if user and check_password_hash(user["pw"], password):
            session["user_id"] = user["id"]
            session["username"] = user["username"]
            flash("เข้าสู่ระบบสำเร็จ", "success")
            return redirect(url_for("qc_form"))
        else:
            flash("ชื่อผู้ใช้หรือรหัสผ่านไม่ถูกต้อง", "danger")

    return render_template("login.html")


@app.route("/register", methods=["GET", "POST"])
def register():
    if request.method == "POST":
        username = _norm(request.form.get("username"))
        password = _norm(request.form.get("password"))
        confirm = _norm(request.form.get("confirm_password"))

        if not username:
            flash("กรุณากรอก Username", "danger")
            return render_template("register.html")

        if username.lower() == "admin":
            flash("Username นี้สงวนไว้สำหรับผู้ดูแลระบบ", "danger")
            return render_template("register.html")

        if not confirm:
            flash("กรุณากรอก Confirm Password", "danger")
            return render_template("register.html")

        if password != confirm:
            flash("Password และ Confirm Password ไม่ตรงกัน", "danger")
            return render_template("register.html")

        if len(password) < 4:
            flash("Password สั้นเกินไป (อย่างน้อย 4 ตัวอักษร)", "danger")
            return render_template("register.html")

        db = get_db()

        # เช็คซ้ำ
        existing = db.execute("SELECT id FROM users WHERE username = ?", (username,)).fetchone()
        if existing:
            flash("Username นี้ถูกใช้แล้ว", "danger")
            return render_template("register.html")

        pw_hash = generate_password_hash(password)
        ok, err = insert_user_fallback(db, username, pw_hash)
        if not ok:
            flash(f"สมัครสมาชิกไม่สำเร็จ (DB schema อาจไม่ตรง): {err}", "danger")
            return render_template("register.html")

        flash("สมัครสมาชิกสำเร็จ กรุณาเข้าสู่ระบบ", "success")
        return redirect(url_for("login"))

    return render_template("register.html")


@app.route("/logout")
def logout():
    session.clear()
    flash("ออกจากระบบเรียบร้อยแล้ว", "success")
    return redirect(url_for("login"))


# =========================================================
# QC Form
# =========================================================
@app.route("/qc", methods=["GET", "POST"])
@login_required
def qc_form():
    db = get_db()

    if request.method == "POST":
        columns_to_add = [
            ("user_id", "INTEGER"),
            ("result_date", "TEXT"),
            ("test_name", "TEXT"),
            ("level", "TEXT"),
            ("value", "REAL"),
            ("ref_min", "REAL"),
            ("ref_max", "REAL"),
            ("bgm_serial", "TEXT"),
            ("strip_lot", "TEXT"),
            ("strip_exp", "TEXT"),
            ("control_lot", "TEXT"),
            ("control_exp", "TEXT"),
        ]
        for col_name, col_type in columns_to_add:
            try:
                db.execute(f"ALTER TABLE qc_results ADD COLUMN {col_name} {col_type}")
            except sqlite3.OperationalError:
                pass

        department = _norm(request.form.get("department"))
        qc_date = request.form.get("qc_date") or datetime.date.today().isoformat()
        bgm_serial = _norm(request.form.get("bgm_serial"))
        strip_lot = _norm(request.form.get("strip_lot"))
        strip_exp = request.form.get("strip_exp") or None

        user_id = session.get("user_id")

        def save_level(level_label: str, prefix: str):
            ctrl_lot = _norm(request.form.get(f"{prefix}_lot"))
            ctrl_exp = request.form.get(f"{prefix}_exp") or None
            ref_min = request.form.get(f"{prefix}_ref_min")
            ref_max = request.form.get(f"{prefix}_ref_max")
            value = request.form.get(f"{prefix}_value")

            if not value:
                return
            try:
                value_f = float(value)
            except ValueError:
                return

            ref_min_f = float(ref_min) if ref_min else None
            ref_max_f = float(ref_max) if ref_max else None

            db.execute(
                """
                INSERT INTO qc_results
                (user_id, result_date, test_name, level,
                 value, ref_min, ref_max,
                 bgm_serial, strip_lot, strip_exp,
                 control_lot, control_exp)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                """,
                (
                    user_id, qc_date, department, level_label,
                    value_f, ref_min_f, ref_max_f,
                    bgm_serial, strip_lot, strip_exp,
                    ctrl_lot, ctrl_exp
                )
            )

        save_level("Level 0", "ctrl0")
        save_level("Level 1", "ctrl1")
        save_level("Level 2", "ctrl2")

        db.commit()
        flash("บันทึกผล QC สำเร็จ", "success")
        return redirect(url_for("qc_form"))

    return render_template("qc_form.html")


# =========================================================
# QC Chart
# =========================================================
@app.route("/qc/chart")
@login_required
def qc_chart():
    db = get_db()

    combos = db.execute(
        """
        SELECT DISTINCT test_name, level
        FROM qc_results
        ORDER BY test_name, level
        """
    ).fetchall()

    mode = request.args.get("mode", "level")  # level / single
    level = request.args.get("level")
    test_name = request.args.get("test_name")
    start_date = request.args.get("start_date", "")
    end_date = request.args.get("end_date", "")

    if not combos:
        return render_template(
            "qc_chart.html",
            combos=[],
            mode=mode,
            test_name=None,
            level=None,
            stats=None,
            data_points=[],
            violations=[],
            start_date=start_date,
            end_date=end_date,
        )

    if mode not in ("level", "single"):
        mode = "level"

    params = []
    if mode == "level":
        if not level:
            level = combos[0]["level"]
        q_display = """
            SELECT id, result_date, value, test_name, level
            FROM qc_results
            WHERE level = ?
        """
        params = [level]
    else:
        if not test_name or not level:
            first = combos[0]
            test_name = first["test_name"]
            level = first["level"]
        q_display = """
            SELECT id, result_date, value, test_name, level
            FROM qc_results
            WHERE test_name = ? AND level = ?
        """
        params = [test_name, level]

    if start_date:
        q_display += " AND result_date >= ?"
        params.append(start_date)
    if end_date:
        q_display += " AND result_date <= ?"
        params.append(end_date)

    q_display += " ORDER BY result_date, test_name, id"
    rows = db.execute(q_display, params).fetchall()

    display_points = [
        {"id": r["id"], "date": r["result_date"], "value": r["value"], "dept": r["test_name"], "level": r["level"]}
        for r in rows if r["value"] is not None
    ]

    if not display_points:
        return render_template(
            "qc_chart.html",
            combos=combos,
            mode=mode,
            test_name=None if mode == "level" else test_name,
            level=level,
            stats=None,
            data_points=[],
            violations=[],
            start_date=start_date,
            end_date=end_date,
        )

    params_all = []
    if mode == "single":
        q_all = """
            SELECT id, result_date, value, test_name, level
            FROM qc_results
            WHERE test_name = ?
        """
        params_all = [test_name]
    else:
        q_all = """
            SELECT id, result_date, value, test_name, level
            FROM qc_results
            WHERE 1=1
        """

    if start_date:
        q_all += " AND result_date >= ?"
        params_all.append(start_date)
    if end_date:
        q_all += " AND result_date <= ?"
        params_all.append(end_date)

    q_all += " ORDER BY result_date, test_name, level, id"
    all_rows = db.execute(q_all, params_all).fetchall()

    all_points = [
        {"id": r["id"], "date": r["result_date"], "value": r["value"], "dept": r["test_name"], "level": r["level"]}
        for r in all_rows if r["value"] is not None
    ]

    level_stats = build_level_stats(all_points)

    disp_vals = [p["value"] for p in display_points]
    mean_disp, sd_disp = _mean_sd(disp_vals)

    if level in level_stats:
        mean_disp = level_stats[level]["mean"]
        sd_disp = level_stats[level]["sd"]

    stats = {"n": len(disp_vals), "mean": mean_disp, "sd": sd_disp}

    from collections import defaultdict
    grp = defaultdict(list)
    for p in display_points:
        grp[p["dept"]].append(p)

    enriched_all = []
    violations_all = []

    bad_r4_ids = apply_run_r4s(all_points, level_stats)

    for dept, pts in grp.items():
        pts_sorted = sorted(pts, key=lambda x: (x["date"], x["id"]))
        enriched, _ = evaluate_westgard_series(pts_sorted, mean_disp, sd_disp)

        for ep in enriched:
            if ep["id"] in bad_r4_ids:
                ep.setdefault("rules", [])
                if "R-4s" not in ep["rules"]:
                    ep["rules"].append("R-4s")
                    ep["rules"] = sorted(ep["rules"])
                ep["severity"] = "reject"

        for ep in enriched:
            if ep.get("severity") == "reject":
                violations_all.append({
                    "id": ep.get("id"),
                    "date": ep.get("date"),
                    "dept": ep.get("dept"),
                    "level": ep.get("level"),
                    "value": ep.get("value"),
                    "z": ep.get("z", 0.0),
                    "rules": ep.get("rules", []),
                })

        enriched_all.extend(enriched)

    return render_template(
        "qc_chart.html",
        combos=combos,
        mode=mode,
        test_name=None if mode == "level" else test_name,
        level=level,
        stats=stats,
        data_points=enriched_all,
        violations=violations_all,
        start_date=start_date,
        end_date=end_date,
    )


# =========================================================
# Admin: Reset password (เหลืออันเดียว! ไม่ซ้ำชื่อฟังก์ชัน)
# =========================================================
@app.route("/admin/users/<int:user_id>/reset_password", methods=["POST"])
@login_required
@admin_required
def admin_reset_password(user_id):
    new_password = _norm(request.form.get("new_password"))
    confirm = _norm(request.form.get("confirm_password"))

    if len(new_password) < 4:
        flash("รหัสผ่านใหม่ต้องยาวอย่างน้อย 4 ตัวอักษร", "danger")
        return redirect(url_for("admin_users"))

    if confirm and (new_password != confirm):
        flash("Password และ Confirm Password ไม่ตรงกัน", "danger")
        return redirect(url_for("admin_users"))

    db = get_db()
    ok, err = set_password(db, user_id, new_password)
    if not ok:
        flash(f"รีเซ็ตรหัสผ่านไม่สำเร็จ: {err}", "danger")
        return redirect(url_for("admin_users"))

    flash("รีเซ็ตรหัสผ่านสำเร็จ", "success")
    return redirect(url_for("admin_users"))


# =========================================================
# Export history CSV
# =========================================================
@app.route("/qc/history/export")
@login_required
@admin_required
def qc_history_export():
    import csv, io

    db = get_db()
    start_date = request.args.get("start_date", "")
    end_date = request.args.get("end_date", "")

    query = """
        SELECT id, result_date, test_name, level,
               value, ref_min, ref_max,
               bgm_serial, strip_lot, strip_exp,
               control_lot, control_exp
        FROM qc_results
        WHERE 1=1
    """
    params = []

    if start_date:
        query += " AND result_date >= ?"
        params.append(start_date)
    if end_date:
        query += " AND result_date <= ?"
        params.append(end_date)

    query += " ORDER BY result_date, test_name, level, id"
    rows = db.execute(query, params).fetchall()

    output = io.StringIO()
    writer = csv.writer(output)

    writer.writerow([
        "ID", "วันที่ตรวจ", "หน่วยงาน/เครื่อง", "Level", "ผล (mg/dL)",
        "ค่าอ้างอิงต่ำสุด", "ค่าอ้างอิงสูงสุด",
        "BGM Serial", "Strip Lot", "Strip Exp", "Control Lot", "Control Exp",
    ])

    for r in rows:
        writer.writerow([
            r["id"], r["result_date"], r["test_name"], r["level"], r["value"],
            r["ref_min"], r["ref_max"],
            r["bgm_serial"], r["strip_lot"], r["strip_exp"], r["control_lot"], r["control_exp"],
        ])

    csv_data = "\ufeff" + output.getvalue()
    output.close()

    resp = make_response(csv_data)
    resp.headers["Content-Type"] = "text/csv; charset=utf-8"
    resp.headers["Content-Disposition"] = "attachment; filename=chondaen_iqc_history.csv"
    return resp

@app.route("/qc/history")
@login_required
@admin_required
def qc_history():
    db = get_db()
    start_date = request.args.get("start_date", "")
    end_date = request.args.get("end_date", "")

    query = """
        SELECT id, result_date, test_name, level,
               value, ref_min, ref_max,
               bgm_serial, strip_lot, strip_exp,
               control_lot, control_exp
        FROM qc_results
        WHERE 1=1
    """
    params = []

    if start_date:
        query += " AND result_date >= ?"
        params.append(start_date)
    if end_date:
        query += " AND result_date <= ?"
        params.append(end_date)

    query += " ORDER BY result_date DESC, test_name, level, id DESC"

    rows = db.execute(query, params).fetchall()
    results = [dict(r) for r in rows]  # ✅ ส่งเป็น dict ชัวร์

    return render_template(
        "qc_history.html",
        results=results,
        start_date=start_date,
        end_date=end_date,
    )


# =========================================================
# Delete QC
# =========================================================
@app.route("/qc/delete/<int:qc_id>", methods=["POST"])
@login_required
@admin_required
def qc_delete(qc_id):
    db = get_db()
    db.execute("DELETE FROM qc_results WHERE id = ?", (qc_id,))
    db.commit()
    flash("ลบรายการ QC เรียบร้อยแล้ว", "success")
    return redirect(request.referrer or url_for("qc_form"))


# =========================================================
# Summary + Export
# =========================================================
@app.route("/qc/summary", methods=["GET"])
@login_required
@admin_required
def qc_summary():
    db = get_db()
    start_date = request.args.get("start_date", "")
    end_date = request.args.get("end_date", "")

    query = """
        SELECT test_name, level, result_date, value, ref_min, ref_max
        FROM qc_results
        WHERE 1=1
    """
    params = []

    if start_date:
        query += " AND result_date >= ?"
        params.append(start_date)
    if end_date:
        query += " AND result_date <= ?"
        params.append(end_date)

    rows = db.execute(query, params).fetchall()

    from collections import defaultdict
    import statistics

    groups = defaultdict(list)
    for r in rows:
        groups[(r["test_name"], r["level"])].append(r)

    summary = []
    for (test_name, level), items in groups.items():
        values = [i["value"] for i in items if i["value"] is not None]
        if not values:
            continue

        mean = statistics.fmean(values)
        sd = statistics.pstdev(values) if len(values) > 1 else 0.0
        vmin = min(values)
        vmax = max(values)

        ref_mins = [i["ref_min"] for i in items if i["ref_min"] is not None]
        ref_maxs = [i["ref_max"] for i in items if i["ref_max"] is not None]
        ref_min = ref_mins[0] if ref_mins else None
        ref_max = ref_maxs[0] if ref_maxs else None

        summary.append({
            "test_name": test_name,
            "level": level,
            "n": len(values),
            "mean": mean,
            "sd": sd,
            "min": vmin,
            "max": vmax,
            "ref_min": ref_min,
            "ref_max": ref_max,
        })

    summary.sort(key=lambda x: (x["test_name"], x["level"]))

    return render_template("qc_summary.html", summary=summary, start_date=start_date, end_date=end_date)


@app.route("/qc/summary/export")
@login_required
@admin_required
def qc_summary_export():
    import csv, io
    db = get_db()

    start_date = request.args.get("start_date", "")
    end_date = request.args.get("end_date", "")

    query = """
        SELECT test_name, level, result_date, value, ref_min, ref_max
        FROM qc_results
        WHERE 1=1
    """
    params = []
    if start_date:
        query += " AND result_date >= ?"
        params.append(start_date)
    if end_date:
        query += " AND result_date <= ?"
        params.append(end_date)

    rows = db.execute(query, params).fetchall()

    from collections import defaultdict
    import statistics

    groups = defaultdict(list)
    for r in rows:
        groups[(r["test_name"], r["level"])].append(r)

    summary_rows = []
    for (test_name, level), items in groups.items():
        values = [i["value"] for i in items if i["value"] is not None]
        if not values:
            continue
        mean = statistics.fmean(values)
        sd = statistics.pstdev(values) if len(values) > 1 else 0.0
        vmin = min(values)
        vmax = max(values)

        ref_mins = [i["ref_min"] for i in items if i["ref_min"] is not None]
        ref_maxs = [i["ref_max"] for i in items if i["ref_max"] is not None]
        ref_min = ref_mins[0] if ref_mins else None
        ref_max = ref_maxs[0] if ref_maxs else None

        summary_rows.append({
            "test_name": test_name,
            "level": level,
            "n": len(values),
            "mean": mean,
            "sd": sd,
            "min": vmin,
            "max": vmax,
            "ref_min": ref_min,
            "ref_max": ref_max,
        })

    summary_rows.sort(key=lambda x: (x["test_name"], x["level"]))

    output = io.StringIO()
    writer = csv.writer(output)

    writer.writerow([
        "หน่วยงาน/เครื่อง", "Level", "จำนวน (n)", "Mean", "SD", "Min", "Max", "Ref Min", "Ref Max"
    ])

    for row in summary_rows:
        writer.writerow([
            row["test_name"], row["level"], row["n"], row["mean"], row["sd"],
            row["min"], row["max"], row["ref_min"], row["ref_max"],
        ])

    csv_data = "\ufeff" + output.getvalue()
    output.close()

    resp = make_response(csv_data)
    resp.headers["Content-Type"] = "text/csv; charset=utf-8"
    resp.headers["Content-Disposition"] = "attachment; filename=chondaen_iqc_summary.csv"
    return resp


# =========================================================
# Admin: Users list (ไม่โชว์ password)
# =========================================================
@app.route("/admin/users")
@login_required
@admin_required
def admin_users():
    db = get_db()
    users = db.execute("SELECT id, username FROM users ORDER BY id").fetchall()
    return render_template("admin_users.html", users=users)


# =========================================================
# Boot
# =========================================================
with app.app_context():
    init_db()
    ensure_admin_user()


if __name__ == "__main__":
    app.run(host="0.0.0.0", port=5000, debug=False)
