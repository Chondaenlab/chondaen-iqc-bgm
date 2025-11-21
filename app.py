from flask import Flask, render_template, request, redirect, url_for, session, flash, Response
from werkzeug.security import generate_password_hash, check_password_hash
from functools import wraps
import sqlite3
from datetime import datetime
import os
import io
import csv

app = Flask(__name__)
app.secret_key = "CHANGE_ME_TO_SOMETHING_SECRET"
DATABASE = "qc_app.db"


# ---------- Helper สำหรับฐานข้อมูล ----------
def get_db():
    conn = sqlite3.connect(DATABASE)
    conn.row_factory = sqlite3.Row
    return conn


def init_db():
    conn = get_db()
    cur = conn.cursor()

    # ตาราง users (เพิ่ม is_admin)
    cur.execute("""
        CREATE TABLE IF NOT EXISTS users (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            username TEXT UNIQUE NOT NULL,
            password_hash TEXT NOT NULL,
            is_admin INTEGER NOT NULL DEFAULT 0
        )
    """)

    # เผื่อมีตาราง users เก่า -> พยายามเพิ่มคอลัมน์ is_admin
    try:
        cur.execute("ALTER TABLE users ADD COLUMN is_admin INTEGER NOT NULL DEFAULT 0")
    except sqlite3.OperationalError:
        pass

    # ตั้งผู้ดูแลระบบตามชื่อที่กำหนด
    cur.execute("UPDATE users SET is_admin = 1 WHERE username = ?", ("เอกชัย สีทาสังข์",))

    # ตาราง qc_results (แบบใหม่ รองรับ BGM Serial, Exp., Ref)
    cur.execute("""
        CREATE TABLE IF NOT EXISTS qc_results (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            test_name TEXT NOT NULL,
            level TEXT NOT NULL,
            bgm_serial TEXT,
            strip_lot TEXT,
            strip_expiry TEXT,
            control_lot TEXT,
            control_expiry TEXT,
            result_value REAL NOT NULL,
            unit TEXT,
            ref_min REAL,
            ref_max REAL,
            test_date TEXT NOT NULL,
            created_at TEXT NOT NULL,
            FOREIGN KEY(user_id) REFERENCES users(id)
        )
    """)

    # กรณีมีฐานข้อมูล qc_results เก่า → เพิ่มคอลัมน์ใหม่ (ถ้ามีอยู่แล้วจะ error ก็ข้าม)
    new_columns = [
        ("bgm_serial", "TEXT"),
        ("strip_expiry", "TEXT"),
        ("control_expiry", "TEXT"),
        ("ref_min", "REAL"),
        ("ref_max", "REAL"),
    ]
    for col_name, col_type in new_columns:
        try:
            cur.execute(f"ALTER TABLE qc_results ADD COLUMN {col_name} {col_type}")
        except sqlite3.OperationalError:
            pass

    conn.commit()
    conn.close()


if not os.path.exists(DATABASE):
    init_db()
else:
    init_db()


# ---------- Decorator บังคับให้ต้องล็อกอิน ----------
def login_required(f):
    @wraps(f)
    def decorated_function(*args, **kwargs):
        if "user_id" not in session:
            flash("กรุณาเข้าสู่ระบบก่อน", "warning")
            return redirect(url_for("login"))
        return f(*args, **kwargs)
    return decorated_function


def is_current_user_admin():
    """เช็กจากฐานข้อมูลว่าผู้ใช้ปัจจุบันเป็น admin หรือไม่"""
    user_id = session.get("user_id")
    if not user_id:
        return False
    conn = get_db()
    cur = conn.cursor()
    cur.execute("SELECT is_admin FROM users WHERE id = ?", (user_id,))
    row = cur.fetchone()
    conn.close()
    if row is None:
        return False
    return bool(row["is_admin"])


# ---------- ฟังก์ชันเช็ก Westgard rules ----------
def evaluate_westgard(values, mean, sd):
    n = len(values)
    if n == 0 or sd is None or sd <= 0:
        return [[] for _ in values]

    z = [(v - mean) / sd for v in values]
    rules_by_point = [[] for _ in values]

    # 1-3s
    for i in range(n):
        if abs(z[i]) >= 3:
            rules_by_point[i].append("1-3s")

    # 1-2s (warning)
    for i in range(n):
        if abs(z[i]) >= 2 and "1-3s" not in rules_by_point[i]:
            rules_by_point[i].append("1-2s")

    # 2-2s: สองค่าติดกัน ฝั่งเดียวกัน >= 2 SD
    for i in range(1, n):
        if abs(z[i]) >= 2 and abs(z[i - 1]) >= 2 and (z[i] * z[i - 1] > 0):
            rules_by_point[i - 1].append("2-2s")
            rules_by_point[i].append("2-2s")

    # R-4s: สองค่าติดกัน คนละฝั่ง mean และห่างกัน >= 4 SD
    for i in range(1, n):
        if (values[i] - mean) * (values[i - 1] - mean) < 0:
            if abs(values[i] - values[i - 1]) >= 4 * sd:
                rules_by_point[i - 1].append("R-4s")
                rules_by_point[i].append("R-4s")

    # 4-1s: 4 ค่าติดกัน ฝั่งเดียวกัน >= 1 SD
    for i in range(3, n):
        segment = z[i - 3:i + 1]
        if all(abs(s) >= 1 for s in segment):
            if all(s > 0 for s in segment) or all(s < 0 for s in segment):
                for j in range(i - 3, i + 1):
                    rules_by_point[j].append("4-1s")

    rules_by_point = [sorted(set(rules)) for rules in rules_by_point]
    return rules_by_point


# ---------- Routes: Auth ----------
@app.route("/register", methods=["GET", "POST"])
def register():
    if request.method == "POST":
        username = request.form["username"].strip()
        password = request.form["password"]

        if not username or not password:
            flash("กรุณากรอก username และ password", "danger")
            return redirect(url_for("register"))

        # ถ้าลงชื่อ "เอกชัย สีทาสังข์" ให้เป็น admin ทันที
        is_admin = 1 if username == "เอกชัย สีทาสังข์" else 0

        conn = get_db()
        cur = conn.cursor()
        try:
            cur.execute(
                "INSERT INTO users (username, password_hash, is_admin) VALUES (?, ?, ?)",
                (username, generate_password_hash(password), is_admin)
            )
            conn.commit()
        except sqlite3.IntegrityError:
            flash("username นี้มีผู้ใช้แล้ว", "danger")
            return redirect(url_for("register"))
        finally:
            conn.close()

        flash("สมัครสมาชิกสำเร็จแล้ว กรุณาเข้าสู่ระบบ", "success")
        return redirect(url_for("login"))

    return render_template("register.html")


@app.route("/login", methods=["GET", "POST"])
def login():
    if request.method == "POST":
        username = request.form["username"].strip()
        password = request.form["password"]

        conn = get_db()
        cur = conn.cursor()
        cur.execute("SELECT * FROM users WHERE username = ?", (username,))
        user = cur.fetchone()
        conn.close()

        if user and check_password_hash(user["password_hash"], password):
            session["user_id"] = user["id"]
            session["username"] = user["username"]
            session["is_admin"] = bool(user["is_admin"])
            flash("เข้าสู่ระบบสำเร็จ", "success")
            return redirect(url_for("qc_list"))
        else:
            flash("username หรือ password ไม่ถูกต้อง", "danger")
            return redirect(url_for("login"))

    return render_template("login.html")


@app.route("/logout")
def logout():
    session.clear()
    flash("ออกจากระบบแล้ว", "info")
    return redirect(url_for("login"))


# ---------- Routes: QC หลัก ----------
@app.route("/")
@login_required
def home():
    return redirect(url_for("qc_list"))


@app.route("/qc/new", methods=["GET", "POST"])
@login_required
def qc_new():
    # ดึงข้อมูลเก่ามาทำ suggestion
    conn = get_db()
    cur = conn.cursor()

    cur.execute("SELECT DISTINCT test_name FROM qc_results ORDER BY test_name")
    departments = [row["test_name"] for row in cur.fetchall()]

    cur.execute("SELECT DISTINCT bgm_serial FROM qc_results WHERE bgm_serial IS NOT NULL ORDER BY bgm_serial")
    bgm_serials = [row["bgm_serial"] for row in cur.fetchall()]

    cur.execute("SELECT DISTINCT control_lot FROM qc_results WHERE control_lot IS NOT NULL ORDER BY control_lot")
    control_lots = [row["control_lot"] for row in cur.fetchall()]

    cur.execute("SELECT DISTINCT ref_min, ref_max FROM qc_results WHERE ref_min IS NOT NULL AND ref_max IS NOT NULL")
    ref_ranges = [(row["ref_min"], row["ref_max"]) for row in cur.fetchall()]

    conn.close()

    if request.method == "POST":
        department = request.form["department"].strip()
        test_date = request.form["test_date"].strip()
        bgm_serial = request.form["bgm_serial"].strip()
        strip_lot = request.form["strip_lot"].strip()
        strip_expiry = request.form["strip_expiry"].strip()

        # ตัดช่องหน่วยออกจากฟอร์ม → กำหนดหน่วยตายตัวเป็น mg/dL
        unit = "mg/dL"

        if not department or not test_date:
            flash("กรุณากรอก หน่วยงาน/เครื่อง และ วันที่ตรวจ", "danger")
            return redirect(url_for("qc_new"))

        levels = [
            ("Level 0", "lv0_"),
            ("Level 1", "lv1_"),
            ("Level 2", "lv2_"),
        ]

        user_id = session["user_id"]
        created_at = datetime.now().isoformat(timespec="seconds")

        inserted_any = False
        conn = get_db()
        cur = conn.cursor()

        for level_name, prefix in levels:
            lot = request.form.get(prefix + "control_lot", "").strip()
            exp = request.form.get(prefix + "control_expiry", "").strip()
            ref_min_str = request.form.get(prefix + "ref_min", "").strip()
            ref_max_str = request.form.get(prefix + "ref_max", "").strip()
            result_str = request.form.get(prefix + "result_value", "").strip()

            # ถ้า Level ไหนไม่กรอก result เลย → ข้าม
            if not result_str:
                continue

            try:
                result_value = float(result_str)
            except ValueError:
                flash(f"ผลการทดสอบของ {level_name} ต้องเป็นตัวเลข", "danger")
                conn.close()
                return redirect(url_for("qc_new"))

            ref_min = None
            ref_max = None
            if ref_min_str:
                try:
                    ref_min = float(ref_min_str)
                except ValueError:
                    flash(f"ค่าอ้างอิงต่ำสุดของ {level_name} ต้องเป็นตัวเลข", "danger")
                    conn.close()
                    return redirect(url_for("qc_new"))

            if ref_max_str:
                try:
                    ref_max = float(ref_max_str)
                except ValueError:
                    flash(f"ค่าอ้างอิงสูงสุดของ {level_name} ต้องเป็นตัวเลข", "danger")
                    conn.close()
                    return redirect(url_for("qc_new"))

            cur.execute("""
                INSERT INTO qc_results (
                    user_id, test_name, level,
                    bgm_serial,
                    strip_lot, strip_expiry,
                    control_lot, control_expiry,
                    result_value, unit,
                    ref_min, ref_max,
                    test_date, created_at
                )
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, (
                user_id, department, level_name,
                bgm_serial,
                strip_lot, strip_expiry,
                lot, exp,
                result_value, unit,
                ref_min, ref_max,
                test_date, created_at
            ))
            inserted_any = True

        if inserted_any:
            conn.commit()
            conn.close()
            flash("บันทึกผล QC สำเร็จ", "success")
            return redirect(url_for("qc_list"))
        else:
            conn.close()
            flash("กรุณากรอกผลการทดสอบอย่างน้อย 1 ระดับ (Level 0/1/2)", "danger")
            return redirect(url_for("qc_new"))

    default_date = datetime.now().strftime("%Y-%m-%d")
    return render_template(
        "qc_new.html",
        default_date=default_date,
        departments=departments,
        bgm_serials=bgm_serials,
        control_lots=control_lots,
        ref_ranges=ref_ranges,
    )


@app.route("/qc")
@login_required
def qc_list():
    test_name = request.args.get("test_name", "").strip()
    date_from = request.args.get("date_from", "").strip()
    date_to = request.args.get("date_to", "").strip()

    sql = "SELECT q.*, u.username FROM qc_results q JOIN users u ON q.user_id = u.id WHERE 1=1"
    params = []

    if test_name:
        sql += " AND q.test_name LIKE ?"
        params.append(f"%{test_name}%")

    if date_from:
        sql += " AND q.test_date >= ?"
        params.append(date_from)

    if date_to:
        sql += " AND q.test_date <= ?"
        params.append(date_to)

    sql += " ORDER BY q.test_date DESC, q.id DESC"

    conn = get_db()
    cur = conn.cursor()
    cur.execute(sql, params)
    rows = cur.fetchall()
    conn.close()

    return render_template("qc_list.html", rows=rows, test_name=test_name,
                           date_from=date_from, date_to=date_to)


@app.route("/qc/export")
@login_required
def qc_export():
    """ส่งออกผลย้อนหลังเป็นไฟล์ CSV (เปิดใน Excel ได้ พร้อมภาษาไทย)"""
    test_name = request.args.get("test_name", "").strip()
    date_from = request.args.get("date_from", "").strip()
    date_to = request.args.get("date_to", "").strip()

    sql = "SELECT q.*, u.username FROM qc_results q JOIN users u ON q.user_id = u.id WHERE 1=1"
    params = []

    if test_name:
        sql += " AND q.test_name LIKE ?"
        params.append(f"%{test_name}%")

    if date_from:
        sql += " AND q.test_date >= ?"
        params.append(date_from)

    if date_to:
        sql += " AND q.test_date <= ?"
        params.append(date_to)

    sql += " ORDER BY q.test_date DESC, q.id DESC"

    conn = get_db()
    cur = conn.cursor()
    cur.execute(sql, params)
    rows = cur.fetchall()
    conn.close()

    output = io.StringIO()
    writer = csv.writer(output)

    # หัวตาราง (ภาษาไทย)
    writer.writerow([
        "วันที่ตรวจ", "หน่วยงาน/เครื่อง", "Level", "Result", "Unit",
        "Ref_min", "Ref_max",
        "BGM Serial", "Strip Lot", "Strip Expiry",
        "Control Lot", "Control Expiry",
        "บันทึกโดย", "บันทึกเมื่อ"
    ])

    # ข้อมูลในแถวต่าง ๆ
    for r in rows:
        writer.writerow([
            r["test_date"],          # วันที่ตรวจ
            r["test_name"],          # หน่วยงาน/เครื่อง
            r["level"],              # Level
            r["result_value"],       # Result
            r["unit"],               # Unit (ตอนนี้ fix เป็น mg/dL)
            r["ref_min"],            # Ref_min
            r["ref_max"],            # Ref_max
            r["bgm_serial"],         # BGM Serial
            r["strip_lot"],          # Strip Lot
            r["strip_expiry"],       # Strip Expiry
            r["control_lot"],        # Control Lot
            r["control_expiry"],     # Control Expiry
            r["username"],           # บันทึกโดย
            r["created_at"],         # บันทึกเมื่อ
        ])

    csv_data = output.getvalue()
    output.close()

    # ใส่ BOM ข้างหน้า ให้ Excel รู้ว่าเป็น UTF-8 → ภาษาไทยไม่เพี้ยน
    csv_data = "\ufeff" + csv_data

    filename = f"qc_results_{datetime.now().strftime('%Y%m%d_%H%M%S')}.csv"
    return Response(
        csv_data,
        mimetype="text/csv; charset=utf-8",
        headers={"Content-Disposition": f"attachment; filename={filename}"}
    )


@app.route("/qc/summary")
@login_required
def qc_summary():
    conn = get_db()
    cur = conn.cursor()
    cur.execute("""
        SELECT
            test_name,
            level,
            COUNT(*) as n,
            AVG(result_value) as mean_value,
            MIN(result_value) as min_value,
            MAX(result_value) as max_value,
            MIN(ref_min) as ref_min,
            MAX(ref_max) as ref_max
        FROM qc_results
        GROUP BY test_name, level
        ORDER BY test_name, level
    """)
    summary_rows = cur.fetchall()

    summary = []
    for row in summary_rows:
        test_name = row["test_name"]
        level = row["level"]

        cur2 = conn.cursor()
        cur2.execute("""
            SELECT result_value FROM qc_results
            WHERE test_name = ? AND level = ?
        """, (test_name, level))
        values = [r["result_value"] for r in cur2.fetchall()]

        if len(values) > 1:
            mean = sum(values) / len(values)
            variance = sum((v - mean) ** 2 for v in values) / len(values)
            sd = variance ** 0.5
        else:
            sd = 0.0

        summary.append({
            "test_name": test_name,
            "level": level,
            "n": row["n"],
            "mean_value": row["mean_value"],
            "min_value": row["min_value"],
            "max_value": row["max_value"],
            "sd": sd,
            "ref_min": row["ref_min"],
            "ref_max": row["ref_max"],
        })

    conn.close()
    return render_template("qc_summary.html", summary=summary)


@app.route("/qc/summary/export")
@login_required
def qc_summary_export():
    """ส่งออกสรุปผลเป็น CSV (เปิดใน Excel ได้ พร้อมภาษาไทย)"""
    conn = get_db()
    cur = conn.cursor()
    cur.execute("""
        SELECT
            test_name,
            level,
            COUNT(*) as n,
            AVG(result_value) as mean_value,
            MIN(result_value) as min_value,
            MAX(result_value) as max_value,
            MIN(ref_min) as ref_min,
            MAX(ref_max) as ref_max
        FROM qc_results
        GROUP BY test_name, level
        ORDER BY test_name, level
    """)
    rows = cur.fetchall()
    conn.close()

    output = io.StringIO()
    writer = csv.writer(output)

    # หัวตาราง (ภาษาไทย)
    writer.writerow([
        "หน่วยงาน/เครื่อง", "Level", "n",
        "Mean", "SD(ยังไม่คำนวณในไฟล์นี้)", "Min", "Max",
        "Ref_min", "Ref_max"
    ])

    # เขียนทีละแถว
    for row in rows:
        writer.writerow([
            row["test_name"],   # หน่วยงาน/เครื่อง
            row["level"],       # Level
            row["n"],           # จำนวนตัวอย่าง
            row["mean_value"],  # Mean
            "",                 # SD (เวอร์ชันนี้ยังไม่ใส่ SD ลงไฟล์)
            row["min_value"],   # Min
            row["max_value"],   # Max
            row["ref_min"],     # Ref_min
            row["ref_max"],     # Ref_max
        ])

    csv_data = output.getvalue()
    output.close()

    # ใส่ BOM ให้ Excel อ่าน UTF-8 ถูก
    csv_data = "\ufeff" + csv_data

    filename = f"qc_summary_{datetime.now().strftime('%Y%m%d_%H%M%S')}.csv"
    return Response(
        csv_data,
        mimetype="text/csv; charset=utf-8",
        headers={"Content-Disposition": f"attachment; filename={filename}"}
    )


# ---------- Route: กราฟ Levey–Jennings + Westgard ----------
@app.route("/qc/chart")
@login_required
def qc_chart():
    conn = get_db()
    cur = conn.cursor()

    cur.execute("""
        SELECT DISTINCT test_name, level
        FROM qc_results
        ORDER BY test_name, level
    """)
    combos = cur.fetchall()

    test_name = request.args.get("test_name")
    level = request.args.get("level")

    data_points = []
    stats = None
    violations = []

    if test_name and level:
        cur.execute("""
            SELECT test_date, result_value, ref_min, ref_max, test_name
            FROM qc_results
            WHERE test_name = ? AND level = ?
            ORDER BY test_date, id
        """, (test_name, level))
        rows = cur.fetchall()

        values = [r["result_value"] for r in rows]

        if values:
            mean = sum(values) / len(values)
            variance = sum((v - mean) ** 2 for v in values) / len(values)
            sd = variance ** 0.5

            ref_min = next((r["ref_min"] for r in rows if r["ref_min"] is not None), None)
            ref_max = next((r["ref_max"] for r in rows if r["ref_max"] is not None), None)

            stats = {
                "mean": mean,
                "sd": sd,
                "n": len(values),
                "ref_min": ref_min,
                "ref_max": ref_max,
                "test_name": test_name,
            }

            rules_by_point = evaluate_westgard(values, mean, sd)

            for idx, (row, rules) in enumerate(zip(rows, rules_by_point), start=1):
                point = {
                    "index": idx,
                    "date": row["test_date"],
                    "value": row["result_value"],
                    "rules": rules,
                    "test_name": row["test_name"],
                }
                data_points.append(point)

                if rules:
                    violations.append(point)

    conn.close()

    return render_template(
        "qc_chart.html",
        combos=combos,
        test_name=test_name,
        level=level,
        data_points=data_points,
        stats=stats,
        violations=violations,
    )


# ---------- จุดเริ่มรันแอป ----------
if __name__ == "__main__":
    app.run(debug=True)
