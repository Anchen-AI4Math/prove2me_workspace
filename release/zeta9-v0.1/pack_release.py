# Pack the zeta9 v0.1 source ZIP: whitelist copy -> sanitize -> scan -> zip.
import os, re, shutil, zipfile, sys

WS = r"D:/users/self_projects/prove2me_workspace"
REL = WS + r"/release/zeta9-v0.1"
STAGE = REL + r"/staging/zeta9-source-v0.1"
ZIPOUT = REL + r"/zeta9-source-v0.1.zip"

if os.path.exists(STAGE):
    shutil.rmtree(STAGE)
os.makedirs(STAGE)

copied = []
def add(src_abs, dst_rel):
    dst = os.path.join(STAGE, dst_rel)
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    shutil.copy2(src_abs, dst)
    copied.append(dst_rel)

def add_tree(src_abs, dst_rel, pred):
    for root, dirs, files in os.walk(src_abs):
        dirs[:] = [d for d in dirs if d != "__pycache__"]
        for f in files:
            p = os.path.join(root, f)
            rel = os.path.relpath(p, src_abs).replace("\\", "/")
            if pred(rel, p):
                add(p, dst_rel + "/" + rel)

Z9 = WS + r"/missions/zeta9"

# --- whitelist -------------------------------------------------------------
add(REL + r"/note/zeta9-research-note-v0.1.html", "note/zeta9-research-note-v0.1.html")
for f in ["README.md", "CHANGELOG.md", "zenodo-metadata.md"]:
    add(REL + "/" + f, f)
add_tree(REL + r"/LICENSES", "LICENSES", lambda rel, p: rel.endswith(".txt"))

add(Z9 + r"/status.md", "missions/zeta9/status.md")
add(Z9 + r"/report.md", "missions/zeta9/report.md")
add_tree(Z9 + r"/research", "missions/zeta9/research",
         lambda rel, p: rel.endswith((".md", ".tex")))
add_tree(Z9 + r"/scripts", "missions/zeta9/scripts",
         lambda rel, p: rel.endswith(".py"))

def small_text(rel, p):
    return rel.endswith((".json", ".jsonl", ".txt", ".py")) and os.path.getsize(p) < 200_000

add_tree(Z9 + r"/verification", "missions/zeta9/verification",
         lambda rel, p: (small_text(rel, p) and not rel.startswith("gram-coeff/"))
                        or (rel.startswith("linear-coeff/") and rel.endswith(".gz")))

for r in range(2, 10):
    base = f"{Z9}/round{r}"
    add(f"{base}/report.md", f"missions/zeta9/round{r}/report.md")
    add_tree(f"{base}/research", f"missions/zeta9/round{r}/research",
             lambda rel, p: rel.endswith(".md"))
    add_tree(f"{base}/scripts", f"missions/zeta9/round{r}/scripts",
             lambda rel, p: rel.endswith(".py"))
    add_tree(f"{base}/verification", f"missions/zeta9/round{r}/verification", small_text)

add_tree(Z9 + r"/roadmap/research", "missions/zeta9/roadmap/research",
         lambda rel, p: rel.endswith(".md"))
add_tree(Z9 + r"/roadmap/verification", "missions/zeta9/roadmap/verification", small_text)
add(Z9 + r"/roadmap/DAG.md", "missions/zeta9/roadmap/DAG.md")
add(Z9 + r"/roadmap/dag.json", "missions/zeta9/roadmap/dag.json")
# platform: only the top-level Lean sources and statement notes (no receipts, no IDs, no wiring/)
add_tree(Z9 + r"/roadmap/platform", "missions/zeta9/roadmap/platform",
         lambda rel, p: ("/" not in rel)
                        and (rel.endswith((".lean",)) or rel.endswith("-statement.md")))

add(WS + r"/missions/zeta7/research/analytic-foundations.md",
    "missions/zeta7/research/analytic-foundations.md")

add(REL + r"/release-checks/zeta9_release_check.py", "release-checks/zeta9_release_check.py")
add(REL + r"/release-checks/zeta9_release_check_out.txt", "release-checks/zeta9_release_check_out.txt")

# --- sanitize ---------------------------------------------------------------
SHORT_IDS = ["a925cba9","207cc87c","cbb9cc51","d6b0eb73","8496d3a0","0f7bb5e3",
             "c1147ec6","a8a15e54","443fb397","60c1cf49","691b1665","42bd3e13",
             "0da22fdd","7463b390","523f37b8"]
RULES = [
    (re.compile(r"8195d8fe-059f-4515-92b4-57b585e2bac6"), "[private-mission-id]"),
    (re.compile(r"06faf23f-00c2-4edf-92ab-1212cdb7d7d6"), "[private-proposal-id]"),
    (re.compile(r"[A-Za-z]:[\\/]Users[\\/][^\s\"'`)\\]+"), "[local-path]"),
    (re.compile(r"[A-Za-z]:[\\/]users[\\/]self_projects[\\/]prove2me_workspace"), "[workspace]"),
] + [(re.compile(re.escape(s)), "[redacted-id]") for s in SHORT_IDS]

TEXT_EXT = (".md", ".py", ".tex", ".json", ".jsonl", ".txt", ".html", ".lean")
n_san = 0
for root, dirs, files in os.walk(STAGE):
    for f in files:
        if not f.endswith(TEXT_EXT):
            continue
        p = os.path.join(root, f)
        with open(p, "r", encoding="utf-8", errors="ignore") as fh:
            t = fh.read()
        t2 = t
        for rx, rep in RULES:
            t2 = rx.sub(rep, t2)
        if t2 != t:
            with open(p, "w", encoding="utf-8") as fh:
                fh.write(t2)
            n_san += 1

# --- scan -------------------------------------------------------------------
BAD = [
    ("uuid", re.compile(r"[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}")),
    ("abs-user-path", re.compile(r"[A-Za-z]:[\\/][Uu]sers[\\/]")),
    ("token", re.compile(r"(?i)(api[_-]?key|secret|password|bearer\s+[a-z0-9]|token\s*[:=])")),
    ("email", re.compile(r"[\w.+-]+@[\w-]+\.[\w.]+")),
    ("phone", re.compile(r"1[3-9]\d{9}")),
]
findings = []
for root, dirs, files in os.walk(STAGE):
    for f in files:
        if not f.endswith(TEXT_EXT):
            continue
        p = os.path.join(root, f)
        with open(p, "r", encoding="utf-8", errors="ignore") as fh:
            t = fh.read()
        for name, rx in BAD:
            for mt in rx.finditer(t):
                findings.append((name, os.path.relpath(p, STAGE), mt.group(0)[:60]))

# --- zip --------------------------------------------------------------------
if os.path.exists(ZIPOUT):
    os.remove(ZIPOUT)
with zipfile.ZipFile(ZIPOUT, "w", zipfile.ZIP_DEFLATED) as z:
    for root, dirs, files in os.walk(STAGE):
        for f in files:
            p = os.path.join(root, f)
            z.write(p, os.path.join("zeta9-source-v0.1", os.path.relpath(p, STAGE)))

total = sum(os.path.getsize(os.path.join(r, f)) for r, d, fs in os.walk(STAGE) for f in fs)
print(f"files copied: {len(copied)}")
print(f"files sanitized: {n_san}")
print(f"staging size: {total/1e6:.2f} MB; zip size: {os.path.getsize(ZIPOUT)/1e6:.2f} MB")
print(f"scan findings: {len(findings)}")
for f_ in findings[:60]:
    print("  ", f_)
