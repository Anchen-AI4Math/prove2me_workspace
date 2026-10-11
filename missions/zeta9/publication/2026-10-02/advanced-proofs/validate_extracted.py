"""Verify ZIP extraction and compile only its five lightweight closed audits.

The exact already-verified same-project artifacts supply imports; all vendored
PNT/task source files are still in the ZIP. No upstream proof is recompiled.
"""
from pathlib import Path
import hashlib
import importlib.util
import json
import os
import re
import subprocess
import zipfile

OUT = Path(__file__).resolve().parent
PROJECT = OUT / "project"
EXTRACTED = OUT / "extracted-source-validation"
ARCHIVE = OUT / "zeta9-advanced-proofs-2026-10-02.zip"
EXTRACTED.mkdir(exist_ok=True)
with zipfile.ZipFile(ARCHIVE) as z:
    for name in z.namelist():
        assert not name.startswith(("/", "\\")) and ".." not in Path(name).parts
    z.extractall(EXTRACTED)
environment = os.environ.copy()
environment.pop("LEAN_PATH", None)
verify = subprocess.run(["python", "verify_package.py"], cwd=EXTRACTED,
                        env=environment, capture_output=True)
assert verify.returncode == 0, verify.stdout + verify.stderr
(EXTRACTED / ".lake").mkdir(exist_ok=True)
targets = {"packages": PROJECT / ".lake/packages", "build": PROJECT / ".lake/build"}
for name, target in targets.items():
    link = EXTRACTED / ".lake" / name
    if not link.exists():
        subprocess.run(["cmd", "/c", "mklink", "/J", str(link), str(target.resolve())],
                       capture_output=True, check=True)
    assert link.resolve() == target.resolve()

steps, chunks = [], []
for source in ["Audit/Kernel.lean", "Audit/C3Signed.lean", "Audit/C3Nonzero.lean", "Audit/NativeC3.lean", "Audit/PNT.lean"]:
    command = ["lake", "env", "lean", source]
    result = subprocess.run(command, cwd=EXTRACTED, env=environment, capture_output=True)
    chunks.append(("\nCOMMAND: " + " ".join(command) + "\n").encode())
    chunks.append(result.stdout + result.stderr)
    steps.append({"source": source, "command": command, "exit_code": result.returncode})
    print(json.dumps(steps[-1]), flush=True)
    if result.returncode:
        break
data = b"".join(chunks)
(OUT / "extracted-audits.log").write_bytes(data)
reports = {}
for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", data.decode("utf-8-sig")):
    reports.setdefault(name, []).append(sorted(x.strip() for x in axioms.split(",") if x.strip()))
spec = importlib.util.spec_from_file_location("advanced_rebuild", PROJECT / "rebuild.py")
helper = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helper)
missing = [name for name in helper.REQUIRED if name not in reports]
bad = {name:values for name,values in reports.items() if any(set(xs) != helper.ALLOWED for xs in values)}
passed = len(steps) == 5 and all(x["exit_code"] == 0 for x in steps) and not missing and not bad
receipt = {
    "status": "PASS" if passed else "FAIL", "archive_sha256": hashlib.sha256(ARCHIVE.read_bytes()).hexdigest(),
    "extracted_payload_verifier_exit": verify.returncode,
    "extracted_payload_verifier_output": verify.stdout.decode().strip(), "steps": steps,
    "audit_log_sha256": hashlib.sha256(data).hexdigest(),
    "required_axiom_reports": {name:reports.get(name,[]) for name in helper.REQUIRED},
    "missing_reports": missing, "unexpected_axioms": bad,
    "required_axiom_declarations": len(helper.REQUIRED),
    "import_artifact_reuse": "Exact verified artifacts from this same advanced source project; no upstream proof recompiled during this extraction check",
    "cache_or_binary_in_archive": False, "network_API_credential_operations": False,
    "platform_acceptance_claimed": False,
}
(OUT / "extracted-validation.json").write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
validation_path = OUT / "package-validation.json"
validation = json.loads(validation_path.read_text(encoding="utf-8-sig"))
validation["extracted_payload_verifier_exit"] = verify.returncode
validation["extracted_five_audit_source_compiles"] = steps
validation["extracted_axiom_declarations_standard_three"] = len(helper.REQUIRED) if passed else 0
validation["extraction_receipt_sha256"] = hashlib.sha256((OUT / "extracted-validation.json").read_bytes()).hexdigest()
validation["extraction_status"] = receipt["status"]
validation_path.write_text(json.dumps(validation, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
sums = []
for name in [ARCHIVE.name, "source-manifest.json", "package-validation.json", "README.md", "extracted-validation.json", "extracted-audits.log"]:
    sums.append(hashlib.sha256((OUT / name).read_bytes()).hexdigest() + "  " + name + "\n")
(OUT / "SHA256SUMS.txt").write_text("".join(sums), encoding="utf-8")
print(json.dumps({"status": receipt["status"], "audit_sources": len(steps), "standard_three_axiom_declarations": len(helper.REQUIRED), "upstream_proofs_recompiled": 0}))
raise SystemExit(0 if passed else 1)
