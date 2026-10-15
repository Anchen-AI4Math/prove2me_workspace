"""Check all Zipf proofs and their exact platform types in one Lean process."""
import json
import hashlib
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts"))
import workspace


def binder_arguments(declaration):
    names = []
    depth = 0
    start = 0
    for index, character in enumerate(declaration):
        if character == "(" :
            if depth == 0:
                start = index + 1
            depth += 1
        elif character == ")":
            depth -= 1
            if depth == 0:
                names.extend(declaration[start:index].split(":", 1)[0].split())
        elif character == ":" and depth == 0:
            break
    return " ".join(names)


def main():
    chunks = ["import Definitions.Def_ZipfLaw_Defs\nset_option autoImplicit false\n"]
    files = sorted((ROOT / "Solutions").glob("Sol_ZipfLaw_*.lean"))
    records = []
    for source in files:
        name = source.stem.removeprefix("Sol_ZipfLaw_")
        code = source.read_text(encoding="utf-8")
        code = "\n".join(line for line in code.splitlines() if not line.startswith("import "))
        target = (ROOT / f"Theorems/Thm_ZipfLaw_{name}.lean").read_text(encoding="utf-8")
        records.append({"source": source.relative_to(ROOT).as_posix(),
                        "sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
                        "reference_sha256": hashlib.sha256(target.encode("utf-8")).hexdigest()})
        declaration = target.split(f"theorem {name}", 1)[1].split(" := by sorry", 1)[0]
        # The reference statement is used as a type; its placeholder is never imported.
        arguments = binder_arguments(declaration)
        chunks.append(f"namespace ZipfAudit.{name}\n{code}\n\nexample {declaration} := solution {arguments}" +
                      "\n\nend ZipfAudit." + name + "\n")
    audit = ROOT / "missions/zipf/verification/ZipfAudit.lean"
    audit.write_text("\n".join(chunks), encoding="utf-8")
    lake, env = workspace.lake_environment()
    process = subprocess.run([lake, "env", "lean", str(audit)], cwd=ROOT, env=env,
                             capture_output=True, text=True, encoding="utf-8")
    log = ROOT / "missions/zipf/verification/audit.log"
    log.write_text(process.stdout + process.stderr, encoding="utf-8")
    summary = {"checked_at": datetime.now(timezone.utc).isoformat(),
               "toolchain": (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip(),
               "exit_code": process.returncode, "no_sorryAx": "sorryAx" not in process.stdout,
               "exact_type_checks": True, "solutions": records}
    (ROOT / "missions/zipf/verification/audit-summary.json").write_text(
        json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(process.stdout + process.stderr, end="")
    print(f"Audited {len(files)} solution files; exit code {process.returncode}.")
    return process.returncode


if __name__ == "__main__":
    raise SystemExit(main())
