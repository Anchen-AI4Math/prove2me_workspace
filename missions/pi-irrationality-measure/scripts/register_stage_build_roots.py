"""Register only this task's three already checked stage proof roots in Lake."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

sys.stdout.reconfigure(encoding="utf-8")

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
MODULES = (
    "independent.OAI_PiExponent_DeterminantAnalyticBound_log_norm_sum_le.Sol_OAI_PiExponent_DeterminantAnalyticBound_log_norm_sum_le",
    "independent.OAI_PiExponent_tendsto_nat_add_one_div_pow.Sol_OAI_PiExponent_tendsto_nat_add_one_div_pow",
    "nodes-preview.OAI_PiExponent_Collision_sum_weight_ge_of_low_count_le.Sol_OAI_PiExponent_Collision_sum_weight_ge_of_low_count_le",
)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--apply", action="store_true")
    args = parser.parse_args()
    lakefile = (ROOT / "lakefile.lean").resolve()
    if lakefile.parent != ROOT.resolve():
        raise ValueError("Unexpected shared Lake configuration path")
    raw = lakefile.read_bytes()
    runtime = json.loads((TASK / "verification/lean-runtime.json").read_bytes())
    expected = runtime["project_hashes"]["lakefile.lean"]
    if digest(raw) != expected:
        raise ValueError("Shared configuration changed since the terminal extraction runtime")
    if b"lean_lib PiExponentStageProofs" in raw:
        raise ValueError("Stage library is already registered; do not append it again")
    owned = set(json.loads((TASK / "scope.json").read_bytes())["build"])
    for module in MODULES:
        file = TASK / "verification" / (module.replace(".", "/") + ".lean")
        if not file.is_file() or file.relative_to(ROOT).as_posix() not in owned:
            raise ValueError("Stage source is missing or outside this mission's build roots")
    quoted = ["`" + ".".join("«" + part + "»" if "-" in part else part
                             for part in module.split(".")) for module in MODULES]
    addition = ("\nlean_lib PiExponentStageProofs where\n"
                '  srcDir := "missions/pi-irrationality-measure/verification"\n'
                "  roots := #[\n    " + ",\n    ".join(quoted) + "\n  ]\n").encode("utf-8")
    result = raw + addition
    archive = TASK / "verification/lakefile-before-stage-root-registration.lean"
    report = {"source": "lakefile.lean", "source_sha256": digest(raw),
              "result_sha256": digest(result), "addition": addition.decode("utf-8"),
              "registered_modules": list(MODULES), "lean_mathlib_pins_changed": False,
              "prior_extraction_terminal": True, "applied": args.apply}
    if args.apply:
        if archive.exists() and archive.read_bytes() != raw:
            raise ValueError("Prior configuration archive exists with different bytes")
        archive.write_bytes(raw)
        if lakefile.read_bytes() != raw:
            raise ValueError("Shared configuration changed before the guarded write")
        lakefile.write_bytes(result)
        if lakefile.read_bytes() != result:
            raise ValueError("Stage root registration did not preserve the exact intended bytes")
        (TASK / "verification/stage-root-registration.json").write_bytes(
            (json.dumps(report, ensure_ascii=False, indent=2)+"\n").encode("utf-8"))
    print(json.dumps(report, ensure_ascii=False))


if __name__ == "__main__":
    main()
