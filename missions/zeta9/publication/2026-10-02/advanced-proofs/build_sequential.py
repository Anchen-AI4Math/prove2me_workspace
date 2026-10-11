"""Resource-limited full-source replay in actual import-topological order.

Does not modify any mathematical source or the shared dependency environment.
"""
from pathlib import Path
import json
import os
import subprocess

OUT = Path(__file__).resolve().parent
PROJECT = OUT / "project"
closures = [json.loads((PROJECT / ("audit/upstream-pnt/" + name)).read_text(encoding="utf-8-sig"))
            for name in ["pnt-import-closure.json", "architect-import-closure.json"]]
modules = {}
for closure in closures:
    modules.update(closure["modules"])
order = []
seen = set()
visiting = set()

def visit(module):
    if module in seen:
        return
    assert module not in visiting, "Import cycle"
    visiting.add(module)
    for dependency in modules[module]["imports"]:
        if dependency in modules:
            visit(dependency)
    visiting.remove(module)
    seen.add(module)
    order.append(module)

for module in modules:
    visit(module)
assert len(order) == 23
order += [
    "Definitions.Def_ZetaNine_HarmonicStability", "Definitions.Def_ZetaNine_ShortZeroCoefficient",
    "Solutions.Sol_ZetaNine_HarmonicStability_harmonic_den_dvd_lcm_power",
    "Solutions.Sol_ZetaNine_ShortZeroCoefficient_A_even_signed_lower",
    "Solutions.Sol_ZetaNine_ShortZeroCoefficient_A_ne_zero_of_even",
    "Theorems.Thm_ZetaNine_ShortZeroCoefficient_A_even_signed_lower",
    "Theorems.Thm_ZetaNine_ShortZeroCoefficient_A_ne_zero_of_even",
    "missions.zeta9.formalization.HarmonicPrimeValuation",
    "missions.zeta9.formalization.HarmonicAsymptotic",
    "missions.zeta9.formalization.PNTTransfer",
    "missions.zeta9.formalization.ShortZeroCoefficient",
    "Audit.Kernel", "Audit.C3Signed", "Audit.C3Nonzero", "Audit.NativeC3", "Audit.PNT",
]
environment = os.environ.copy()
environment.pop("LEAN_PATH", None)
steps = []
log = OUT / "sequential-build.log"
with log.open("wb") as stream:
    for module in order:
        command = ["lake", "--no-cache", "build", module]
        result = subprocess.run(command, cwd=PROJECT, env=environment, capture_output=True)
        stream.write(("\nCOMMAND: " + " ".join(command) + "\n").encode())
        stream.write(result.stdout + result.stderr)
        stream.flush()
        steps.append({"module": module, "command": command, "exit_code": result.returncode})
        print(json.dumps(steps[-1]), flush=True)
        if result.returncode:
            break
(OUT / "sequential-build-steps.json").write_text(json.dumps({"steps": steps, "upstream_import_topological_order": order[:23],
    "mathematical_source_changes": [], "source_or_PNT_binary_cache_reused": False}, indent=2) + "\n", encoding="utf-8")
success = len(steps) == len(order) and all(step["exit_code"] == 0 for step in steps)
(OUT / "sequential-build-exit.txt").write_text(("0" if success else "1") + "\n", encoding="utf-8")
raise SystemExit(0 if success else 1)
