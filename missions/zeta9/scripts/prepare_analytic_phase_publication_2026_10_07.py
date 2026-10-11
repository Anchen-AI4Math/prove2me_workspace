"""Pure public metadata and exact payload copies; no Lean, API or credentials."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re

TASK = Path(__file__).resolve().parents[1]
BATCH = TASK / "formalization/platform/analytic-phase"
OUT = BATCH / "publication-preparation-2026-10-07"
NEW = "19653cff-d481-498a-a717-10630d1ca1b7"


def bind(p):
    b = p.read_bytes()
    return {"task_relative": p.relative_to(TASK).as_posix(), "bytes": len(b), "sha256": hashlib.sha256(b).hexdigest()}


def save(name, value):
    (OUT / name).write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def main():
    assert not OUT.exists(), "Preserve earlier metadata; use a new version for changes"
    plan = json.loads((BATCH / "target-plan.json").read_text(encoding="utf-8"))
    assert plan["definition"] == "ZetaNine_AnalyticPhase" and len(plan["payloads"]) == 7
    assert len(plan["targets"]) == 3 and not plan["canonical_dependencies"]
    checked = []
    for item in plan["payloads"]:
        source = TASK / item["binding"]["task_relative"]
        assert bind(source) == item["binding"]
        assert not Path(item["path"]).is_absolute() and ".." not in Path(item["path"]).parts
        checked.append((item, source))
    OUT.mkdir()
    copied = []
    for item, source in checked:
        p = OUT / "exact-payloads" / item["path"]
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_bytes(source.read_bytes())
        copied.append({"kind": item["kind"], "root_relative": item["path"], "staged_source": bind(source), "publication_source_copy": bind(p)})
    provenance = ("ZetaNine local research, AnalyticPhase.lean and AnalyticPhaseUpperBound.lean; "
                  "independently compiled exports SHA-256 2b53b56f103bc69322c35d18e120c248cc34402fe831b7be86651f584d3bf4bd "
                  "and 388c2be7c6401e0b0944e5ee9601ddd4f9359f85d05319ce191e6c6a4d0f1635. "
                  "Native independent audit SHA-256 f487b27f1668432926ad505e4f30a67e41c1abf75ad9690cc2c84369487067cc.")
    definitions = [{"definition_name": plan["definition"], "definition_title": "Actual phase and auxiliary functions for zeta(9)",
        "definition": (BATCH / "staged" / plan["local_definition"]).read_text(encoding="utf-8"),
        "natural_language_statement": "Define f(x)=10x log(x)+(x+2)log(x+2)-(x-1)log(x-1)-10(x+1)log(x+1), its derivative ratio, and the auxiliary functions used for its whole-domain upper bound.",
        "source": provenance, "env": plan["Mathlib_ENV"], "private": False}]
    text = {
        "phase_strictAntiOn_right": ("Actual phase decreases strictly on [101/100, infinity)",
            "For any real x and y with 101/100 ≤ x < y, f(y) < f(x).",
            "The derivative is the logarithm of (x+2)x^10/((x-1)(x+1)^10). A polynomial expanded about 101/100 has eleven strictly positive rational coefficients, which prove the ratio is below one throughout this interval. The derivative criterion yields strict antitonicity."),
        "phase_global_lt_certified": ("Strict certified bound for the actual phase on x>1",
            "For every real x>1, f(x)<-10564011/1000000.",
            "On 1<x≤101/100 the smooth correction is nonpositive and u(1+log(A/u))≤A gives f(x)≤f(1)+A. Strict decrease controls the remaining interval. Six and eleven exact logarithm-series terms with the proved geometric remainder give log(2)>693147/1000000 and log(3)<1098613/1000000, while A<309/100000. These rational inequalities certify the strict bound."),
        "phase_global_upper_bound": ("Whole-domain actual phase bound -2641/250",
            "For every real x>1, f(x)≤-2641/250.",
            "The independently verified strict bound f(x)<-10564011/1000000 holds on the complete open domain x>1. Rational comparison gives the requested upper bound. This is the phase component; the full moment estimates, integer height and irrationality remain separate obligations.")}
    problems, explanations = [], {}
    for target in plan["targets"]:
        reference = (BATCH / "staged" / target["local_reference"]).read_text(encoding="utf-8")
        marker = "theorem " + target["theorem_name"]
        assert reference.count(marker) == 1
        preamble, formal = reference.split(marker, 1)
        preamble = preamble.rstrip()
        formal = marker + formal.rstrip()
        assert formal.endswith(" := by sorry")
        assert reference == preamble + "\n\n" + formal + "\n"
        short = target["theorem_name"].rsplit(".", 1)[1]
        title, nl, explanation = text[short]
        problems.append({"theorem_name": target["theorem_name"], "theorem_title": title,
                         "natural_language_statement": nl, "formal_statement": formal, "preamble": preamble, "source": provenance})
        explanations[target["theorem_name"]] = explanation
    save("definitions-request-v1.json", definitions)
    save("problems-request-v1.json", {"env": plan["Mathlib_ENV"], "private": False, "problems": problems})
    save("proof-explanations-v1.json", explanations)
    save("prepared-publication-v1.json", {"prepared_at": datetime.now(timezone.utc).isoformat(), "new_proposal_id": NEW,
        "environment": plan["Mathlib_ENV"], "seven_payloads": copied, "target_plan": bind(BATCH / "target-plan.json"),
        "native_independent_report": bind(TASK / "verification/formalization-analytic-phase-upper-bound-independent-2026-10-07/independent-audit.json"),
        "Root_native_full_rehash": bind(TASK / "verification/formalization-project-handoff-2026-10-07/root-phase-independent-complete-binding-rehash.json"),
        "metadata": [bind(OUT / n) for n in ["definitions-request-v1.json", "problems-request-v1.json", "proof-explanations-v1.json"]],
        "proposal_mutation_permitted": False, "mission_link_permitted": False, "Lean_calls": 0, "API_calls": 0,
        "publication_requires_complete_platform_author_and_independent_Root_pins": True})
    print("Exact seven payloads copied; public metadata prepared; API/Lean/credentials operations: 0")


if __name__ == "__main__":
    main()
