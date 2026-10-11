"""Offline integration of the independently reviewed finite-prime proofs.

The first six-theorem batch and the released research archive stay frozen.
This creates a separate batch, without credentials or network operations.
"""
from __future__ import annotations

import hashlib
import json
import re

from prepare_formalization_2026_10_02 import TASK, WORKSPACE, ENV, lean_code, without_definition, write

OUT = TASK / "formalization/platform/prime-valuation"


def main():
    assert not list(OUT.glob("*-receipts/*.json")), "Already submitted; preserve batch payloads"
    review = json.loads((TASK / "formalization/platform/prime-valuation-review.json").read_text(encoding="utf-8"))
    assert review["verdict"].startswith("PASS:")
    source = TASK / "formalization/HarmonicPrimeValuation.lean"
    assert hashlib.sha256(source.read_bytes()).hexdigest() == review["reviewed_sources"][0]["sha256"]
    definition = {k: review["definition_candidate"][k] for k in (
        "definition_name", "definition_title", "definition", "natural_language_statement", "source", "tags", "env", "private", "local_path")}
    write(WORKSPACE / definition["local_path"], definition["definition"])
    core = lean_code(source.read_text(encoding="utf-8"))
    core = without_definition(without_definition(core, "primeRemainder"), "harmonicExceptionalProduct")
    core = "import Definitions.Def_ZetaNine_HarmonicPrimeValuation\n" + core
    problems = []
    signatures = {}
    for candidate in review["theorem_candidates"]:
        item = {k: candidate[k] for k in ("theorem_name", "theorem_title", "formal_statement", "natural_language_statement", "preamble", "source", "tags", "definition_dependency", "existing_definition_dependency", "explanation")}
        short = item["theorem_name"].split(".")[-1]
        match = re.search(rf"(?m)^theorem {short}\b([\s\S]*?)\s*:=", core)
        assert match, short
        signature = match.group(1)
        expected = "theorem " + item["theorem_name"] + signature + " := by sorry"
        assert re.sub(r"\s+", " ", expected).strip() == re.sub(r"\s+", " ", item["formal_statement"]).strip()
        # Preserve the exact source quantifiers in both the reference and the wrapper.
        item["formal_statement"] = expected
        item["local_solution"] = candidate["suggested_local_solution"]
        item["local_reference"] = candidate["suggested_local_reference"]
        checked = "checked_" + short
        proof = re.sub(rf"\b{short}\b", checked, core)
        arguments = "s N p hp hs hNp hN hunit" if short == "harmonic_large_prime_den_valuation" else "s K N S hs hS"
        proof += "\n\nopen ZetaNine.HarmonicStability\n\ntheorem solution" + signature
        proof += " := by\n  exact ZetaNine.HarmonicStability." + checked + " " + arguments
        proof += "\n\n#print axioms solution\n"
        write(WORKSPACE / item["local_solution"], proof)
        write(WORKSPACE / item["local_reference"], item["preamble"] + "\nset_option autoImplicit false\n\n" + expected)
        signatures[item["theorem_name"]] = {"signature_matches_original_source": True, "solution_sha256": hashlib.sha256((WORKSPACE / item["local_solution"]).read_bytes()).hexdigest()}
        problems.append(item)
    write(OUT / "definitions-request.json", json.dumps([definition], ensure_ascii=False, indent=2))
    write(OUT / "problems-request.json", json.dumps({"env": ENV, "private": False, "problems": problems}, ensure_ascii=False, indent=2))
    write(OUT / "integration-provenance.json", json.dumps({"source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(), "review_sha256": hashlib.sha256((TASK / "formalization/platform/prime-valuation-review.json").read_bytes()).hexdigest(), "signature_checks": signatures, "whole_harmonic_asymptotic_formalized": False}, ensure_ascii=False, indent=2))
    scope_path = TASK / "scope.json"
    scope = json.loads(scope_path.read_text(encoding="utf-8"))
    additions = [definition["local_path"], "missions/zeta9/scripts/prepare_prime_valuation_2026_10_02.py", "missions/zeta9/scripts/publish_formalization_2026_10_02.py"]
    additions += [p[k] for p in problems for k in ("local_solution", "local_reference")]
    scope["sources"] = list(dict.fromkeys(scope["sources"] + additions))
    scope["build"] = list(dict.fromkeys(scope["build"] + [p["local_solution"] for p in problems]))
    write(scope_path, json.dumps(scope, ensure_ascii=False, indent=2))
    print("Prepared one lightweight definition and three exact finite-prime proof targets; no API calls.")


if __name__ == "__main__":
    main()
