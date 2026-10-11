"""Independent offline checks of the harmonic prime-valuation integration.

No credentials, network, shared-file edits, or platform calls are used.
"""
from pathlib import Path
import hashlib
import json
import re
from fractions import Fraction

BATCH = Path(__file__).resolve().parent
TASK = BATCH.parents[2]
ROOT = TASK.parents[1]
SOURCE = TASK / "formalization/HarmonicPrimeValuation.lean"

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def normalize(text):
    return "".join(text.split())

def no_comments(text):
    text = re.sub(r"/-[\s\S]*?-/", "", text)
    return re.sub(r"(?m)--.*$", "", text)

def signature(text, name):
    match = re.search(rf"(?m)^theorem {re.escape(name)}\b([\s\S]*?)\s*:=", text)
    assert match, name
    return normalize(match.group(1))

def remove_definition(text, name):
    pattern = rf"(?m)^def {re.escape(name)}\b[\s\S]*?(?=\n\n)"
    assert re.search(pattern, text), name
    return re.sub(pattern, "", text)

def proof_core(text):
    text = no_comments(text)
    text = re.sub(r"(?m)^import .*\n", "", text)
    text = re.sub(r"(?m)^#print axioms .*\n?", "", text)
    return normalize(text)

definitions = json.loads((BATCH / "definitions-request.json").read_text(encoding="utf-8"))
problems = json.loads((BATCH / "problems-request.json").read_text(encoding="utf-8"))
provenance = json.loads((BATCH / "integration-provenance.json").read_text(encoding="utf-8"))
source = SOURCE.read_text(encoding="utf-8")
hashes = {"missions/zeta9/formalization/HarmonicPrimeValuation.lean": sha(SOURCE)}
checks = []
findings = []

def check(name, condition, details=""):
    checks.append({"check": name, "pass": bool(condition), "details": details})
    if not condition:
        findings.append(name + (": " + details if details else ""))

check("original_source_sha_matches_provenance", sha(SOURCE) == provenance["source_sha256"])
check("pinned_mathlib_environment", problems["env"] == "0df444a360eaa60ab8c11dca51a86af692955474")
check("three_theorem_interfaces", len(problems["problems"]) == 3)
check("public_user_authorized_batch", problems["private"] is False)
check("batch_does_not_claim_unconditional_harmonic_asymptotic", provenance["whole_harmonic_asymptotic_formalized"] is False)

assert len(definitions) == 1
d = definitions[0]
definition_path = ROOT / d["local_path"]
definition_text = definition_path.read_text(encoding="utf-8")
hashes[d["local_path"]] = sha(definition_path)
check("definition_payload_is_exact_shared_file", d["definition"] == definition_text)
check("definition_module_is_lightweight", not re.search(r"(?m)^\s*(theorem|lemma|axiom|opaque)\b", no_comments(definition_text)))
check("definition_dependencies_are_actual_harmonic_objects", "import Definitions.Def_ZetaNine_HarmonicStability" in definition_text)
for name in ["primeRemainder", "harmonicExceptionalProduct"]:
    pattern = rf"(?m)^def {name}\b[\s\S]*?(?=\n\n)"
    check(name + "_definition_matches_original", normalize(re.search(pattern, definition_text).group(0)) == normalize(re.search(pattern, source).group(0)))

stripped_source = source
for name in ["primeRemainder", "harmonicExceptionalProduct"]:
    stripped_source = remove_definition(stripped_source, name)

expected_args = {
    "harmonic_finite_prime_product_dvd": "s K N S hs hS",
    "harmonic_finite_prime_log_lower_bound": "s K N S hs hS",
    "harmonic_large_prime_den_valuation": "s N p hp hs hNp hN hunit",
}

for p in problems["problems"]:
    full = p["theorem_name"]
    short = full.rsplit(".", 1)[-1]
    solution_path = ROOT / p["local_solution"]
    reference_path = ROOT / p["local_reference"]
    solution = solution_path.read_text(encoding="utf-8")
    reference = reference_path.read_text(encoding="utf-8")
    hashes[p["local_solution"]] = sha(solution_path)
    hashes[p["local_reference"]] = sha(reference_path)
    check(short + ": source_payload_signature_identical", signature(source, short) == signature(p["formal_statement"], full))
    check(short + ": source_top_solution_signature_identical", signature(source, short) == signature(solution, "solution"))
    check(short + ": exact_reference_payload", normalize(reference) == normalize(p["preamble"] + "\nset_option autoImplicit false\n\n" + p["formal_statement"]))
    check(short + ": reference_has_only_target_sorry", len(re.findall(r"\bsorry\b", no_comments(reference))) == 1)
    check(short + ": solution_has_no_sorry_or_custom_axiom", not re.search(r"\b(sorry|sorryAx|axiom)\b", no_comments(solution)))
    check(short + ": solution_imports_no_target_stub", not re.search(r"(?m)^import (Theorems\.|.*Thm_)", solution))
    check(short + ": solution_body_exact_checked_theorem_application", f"exact ZetaNine.HarmonicStability.checked_{short} {expected_args[short]}" in solution)
    core = solution.split("\nopen ZetaNine.HarmonicStability\n\ntheorem solution", 1)[0]
    core = re.sub(rf"\bchecked_{re.escape(short)}\b", short, core)
    check(short + ": whole_original_proof_body_preserved", proof_core(core) == proof_core(stripped_source))
    check(short + ": solution_sha_matches_provenance", sha(solution_path) == provenance["signature_checks"][full]["solution_sha256"])

base_definition = ROOT / "Definitions/Def_ZetaNine_HarmonicStability.lean"
hashes["Definitions/Def_ZetaNine_HarmonicStability.lean"] = sha(base_definition)
check("base_harmonic_definition_is_original_finite_sum", "∑ j ∈ Finset.Icc 1 N, 1 / (j : ℚ) ^ s" in base_definition.read_text(encoding="utf-8"))

build_log = BATCH / "task-build.log"
build_exit = BATCH / "task-build-exit.txt"
log = build_log.read_text(encoding="utf-8-sig")
check("formal_scoped_build_exit_zero", build_exit.read_text(encoding="utf-8-sig").strip() == "0")
check("formal_scoped_build_completed", "Build completed successfully" in log)
for p in problems["problems"]:
    line = next((line for line in log.splitlines() if p["local_solution"] in line and "depends on axioms" in line), "")
    check(p["theorem_name"] + ": compiled_solution_only_standard_axioms", "[propext, Classical.choice, Quot.sound]" in line and "sorryAx" not in line)

h2 = Fraction(1) + Fraction(1, 2 ** 9)
h38 = sum((Fraction(1, j ** 9) for j in range(1, 39)), Fraction(0))
exponent = 0
den = h38.denominator
while den % 19 == 0:
    den //= 19
    exponent += 1
check("natural_statement_actual_exception_example", h2 == Fraction(513, 512) and exponent == 8)

for name in ["definitions-request.json", "problems-request.json", "integration-provenance.json", "task-build.log", "task-build-exit.txt"]:
    hashes["missions/zeta9/formalization/platform/prime-valuation/" + name] = sha(BATCH / name)

result = {
    "verdict": "PASS" if not findings else "FAIL",
    "reviewer": "independent harmonic-asymptotic agent",
    "scope": "one lightweight definition, three exact original finite-prime theorem interfaces, three proof solutions and their task-scoped Lean build",
    "mathematical_reading": {
        "quantifiers": "All original natural parameters and every finite admitted prime set are retained; positive s, primality, floor-block, explicit exception, and original numerator-unit hypotheses are unchanged.",
        "actual_objects": "Reduced numerator and positive reduced denominator of the original rational generalized harmonic sums are used throughout.",
        "unproved_goal_boundary": "This finite-prime batch neither proves PNT nor the unconditional full harmonic denominator rate, and does not close zeta(9) irrationality.",
        "target_stubs": "Theorems files intentionally register sorry targets; no Solutions file imports them, and all three top-level solution axiom reports are standard only.",
    },
    "checks": checks,
    "findings": findings,
    "sha256": hashes,
}
(BATCH / "independent-integration-review.json").write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"verdict": result["verdict"], "checks": len(checks), "findings": findings}, ensure_ascii=True))
raise SystemExit(0 if not findings else 1)
