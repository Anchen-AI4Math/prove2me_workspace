"""Bind the independent mathematical review to frozen source and actual Lean evidence."""
from pathlib import Path
import hashlib
import json
import re
from datetime import datetime, timezone

OUT = Path(__file__).resolve().parent
BASE = OUT.parent
TASK = OUT.parents[2]
EXPECTED = "e055780f1abf389593fbccba2194fc52ee85108bbb4593439c32230944b3ab03"
def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):
    return json.loads(p.read_text(encoding="utf-8-sig"))
source = TASK / "formalization/CoefficientMap.lean"
assert sha(source) == EXPECTED
receipt = load(OUT / "independent-compile-receipt.json")
assert receipt["status"] == "PASS" and not receipt["unexpected_axioms"] and not receipt["missing_original_reports"]
assert len(receipt["steps"]) == 2 and all(row["exit_code"] == 0 for row in receipt["steps"])
assert receipt["original_source_unchanged_after_review"] and receipt["independent_copy_exact_bytes"]
author = load(BASE / "compile-receipt.json")
assert author["source_sha256"] == EXPECTED
assert author["source_compile"]["exit_code"] == 0 and author["imported_statement_audit"]["exit_code"] == 0
types = load(BASE / "type-report.json")
assert len(types) == 28
allowed = {"propext", "Classical.choice", "Quot.sound"}
assert all(set(row["axioms"]) == allowed for row in types)
actual_names = {row["declaration"] for row in types}
text = source.read_text(encoding="utf-8-sig")
native_names = {"ZetaNine.CoefficientMap." + x for x in re.findall(r"(?m)^(?:def|theorem)\s+(\w+)", text)}
assert len(native_names) == 27 and native_names <= actual_names
definitions = [row for row in types if row["declaration"] in native_names and row["definitionValue"] is not None]
assert len(definitions) == 9
assert not re.search(r"(?m)^\s*axiom\s", text)
assert "by sorry" not in text and "sorryAx" not in text
assert "(n.choose j" not in text[text.index("def leadingPoleCoefficient"):text.index("def weightedR")]
frozen_zip = TASK / "publication/2026-10-02/advanced-proofs/zeta9-advanced-proofs-2026-10-02.zip"
assert sha(frozen_zip) == "87c7ea2680bda568e8e2b36b82f48dab6910ab9bf92e8b4486471c547792e31c"

checks = [
    {"check": "actual Eq(1) specialization", "pass": True,
     "detail": "p=9,q=1,m=n gives n!^9/(n!)^2=n!^7. The first finite product t-1,...,t-n equals the rising Pochhammer (t-n)_n by reordering; the second is (t+n+1)_n. The pole product is exactly product(k=0..n,t+k)^9."},
    {"check": "coefficient defined from genuine rational product", "pass": True,
     "detail": "actualR is numerator/poleProduct^9; clearedR removes exactly the j factor; leadingPoleCoefficient is clearedR evaluated at -j. Its definition contains no closed binomial coefficient formula."},
    {"check": "regular-point clearing and denominator safety", "pass": True,
     "detail": "clear_highest_pole assumes j<=n and every t+k !=0, then proves actualR*(t+j)^9=clearedR. The proof factors the pole product and supplies nonzero factor and deleted product. clearedPoleProduct_ne_zero proves the denominator at -j is nonzero, even without j<=n."},
    {"check": "actual product computation of highest coefficient", "pass": True,
     "detail": "numerator_eval derives (-1)^n*n!^9*choose(n+j,n)*choose(2n-j,n). clearedPoleProduct_eval derives (-1)^j*j!*(n-j)!. Their ninth-power quotient, factorial nonzero facts and Nat.cast_choose give the formula; it is not a definitional rfl substitution."},
    {"check": "Eq(6) phase and binomial factors", "pass": True,
     "detail": "The specialized phase (-1)^(9j+n) equals (-1)^(n+j). Factors are choose(n,j)^9, choose(n+j,n), choose(2n-j,n). The general theorem covers odd n; only the even corollary drops (-1)^n."},
    {"check": "zero boundary and endpoint signs", "pass": True,
     "detail": "Independent Lean wrappers prove leadingPoleCoefficient(0,0)=1, (1,0)=-2, (1,1)=2, and (2,1)=-4608. n=0 uses empty numerator/deleted products. At a pole totalized rational division in actualR is not substituted into the clearing identity, whose regularity hypothesis is explicit."},
    {"check": "unweighted integrality and nonvanishing", "pass": True,
     "detail": "For every j<=n all three binomial factors are strictly positive, so the actual coefficient is nonzero. Its explicit integer witness is the signed binomial product. The final rfl in the integer proof checks casts after leadingPoleCoefficient_eq has already been proved."},
    {"check": "even signed positivity", "pass": True,
     "detail": "For even n, (-1)^j*leadingPoleCoefficient(n,j)>0 follows by squaring the sign and positivity of all three actual binomial factors. No replacement positive coefficient is introduced."},
    {"check": "actual weighted family and local coordinate", "pass": True,
     "detail": "weightedR is actualR times W.eval(t*(t+n)); the coordinate t=-j+z is exactly -j(n-j)+(n-2j)z+z^2, with no n^-2 scaling. The weighted regular-point clearing theorem follows from the actual unweighted identity."},
    {"check": "highest-order part of Eq(5)", "pass": True,
     "detail": "For every W in Q[X], the highest cleared value is the actual unweighted coefficient multiplied by W(-j(n-j)). This formalizes the highest-order term of Eq(5) and the exact local coordinate identity, not the whole lower-order Taylor convolution."},
    {"check": "weighted nonvanishing boundary retained", "pass": True,
     "detail": "The independent Lean audit proves weightedLeadingPoleCoefficient !=0 iff W(-j(n-j)) !=0, using the actual unweighted nonzero theorem. It also proves W=X+1 cancels the highest coefficient at n=2,j=1. A nonzero polynomial W therefore does not by itself give a nonzero highest coefficient."},
    {"check": "source and definition/type coverage", "pass": True,
     "detail": "All 27 actual source declarations are covered by the author's imported Lean record, including all nine definition values; a 28th closed actual-product statement is also checked. The independent compile re-elaborates the exact original source bytes and prints the genuine product definitions."},
    {"check": "actual compiler and axiom evidence", "pass": True,
     "detail": "Independent lake --no-cache build CoefficientMap and lake env lean ReviewAudit.lean both exit 0 in a separate minimal project. The original eight endpoints and ten review statements have no axioms outside propext, Classical.choice, Quot.sound. No source sorry or own axiom is present."},
    {"check": "finite exact arithmetic regression", "pass": True,
     "detail": "Fraction-only independent product evaluation checks 91 local coefficients, 364 regular-point identities and 455 weighted values across 0<=n<=12, 0<=j<=n, including integer and rational polynomials. These finite checks support the implementation and do not replace the universal Lean proof."},
]
remaining = [
    "All lower-order local Taylor/partial-fraction coefficients and the complete Eq(5) convolution.",
    "A full partial-fraction decomposition of the actual rational function; formal Laurent-series machinery is not included here.",
    "Reflection identities, all even coefficient sums and the order-one cancellation needed by the infinite sum.",
    "Exact L(W)=B(W)+A3*zeta(3)+A5*zeta(5)+A7*zeta(7)+A9*zeta(9), including convergence and constants.",
    "The actual complete five-dimensional coefficient map F, all-even invertibility and prescribed (b,a) inverse images.",
    "The infinite small nonzero integer linear forms required for zeta(9) irrationality.",
]
review = {
    "status": "PASS", "verdict": "PASS_ACTUAL_FINITE_LEADING_POLE_ENTRY_ONLY",
    "review_role": "Independent mathematical and Lean reviewer; proof source authored and frozen by another agent",
    "checked_at": datetime.now(timezone.utc).isoformat(),
    "source": "missions/zeta9/formalization/CoefficientMap.lean", "source_sha256": EXPECTED,
    "written_source": "missions/zeta9/round5/research/arithmetic.md", "written_source_sha256": sha(TASK / "round5/research/arithmetic.md"),
    "written_scope": "Section 1 Eq(1), highest-order part of Eq(5), Section 2 Eq(6), specialized p=9,q=1,m=n",
    "environment": {"compiler": receipt["compiler"], "mathlib_revision": receipt["mathlib_revision"]},
    "checks": checks, "source_defects": [], "remaining_obligations": remaining,
    "full_F_completed": False, "invertibility_completed": False, "exact_infinite_L_completed": False,
    "irrationality_proved": False, "platform_acceptance_claimed": False,
    "independent_build_steps": receipt["steps"], "independent_source_axiom_endpoints": 8,
    "additional_independent_review_statements": 10,
    "allowed_axioms": sorted(allowed), "unexpected_axioms": {},
    "original_declarations_imported_type_and_definition_records": 27,
    "author_extra_checked_actual_endpoint_records": 1,
    "finite_arithmetic": receipt["finite_arithmetic"],
    "evidence": {
        "author_compile_receipt_sha256": sha(BASE / "compile-receipt.json"),
        "author_type_report_sha256": sha(BASE / "type-report.json"),
        "independent_compile_log": "independent-review/independent-compile.log",
        "independent_compile_log_sha256": sha(OUT / "independent-compile.log"),
        "independent_compile_receipt": "independent-review/independent-compile-receipt.json",
        "independent_compile_receipt_sha256": sha(OUT / "independent-compile-receipt.json"),
        "review_audit_source_sha256": sha(OUT / "project/ReviewAudit.lean"),
        "exact_arithmetic_sha256": sha(OUT / "exact-arithmetic.json"),
    },
    "original_source_unchanged": True,
    "frozen_advanced_zip_unchanged_sha256": sha(frozen_zip),
    "proof_source_edits": [], "shared_root_or_scope_edits": [], "advanced_zip_or_sidecar_edits": [],
    "network_API_credential_operations": False,
    "review_harness_attempts": "Two failed finite audit-wrapper normalization attempts are preserved under independent-review; only the review wrapper was repaired, and the original proof passed every independent source build.",
}
(BASE / "independent-review.json").write_text(json.dumps(review, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
summary = """# Independent CoefficientMap review

PASS for the actual finite leading-pole entry, source SHA256
`e055780f1abf389593fbccba2194fc52ee85108bbb4593439c32230944b3ab03`.

The source defines the genuine p=9,q=1,m=n rational numerator and full pole
product. It proves the regular-point clearing identity with nonzero denominator,
then computes the cleared value at -j from factorial products. The coefficient
is not defined by its binomial closed form. The unweighted actual coefficient
is integral, nonzero for all j<=n, and has the correct general phase (-1)^(n+j).
Its even signed positivity and n=0,j=0 value 1 are verified.

For arbitrary rational-coefficient polynomial W, the actual highest local
coefficient is multiplied by W(-j(n-j)). A nonzero W can vanish at this node;
the independent Lean audit proves the exact nonzero criterion and a cancelling
W=X+1 example at n=2,j=1. The local coordinate identity uses the unscaled u.

Independent original-source build and closed statement/boundary audit both
exit 0 under Lean 4.33.1 and Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
Eight original endpoints and ten independent review statements have no axioms
outside propext, Classical.choice, Quot.sound. All 27 original declarations
are covered by the author's imported type/definition-value records. Finite
Fraction regressions separately check 91 local coefficients, 364 regular
identities and 455 weighted coefficients; they are not the universal proof.

The full lower-order Eq(5) convolution, complete partial fractions, exact
infinite L, full five-dimensional F, invertibility and prescribed-output
inverse images remain unproved by this file. Irrationality remains open.
No source, shared root, scope, frozen advanced package or API state was edited.

See independent-review.json and independent-review/independent-compile.log.
"""
(BASE / "independent-review.md").write_text(summary, encoding="utf-8")
names = ["independent-review.json", "independent-review.md", "independent-review/independent-compile.log",
         "independent-review/independent-compile-receipt.json", "independent-review/exact-arithmetic.json",
         "independent-review/project/ReviewAudit.lean", "independent-review/project/CoefficientMap.lean"]
sums = "".join(sha(BASE / name) + "  " + name + "\n" for name in names)
(BASE / "independent-review-SHA256SUMS.txt").write_text(sums, encoding="utf-8")
print(json.dumps({"status": "PASS", "review_sha256": sha(BASE / "independent-review.json"),
                  "checks": len(checks), "independent_build_exit_codes": [row["exit_code"] for row in receipt["steps"]],
                  "original_endpoints": 8, "additional_review_statements": 10,
                  "full_F_completed": False, "exact_infinite_L_completed": False}))
