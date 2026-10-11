"""Finalize the independent Jet review with explicit formal/analytic boundaries."""
from pathlib import Path
from fractions import Fraction
from datetime import datetime, timezone
import hashlib
import json
import re
import subprocess

OUT = Path(__file__).resolve().parent
BASE = OUT.parent
TASK = OUT.parents[2]
ROOT = TASK.parents[1]
PINS = {"CoefficientMap.lean": "e055780f1abf389593fbccba2194fc52ee85108bbb4593439c32230944b3ab03",
        "CoefficientMapJet.lean": "e50e11c0afd2eaac1d5c58c412e5e59bc5c2068c9826063eacee8dc88fc1735a"}
PIN = "0df444a360eaa60ab8c11dca51a86af692955474"
def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):
    return json.loads(p.read_text(encoding="utf-8-sig"))
for name,pin in PINS.items():
    assert sha(TASK/"formalization"/name)==pin
receipt=load(OUT/"independent-compile-receipt.json")
assert receipt["status"]=="PASS" and not receipt["unexpected_axioms"] and not receipt["missing_reports"]
assert len(receipt["steps"])==3 and all(x["exit_code"]==0 for x in receipt["steps"])
assert receipt["original_sources_unchanged"]
author=load(BASE/"compile-receipt.json")
assert author["source_sha256"]==PINS["CoefficientMapJet.lean"]
assert author["source_compile"]["exit_code"]==0 and author["imported_statement_audit"]["exit_code"]==0
types=load(BASE/"type-report.json")
assert len(types)==29
allowed={"propext","Classical.choice","Quot.sound"}
assert all(set(x["axioms"])==allowed for x in types)
source=TASK/"formalization/CoefficientMapJet.lean"
text=source.read_text(encoding="utf-8-sig")
native_names={"ZetaNine.CoefficientMapJet."+x for x in re.findall(r"(?m)^(?:def|theorem)\s+(\w+)",text)}
assert len(native_names)==28 and native_names <= {x["declaration"] for x in types}
assert sum(x["definitionValue"] is not None for x in types)==9
assert "PowerSeries.coeff_mul" in text and "Finset.sum_nbij'" in text
assert not re.search(r"(?m)^\s*axiom\s",text) and "by sorry" not in text and "sorryAx" not in text
for name in ["localCoefficient","weightedLocalCoefficient"]:
    value=next(x["definitionValue"] for x in types if x["declaration"]=="ZetaNine.CoefficientMapJet."+name)
    assert "PowerSeries.coeff (9 - s)" in value
mathlib=ROOT/".lake/packages/mathlib"
actual_mathlib=subprocess.run(["git","rev-parse","HEAD"],cwd=mathlib,capture_output=True,text=True,check=True).stdout.strip()
assert actual_mathlib==PIN
inverse_source=mathlib/"Mathlib/RingTheory/PowerSeries/Inverse.lean"
frozen_zip=TASK/"publication/2026-10-02/advanced-proofs/zeta9-advanced-proofs-2026-10-02.zip"
assert sha(frozen_zip)=="87c7ea2680bda568e8e2b36b82f48dab6910ab9bf92e8b4486471c547792e31c"

# Independent exact local quotient recurrence: coefficient 1 in N/D^9.
# N(0)=3072, N'[0]=-2816, D(0)=2, [z]D=3 for n=2,j=0.
c0=Fraction(3072,2**9)
c1=(Fraction(-2816)-Fraction(9*2**8*3)*c0)/Fraction(2**9)
assert c0==6 and c1==Fraction(-173,2)
rational_example={"n":2,"j":0,"s":8,"integer_W":"1",
    "local_coefficient":"-173/2","integer":False,
    "method":"Exact rational quotient recurrence from the actual shifted products: 512*c1+6912*6=-2816",
    "example_is_a_mathematical_arithmetic_check_not_an_extra_Lean_theorem":True}

checks=[
    {"check":"actual shifted products, not assumed coefficients","pass":True,
     "detail":"shiftedVariable=X-C(j); shiftedNumerator is n!^7 times the actual two shifted n-factor products; shiftedClearedDenominator is the actual pole product with j erased. localCoefficient and weightedLocalCoefficient extract coeff(9-s) from their genuine series, with no coefficient array input or target identity premise."},
    {"check":"point-value unweighted and weighted rational bridges","pass":True,
     "detail":"Polynomial evaluations are proved equal to numerator(-j+z), clearedPoleProduct(-j+z), and actual clearedR/clearedWeightedR. These are algebraic rational quotients using the actual frozen base definitions, not a replacement binomial formula."},
    {"check":"denominator unit from the actual nonzero constant","pass":True,
     "detail":"The polynomial's formal constant coefficient equals the erased pole product at -j, proved nonzero by the frozen base lemma. Its ninth power has nonzero constant coefficient. Mathlib's PowerSeries inverse cancel lemmas require exactly this fact, which is proved rather than assumed."},
    {"check":"formal quotient existence and uniqueness","pass":True,
     "detail":"clearedSeries=N*(D^9)^-1 satisfies S*D^9=N, and multiplication by the actual inverse proves uniqueness. The independent audit proves the closed exists-unique statement without a coefficient/decomposition/invertibility hypothesis."},
    {"check":"weighted formal quotient existence and uniqueness","pass":True,
     "detail":"weightedClearedSeries is S times the actual composed polynomial W(localU). The source proves the weighted denominator identity. The independent audit additionally proves it equals (N*W(localU))*(D^9)^-1 and is the unique solution of the weighted identity, for every W in Q[X]."},
    {"check":"bridge to the actual weighted rational function at regular points","pass":True,
     "detail":"The independent audit composes the Jet weighted evaluation bridge with the frozen base clear_weighted_highest_pole theorem. For j<=n and all -j+z+k nonzero, actual weightedR(-j+z)*z^9 equals the displayed genuine shifted polynomial quotient."},
    {"check":"all orders and correct index bounds","pass":True,
     "detail":"For 1<=s<=9 the coefficient is exactly degree 9-s of the cleared series. Nat subtraction outside that domain is not interpreted as an extra pole order; valid actual pole interpretation also uses 0<=j<=n."},
    {"check":"genuine coeff_mul convolution and bijective reindexing","pass":True,
     "detail":"The source unfolds the actual weighted coefficient and applies PowerSeries.coeff_mul. On antidiagonal(a+b=9-s), l=9-a ranges over Icc s 9; the inverse map is (9-l,l-s). Lean checks both membership directions, both inverse equations and the matching summands, with bounds controlling every truncated subtraction."},
    {"check":"unscaled local coordinate","pass":True,
     "detail":"localU equals -j(n-j)+(n-2j)X+X^2 for j<=n, by the actual shifted product. No u/n^2 scaling, hidden denominator rescaling, or substitute local variable is used."},
    {"check":"integer polynomial coefficients correctly cast into Q","pass":True,
     "detail":"integerLocalU is in Z[X], maps exactly to localU under Int.castRingHom Q, and Polynomial.map_comp gives the coefficient identity. The full integer-W convolution multiplies actual rational localCoefficient values by the cast integer coefficients of W.comp(integerLocalU). The independent audit proves these multiplier coefficients have integer witnesses."},
    {"check":"integer multiplier does not assert all local coefficients integral","pass":True,
     "detail":"The rational coefficients of S remain in Q. No denominator-clearing theorem for lower local coefficients is proved here. For n=2,j=0,s=8,W=1 the actual local quotient recurrence gives -173/2, so interpreting integer_coefficient_convolution as coefficientwise integrality would be false."},
    {"check":"highest coefficient compatibility and n=0 boundary","pass":True,
     "detail":"localCoefficient_nine and weightedLocalCoefficient_nine equal the frozen actual cleared-pole values. The independent audit proves S_(0,0)=1, c_(0,0,9)=1 and all c_(0,0,s)=0 for 1<=s<9, without altering the original even n>=2 application."},
    {"check":"arbitrary local W versus global growth constraints","pass":True,
     "detail":"The local convolution is valid for arbitrary polynomial W, including the original integer quartic regime. It does not prove that unrestricted degree W satisfies the infinity degree bound required for a convergent infinite-sum/partial-fraction application."},
    {"check":"formal series and analytic/Laurent trust boundary","pass":True,
     "detail":"This is the unique formal local quotient in Q[[z]], determined by the actual polynomial numerator and unit denominator. Polynomial point-value bridges are not an evaluation/convergence theorem for an infinite formal series at nonzero z. No analytic Taylor convergence, Lean LaurentSeries/RatFunc embedding, full global partial fractions or coefficient-sum identities are established here."},
    {"check":"actual type/definition coverage and no imported theorem stub","pass":True,
     "detail":"All 28 actual Jet declarations, including nine definition values and nineteen proofs, are covered by the author's imported record, plus one closed statement in the original even n>=2, j<=n, integer-quartic, s=1..9 regime. The actual imports are only the frozen complete CoefficientMap and the needed Mathlib modules; no PNT, registration stub or other mission is imported."},
    {"check":"independent compilation, axioms and exact regressions","pass":True,
     "detail":"Exact byte copies at original module paths compile sequentially in a separate minimal project: base exit0, Jet exit0, ten independent closed review statements exit0. Ten original Jet endpoints and ten review statements use no axioms outside propext, Classical.choice, Quot.sound. Exact rational recurrence regressions check all nine orders in 2025 weighted cases and 675 regular bridges; finite data is not the universal proof."},
]
remaining=[
    "Formal LaurentSeries/RatFunc embedding if needed as a separate formal interface; no analytic convergence follows from the current formal series equality.",
    "Global partial-fraction identity for the actual weighted rational function, including any polynomial part when degree bounds are not imposed.",
    "Reflection identities, all even total coefficient cancellations, and the order-one cancellation.",
    "Lower coefficient denominator-clearing/valuation bounds and integrality of the complete linear-form normalization.",
    "Exact convergent infinite-sum identity L(W), including harmonic constants and zeta coefficients.",
    "Actual full five-dimensional coefficient map F, all-even invertibility and exact prescribed-output inverse images.",
    "Infinite nonzero small integer linear forms and zeta(9) irrationality.",
]
review={"status":"PASS","verdict":"PASS_ACTUAL_FORMAL_LOCAL_ALL_NINE_ORDERS_ONLY",
    "review_role":"Independent mathematical and Lean reviewer; another agent authored and froze the source",
    "checked_at":datetime.now(timezone.utc).isoformat(),"sources_sha256":PINS,
    "source":"missions/zeta9/formalization/CoefficientMapJet.lean",
    "written_source":"missions/zeta9/round5/research/arithmetic.md Eq(5), specialized p=9,q=1,m=n",
    "written_source_sha256":sha(TASK/"round5/research/arithmetic.md"),
    "author_scope_note_sha256":sha(TASK/"research/coefficient-map-jet-2026-10-03.md"),
    "environment":{"compiler":receipt["compiler"],"mathlib_revision":PIN,"actual_mathlib_git_revision":actual_mathlib,
                   "inspected_actual_inverse_module_sha256":sha(inverse_source)},
    "checks":checks,"source_defects":[],"remaining_obligations":remaining,
    "scope_flags":{"actual_formal_local_jet":True,"all_s_one_to_nine_convolution":True,
        "integer_W_composition_coefficients":True,"all_lower_coefficients_integer":False,
        "analytic_series_convergence_proved":False,"full_Laurent_interface_proved":False,
        "global_partial_fractions_proved":False,"full_F_completed":False,
        "invertibility_completed":False,"exact_infinite_L_completed":False,"irrationality_proved":False},
    "independent_build_steps":receipt["steps"],"original_Jet_axiom_endpoints":10,"independent_closed_review_statements":10,
    "allowed_axioms":sorted(allowed),"unexpected_axioms":{},"imported_type_records":29,
    "actual_source_definition_values":9,"actual_source_theorems":19,
    "finite_arithmetic":receipt["finite_arithmetic"],"rational_lower_coefficient_example":rational_example,
    "evidence":{"author_compile_receipt_sha256":sha(BASE/"compile-receipt.json"),
        "author_type_report_sha256":sha(BASE/"type-report.json"),
        "independent_compile_log":"independent-review/independent-compile.log",
        "independent_compile_log_sha256":sha(OUT/"independent-compile.log"),
        "independent_compile_receipt_sha256":sha(OUT/"independent-compile-receipt.json"),
        "review_audit_source_sha256":sha(OUT/"project/JetReviewAudit.lean"),
        "exact_arithmetic_sha256":sha(OUT/"exact-arithmetic.json")},
    "original_sources_unchanged":True,"frozen_advanced_zip_unchanged_sha256":sha(frozen_zip),
    "source_root_scope_frozen_package_edits":[],"network_API_credential_operations":False,
    "platform_acceptance_claimed":False}
(BASE/"independent-review.json").write_text(json.dumps(review,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
summary="""# Independent CoefficientMapJet review

PASS for the actual formal local coefficients and all s=1,...,9 convolution.
Frozen Jet source SHA256:
`e50e11c0afd2eaac1d5c58c412e5e59bc5c2068c9826063eacee8dc88fc1735a`.

The coefficients are extracted from the genuine shifted numerator divided in
Q[[z]] by the ninth power of the genuine erased-pole polynomial. Its constant
coefficient is proved nonzero from the actual product. Mathlib inverse laws
prove the denominator identity and uniqueness. No coefficient array, target
convolution, partial-fraction formula or inverse-map assertion is an input.
The independent audit also proves the weighted quotient exists uniquely and
bridges it to actual weightedR(-j+z)*z^9 at every regular point.

The full Icc(s,9) convolution comes from PowerSeries.coeff_mul and a checked
antidiagonal bijection. For integer W the composed multiplier coefficients
are integers and are cast to Q exactly. The local coefficients themselves
remain rational: n=2,j=0,s=8,W=1 gives -173/2 by exact quotient recurrence.
Thus this file does not close lower coefficient denominator normalization.
The highest coefficients agree with the frozen CoefficientMap entry; the
n=0 formal series is independently checked to be 1 with all lower pole
coefficients zero. Arbitrary W is allowed locally, without claiming its degree
satisfies the global decay condition.

Separate exact-source base build, Jet build and independent audit all exit 0
under Lean 4.33.1 and actual Mathlib commit
0df444a360eaa60ab8c11dca51a86af692955474. Ten original Jet endpoints and ten
independent review statements have no axioms outside propext,
Classical.choice, Quot.sound. The imported report covers all nine definitions
and nineteen proofs, plus the original integer-quartic statement. Exact
Fraction regressions separately check 2025 all-order weighted coefficients,
540 integer multiplier coefficients and 675 regular weighted bridges.

The proved object is a formal local quotient. Its polynomial evaluation
bridges do not evaluate an infinite formal series numerically and do not
assert analytic convergence. A full Laurent/RatFunc interface, global partial
fractions, reflection/total-coefficient cancellation, exact infinite L,
complete F, invertibility and prescribed-output inverse images remain open.
Irrationality remains open. No original source, shared root, scope, API state,
credentials, or frozen advanced source package was edited by this review.

See independent-review.json and independent-review/independent-compile.log.
"""
(BASE/"independent-review.md").write_text(summary,encoding="utf-8")
names=["independent-review.json","independent-review.md","independent-review/independent-compile.log",
    "independent-review/independent-compile-receipt.json","independent-review/exact-arithmetic.json",
    "independent-review/project/JetReviewAudit.lean","independent-review/project/missions/zeta9/formalization/CoefficientMap.lean",
    "independent-review/project/missions/zeta9/formalization/CoefficientMapJet.lean"]
(BASE/"independent-review-SHA256SUMS.txt").write_text("".join(sha(BASE/name)+"  "+name+"\n" for name in names),encoding="utf-8")
print(json.dumps({"status":"PASS","review_sha256":sha(BASE/"independent-review.json"),"checks":len(checks),
    "compile_exits":[x["exit_code"] for x in receipt["steps"]],"original_Jet_endpoints":10,
    "independent_review_statements":10,"all_s_one_to_nine":True,"full_F_completed":False,"exact_infinite_L_completed":False}))
