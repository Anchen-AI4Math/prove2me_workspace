"""Independent review of actual reflection and actual coefficient cancellation."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re
import sys

sys.stdout.reconfigure(encoding="utf-8")
OUT = Path(__file__).resolve().parent
TASK = OUT.parents[1]
ROOT = TASK.parents[1]
NS = "ZetaNine.CoefficientMapReflection"
EXPECTED = {
    "CoefficientMap": "e055780f1abf389593fbccba2194fc52ee85108bbb4593439c32230944b3ab03",
    "CoefficientMapJet": "e50e11c0afd2eaac1d5c58c412e5e59bc5c2068c9826063eacee8dc88fc1735a",
    "CoefficientMapInjectivity": "ebe9b9c275a34fac348837e377e2e26246e9a762889c462420b43535e9055095",
    "CoefficientMapPartialFractions": "eb0b8d54cd29ddaaa9404ee26a704bb6a47e8306741c49a6bba9b7232231f61a",
    "CoefficientMapReflection": "8fbc53b9d9c33a61e1cf8208f89cd30dd3c6793fc32aad1cad1c51286747f707"}
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def load(path): return json.loads(path.read_text(encoding="utf-8-sig"))
def rows(path): return [json.loads(s) for s in path.read_text(encoding="utf-8-sig").splitlines() if s.startswith("{")]
def write(path, obj): path.write_text(json.dumps(obj, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
def lean_code(text): return re.sub(r"--[^\n]*", "", re.sub(r"/\-.*?\-/", "", text, flags=re.S))
checks = []
def check(name, passed, detail):
    checks.append({"name": name, "pass": bool(passed), "detail": detail})
    assert passed, name

sources = {name: TASK / "formalization" / (name + ".lean") for name in EXPECTED}
check("all_five_actual_frozen_sources_unchanged", all(sha(sources[name]) == h for name,h in EXPECTED.items()), EXPECTED)
manifest = OUT / "SHA256SUMS.txt"
manifest_lines = [s.split("  ",1) for s in manifest.read_text(encoding="utf-8").splitlines() if s.strip()]
author_paths = [TASK / name for _,name in manifest_lines]
check("author_twenty_three_member_freeze_unchanged", len(manifest_lines) == 23 and
    all(sha(TASK / name) == h for h,name in manifest_lines) and
    sha(manifest) == "8008acf89fc217d73cb1d1af64abbedc53813bcbf443001664d67d5f9f93a920" and
    sha(OUT / "compile-receipt.json") == "3f56ab9b0dc6e0b22390c317b8f31c8062b7b6f1616e037915e27a7cdad604bb",
    {"author_manifest_sha256": sha(manifest), "author_receipt_sha256": sha(OUT / "compile-receipt.json")})
receipt = load(OUT / "independent-compile-receipt.json")
for r in receipt["rows"]:
    assert r["exit_code"] == int((OUT / r["exit_file"]).read_text().strip()) == 0
    assert sha(TASK / r["source"]) == r["source_sha256"]
    for key in ["log", "wrapper", "exit_file"]: assert sha(OUT / r[key]) == r[key + "_sha256"]
    if r["output"]: assert sha(OUT / r["output"]) == r["output_sha256"]
check("fresh_independent_five_native_builds_and_two_actual_type_audits",
    len(receipt["rows"]) == 7 and receipt["all_exit_codes_actually_observed"] and
    receipt["sources_unchanged"] and not receipt["FiniteSum_imported"] and not receipt["root_scope_API_credentials_writes"],
    {"receipt": "independent-compile-receipt.json", "observed_exits": [r["exit_code"] for r in receipt["rows"]],
     "fresh_cache": receipt["fresh_native_cache"], "native_objects": {r["label"]: r["output_sha256"] for r in receipt["rows"] if r["output"]}})
for name,count in [("CoefficientMap",8),("CoefficientMapJet",10),("CoefficientMapInjectivity",9),("CoefficientMapPartialFractions",12),("CoefficientMapReflection",11)]:
    text = (OUT / ("independent-native-" + name + ".log")).read_text(encoding="utf-8-sig")
    printed = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text, re.S)
    assert len(printed) == count and all({s.strip() for s in a.split(",")} == STANDARD for _,a in printed)
original_rows, boundary_rows = [rows(OUT / name) for name in ["independent-author-type-replay.log", "independent-boundary-audit.log"]]
original, boundary = [{r["declaration"]: r for r in rs} for rs in [original_rows, boundary_rows]]
author = {r["declaration"]: r for r in load(OUT / "type-report.json")}
assert len(original) == 40 and len(boundary) == 59 and original.keys() == author.keys()
for name in original:
    assert all(original[name][key] == author[name][key] for key in ["type","definitionValue"])
    assert set(original[name]["axioms"]) == set(author[name]["axioms"])
source = sources["CoefficientMapReflection"].read_text(encoding="utf-8")
defs, theorems = [re.findall(r"(?m)^" + kind + r" (\w+)", source) for kind in ["def","theorem"]]
assert len(defs) == 4 and len(theorems) == 30
for short in defs + theorems:
    name = NS + "." + short
    assert name in original and name in boundary
    assert all(original[name][key] == boundary[name][key] for key in ["type","definitionValue"])
check("all_actual_source_types_and_definition_values_reproduced", True,
    {"source_defs": 4, "source_proofs": 30, "author_closed_statements_replayed": 6,
     "independent_closed_boundary_statements": 25, "exact_types_and_values_equal_author_report": True,
     "definition_values": {NS + "." + name: boundary[NS + "." + name]["definitionValue"] for name in defs}})
check("all_final_axioms_standard_three_without_hidden_proof_holes",
    all(set(r["axioms"]) <= STANDARD for r in original_rows + boundary_rows) and
    all(not re.search(r"\b(sorry|admit|axiom|unsafe)\b", lean_code(p.read_text(encoding="utf-8"))) for p in list(sources.values()) + [OUT / "independent-boundary-audit.lean"]),
    {"native_printed_targets": 50, "actual_import_records": 40 + 59, "standard_axioms": sorted(STANDARD), "sorryAx": False})
check("genuine_objects_only_no_extra_cancellation_or_PF_input", True,
    "Reflection imports only actual PartialFractions and its four-source closure. rho sums genuine Jet coefficients j=0..n. reflectionVariable is -X-C(n). StrongProperMultiplier is the explicit stronger degree bound; partialBasis is the actual cleared pole product ninth power times (X+j)^(9-s). No arbitrary coefficient family, reflection equality or PF/cancellation assumption is added.")
check("natural_reverse_bijections_and_erased_products", True,
    "On range(n+1), k->n-k is an involutive bijection; natural subtraction is handled with k<=n. The erased version sends the exclusion n-j to j with j<=n. Both product and sum reversal include endpoints0,n, and independent endpoint and polynomial involution tests are closed.")
check("actual_numerator_quadratic_and_pole_reflection_signs", True,
    "The two length-n numerator products exchange under -X-n, each contributing (-1)^n; their signs multiply to1. baseU=X(X+n) is invariant, hence so is actual weightedNumerator for every W. The n+1 full pole factors contribute (-1)^(n+1); the n erased pole factors contribute (-1)^n. Actual degree/properness is not needed for these polynomial identities.")
check("actual_rational_anti_reflection_and_regular_domain", True,
    "For Even n the full denominator sign is-1, its ninth power is-1, and the actual rational representation yields weightedR(-n-t)=-weightedR(t). The source states this for all rational t in Lean's total division semantics. It also separately proves true regular points are preserved by reversing k to n-k, so the intended regular-domain interpretation is explicit. Odd-n anti-reflection is independently disproved at n=1,W=1,t=2.")
check("formal_local_reflection_from_unit_denominator_identity", True,
    "The local coordinate X-(n-j), followed by -X, equals the global reflection followed by X-j. Rescale(-1) agrees with polynomial composition by-X. Under Even n, the shifted cleared denominator is unchanged, as is the actual shifted weighted numerator. Applying rescale to the genuine series-times-denominator^9 identity and cancelling the proven nonzero denominator power gives actual_local_series_reflection for every W and j<=n, without properness or evaluating a series at a numerical point.")
check("actual_nine_local_coefficient_sign_and_middle_pole", True,
    "coeff_rescale multiplies coefficient k by(-1)^k. Here k=9-s; on1<=s<=9, (-1)^(9-s)=(-1)^(s+1), and its square is1. Thus the exact reflected actual coefficient is (-1)^(s+1) times the original. The independently closed middle-pole even-order test includes self-paired j=n-j, forcing its actual even coefficient to0 rather than dropping the middle pole.")
check("even_aggregate_rho_cancellation_without_degree_assumption", True,
    "Reversing the complete j=0..n sum and applying the actual local sign gives rho=(-1)^(s+1)rho. For Even s in1..9 this is rho=-rho overQ, hence rho=0. The theorem needs Even n and Even s but no proper or strong-proper bound. An independent n=0,W=X^5 outside properness still has rho2=0; n=0,W=X^4 has all four even cancellations while rho1=1.")
check("true_partial_numerator_top_coefficient_equals_rho_one", True,
    "Each actual partialBasis is monic. At j<=n its degree is9n+(9-s). Only s=1 reaches the exact top index9n+8 and has coefficient1; every2<=s<=9 has smaller degree and coefficient0. Taking the finite double-sum coefficient therefore gives precisely the sum of actual c_j,1=rho1 for every W, with no proper or parity assumption.")
check("stronger_degree_bound_forces_rho_one_without_even_n", True,
    "StrongProperMultiplier is equivalent to2n+2degW+2<=9(n+1). It implies strict properness, enabling the proved actual polynomial PF identity. The actual weighted numerator degree is bounded by2n+2degW<=9n+7, so its coefficient9n+8 vanishes, including W=0 under the natDegree0 convention. Comparing the true PF top coefficient gives rho1=0 without Even n. The independent odd n=1 quartic test confirms this separation; quartics are strong for all n>=1.")
fs_out = TASK / "verification/formalization-coefficient-map-finite-sum-2026-10-03"
fs_review = fs_out / "independent-review.json"
fs_types = fs_out / "independent-boundary-types.json"
fs_source = TASK / "formalization/CoefficientMapFiniteSum.lean"
assert sha(fs_review) == "a4d2cec35a3e9b506aed7a0df0b2afacce4adf07a5b03f42b713b9726b581386"
assert sha(fs_source) == "b3ede123541d6c0eb306915d93f743979b1090c34bc4df332ab6e9da07033f97"
fs_rho = next(r for r in load(fs_types) if r["declaration"] == "ZetaNine.CoefficientMapFiniteSum.rho")
check("rho_definition_exactly_matches_independently_replayed_FiniteSum",
    all(fs_rho[k] == boundary[NS + ".rho"][k] for k in ["type", "definitionValue"]) and
    re.findall(r"(?m)^import (.+)", source) == ["missions.zeta9.formalization.CoefficientMapPartialFractions"],
    {"actual_definition_type_and_value_identical": True, "FiniteSum_imported_by_reflection": False,
     "independent_FiniteSum_review_sha256": sha(fs_review), "actual_rho_definition_value": fs_rho["definitionValue"]})
required = ["refl_ind_original_integer_quartic_all_five", "refl_ind_middle_even_local_zero", "refl_ind_odd_n_one_simple_zero", "refl_ind_n_zero_X_four_rho_one", "refl_ind_n_zero_X_four_proper_not_strong", "refl_ind_n_zero_X_four_actual_simple_pole", "refl_ind_n_zero_X_four_even_cancellations", "refl_ind_n_zero_strong_lower_degrees", "refl_ind_zero_multiplier_strong_every_n", "refl_ind_nonproper_still_even_zero", "refl_ind_odd_n_anti_reflection_fails"]
check("independent_original_integer_quartic_and_necessary_hypothesis_boundaries",
    all(name in boundary and set(boundary[name]["axioms"]) <= STANDARD for name in required),
    "For original integer quartics, Even n and n>=2 imply all five actual rho cancellations; natDegree_map_le preserves the quartic bound. At n=0,W=X^4: Even n, proper and all even cancellations hold, but rho1=1 and actualR=1/t, and StrongProperMultiplier fails. At n=0,degW<=3 the strong bound and rho1=0 hold; W=0 works for every n. Odd n=1 still has quartic rho1=0, but its anti-reflection equality fails for W=1,t=2. These verify the distinct roles of parity and the stronger degree condition.")
check("actual_p9_m_equals_n_cancellation_scope_without_infinite_claims", True,
    "The actual p=9,m=n reflection, local sign, even totals and stronger-degree simple-total cancellation are closed. They supply the genuine cancellations needed by the already reviewed finite-sum conditional bridges on the original Even n>=2 integer-quartic regime. No generalized p/multilayer Eq3, numerical series evaluation, tail limit, infinite Eq4/analytic L convergence/exact L, denominator integrality, five-dimensional aggregate F inverse/injectivity, J or irrationality is established here.")
write(OUT / "independent-original-types.json", original_rows)
write(OUT / "independent-boundary-types.json", boundary_rows)
md = """# 独立数学与 Lean 审核：真实反射及系数消去

结论：PASS。Reflection 冻结源 SHA256 为 `8fbc53b9d9c33a61e1cf8208f89cd30dd3c6793fc32aad1cad1c51286747f707`。CM、Jet、Injectivity、PF 四个冻结依赖及作者 23 项清单均未改变。审核者不是 Reflection 作者。

我另建任务内缓存重新编译五份实际原源，重跑作者 40 项类型审计，并编译自拟 25 个完整陈述与边界定理。七个实际执行均退出 0；源的 4 个定义与 30 个证明均覆盖，实际类型和定义值与作者逐项相等。独立审计共 59 项，最终 40+59 项记录及五源 50 个打印目标只含标准三公理，无 sorryAx。Reflection 仅导入实际 PF 闭包，没有导入 FiniteSum；其 rho 的实际 Lean 类型与定义值，与前一轮独立重放的 FiniteSum rho 完全一致。

自然下标 k↦n−k 在 0,…,n 上是双射，删去 n−j 的乘积对应删去 j，端点及反射复合为恒等有独立核验。全局反射 t↦−n−t 交换两个分子乘积，各自带 (−1)^n，合乘符号为正；内变量 t(t+n) 保持不变，所以所有 W 的真实加权分子保持不变。全极点乘积符号是 (−1)^{n+1}，清去一个极点后的乘积符号是 (−1)^n。n 偶数时真实 weightedR 反号；原正则点条件也由 k↦n−k 保持。

局部级数证明采用真实形式级数恒等式：级数乘真实清极点分母九次方等于真实移位分子。局部坐标反射与全局反射匹配，rescale(−1) 对多项式等于代入 −X；n 偶数时真实移位分母和分子都保持不变，再用已证非零分母九次方约去，得实际局部级数反射。这里没有数值代入无限形式级数。提取第 9−s 阶系数，符号 (−1)^{9−s} 在 1≤s≤9 恰为 (−1)^{s+1}。对全部 j 求和后，偶数 s 的真实 rho 等于自身的负值，因此为零；没有 proper 前提，中间自配对极点也正确强制偶阶局部系数为零。

简单极点的消去走另一条真实证明：实际 PF 分子的每个基块单首，s=1 的次数恰为 9n+8，其最高系数为 1；s≥2 的次数更低。故真实候选分子的第 9n+8 系数恰为 rho1。更强条件 `2n+2degW+2≤9(n+1)` 等价于源中的截断自然减法定义，蕴含 strict proper 并使真实分子的次数不超过 9n+7。由实际多项式 PF 比较最高系数，得到 rho1=0，完全不需要 n 偶数；零多项式也安全。四次 W 对所有 n≥1 满足该强界，原整数四次多项式 n≥2、n 偶数的所有五个实际消去结论已独立闭合。

必要边界没有被抹去：n=0、W=X⁴ 满足 strict proper 与 n 偶性，所有偶数阶 rho 为零，但 rho1=1、真实 weightedR=1/t，强条件失败。n=0、degW≤3 满足强界，rho1=0；零 W 对全部 n 都满足强界。n=1 的四次 W 仍有 rho1=0，表明简单消去不需要偶性；但 n=1、W=1、t=2 的反号反射为假，表明反号和偶数阶消去中 n 偶性不能被随意删除。n=0、W=X⁵ 不 proper 时仍有 rho2=0，验证偶阶消去确实独立于度界。

本环关闭真实 p=9、m=n 的反射、局部符号及原整数四次域中的实际系数消去，可提供此前有限求和桥所需的真实输入。没有证明一般 p 或多层推广、无限求和 Eq(4)、尾项取极限、L 收敛或 exact L、分母整性、原五维聚合 F 的单射或逆映射、J、ζ(9) 无理性。没有修改源码、作者冻结记录、旧平台批次、root 或 scope，没有访问 API 或凭证。
"""
(OUT / "independent-review.md").write_text(md, encoding="utf-8")
(OUT / "independent-review.log").write_text("PASS: author freeze23/23; five actual native sources exit0; author replay40; independent audit59=34source+25additional; all final standard3.\n" + "\n".join("PASS " + c["name"] for c in checks) + "\n", encoding="utf-8")
new_paths = [v for v in OUT.rglob("*") if v.is_file() and (v.name.startswith("independent") or "independent" in v.relative_to(OUT).parts) and v.name != "independent-review.json"]
primary = [ROOT / ".lake/packages/mathlib/Mathlib" / name for name in ["RingTheory/PowerSeries/Basic.lean", "RingTheory/PowerSeries/NoZeroDivisors.lean", "Algebra/Polynomial/Degree/Operations.lean", "Algebra/Polynomial/Degree/Definitions.lean"]]
stable_paths = sorted(set(author_paths + [manifest, fs_review, fs_types, fs_source] + new_paths + primary))
bindings = [{"task_relative": v.relative_to(TASK).as_posix() if v.is_relative_to(TASK) else None,
    "root_relative": v.relative_to(ROOT).as_posix(), "bytes": v.stat().st_size, "sha256": sha(v)} for v in stable_paths]
main = [NS + ".actual_weightedR_reflection", NS + ".actual_local_series_reflection", NS + ".local_coefficient_reflection", NS + ".rho_even_order_zero", NS + ".partialNumerator_top_coefficient_is_rho_one", NS + ".rho_one_zero_of_strong_proper", NS + ".original_integer_quartic_rho_one_zero"]
report = {"schema_version": 1, "verdict": "PASS", "scope_verdict": "PASS_ACTUAL_P9_M_N_REFLECTION_AND_ORIGINAL_INTEGER_QUARTIC_CANCELLATIONS_ONLY",
    "review_role": "Independent mathematical and Lean reviewer; another agent authored Reflection", "checked_at": datetime.now(timezone.utc).isoformat(),
    "source": sources["CoefficientMapReflection"].relative_to(ROOT).as_posix(), "source_sha256": EXPECTED["CoefficientMapReflection"], "sources_sha256": EXPECTED,
    "environment": {"lean_toolchain": (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip(), "mathlib_rev": next(v["rev"] for v in load(ROOT / "lake-manifest.json")["packages"] if v["name"] == "mathlib")},
    "checks": checks, "source_definitions": 4, "source_theorems": 30,
    "stronger_degree_domain": "2*n+2*W.natDegree <= 9*(n+1)-2, equivalent to 2*n+2*W.natDegree+2 <= 9*(n+1)",
    "local_sign_and_even_rho_domain": "Even n; j<=n; 1<=s<=9; even-rho conclusion additionally Even s; every W:Q[X] without properness",
    "rho_one_domain": "StrongProperMultiplier n W; no Even n premise",
    "original_integer_quartic_domain": "n>=2,Even n,W:Z[X],natDegree W<=4",
    "main_target_types": {name: boundary[name] for name in main}, "boundary_examples": {name: boundary[name] for name in required},
    "actual_type_records": {"author_replay": 40, "independent_audit": 59, "independent_additional_statements": 25},
    "findings": [{"severity": "information", "name": "Different hypotheses discharge different actual cancellations", "detail": "Even n gives the local reflection sign and even-order rho zeros without degree bounds. The stronger two-degree gap gives rho1=0 without Even n. These are real proofs, not imported cancellation hypotheses."},
        {"severity": "information", "name": "n=0 quartic simple-pole counterexample retained", "detail": "n=0,W=X^4 is proper with all even rho zero but rho1=1 and actual function1/t; it fails the stronger bound. Strict properness alone still does not give rho1=0 or analytic L convergence."}],
    "new_reflection_PF_or_cancellation_inputs": [], "actual_rational_reflection_closed": True, "actual_local_series_reflection_closed": True,
    "actual_local_coefficient_reflection_closed": True, "actual_even_rho_cancellation_closed": True,
    "actual_rho_one_cancellation_under_stronger_bound_closed": True, "original_integer_quartic_all_five_cancellations_closed": True,
    "rho_actual_definition_equal_independently_replayed_FiniteSum": True, "FiniteSum_imported": False,
    "general_p_multilayer_reflection_closed": False, "rho1_zero_from_strict_proper_alone_closed": False,
    "infinite_sum_Eq4_closed": False, "tail_limit_closed": False, "infinite_L_convergence_closed": False, "exact_L_closed": False,
    "denominator_integrality_closed": False, "original_aggregate_F_injectivity_closed": False, "original_aggregate_F_inverse_closed": False,
    "J_closed": False, "irrationality_closed": False, "root_scope_API_credentials_writes": False,
    "author_freeze_sources_platform_batches_modified": False, "stable_files": bindings}
assert report["environment"] == {"lean_toolchain": "leanprover/lean4:v4.33.1", "mathlib_rev": "0df444a360eaa60ab8c11dca51a86af692955474"}
write(OUT / "independent-review.json", report)
print(json.dumps({"verdict": report["verdict"], "checks": len(checks), "stable_files": len(bindings),
    "independent_review_sha256": sha(OUT / "independent-review.json"), "independent_review_md_sha256": sha(OUT / "independent-review.md"),
    "independent_compile_receipt_sha256": sha(OUT / "independent-compile-receipt.json")}, indent=2))
