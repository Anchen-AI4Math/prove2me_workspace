"""Independent mathematical review of genuine finite global partial fractions."""
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
NS = "ZetaNine.CoefficientMapPartialFractions"
EXPECTED = {"CoefficientMap": "e055780f1abf389593fbccba2194fc52ee85108bbb4593439c32230944b3ab03", "CoefficientMapJet": "e50e11c0afd2eaac1d5c58c412e5e59bc5c2068c9826063eacee8dc88fc1735a", "CoefficientMapInjectivity": "ebe9b9c275a34fac348837e377e2e26246e9a762889c462420b43535e9055095", "CoefficientMapPartialFractions": "eb0b8d54cd29ddaaa9404ee26a704bb6a47e8306741c49a6bba9b7232231f61a"}
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def load(path): return json.loads(path.read_text(encoding="utf-8-sig"))
def rows(path): return [json.loads(s) for s in path.read_text(encoding="utf-8-sig").splitlines() if s.startswith("{")]
def write(path, obj): path.write_text(json.dumps(obj, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
checks = []
def check(name, passed, detail):
    checks.append({"name": name, "pass": bool(passed), "detail": detail})
    assert passed, name

source_paths = {name: TASK / "formalization" / (name + ".lean") for name in EXPECTED}
check("all_four_frozen_sources_unchanged", all(sha(source_paths[name]) == h for name,h in EXPECTED.items()), EXPECTED)
manifest_path = OUT / "SHA256SUMS.txt"
manifest_lines = [s.split("  ",1) for s in manifest_path.read_text(encoding="utf-8").splitlines()]
author_paths = [TASK / name for _,name in manifest_lines]
check("author_twenty_member_freeze_unchanged", len(manifest_lines) == 20 and all(sha(TASK / name) == h for h,name in manifest_lines) and sha(manifest_path) == "61b04645de44038ed16e623390f4623df2e9c1ebd6eb19a32e3173f2fc56ce68" and sha(OUT / "compile-receipt.json") == "a422a5d3b6d5ddaaa1a26ac8e468266331b08ac78ec3788707db2e131809075d", {"manifest_sha256": sha(manifest_path), "author_receipt_sha256": sha(OUT / "compile-receipt.json")})
receipt = load(OUT / "independent-compile-receipt.json")
for r in receipt["rows"]:
    assert r["exit_code"] == int((OUT / r["exit_file"]).read_text().strip()) == 0
    assert sha(TASK / r["source"]) == r["source_sha256"]
    for key in ["log", "wrapper", "exit_file"]: assert sha(OUT / r[key]) == r[key + "_sha256"]
    if r["output"]: assert sha(OUT / r["output"]) == r["output_sha256"]
check("fresh_independent_four_native_builds_and_two_type_audits", len(receipt["rows"]) == 6 and receipt["all_exit_codes_actually_observed"] and receipt["sources_unchanged"] and not receipt["root_scope_API_credentials_writes"], {"receipt": "independent-compile-receipt.json", "observed_exits": [r["exit_code"] for r in receipt["rows"]], "fresh_cache": receipt["fresh_native_cache"], "native_objects": {r["label"]: r["output_sha256"] for r in receipt["rows"] if r["output"]}})
for name,count in [("CoefficientMap",8),("CoefficientMapJet",10),("CoefficientMapInjectivity",9),("CoefficientMapPartialFractions",12)]:
    text = (OUT / ("independent-native-" + name + ".log")).read_text(encoding="utf-8-sig")
    printed = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text, re.S)
    assert len(printed) == count and all({s.strip() for s in a.split(",")} == STANDARD for _,a in printed)
original_rows, boundary_rows = [rows(OUT / name) for name in ["independent-author-type-replay.log", "independent-boundary-audit.log"]]
original, boundary = [{r["declaration"]: r for r in rs} for rs in [original_rows, boundary_rows]]
author = {r["declaration"]: r for r in load(OUT / "type-report.json")}
assert len(original) == 39 and len(boundary) == 51 and original.keys() == author.keys()
for name in original:
    assert all(original[name][key] == author[name][key] for key in ["type","definitionValue"])
    assert set(original[name]["axioms"]) == set(author[name]["axioms"])
source = source_paths["CoefficientMapPartialFractions"].read_text(encoding="utf-8")
defs, theorems = [re.findall(r"(?m)^" + kind + r" (\w+)", source) for kind in ["def","theorem"]]
assert len(defs) == 5 and len(theorems) == 27
for short in defs + theorems:
    name = NS + "." + short
    assert name in original and name in boundary
    assert all(original[name][key] == boundary[name][key] for key in ["type","definitionValue"])
check("all_actual_source_types_and_definition_values_reproduced", True, {"source_defs": 5, "source_proofs": 27, "author_closed_statements_replayed": 7, "independent_closed_boundary_statements": 19, "definition_values": {NS + "." + name: boundary[NS + "." + name]["definitionValue"] for name in defs}, "exact_types_and_values_equal_frozen_author_report": True})
check("all_final_native_and_import_axioms_standard_three_only", all(set(r["axioms"]) <= STANDARD for r in original_rows + boundary_rows) and not re.search(r"\b(sorry|admit|axiom|unsafe)\b",source), {"standard_axioms": sorted(STANDARD), "native_printed_targets": 39, "actual_import_records": 39 + 51, "final_sorryAx": False})
check("actual_finite_numerator_denominator_and_coefficients", True, "The polynomial numerator is frozen baseNumerator*W.comp(baseU), with baseU=X(X+n). partialNumerator takes only n,W and uses the actual weightedLocalCoefficient double sum over j=0..n,s=1..9. candidateClearedSeries uses the genuine shifted cleared denominator. No arbitrary coefficient array or global decomposition assumption is supplied.")
check("actual_nine_term_truncation_reindexing", True, "PowerSeries.trunc9 retains exactly coefficients k=0..8. The bijection k->s=9-k with inverse s->9-s sends range9 to Icc1 9 and restores 9-(9-k)=k. Thus each block uses the exact actual coefficient attached to the power (X+j)^(9-s), including the simple-pole order s=1.")
check("own_block_nine_jets_from_true_denominator_identity", True, "The shifted own block is D_j(z)^9*T_j(z). The actual weightedClearedSeries times the same D_j^9 is the genuine shifted weighted numerator. X^9 divides the series minus its truncation by coeff_trunc. Multiplication and polynomial coefficient transfer give the exact shifted own-block difference divisible by X^9; no final global PF theorem is used here.")
check("other_blocks_and_full_candidate_match_every_pole", True, "For j<=n and i!=j, the erased product B_i contains X+j, so its ninth power divides the ith block. Shifting to j turns this into X^9 divisibility. Splitting the finite sum into the own block and all erased other blocks proves X^9 divides the shifted actual-minus-candidate difference at every pole.")
check("inverse_shift_and_pairwise_coprime_full_denominator", True, "Composing with X+j inverts X-j and turns the shifted divisor into (X+j)^9. Distinct actual pole factors are pairwise coprime by the frozen Injectivity proof; Finset.prod_dvd_of_coprime therefore gives polePolynomial^9 dividing the complete actual-minus-candidate polynomial. This conclusion is valid without properness.")
check("candidate_formal_first_nine_coefficients_are_actual", True, "The candidate divides its shifted polynomial numerator by the same actual unit denominator. The X^9-divisible numerator difference remains divisible after multiplication by the actual inverse. Hence its first nine coefficients vanish, giving candidate_first_nine_coefficients and candidate_local_coefficients without properness or a PF hypothesis. Formal power-series coefficient reasoning is not numerical evaluation of an infinite series.")
check("strict_proper_degree_eliminates_residual_polynomial", True, "For j<=n, degree B_j=n, truncation degree<=8, and shift degree1, so every block and its finite sum have natDegree<=9n+8. Actual weighted numerator degree<=2n+2 natDegree W<9(n+1). The difference has degree bounded by their maximum. Degree divisibility is applied only under a temporary difference!=0 hypothesis, avoiding the zero-polynomial convention, and contradicts degree polePolynomial^9=9(n+1). The resulting actual polynomial equality has only the proper premise.")
check("actual_regular_Q_evaluation_and_each_term_division", True, "polePolynomial.eval equals the actual pole product and is nonzero from every t+k!=0 for natural k<=n. Its factorization at j is (t+j)*B_j(t). For 1<=s<=9, exponent (9-s)+s=9, so each candidate term divided by Q(t)^9 equals actual c_j,s/(t+j)^s. Both denominators are explicitly proved nonzero. Evaluating the proved polynomial identity yields exactly the actual finite weightedR double sum at rational regular points.")
check("faithful_main_closed_types_and_original_integer_quartics", True, "Independent explicit closed restatements spell out both full sums and preserve precisely the proper-degree condition and regular-point quantifier. Quartic validity is independently restated for all n, with the original Even n,n>=2,Z[X] regime checked through the coefficientwise map. No PF equality, coefficient family, reflection, or inverse-map premise is added.")
required = ["pf_ind_n_zero_X_four_proper", "pf_ind_n_zero_X_four_simple_coefficient", "pf_ind_n_zero_total_simple_coefficient", "pf_ind_n_zero_X_four_actual_simple_pole", "pf_ind_n_zero_X_four_not_two_degree_gap", "pf_ind_n_zero_X_four_actual_global_sum", "pf_ind_n_zero_X_five_not_proper", "pf_ind_n_zero_nonproper_polynomial_failure", "pf_ind_n_zero_nonproper_regular_point_failure"]
check("independent_n_zero_simple_pole_and_nonproper_counterexamples", all(name in boundary and set(boundary[name]["axioms"]) <= STANDARD for name in required), "At n=0,W=X^4, properness holds, the actual s=1 coefficient and its total are 1, actual weightedR=1/t at t!=0, and the actual global sum also equals1/t. The two-degree-gap condition fails. At n=0,W=X^5, all nine local coefficients and partialNumerator vanish, but the actual numerator is nonzero and the regular t=1 function is1 while the double sum is0. Strict properness is therefore essential.")
check("finite_global_PF_without_extra_analytic_or_aggregate_claims", True, "Finite global polynomial partial fractions and the rational regular-point identity are now closed in the exact proper domain. This does not supply rho1=0, a uniform stronger O(1/t^2) conclusion for every proper W, infinite summation/convergence/exact L, reflection or higher aggregate cancellation, denominator integrality, the five-dimensional aggregate F inverse, J, or irrationality. The n=0 quartic example specifically prevents conflating the weaker strict-proper condition with the stronger degree gap.")

write(OUT / "independent-original-types.json", original_rows)
write(OUT / "independent-boundary-types.json", boundary_rows)
md = """# 独立数学与 Lean 审核：真实有限全局部分分式

结论：PASS。冻结 PF 源 SHA256 为 `eb0b8d54cd29ddaaa9404ee26a704bb6a47e8306741c49a6bba9b7232231f61a`；CM、Jet、Injectivity 三个冻结依赖未改变。审核者不是 PF 作者，作者 20 项冻结清单全部吻合。

我在新的任务内缓存重新编译 CM、Jet、Injectivity、PF 四份原源，并重跑作者的 39 项类型审计，再编译自己写的 19 个完整陈述和边界定理。六个最终执行退出码均为 0。PF 的 5 个定义和 27 个证明全部实际导入覆盖，定义值及类型与作者冻结记录一致；最终 39+51 项类型记录与四源 39 个打印目标均只含标准三公理，无 sorryAx。

`partialNumerator` 确实使用冻结实际局部级数提取的 c^W_{j,s}，双和范围为 j=0,…,n、s=1,…,9。九项截断保留 k=0,…,8，通过 s=9−k 正确换元，幂为 9−s。自身块与实际移位分子的差被 X⁹ 整除，来自真实级数乘清极点分母的恒等式与截断余项；其他块含该极点因子的九次幂。逆移位及真实因子的互素性给 Q⁹ 整除完整候选差，未先假设全局 PF。

候选次数不超过 9n+8；实际分子次数不超过 2n+2deg W。严格 proper 界 `2n+2deg W<9(n+1)` 使两者之差的次数也小于 Q⁹ 的次数。整除次数定理只在差非零的分支使用，因此零多项式的 natDegree=0 约定没有漏洞。由此得到真正的多项式恒等式。点值恒等式进一步明确要求所有自然 k≤n 的 t+k≠0，通过 Q(t)=(t+j)B_j(t) 和 (9−s)+s=9，逐项合法地除成真实 c^W_{j,s}/(t+j)^s。

独立边界定理确认：n=0、W=X⁴ 满足 proper 条件，真实函数及真实部分分式双和都等于 1/t（t≠0），简单极点系数总和为 1，却不满足更强的两次数差界。因此不能把有限 PF 或 strict proper 性提升为 rho1=0、普遍 O(t⁻²) 或 L 收敛。删除 proper 条件也确实会使全局等式为假：n=0、W=X⁵ 的九个局部系数及候选分子全为零，但实际分子非零，在正则点 t=1 左侧为 1、右侧为 0；这体现剩余多项式部分。

本环完成实际有限全局多项式 PF 以及正则有理点上的真实函数 PF。形式局部级数没有被当作可在非零数值点求值的无限级数。反射、简单极点消去、高阶聚合消去、无限和/取极限、分母整性、五维聚合 F 的单射或逆映射、exact L、J 和 ζ(9) 无理性均未由此关闭。

源码、作者冻结记录、root、scope、平台批次均未修改，未读凭证或调用 API。首次自拟 n=0 补充审计的无类型 `k≤0` 被 Lean 推为有理量，导致编译失败；已在独立文件中明确 k:ℕ，失败源、日志与 receipt 保留，最终实际执行 0 且所有 51 项记录无 sorryAx。该审计错误不涉及作者源码。
"""
(OUT / "independent-review.md").write_text(md, encoding="utf-8")
(OUT / "independent-review.log").write_text("PASS: author freeze20/20; independent native sources4/4 exit0; author type replay39; independent audit51=32source+19additional; all final standard3.\n" + "\n".join("PASS " + c["name"] for c in checks) + "\n", encoding="utf-8")
new_paths = [v for v in OUT.rglob("*") if v.is_file() and (v.name.startswith("independent") or "independent" in v.relative_to(OUT).parts) and v.name != "independent-review.json"]
primary = [ROOT / ".lake/packages/mathlib/Mathlib" / name for name in ["RingTheory/PowerSeries/Trunc.lean", "RingTheory/PowerSeries/Basic.lean", "Algebra/Polynomial/Degree/Domain.lean", "RingTheory/Coprime/Lemmas.lean"]]
stable_paths = sorted(set(author_paths + [manifest_path] + new_paths + primary))
bindings = [{"task_relative": v.relative_to(TASK).as_posix() if v.is_relative_to(TASK) else None, "root_relative": v.relative_to(ROOT).as_posix(), "bytes": v.stat().st_size, "sha256": sha(v)} for v in stable_paths]
main_targets = [NS + ".actual_global_polynomial_partial_fractions", NS + ".actual_global_partial_fractions"]
report = {"schema_version": 1, "verdict": "PASS", "scope_verdict": "PASS_ACTUAL_FINITE_GLOBAL_PARTIAL_FRACTIONS_IN_PROPER_REGULAR_DOMAIN_ONLY", "review_role": "Independent mathematical and Lean reviewer; another agent authored PF", "checked_at": datetime.now(timezone.utc).isoformat(),
          "source": source_paths["CoefficientMapPartialFractions"].relative_to(ROOT).as_posix(), "source_sha256": EXPECTED["CoefficientMapPartialFractions"], "sources_sha256": EXPECTED,
          "environment": {"lean_toolchain": (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip(), "mathlib_rev": next(v["rev"] for v in load(ROOT / "lake-manifest.json")["packages"] if v["name"] == "mathlib")},
          "checks": checks, "source_definitions": 5, "source_theorems": 27, "proper_domain": "2*n + 2*W.natDegree < 9*(n+1)", "rational_point_domain": "t:Q and forall k:N, k<=n -> t+(k:Q)!=0",
          "main_target_types": {name: boundary[name] for name in main_targets}, "boundary_examples": {name: boundary[name] for name in required},
          "actual_type_records": {"author_replay": 39, "independent_audit": 51, "independent_additional_statements": 19},
          "findings": [{"severity": "information", "name": "Finite PF retains a possible nonzero total simple-pole coefficient", "detail": "n=0,W=X^4 has total simple-pole coefficient1 and exact actual finite PF=1/t; stronger uniform decay, rho1 cancellation and L convergence are not claimed."}, {"severity": "information", "name": "Strict properness excludes a real polynomial remainder", "detail": "n=0,W=X^5 is outside the proper domain; all actual jets and candidate vanish but actual rational value at regular t=1 is1, so removing properness is false."}],
          "retained_failed_audit_attempt": {"exit_code": 1, "source": "independent-boundary-audit.lean.before-regular-binder-fix", "log": "independent-boundary-audit.log.before-regular-binder-fix", "receipt": "independent-compile-receipt.json.before-regular-binder-fix", "reason": "Only supplemental review binder type inference; fixed by explicitly declaring k:Nat. Frozen authors' source and replay were successful already."},
          "actual_global_polynomial_PF_closed": True, "actual_global_regular_Q_PF_closed": True, "arbitrary_coefficient_or_PF_hypotheses": [],
          "rho1_zero_closed": False, "uniform_stronger_O_one_over_t_squared_closed": False, "infinite_sum_convergence_closed": False, "exact_L_closed": False,
          "reflection_cancellation_closed": False, "denominator_integrality_closed": False, "original_aggregate_F_injectivity_closed": False, "original_aggregate_F_inverse_closed": False, "J_closed": False, "irrationality_closed": False,
          "root_scope_API_credentials_writes": False, "author_freeze_sources_platform_batches_modified": False, "stable_files": bindings}
assert report["environment"] == {"lean_toolchain": "leanprover/lean4:v4.33.1", "mathlib_rev": "0df444a360eaa60ab8c11dca51a86af692955474"}
write(OUT / "independent-review.json", report)
print(json.dumps({"verdict": report["verdict"], "checks": len(checks), "stable_files": len(bindings), "independent_review_sha256": sha(OUT / "independent-review.json"), "independent_review_md_sha256": sha(OUT / "independent-review.md"), "independent_compile_receipt_sha256": sha(OUT / "independent-compile-receipt.json")}, indent=2))
