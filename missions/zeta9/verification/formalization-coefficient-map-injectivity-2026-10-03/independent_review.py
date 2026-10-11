"""Freeze a genuinely independent native/math/boundary review; author files read only."""
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
EXPECTED = {"CoefficientMap": "e055780f1abf389593fbccba2194fc52ee85108bbb4593439c32230944b3ab03", "CoefficientMapJet": "e50e11c0afd2eaac1d5c58c412e5e59bc5c2068c9826063eacee8dc88fc1735a", "CoefficientMapInjectivity": "ebe9b9c275a34fac348837e377e2e26246e9a762889c462420b43535e9055095"}
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
NS = "ZetaNine.CoefficientMapInjectivity"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def load(path): return json.loads(path.read_text(encoding="utf-8-sig"))
def rows(path): return [json.loads(s) for s in path.read_text(encoding="utf-8-sig").splitlines() if s.startswith("{")]
def write(path, value): path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
checks = []
def check(name, passed, detail):
    checks.append({"name": name, "pass": bool(passed), "detail": detail})
    assert passed, name

source_paths = {name: TASK / "formalization" / (name + ".lean") for name in EXPECTED}
check("three_frozen_source_hashes_unchanged", all(sha(source_paths[name]) == h for name,h in EXPECTED.items()), EXPECTED)
manifest_path = OUT / "SHA256SUMS.txt"
manifest_lines = [s.split("  ",1) for s in manifest_path.read_text().splitlines()]
author_paths = [TASK / name for h,name in manifest_lines]
check("author_frozen_seventeen_member_manifest_unchanged", len(manifest_lines) == 17 and all(sha(TASK / name) == h for h,name in manifest_lines) and sha(manifest_path) == "ac59c1b702eb6de6ad19c6eee812db1253ec8afb3a7b04820361b20af810a3b6" and sha(OUT / "compile-receipt.json") == "c15cc9b3e545095c944db689aca5140723603fb63119697f47d81749d1dedcfc", {"manifest_sha256": sha(manifest_path), "author_receipt_sha256": sha(OUT / "compile-receipt.json")})
receipt = load(OUT / "independent-compile-receipt.json")
for r in receipt["rows"]:
    assert r["exit_code"] == int((OUT / r["exit_file"]).read_text().strip()) == 0
    assert sha(TASK / r["source"]) == r["source_sha256"]
    for key in ["log", "wrapper", "exit_file"]: assert sha(OUT / r[key]) == r[key + "_sha256"]
    if r["output"]: assert sha(OUT / r["output"]) == r["output_sha256"]
check("independent_fresh_native_three_source_replay_and_two_type_audits", len(receipt["rows"]) == 5 and receipt["all_exit_codes_actually_observed"] and receipt["sources_unchanged"] and not receipt["root_scope_API_credentials_writes"], {"receipt": "independent-compile-receipt.json", "observed_exits": [r["exit_code"] for r in receipt["rows"]], "fresh_cache": receipt["fresh_native_cache"], "native_object_hashes": {r["label"]: r["output_sha256"] for r in receipt["rows"] if r["output"]}})
for name, count in [("CoefficientMap",8), ("CoefficientMapJet",10), ("CoefficientMapInjectivity",9)]:
    text = (OUT / ("independent-native-" + name + ".log")).read_text(encoding="utf-8-sig")
    axs = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text, re.S)
    assert len(axs) == count and all({s.strip() for s in a.split(",")} == STANDARD for _,a in axs)
original_rows = rows(OUT / "independent-author-type-replay.log")
boundary_rows = rows(OUT / "independent-boundary-audit.log")
original_map = {r["declaration"]: r for r in original_rows}
boundary_map = {r["declaration"]: r for r in boundary_rows}
author_map = {r["declaration"]: r for r in load(OUT / "type-report.json")}
assert len(original_map) == 30 and len(boundary_map) == 41
assert original_map.keys() == author_map.keys()
for name in original_map:
    assert all(original_map[name][key] == author_map[name][key] for key in ["type", "definitionValue"])
    assert set(original_map[name]["axioms"]) == set(author_map[name]["axioms"])
source = source_paths["CoefficientMapInjectivity"].read_text(encoding="utf-8")
defs = re.findall(r"(?m)^def (\w+)",source)
theorems = re.findall(r"(?m)^theorem (\w+)",source)
assert len(defs) == 7 and len(theorems) == 18
for short in defs + theorems:
    name = NS + "." + short
    assert name in original_map and name in boundary_map
    assert all(original_map[name][key] == boundary_map[name][key] for key in ["type","definitionValue"])
check("complete_native_definitions_and_closed_types_reproduced", True, {"source_defs": 7, "source_proofs": 18, "author_closed_scope_statements_replayed": 5, "independent_closed_and_boundary_statements": 16, "actual_definition_values": {NS + "." + short: boundary_map[NS + "." + short]["definitionValue"] for short in defs}, "all_source_type_and_value_outputs_equal_frozen_author_report": True})
check("only_standard_three_axioms_in_all_final_proofs_and_definitions", all(set(r["axioms"]) <= STANDARD for r in original_rows + boundary_rows) and not re.search(r"\b(sorry|admit|axiom|unsafe)\b", source), {"standard_axioms": sorted(STANDARD), "final_source_prints": 27, "actual_import_type_records": 30 + 41, "final_audit_holes": False})

# Mathematical judgments follow direct examination of the frozen source and
# actual imported Mathlib lemma statements, corroborated by the native kernel.
check("actual_weighted_numerator_and_pole_denominator", True, "baseNumerator is n!^7 times both original finite products; baseU=X*(X+C n). The independent exact quotient-evaluation theorem identifies weightedNumerator.eval/polePolynomial.eval^9 with frozen actual weightedR. No abstract numerator or coefficient input replaces these constructions.")
check("all_nine_orders_and_9_minus_s_indexing", True, "For every k<9, s=9-k lies in 1..9 and 9-(9-k)=k. Zero of all nine actual weightedLocalCoefficient values therefore gives precisely coefficients 0..8 zero of the genuine weightedClearedSeries. PowerSeries.X_pow_dvd_iff proves X^9 divisibility; multiplication by the actual denominator identity and Polynomial.coeff_coe transfer it to the shifted polynomial numerator.")
check("inverse_shift_and_actual_pole_factor_divisibility", True, "weightedNumerator.comp(X-C j) is the actual shifted weighted numerator. Composing a divisibility witness with X+C j cancels the shift and transforms X^9 into (X+C j)^9. The sign and inverse order are correct; no coefficient or factor-divisibility hypothesis is added.")
check("pairwise_coprime_all_poles_and_full_ninth_power", True, "Distinct natural a,b remain distinct in Q. The differences of roots -a,-b are nonzero units, giving coprime X+C a and X+C b and their ninth powers. Finset.prod_dvd_of_coprime across range(n+1), with j<=n obtained from membership, gives the full polePolynomial^9 dividing the actual weighted numerator.")
check("proper_degree_contradiction_handles_zero_correctly", True, "The full denominator has degree 9(n+1), and the actual weighted numerator has degree at most 2n+2 natDegree W. The proof uses natDegree_le_of_dvd only under a temporary weightedNumerator!=0 hypothesis. Thus zero natDegree conventions cannot create a false divisibility comparison; the strict bound forces numerator=0.")
check("nonzero_base_and_nondegenerate_quadratic_cancel_to_W_zero", True, "The actual base numerator is nonzero by nonzero n!^7 and nonzero linear factors, also for n=0. The actual baseU has degree 2 for every n. Polynomial.comp_eq_zero_iff leaves W=0 or a constant inner polynomial; the latter contradicts degree 2. This is genuine polynomial composition cancellation, with no assumed matrix injection.")
check("difference_proper_domain_and_actual_linearity", True, "natDegree(W-V)<=max(natDegree W,natDegree V) makes the strict domain closed under differences when both W and V are proper; independent_difference_proper independently checks this. Polynomial sub_comp, polynomial-to-series subtraction, multiplication and coeff maps prove the actual coefficient difference identity. The zero kernel then gives W=V.")
check("Fin_n_plus_one_by_Fin_nine_subtype_array_is_complete", True, "fullLocalCoefficientMap reads j.val and s.val+1, not only highest coefficients. To recover each 1<=s<=9 comparison from array equality, use Fin 9 value s-1; its bound and s-1+1=s are checked by omega. j<=n becomes j<n+1. The injective map domain is exactly the ProperMultiplier subtype, independently restated with the explicit inequality.")
check("quartic_all_n_original_integer_regime_and_zero_multiplier", True, "Degree<=4 gives 2n+8<9(n+1) for every n>=0. Independent closed checks cover quartic array injection, n=0, and original Even n / n>=2 integer quartics via the injective Z-to-Q polynomial map. An independent theorem proves the zero multiplier remains proper for all n.")
required = ["independent_n_zero_quartic_proper", "independent_n_zero_nonzero_simple_pole", "independent_n_zero_quartic_no_two_degree_gap", "independent_n_zero_actual_simple_pole", "independent_n_zero_nonproper_kernel", "independent_n_zero_nonproper_nonzero", "independent_n_zero_nonproper_bound"]
check("strict_proper_boundary_and_essential_degree_condition", all(name in boundary_map and set(boundary_map[name]["axioms"]) <= STANDARD for name in required), "Independently compiled counterexamples: n=0,W=X^4 is proper, its actual coefficient at order s=1 is 1 and weightedR(t)=1/t for t!=0; it fails the two-degree-gap condition. For n=0,W=X^5 the multiplier is nonzero and not proper but every actual local coefficient vanishes. Thus strict properness permits simple poles and is essential for full-array injection; it does not establish rho1=0 or L convergence.")
check("full_array_only_and_formal_analytic_aggregate_boundary", True, "This proves zero kernel and injection of the complete actual (n+1)*9 local coefficient array in the strict proper domain. It does not prove injection/inversion of the five aggregated zeta/constant outputs. Formal Q[[z]] coefficients are not numerical series evaluations. No global partial fractions, reflection/cancellation, denominator integrality, exact infinite L identity, prescribed output inverse, J certificate, or irrationality is supplied.")

write(OUT / "independent-original-types.json", original_rows)
write(OUT / "independent-boundary-types.json", boundary_rows)
markdown = """# 独立数学与 Lean 审核：完整实际局部系数阵列的单射

结论：PASS。审核对象为冻结的 `CoefficientMapInjectivity.lean`，SHA256 `ebe9b9c275a34fac348837e377e2e26246e9a762889c462420b43535e9055095`，以及未改变的 CM `e055…ab03` 和 Jet `e50e…1735a`。审核者不是 Injectivity 作者。

我在新的任务内缓存依次重新编译 CM、Jet、Injectivity，随后重放作者的 30 项完整类型审计，并编译自己写的 16 个完整陈述与边界定理。五个最终执行退出码均为 0；所有 7 个定义和 18 个源证明被实际导入覆盖，定义值及类型与作者冻结记录相同，最终全部公理仅为 `propext`、`Classical.choice`、`Quot.sound`。作者 17 项冻结清单逐项无变化。

数学链成立。对 k=0,…,8 取 s=9-k，原 `9-s` 系数索引恰好回到 k；全部实际局部系数为零给实际加权级数 X⁹ 整除。乘以真实清极点分母恒等式后得到移位多项式分子整除，复合 X+j 正确抵消原 X-j，给每个 (X+j)⁹ 因子。不同 j 的九次幂互素，乘积覆盖所有 0≤j≤n。分母次数为 9(n+1)，分子次数不超过 2n+2deg W。整除次数界只在分子非零的分支应用，严格 proper 条件迫使分子为零；非零实际基础分子和次数恰为 2 的实际内层复合随后给 W=0。

对 W−V 的次数使用 max 界，两个 proper 假设保证差仍 proper；实际系数线性性给零核。Fin(n+1)×Fin9 数组保存全部 j 和全部 s=1,…,9，通过 s−1 恢复原顺序，没有遗漏简单极点或端点。四次域对所有 n，包括 n=0，都满足严格界；原偶数 n≥2 的整数四次语境也已独立检查。

必须保留次数边界：`ProperMultiplier` 只保证严格真分式的次数界，允许 O(1/t) 级别。独立 Lean 定理确认 n=0、W=X⁴ 时实际 weightedR(t)=1/t（t≠0）、s=1 系数为 1，并不满足更强的两次数差界。因此不能由本结果声称简单极点和为零、rho1=0 或 L 收敛。删除 proper 条件也会使单射为假：n=0、W=X⁵ 非零却使全部九个实际局部系数为零；该乘子明确不在 proper 域。

这是完整局部数组的单射，不是五维聚合输出 F 的单射、满射或逆映射。聚合仍可能丢失信息。全局部分分式、反射/消去、分母整性、形式级数的解析收敛、exact L、指定整数输出的逆像、J 与 ζ(9) 无理性仍未由此完成。

未修改源码、作者冻结记录、两个已冻结平台批次、root、scope，未读取凭证或调用 API。首次补充边界审计存在我自己的 tactic 归一化失败（自动生成的错误环境中出现 sorryAx）；失败日志与 receipt 已保留，未当作证明。修正仅发生在独立审计文件，最终实际执行 0 且所有 41 项记录均无 sorryAx。
"""
(OUT / "independent-review.md").write_text(markdown, encoding="utf-8")
(OUT / "independent-review.log").write_text("PASS: frozen author manifest 17/17; independent native sources 3/3 exit0; actual type audit 30 records; independent boundary audit 41 records =25 source +16 extra; all final axioms standard3 only.\n" + "\n".join("PASS " + c["name"] for c in checks) + "\n", encoding="utf-8")
independent_paths = [v for v in OUT.rglob("*") if v.is_file() and (v.name.startswith("independent") or "independent" in v.relative_to(OUT).parts) and v.name != "independent-review.json"]
primary_lemma_paths = [ROOT / ".lake/packages/mathlib/Mathlib" / name for name in ["Algebra/Polynomial/Degree/Lemmas.lean", "Algebra/Polynomial/Degree/Domain.lean", "Algebra/Polynomial/RingDivision.lean", "RingTheory/Coprime/Lemmas.lean", "RingTheory/PowerSeries/Basic.lean"]]
stable_paths = sorted(set(author_paths + [manifest_path] + independent_paths + primary_lemma_paths))
bindings = [{"task_relative": v.relative_to(TASK).as_posix() if v.is_relative_to(TASK) else None, "root_relative": v.relative_to(ROOT).as_posix(), "bytes": v.stat().st_size, "sha256": sha(v)} for v in stable_paths]
report = {"schema_version": 1, "verdict": "PASS", "scope_verdict": "PASS_ACTUAL_PROPER_COMPLETE_LOCAL_COEFFICIENT_ARRAY_INJECTIVITY_ONLY", "review_role": "Independent mathematical and Lean reviewer; another agent authored Injectivity", "checked_at": datetime.now(timezone.utc).isoformat(),
          "source": source_paths["CoefficientMapInjectivity"].relative_to(ROOT).as_posix(), "source_sha256": EXPECTED["CoefficientMapInjectivity"], "sources_sha256": EXPECTED,
          "environment": {"lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(), "mathlib_rev": next(v["rev"] for v in load(ROOT / "lake-manifest.json")["packages"] if v["name"] == "mathlib")},
          "checks": checks, "proper_domain": "2*n + 2*W.natDegree < 9*(n+1)", "source_definitions": 7, "source_theorems": 18,
          "actual_type_records": {"author_audit_replayed": 30, "independent_audit": 41, "independent_additional_closed_boundary_statements": 16},
          "boundary_examples": {name: boundary_map[name] for name in required},
          "findings": [{"severity": "information", "name": "Strict properness allows a nonzero simple pole", "detail": "The independently proved n=0,W=X^4 example has s=1 coefficient1 and actual function1/t. Stronger O(1/t^2), rho1 cancellation and infinite L convergence are not claimed."}, {"severity": "information", "name": "Proper domain is essential", "detail": "The independently proved n=0,W=X^5 example is nonzero with all local jets zero, and lies outside ProperMultiplier."}, {"severity": "information", "name": "Complete array does not establish aggregate map injection", "detail": "No five-dimensional aggregate F implication is supplied; that remains open."}],
          "retained_failed_audit_attempt": {"exit_code": 1, "log": "independent-boundary-audit.log.before-boundary-fix", "receipt": "independent-compile-receipt.json.before-boundary-fix", "scope": "Only independent supplemental audit tactic normalization; frozen sources compiled0 already; final supplemental proof audit0 has no sorryAx."},
          "full_local_array_injectivity_closed": True, "original_aggregated_F_injectivity_closed": False, "original_aggregated_F_inverse_closed": False,
          "global_partial_fractions_closed": False, "stronger_uniform_O_one_over_t_squared_closed": False, "rho1_zero_closed": False,
          "numerical_series_convergence_closed": False, "exact_L_closed": False, "J_closed": False, "irrationality_closed": False,
          "root_scope_API_credentials_writes": False, "author_freeze_and_platform_batches_modified": False, "stable_files": bindings}
assert report["environment"] == {"lean_toolchain": "leanprover/lean4:v4.33.1", "mathlib_rev": "0df444a360eaa60ab8c11dca51a86af692955474"}
write(OUT / "independent-review.json", report)
print(json.dumps({"verdict": report["verdict"], "checks": len(checks), "stable_files": len(bindings), "independent_review_sha256": sha(OUT / "independent-review.json"), "independent_review_md_sha256": sha(OUT / "independent-review.md"), "independent_compile_receipt_sha256": sha(OUT / "independent-compile-receipt.json")}, indent=2))
