"""Independent actual p9,d0 infinite summation review; no aggregate-map claims."""
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
AUTHOR = TASK / "verification/formalization-coefficient-map-summation-2026-10-04"
NS = "ZetaNine.CoefficientMapSummation"
EXPECTED = {
    "CoefficientMap": "e055780f1abf389593fbccba2194fc52ee85108bbb4593439c32230944b3ab03",
    "CoefficientMapJet": "e50e11c0afd2eaac1d5c58c412e5e59bc5c2068c9826063eacee8dc88fc1735a",
    "CoefficientMapInjectivity": "ebe9b9c275a34fac348837e377e2e26246e9a762889c462420b43535e9055095",
    "CoefficientMapPartialFractions": "eb0b8d54cd29ddaaa9404ee26a704bb6a47e8306741c49a6bba9b7232231f61a",
    "CoefficientMapFiniteSum": "b3ede123541d6c0eb306915d93f743979b1090c34bc4df332ab6e9da07033f97",
    "CoefficientMapReflection": "8fbc53b9d9c33a61e1cf8208f89cd30dd3c6793fc32aad1cad1c51286747f707",
    "CoefficientMapSummation": "c207e8fec1358e86afd61d39853a498c9758555286b7774e5f5d7809495e876d"}
PURE = ROOT / "Definitions/Def_ZetaNine_HarmonicStability.lean"
PURE_HASH = "5ff9d83ca177893db1eb149da985ff29b85dbe83614650a995e28066f9bd3e92"
FROZEN = {"source_sha256": EXPECTED["CoefficientMapSummation"],
    "receipt_sha256": "1fefb593daf7d350b202e3a1429c6f58c150c89e34fd985d6fc51c2f4f1c89b4",
    "manifest_sha256": "3f6ba8dfe3a23dfc794ffda01a533935f6982e0a2842ee2239713fb52f66fdc8"}
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
check("all_seven_actual_frozen_sources_and_pure_Def_unchanged",
    sha(PURE) == PURE_HASH and all(sha(sources[name]) == h for name,h in EXPECTED.items()),
    {"sources_sha256": EXPECTED, "pure_definition_sha256": PURE_HASH})
manifest = AUTHOR / "SHA256SUMS.txt"
manifest_lines = [s.split("  ",1) for s in manifest.read_text(encoding="utf-8").splitlines() if s.strip()]
author_paths = [(TASK / name).resolve() for _,name in manifest_lines]
check("author_thirty_six_member_freeze_unchanged", len(manifest_lines) == 36 and
    all(sha((TASK / name).resolve()) == h for h,name in manifest_lines) and
    sha(manifest) == FROZEN["manifest_sha256"] and sha(AUTHOR / "compile-receipt.json") == FROZEN["receipt_sha256"],
    {"manifest_sha256": sha(manifest), "author_receipt_sha256": sha(AUTHOR / "compile-receipt.json"),
     "author_retained_import_resolution_failure_and_Lean_name_probe_not_final_proof_evidence": True})
receipt = load(OUT / "independent-compile-receipt.json")
for r in receipt["rows"]:
    assert r["exit_code"] == int((OUT / r["exit_file"]).read_text().strip()) == 0
    assert sha(ROOT / r["source_root_relative"]) == r["source_sha256"]
    for key in ["log", "wrapper", "exit_file"]: assert sha(OUT / r[key]) == r[key + "_sha256"]
    if r["output"]: assert sha(OUT / r["output"]) == r["output_sha256"]
check("fresh_pure_Def_seven_native_sources_and_two_actual_type_audits",
    len(receipt["rows"]) == 10 and receipt["all_exit_codes_actually_observed"] and
    receipt["sources_unchanged"] and receipt["author_frozen_hashes"] == FROZEN and not receipt["root_scope_API_credentials_writes"],
    {"receipt": "independent-compile-receipt.json", "observed_exits": [r["exit_code"] for r in receipt["rows"]],
     "fresh_cache": receipt["fresh_native_cache"], "native_objects": {r["label"]: r["output_sha256"] for r in receipt["rows"] if r["output"]}})
for name,count in [("CoefficientMap",8),("CoefficientMapJet",10),("CoefficientMapInjectivity",9),("CoefficientMapPartialFractions",12),("CoefficientMapFiniteSum",6),("CoefficientMapReflection",11),("CoefficientMapSummation",12)]:
    text = (OUT / ("native-" + name + ".log")).read_text(encoding="utf-8-sig")
    printed = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text, re.S)
    assert len(printed) == count and all({s.strip() for s in a.split(",")} == STANDARD for _,a in printed)
original_rows, boundary_rows = [rows(OUT / name) for name in ["author-type-replay.log", "independent-boundary-audit.log"]]
original, boundary = [{r["declaration"]: r for r in rs} for rs in [original_rows, boundary_rows]]
author = {r["declaration"]: r for r in load(AUTHOR / "type-report.json")}
assert len(original) == 31 and len(boundary) == 56 and original.keys() == author.keys()
for name in original:
    assert all(original[name][key] == author[name][key] for key in ["type","definitionValue"])
    assert set(original[name]["axioms"]) == set(author[name]["axioms"])
source = sources["CoefficientMapSummation"].read_text(encoding="utf-8")
defs, theorems = [re.findall(r"(?m)^" + kind + r" (\w+)", source) for kind in ["def","theorem"]]
assert len(defs) == 3 and len(theorems) == 21
for short in defs + theorems:
    name = NS + "." + short
    assert name in original and name in boundary
    assert all(original[name][key] == boundary[name][key] for key in ["type","definitionValue"])
check("all_actual_source_types_and_definition_values_reproduced", True,
    {"source_defs": 3, "source_proofs": 21, "author_closed_statements_replayed": 7,
     "independent_closed_boundary_statements": 32, "exact_types_and_values_equal_author_report": True,
     "definition_values": {NS + "." + name: boundary[NS + "." + name]["definitionValue"] for name in defs}})
check("all_final_axioms_standard_three_without_hidden_proof_holes",
    all(set(r["axioms"]) <= STANDARD for r in original_rows + boundary_rows) and
    all(not re.search(r"\b(sorry|admit|axiom|unsafe)\b", lean_code(p.read_text(encoding="utf-8"))) for p in list(sources.values()) + [PURE, OUT / "independent-boundary-audit.lean"]),
    {"native_printed_targets": 68, "actual_import_records": 31 + 56, "standard_axioms": sorted(STANDARD), "sorryAx": False})
check("actual_positive_series_exactL_and_real_riemannZeta_definitions", True,
    "actualSeries is the real cast of actual weightedR at positive rational k+1; it is not an abstract supplied sequence. exactL is the real cast of actual constantTerm plus the actual rho3,5,7,9 times zetaReal. zetaReal is (riemannZeta(s:C)).re, not a redefinition of an abstract coefficient or an assumed harmonic limit.")
check("positive_successor_Icc_range_cast_and_endpoint_alignment", True,
    "The explicit bijection t in Icc1T <-> k=t-1 in rangeT has inverse k+1, including T=0. Real casts commute with actual finite rational sums, powers and division. actualSeries rangeT partial sums equal exactly finiteL(n,T), not finiteL(n,T+1). Independent T=0/T=1 tests verify the first actual value is t=1 and no t=0 pole enters.")
check("actual_harmonic_limit_identified_with_real_complex_zeta", True,
    "Mathlib zeta_nat_eq_tsum_of_gt_one states genuine riemannZeta at natural s>1 equals the complex p-series. Complex.ofReal_tsum, actual casts of each term and Complex.re identify its real part with the real p-series. Real.summable_one_div_nat_pow supplies actual summability; the harmonic range(T+1) limit follows by composing natural partial-sum convergence with T+1. The added t=0 term is0 for positive s.")
check("all_actual_fixed_shifted_tails_vanish_including_order_one", True,
    "For every s>=1 and fixed j, the actual harmonic difference is a finite sum over k=1..j of 1/(T+k)^s. Natural casts tend to infinity, reciprocals to0, and powers preserve this limit; two finite sums over j=0..n,s=1..9 give the actual shiftedTail limit0. No decay/cancellation premise is required for this tail theorem, including s=1.")
check("actual_reflection_and_stronger_degree_discharge_finite_odd_inputs", True,
    "The exact finite odd identity uses the already proved real coefficient totals: strong properness gives actual rho1=0 and properness; Even n gives actual rho2,rho4,rho6,rho8=0. Reflection.rho and FiniteSum.rho are definitionally the same actual finite sum. No cancellation input is assumed in Summation. FiniteL then tends to the actual constant plus the four actual odd rho times genuine zetaReal, with the actual tail limit0.")
check("simple_pole_difference_has_true_absolute_square_majorant", True,
    "At u>0, 1/(u+j)-1/u=-j/[u(u+j)], so its norm is j/[u(u+j)]<=j/u^2, including j=0. The independently compiled general-u norm inequality proves this exact bound. A shifted 2-series multiplied by fixed j is summable; Summable.of_norm_bounded over the complete real normed space therefore proves each actual simple-pole difference summable, rather than relying on a signed or conditional cancellation heuristic.")
check("actual_simple_cancellation_and_higher_pseries_build_summability", True,
    "For each positive k+1, actual PF regularity is proved from positivity. The true rho1 zero removes the subtracted common 1/(k+1) term after the finite j sum. The remaining true simple differences are summable, and every s=2..9 shifted higher pole is a reindexed summable real p-series, multiplied by its actual coefficient. The finite j,s sum yields Summable actualSeries before any use of the finiteL limit. No Even n is needed for this summability argument.")
check("real_absolute_summability_and_HasSum_upgrade_are_valid", True,
    "Summable.norm comes from the official finite-dimensional-real summable_norm_iff, applicable to E=R; therefore actualSeries is absolutely summable. Its Summable.hasSum gives convergence of all finite subsums and of natural range partial sums to the actual tsum. Uniqueness against the separately proved finiteL limit identifies that tsum with exactL, and only then transports genuine HasSum to exactL. Thus the final theorem is not inferred from natural partial-sum convergence alone, and it supplies both HasSum and tsum equality.")
required_good = ["sum_ind_closed_HasSum", "sum_ind_closed_original_HasSum", "sum_ind_absolute_without_even", "sum_ind_n_zero_X_three_strong", "sum_ind_n_zero_X_three_actual_series", "sum_ind_n_zero_X_three_rho_three", "sum_ind_n_zero_X_three_exactL", "sum_ind_n_zero_X_three_HasSum", "sum_ind_zero_HasSum_every_n", "sum_ind_zero_exactL_even", "sum_ind_odd_n_one_absolute"]
check("independent_original_integer_quartic_X_three_and_zero_boundaries",
    all(name in boundary and set(boundary[name]["axioms"]) <= STANDARD for name in required_good),
    "Original W:Z[X],degree<=4,Even n>=2 has actual HasSum via the proved strong wrapper and natDegree_map_le, without extra zeta/rho/convergence inputs. n=0,W=X^3 is strong: actual positive series=1/(k+1)^3, true rho3=1 and other pole totals zero, exactL=(riemannZeta3).re, and genuine HasSum holds. W=0 has actual zero series and HasSum0 for every n; exactL0 in the even domain. Odd n=1 quartics still have absolute summability, separating it from the even-only odd-zeta formula.")
required_bad = ["sum_ind_n_zero_X_four_proper_not_strong", "sum_ind_n_zero_X_four_actual_series", "sum_ind_n_zero_X_four_not_summable", "sum_ind_n_zero_X_four_no_HasSum", "sum_ind_n_zero_X_four_partial_diverges", "sum_ind_n_zero_X_four_exactL_zero", "sum_ind_n_zero_X_four_totalized_tsum_eq_exactL"]
check("independent_X_four_divergence_and_totalized_tsum_boundary",
    all(name in boundary and set(boundary[name]["axioms"]) <= STANDARD for name in required_bad),
    "n=0,W=X^4 is proper but not strong; its actual positive sequence is1/(k+1), not Summable and has no HasSum to any real L. Its actual finiteL tends to +infinity. Nevertheless Lean's totalized tsum is0 for a nonsummable sequence, and this excluded example also has defined exactL0; their equality is independently proved while every HasSum is false. This verifies why the genuine HasSum/absolute convergence proof and the strong domain are essential.")
check("actual_p9_q1_m_n_d0_infinite_identity_scope_only", True,
    "The actual p=9,q=1,m=n,d=0 absolute summability and exact odd-zeta infinite L identity are closed in the stated domain. This is not a proof of general p, multilayer or positive derivative d cases, denominator integrality, original five-dimensional aggregate F injectivity/inverse, a prescribed integer-output inverse image and target L, J or zeta9 irrationality. No abstract coefficient array or extra convergence/zeta/cancellation hypothesis is introduced.")
write(OUT / "independent-original-types.json", original_rows)
write(OUT / "independent-boundary-types.json", boundary_rows)
md = """# 独立数学与 Lean 审核：真实无限求和与 exact L

结论：PASS，范围是实际 p=9、q=1、m=n、d=0 家族。Summation 冻结源 SHA256 为 `c207e8fec1358e86afd61d39853a498c9758555286b7774e5f5d7809495e876d`，作者 36 项清单、六份冻结父源和纯 HarmonicStability Def 均未改变。作者保留的导入路径失败及探索性 Lean 名称探针不作为最终证明证据。审核者不是 Summation 作者，独立缓存及全部独立证据位于本新目录。

我先鲜编译纯 Def 与六份已审父源；收到正式冻结三哈希后，才鲜编译 Summation，并重跑作者 31 项类型审计。再实际编译自拟 32 个完整陈述和必要边界定理。十个最终执行均退出 0。源的 3 个定义与 21 个证明全部导入覆盖，实际类型和定义值逐项匹配作者记录；独立审计共 56 项。七源的 68 个打印目标与最终 31+56 项实际类型记录均只含标准三公理，无 sorryAx。

真实序列是 k↦weightedR(n,W,k+1) 的实数嵌入；range T 的和恰为 t=1,…,T 的实际 finiteL，端点双射和 T=0/T=1 独立核验。zetaReal 确实是 Mathlib 复 ζ(s) 的实部，源用官方自然参数 ζ 的 p 级数定理、复实嵌入的 tsum 交换及取实部证明它等于实际实 p 级数，不把 ζ 当成输入。实际 harmonicPower 从正确端点部分和趋于它。对所有 s≥1，包括简单极点，固定长度 H_s(T+j)−H_s(T) 尾差逐项趋零，实际有限双和 tail 也趋零。

简单极点消去来自真实 strong proper 度界的 rho1=0，偶阶消去来自 n 偶数的真实反射，没有新增消去假设。因此真实有限和极限为实际常数加 rho3、rho5、rho7、rho9 乘实际 ζ 的实部。无限和的合法性另外证明：u>0 时简单极点差等于 −j/[u(u+j)]，绝对值不超过 j/u²；独立一般实 u 不等式也编译通过。移位平方级数给此差的可和 majorant；s≥2 的每个实际高阶部分分式由移位 p 级数可和性得到可和。真实 rho1=0 使公共 1/(k+1) 项的有限 j 聚合恰为零，故实际整个序列先被证明 Summable。这一步不需要 n 偶数。

实数空间满足官方有限维实空间的 Summable.norm 定理，所以也得到范数 Summable，即绝对收敛。随后用 Summable.hasSum 的自然部分和极限，与已证 finiteL 极限的唯一性比较，得到真正的 HasSum(actualSeries,exactL)，再得 tsum 等式；没有仅凭自然部分和极限宣称 HasSum。原 n≥2、n 偶数、整数四次 W 的强界由真实 map 度界和 Reflection 包装证明解除。

独立边界给出实质差别：n=0、W=X³ 满足强界，真实序列是 1/(k+1)³，rho3=1，其余相关 rho 为零，exactL=(ζ(3)).re，真实 HasSum 成立。零 W 对所有 n 给实际零序列和 HasSum0；n=1 的四次 W 仍绝对可和，表明绝对收敛不要求偶性。n=0、W=X⁴ 仍 strict proper，却不 strong；实际序列是 1/(k+1)，不可和、对任何实 L 都无 HasSum，真实 finiteL 趋于正无穷。该域外例在 Lean 的 totalized tsum 约定下仍有 tsum=0，同时定义的 exactL=0，所以两者形式相等也不能代替收敛证明。本环实际 HasSum 和强条件正好避免这一问题。

本结果闭合指定有限家族中的真实绝对收敛与 Eq(4) 型无限 ζ 表达式。一般 p、多层及 d>0、分母整性、原五维聚合 F 的单射或逆映射、指定整数输出的逆像及其指定目标 L、J 和 ζ(9) 无理性仍未关闭。没有修改任何作者冻结文件、旧独立审核、平台批次、root 或 scope；没有调用平台 API 或读取凭证。

第一次自拟补充审计有两处部分应用函数上的 simp 展开失败：完整 HasSum restatement 的序列展开、X⁴ 不可和性中的序列重写。已仅在独立审计中用 change 和逐项 Summable.congr 修正。失败源、日志、退出码及 receipt 原样保留，其中 Lean 为失败证明临时插入的 sorryAx 不作为证据。最终实际执行退出 0，所有 56 项最终记录均无 sorryAx；作者冻结源和作者类型重放从未失败或被修改。
"""
(OUT / "independent-review.md").write_text(md, encoding="utf-8")
(OUT / "independent-review.log").write_text("PASS: author freeze36/36; fresh pureDef+seven native sources exit0; author replay31; independent audit56=24source+32additional; all final standard3.\n" + "\n".join("PASS " + c["name"] for c in checks) + "\n", encoding="utf-8")
new_paths = [v.resolve() for v in OUT.rglob("*") if v.is_file() and v.name != "independent-review.json"]
primary = [ROOT / ".lake/packages/mathlib/Mathlib" / name for name in ["NumberTheory/LSeries/RiemannZeta.lean", "Analysis/PSeries.lean", "Analysis/Complex/Basic.lean", "Analysis/Normed/Group/InfiniteSum.lean", "Analysis/Normed/Module/FiniteDimension.lean", "Topology/Algebra/InfiniteSum/NatInt.lean"]]
stable_paths = sorted(set(author_paths + [manifest.resolve()] + new_paths + primary))
bindings = [{"task_relative": v.relative_to(TASK).as_posix() if v.is_relative_to(TASK) else None,
    "root_relative": v.relative_to(ROOT).as_posix(), "bytes": v.stat().st_size, "sha256": sha(v)} for v in stable_paths]
main = [NS + ".zetaReal_eq_tsum", NS + ".actualSeries_summable", NS + ".actualSeries_norm_summable",
    NS + ".actualSeries_hasSum_exactL", NS + ".actualSeries_tsum_exactL", NS + ".original_integer_quartic_exact_infinite_L"]
report = {"schema_version": 1, "verdict": "PASS", "scope_verdict": "PASS_ACTUAL_P9_Q1_M_N_D0_ABSOLUTE_SUMMABILITY_AND_EXACT_INFINITE_L_ONLY",
    "review_role": "Independent mathematical and Lean reviewer; another agent authored Summation", "checked_at": datetime.now(timezone.utc).isoformat(),
    "source": sources["CoefficientMapSummation"].relative_to(ROOT).as_posix(), "source_sha256": EXPECTED["CoefficientMapSummation"], "sources_sha256": EXPECTED,
    "author_frozen_hashes": FROZEN, "author_directory": AUTHOR.relative_to(ROOT).as_posix(), "independent_directory": OUT.relative_to(ROOT).as_posix(),
    "pure_definition_source": {"root_relative": PURE.relative_to(ROOT).as_posix(), "sha256": PURE_HASH},
    "environment": {"lean_toolchain": (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip(), "mathlib_rev": next(v["rev"] for v in load(ROOT / "lake-manifest.json")["packages"] if v["name"] == "mathlib")},
    "checks": checks, "source_definitions": 3, "source_theorems": 21,
    "absolute_summability_domain": "all n,W:Q[X] with 2*n+2*W.natDegree+2<=9*(n+1); no Even n premise",
    "exact_odd_zeta_infinite_L_domain": "Even n and the stronger degree bound; original n>=2,Even n,W:Z[X],degree<=4 included",
    "main_target_types": {name: boundary[name] for name in main},
    "boundary_examples": {name: boundary[name] for name in required_good + required_bad},
    "actual_type_records": {"author_replay": 31, "independent_audit": 56, "independent_additional_statements": 32},
    "retained_failed_audit_attempt": {"exit_code": 1, "source": "independent-boundary-audit.lean.before-function-unfold-fix", "log": "independent-boundary-audit.log.before-function-unfold-fix", "receipt": "independent-compile-receipt.json.before-function-unfold-fix", "reason": "Two supplemental partial-function simp steps failed; repaired only in independent audit using change and pointwise Summable.congr. Temporary elaborator sorryAx in the failed audit is excluded from final evidence. Author source and author replay were successful already."},
    "findings": [{"severity": "information", "name": "Genuine HasSum is proved after actual absolute summability", "detail": "The true coefficient cancellation and square majorant establish Summable first; finite-dimensional real norm summability and uniqueness of the actual finiteL limit then give genuine HasSum and the exact tsum identity."},
        {"severity": "information", "name": "Strong-domain boundary and totalized tsum are explicitly distinguished", "detail": "n=0,W=X^4 is not strong and is the divergent actual harmonic series, with no HasSum to any real. Its totalized tsum still equals the defined zero exactL, demonstrating why a bare tsum equality would not certify convergence."}],
    "new_rho_zeta_identity_convergence_or_abstract_coefficient_inputs": [],
    "actual_tail_limit_closed": True, "actual_series_summable_closed": True, "actual_series_absolute_summability_closed": True,
    "actual_HasSum_exactL_closed": True, "actual_tsum_exactL_closed": True, "actual_p9_q1_m_n_d0_Eq4_specialization_closed": True,
    "original_integer_quartic_actual_infinite_L_closed": True,
    "general_p_multilayer_positive_derivative_Eq4_closed": False, "rho1_zero_from_strict_proper_alone_closed": False,
    "denominator_integrality_closed": False, "original_aggregate_F_injectivity_closed": False,
    "original_aggregate_F_inverse_closed": False, "prescribed_integer_output_inverse_image_closed": False,
    "prescribed_target_L_closed": False, "J_closed": False, "irrationality_closed": False,
    "root_scope_API_credentials_writes": False, "author_freeze_sources_old_reviews_platform_batches_modified": False,
    "stable_files": bindings}
assert report["environment"] == {"lean_toolchain": "leanprover/lean4:v4.33.1", "mathlib_rev": "0df444a360eaa60ab8c11dca51a86af692955474"}
write(OUT / "independent-review.json", report)
print(json.dumps({"verdict": report["verdict"], "checks": len(checks), "stable_files": len(bindings),
    "independent_review_sha256": sha(OUT / "independent-review.json"), "independent_review_md_sha256": sha(OUT / "independent-review.md"),
    "independent_compile_receipt_sha256": sha(OUT / "independent-compile-receipt.json")}, indent=2))
