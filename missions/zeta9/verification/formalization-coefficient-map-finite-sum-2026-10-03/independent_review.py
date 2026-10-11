"""Independent finite-sum mathematical, native, type/value and freeze review."""
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
NS = "ZetaNine.CoefficientMapFiniteSum"
EXPECTED = {
    "CoefficientMap": "e055780f1abf389593fbccba2194fc52ee85108bbb4593439c32230944b3ab03",
    "CoefficientMapJet": "e50e11c0afd2eaac1d5c58c412e5e59bc5c2068c9826063eacee8dc88fc1735a",
    "CoefficientMapInjectivity": "ebe9b9c275a34fac348837e377e2e26246e9a762889c462420b43535e9055095",
    "CoefficientMapPartialFractions": "eb0b8d54cd29ddaaa9404ee26a704bb6a47e8306741c49a6bba9b7232231f61a",
    "CoefficientMapFiniteSum": "b3ede123541d6c0eb306915d93f743979b1090c34bc4df332ab6e9da07033f97"}
PURE = ROOT / "Definitions/Def_ZetaNine_HarmonicStability.lean"
PURE_HASH = "5ff9d83ca177893db1eb149da985ff29b85dbe83614650a995e28066f9bd3e92"
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
check("all_five_actual_frozen_sources_and_pure_definition_unchanged",
    sha(PURE) == PURE_HASH and all(sha(sources[name]) == h for name,h in EXPECTED.items()),
    {"sources_sha256": EXPECTED, "pure_harmonic_definition_sha256": PURE_HASH})
manifest = OUT / "SHA256SUMS.txt"
manifest_lines = [s.split("  ",1) for s in manifest.read_text(encoding="utf-8").splitlines() if s.strip()]
author_paths = [TASK / name for _,name in manifest_lines]
check("author_fifteen_member_freeze_unchanged", len(manifest_lines) == 15 and
    all(sha(TASK / name) == h for h,name in manifest_lines) and
    sha(manifest) == "20bb9571ba031b2cb75dafb100c3c2f0704e5c3d05f1997324293872a5576948" and
    sha(OUT / "compile-receipt.json") == "ed4208781a35fc1b7b81abbe1dd762c64d96e4bb704a6e287743dea4e956212f",
    {"author_manifest_sha256": sha(manifest), "author_receipt_sha256": sha(OUT / "compile-receipt.json")})
receipt = load(OUT / "independent-compile-receipt.json")
for r in receipt["rows"]:
    assert r["exit_code"] == int((OUT / r["exit_file"]).read_text().strip()) == 0
    assert sha(ROOT / r["source_root_relative"]) == r["source_sha256"]
    for key in ["log", "wrapper", "exit_file"]: assert sha(OUT / r[key]) == r[key + "_sha256"]
    if r["output"]: assert sha(OUT / r["output"]) == r["output_sha256"]
check("fresh_five_native_sources_plus_pure_definition_and_two_audits",
    len(receipt["rows"]) == 8 and receipt["all_exit_codes_actually_observed"] and
    receipt["sources_unchanged"] and not receipt["root_scope_API_credentials_writes"],
    {"receipt": "independent-compile-receipt.json", "observed_exits": [r["exit_code"] for r in receipt["rows"]],
     "fresh_cache": receipt["fresh_native_cache"], "native_objects": {r["label"]: r["output_sha256"] for r in receipt["rows"] if r["output"]}})
for name,count in [("CoefficientMap",8),("CoefficientMapJet",10),("CoefficientMapInjectivity",9),("CoefficientMapPartialFractions",12),("CoefficientMapFiniteSum",6)]:
    text = (OUT / ("independent-native-" + name + ".log")).read_text(encoding="utf-8-sig")
    printed = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text, re.S)
    assert len(printed) == count and all({s.strip() for s in a.split(",")} == STANDARD for _,a in printed)
original_rows, boundary_rows = [rows(OUT / name) for name in ["independent-author-type-replay.log", "independent-boundary-audit.log"]]
original, boundary = [{r["declaration"]: r for r in rs} for rs in [original_rows, boundary_rows]]
author = {r["declaration"]: r for r in load(OUT / "type-report.json")}
assert len(original) == 17 and len(boundary) == 40 and original.keys() == author.keys()
for name in original:
    assert all(original[name][key] == author[name][key] for key in ["type","definitionValue"])
    assert set(original[name]["axioms"]) == set(author[name]["axioms"])
source = sources["CoefficientMapFiniteSum"].read_text(encoding="utf-8")
defs, theorems = [re.findall(r"(?m)^" + kind + r" (\w+)", source) for kind in ["def","theorem"]]
assert len(defs) == 4 and len(theorems) == 7
for short in defs + theorems:
    name = NS + "." + short
    assert name in original and name in boundary
    assert all(original[name][key] == boundary[name][key] for key in ["type","definitionValue"])
check("all_source_types_and_actual_definition_values_reproduced", True,
    {"source_defs": 4, "source_proofs": 7, "author_closed_statements_replayed": 6,
     "independent_closed_boundary_statements": 27, "independent_pure_definition_records": 2,
     "exact_types_and_values_equal_author_report": True,
     "definition_values": {NS + "." + name: boundary[NS + "." + name]["definitionValue"] for name in defs}})
pure_code = lean_code(PURE.read_text(encoding="utf-8"))
old_light = TASK / "formalization/HarmonicStabilityDefinitions.lean"
old_proof = TASK / "formalization/HarmonicStability.lean"
def harmonic_block(path):
    txt = path.read_text(encoding="utf-8")
    m = re.search(r"def harmonicPower \(s N : ℕ\) : ℚ :=\s*∑ j ∈ Finset\.Icc 1 N, 1 / \(j : ℚ\) \^ s", txt)
    assert m
    return re.sub(r"\s+", " ", m.group())
check("pure_harmonic_definition_is_original_actual_finite_sum", 
    harmonic_block(PURE) == harmonic_block(old_light) == harmonic_block(old_proof) and
    len(re.findall(r"\bdef\s+", pure_code)) == 2 and not re.search(r"\b(theorem|lemma|axiom|sorry|admit)\b", pure_code) and
    boundary["ZetaNine.HarmonicStability.harmonicPower"]["definitionValue"] is not None,
    {"actual_definition": "harmonicPower(s,N)=sum j in Icc1N,1/(j:Q)^s", "same_body_as_original_HarmonicStability": True,
     "pure_module_definitions": ["logDen", "harmonicPower"], "old_harmonic_proofs_imported": False,
     "harmonicPower_actual_value": boundary["ZetaNine.HarmonicStability.harmonicPower"]["definitionValue"]})
check("all_final_axioms_standard_three_without_hidden_proof_holes", 
    all(set(r["axioms"]) <= STANDARD for r in original_rows + boundary_rows) and
    all(not re.search(r"\b(sorry|admit|axiom|unsafe)\b",lean_code(p.read_text(encoding="utf-8"))) for p in list(sources.values()) + [PURE, OUT / "independent-boundary-audit.lean"]),
    {"native_printed_targets": 45, "actual_import_records": 17 + 40, "standard_axioms": sorted(STANDARD), "sorryAx": False})
check("actual_finite_F_and_actual_coefficient_aggregation", True,
    "finiteL is exactly the finite actual weightedR sum at natural t=1..T. rho is the finite j=0..n sum of genuine Jet weightedLocalCoefficient; neither an arbitrary coefficient array nor an aggregate F inverse is supplied. constantTerm is minus the actual coefficient-weighted H_s(j) double sum, and shiftedTail is the actual coefficient-weighted H_s(T+j)-H_s(T) double sum.")
check("regular_points_follow_from_actual_positive_integer_bounds", True,
    "Each t in Icc1T satisfies t>=1. Hence (t:Q)+(k:Q)>0 for every natural k<=n, so the exact global PF regular-domain hypotheses are proved within the finite identity. This also covers T=0 by the empty sum, rather than silently requiring T>0 or supplying a PF assumption.")
check("finite_interchange_no_analytic_summation_premise", True,
    "Two uses of Finset.sum_comm reorder the finite t,j,s sums. The true fixed coefficient is factored with Finset.mul_sum after division is rewritten as multiplication by the reciprocal. An independently compiled arbitrary-f finite exchange statement retains precisely the same ranges; no infinite sum or limiting interchange appears.")
check("harmonic_shift_indices_and_endpoint_cases", True,
    "Induction starts at T=0 and adds t=T+1. The right endpoint T+1+j=(T+j)+1 gives exactly H_s(T+j)-H_s(j), with all natural orders s including0. Independent closed tests include T=0,j=0,s=0, and the positive tail difference sum over k=1..j with denominator T+k; no endpoint is off by one.")
check("constant_main_tail_signs_and_grouping", True,
    "The fixed H_s(T) term is grouped by summing j into actual rho, again by finite commutation. Pointwise c*(H_s(T+j)-H_s(j))=-c*H_s(j)+c*H_s(T)+c*(H_s(T+j)-H_s(T)). Thus the constant is negative, main rho sum positive, and tail positive. The independent T=0 test shows tail=-constant with no proper premise; n=0 makes both constant and tail zero.")
check("no_simple_pole_bridge_requires_actual_rho_one_cancellation", True,
    "The Icc1 9 sum is split into s=1 plus Icc2 9 using the genuine lower-endpoint interval lemma. The bridge explicitly assumes rho n 1 W=0 in addition to strict properness. Its independently closed type preserves both inputs; it does not prove that assumption from properness.")
check("odd_bridge_preserves_all_five_actual_cancellation_inputs", True,
    "The odd identity explicitly assumes actual rho1,rho2,rho4,rho6,rho8 each equal0, with strict properness. Only then are s=3,5,7,9 retained. FiniteSum has no reflected local series theorem, Even n premise or proof supplying these cancellations; a separate Reflection development must be reviewed before treating them as discharged.")
required = ["fs_ind_n_zero_X_four_proper", "fs_ind_n_zero_X_four_rho_one", "fs_ind_n_zero_X_four_rho_higher", "fs_ind_n_zero_X_four_no_simple_cancellation", "fs_ind_n_zero_X_four_actual_simple_pole", "fs_ind_n_zero_X_four_actual_finite", "fs_ind_no_simple_without_cancellation_false", "fs_ind_n_zero_X_four_not_two_degree_gap"]
check("independent_n_zero_quartic_retains_true_simple_harmonic_term",
    all(name in boundary and set(boundary[name]["axioms"]) <= STANDARD for name in required),
    "n=0,W=X^4 satisfies strict properness. Actual weightedR=1/t for t!=0, rho1=1, and all higher rho2..9 vanish. The actual finite sum is H_1(T). At T=1 the left side is1, while the grouped RHS dropping rho1 is0, so removing the cancellation input is formally false. The stronger two-degree-gap bound fails.")
check("finite_identity_scope_without_infinite_L_or_aggregate_claims", True,
    "This review closes only the actual finite rational summation identities in the proper domain and the conditional cancellation bridges. Strict properness supplies a one-degree gap; it must not be conflated with the stronger two-degree gap and O(1/t^2). No actual reflection cancellation, tail limit, infinite summation, analytic L convergence/exact L, denominator integrality, original aggregate F injectivity/inverse, J or irrationality is established here.")
write(OUT / "independent-original-types.json", original_rows)
write(OUT / "independent-boundary-types.json", boundary_rows)
md = """# 独立数学与 Lean 审核：真实有限调和求和

结论：PASS。冻结 FiniteSum 源 SHA256 为 `b3ede123541d6c0eb306915d93f743979b1090c34bc4df332ab6e9da07033f97`。四份实际 CM/Jet/Injectivity/PF 依赖、纯 HarmonicStability 定义和作者 15 项冻结记录均未改变。审核者不是 FiniteSum 作者。

我在新的任务内缓存重新编译纯 HarmonicStability Def 和五份实际系数原源，重跑作者 17 项类型审计，再编译自拟 27 个完整陈述及边界定理。八个实际执行退出码全部为 0。源的 4 个定义和 7 个证明均在导入审计覆盖，定义值与类型逐项匹配作者记录；独立审计另覆盖纯 Def 的 2 个定义，合计 40 项。全部最终 17+40 项类型记录和五源的 45 个打印目标只含标准三公理，无 sorryAx。纯模块仅含 logDen 与实际 harmonicPower；harmonicPower 的定义体与旧原源相同，没有导入旧 HarmonicStability 的证明。

有限对象确实是 `finiteL(n,T,W)=Σ_{t=1}^T weightedR(n,W,t)`；rho 是实际局部系数 c^W_{j,s} 对 j=0,…,n 的和。每个求和 t≥1，使全部自然 k≤n 的 t+k>0，故真实全局 PF 的正则点条件在证明内部被解除。两次有限换序和提取系数后，准确得到 `Σ c^W_{j,s}(H_s(T+j)−H_s(j))`。移位公式通过 T 归纳，末端为 T+1+j=(T+j)+1；s=0、T=0 和 j=0 都有独立闭合核验。

分组恒等式的常数项是负的 `−ΣcH_s(j)`，主项是正的 `Σrho_s H_s(T)`，尾项也是正的 `Σc(H_s(T+j)−H_s(T))`。独立 T=0 定理验证尾项恰好抵消常数项；n=0 时常数和尾项均为零。尾差进一步精确等于 k=1,…,j 的 `(T+k)^{−s}` 有限和。

去掉简单极点的桥明确需要实际 `rho1=0`，奇数阶桥进一步明确需要实际 rho2、rho4、rho6、rho8=0；这些是原定理的输入，本源没有证明反射消去。严格 proper 条件仍是 `2n+2deg W<9(n+1)`。独立真实边界核验：n=0、W=X⁴ 满足 proper，weightedR=1/t（t≠0），rho1=1、rho2,…,rho9=0，有限和恰为 H_1(T)。在 T=1，删掉简单项的右侧为 0、真实左侧为 1，因此不能删除消去前提。该例也不满足更强的两次数差条件。

本环仅关闭真实有限有理求和与条件式消去桥；没有取极限、无限和、尾项收敛或 exact L，没有由 strict proper 性推出更强的普遍 O(t⁻²)。实际反射、分母整性、原五维聚合 F 的单射或逆映射、J 与 ζ(9) 无理性仍在范围之外。没有修改作者冻结源、旧平台批次、root 或 scope，没有访问 API 或凭证。

首次自拟 T=0 补充审计的 `Icc 1 0` 被 Lean 推为有理区间，造成类型检查失败；已在独立文件中显式标注自然数端点，失败源、日志、退出码和 receipt 原样保留。该错误仅在自拟审计，原冻结源码与作者类型重放已成功。最终执行 0，40 项实际记录无 sorryAx。
"""
(OUT / "independent-review.md").write_text(md, encoding="utf-8")
(OUT / "independent-review.log").write_text("PASS: author freeze15/15; independent pureDef+five actual sources exit0; author replay17; independent audit40=11source+2pureDef+27additional; all final standard3.\n" + "\n".join("PASS " + c["name"] for c in checks) + "\n", encoding="utf-8")
new_paths = [v for v in OUT.rglob("*") if v.is_file() and (v.name.startswith("independent") or "independent" in v.relative_to(OUT).parts) and v.name != "independent-review.json"]
primary = [ROOT / ".lake/packages/mathlib/Mathlib" / name for name in ["Algebra/BigOperators/Intervals.lean", "Algebra/Order/BigOperators/Group/LocallyFinite.lean", "Algebra/BigOperators/Group/Finset/Basic.lean"]]
stable_paths = sorted(set(author_paths + list(sources.values()) + [manifest, PURE, old_light, old_proof] + new_paths + primary))
bindings = [{"task_relative": v.relative_to(TASK).as_posix() if v.is_relative_to(TASK) else None,
    "root_relative": v.relative_to(ROOT).as_posix(), "bytes": v.stat().st_size, "sha256": sha(v)} for v in stable_paths]
main = [NS + ".actual_finite_harmonic_identity", NS + ".actual_grouped_finite_identity", NS + ".actual_grouped_finite_identity_no_simple_pole", NS + ".actual_grouped_finite_identity_odd"]
report = {"schema_version": 1, "verdict": "PASS", "scope_verdict": "PASS_ACTUAL_FINITE_SUM_IN_PROPER_DOMAIN_AND_CONDITIONAL_CANCELLATION_BRIDGES_ONLY",
    "review_role": "Independent mathematical and Lean reviewer; another agent authored FiniteSum", "checked_at": datetime.now(timezone.utc).isoformat(),
    "source": sources["CoefficientMapFiniteSum"].relative_to(ROOT).as_posix(), "source_sha256": EXPECTED["CoefficientMapFiniteSum"], "sources_sha256": EXPECTED,
    "pure_harmonic_definition": {"root_relative": PURE.relative_to(ROOT).as_posix(), "sha256": PURE_HASH, "same_actual_harmonicPower_body_as_original": True},
    "environment": {"lean_toolchain": (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip(), "mathlib_rev": next(v["rev"] for v in load(ROOT / "lake-manifest.json")["packages"] if v["name"] == "mathlib")},
    "checks": checks, "source_definitions": 4, "source_theorems": 7, "proper_domain": "2*n + 2*W.natDegree < 9*(n+1)",
    "finite_regular_points": "t:N,1<=t<=T imply forall k:N,k<=n -> (t:Q)+(k:Q)!=0; T=0 is empty sum",
    "main_target_types": {name: boundary[name] for name in main}, "boundary_examples": {name: boundary[name] for name in required},
    "actual_type_records": {"author_replay": 17, "independent_audit": 40, "independent_additional_statements": 27, "independent_pure_definition_records": 2},
    "retained_failed_audit_attempt": {"exit_code": 1, "source": "independent-boundary-audit.lean.before-Nat-interval-fix", "log": "independent-boundary-audit.log.before-Nat-interval-fix", "receipt": "independent-compile-receipt.json.before-Nat-interval-fix", "reason": "Only the supplemental T=0 interval inferred Q; fixed by Icc (1:Nat) 0. Frozen source and author replay were already successful."},
    "findings": [{"severity": "information", "name": "Actual cancellation inputs retained", "detail": "no_simple_pole requires rho1=0; odd bridge requires rho1,rho2,rho4,rho6,rho8=0. This source proves neither reflection nor these actual cancellations."},
        {"severity": "information", "name": "Proper quartic may retain harmonic divergence term", "detail": "n=0,W=X^4 has rho1=1 and finiteL=H_1(T), while higher rho vanish. At T=1 the formula obtained by dropping rho1 is false. Properness is weaker than the two-degree-gap bound; no L convergence is claimed."}],
    "actual_finite_harmonic_identity_closed": True, "actual_grouped_finite_identity_closed": True,
    "conditional_no_simple_bridge_closed": True, "conditional_odd_bridge_closed": True,
    "reflection_cancellation_closed": False, "rho1_zero_without_added_condition_closed": False,
    "uniform_stronger_O_one_over_t_squared_closed": False, "tail_limit_closed": False, "infinite_sum_convergence_closed": False,
    "exact_L_closed": False, "denominator_integrality_closed": False, "original_aggregate_F_injectivity_closed": False,
    "original_aggregate_F_inverse_closed": False, "J_closed": False, "irrationality_closed": False,
    "root_scope_API_credentials_writes": False, "author_freeze_sources_platform_batches_modified": False, "stable_files": bindings}
assert report["environment"] == {"lean_toolchain": "leanprover/lean4:v4.33.1", "mathlib_rev": "0df444a360eaa60ab8c11dca51a86af692955474"}
write(OUT / "independent-review.json", report)
print(json.dumps({"verdict": report["verdict"], "checks": len(checks), "stable_files": len(bindings),
    "independent_review_sha256": sha(OUT / "independent-review.json"), "independent_review_md_sha256": sha(OUT / "independent-review.md"),
    "independent_compile_receipt_sha256": sha(OUT / "independent-compile-receipt.json")}, indent=2))
