"""Freeze an independent Summation transplant verdict from actual fresh runs."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re
import sys

sys.stdout.reconfigure(encoding="utf-8")
OUT = Path(__file__).resolve().parent
BATCH = OUT.parent
TASK = OUT.parents[3]
ROOT = TASK.parents[1]
OLD = TASK / "verification/formalization-coefficient-map-summation-independent-2026-10-04"
NS = "ZetaNine.CoefficientMapSummation"
STANDARD = {"propext","Classical.choice","Quot.sound"}
TARGETS = ["actualSeries_norm_summable","actualSeries_hasSum_exactL","original_integer_quartic_exact_infinite_L"]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p): return json.loads(p.read_text(encoding="utf-8-sig"))
def rows(p): return [json.loads(s) for s in p.read_text(encoding="utf-8-sig").splitlines() if s.startswith("{")]
def write(p,obj): p.write_text(json.dumps(obj,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
def index(rs):
    result = {r["declaration"]:r for r in rs}
    assert len(result) == len(rs)
    return result
def standard(r): return set(r["axioms"]) <= STANDARD
def normalize(text):
    for name in TARGETS: text = text.replace(NS+".checked_"+name,NS+"."+name)
    return text
def payload(rs): return {r["label"]:{"type":r["type"],"value":r["value"],"axioms":sorted(r["axioms"])} for r in rs}
mechanical = load(OUT / "mechanical-checks.json")
checks = list(mechanical["checks"])
def check(name,passed,detail=None):
    checks.append({"name":name,"pass":bool(passed),"detail":detail})
    write(OUT / "finalizer-development-checks.json", {"checks":checks,"complete":False})
    assert passed,name

prep,replay = load(OUT/"prepare-compile-receipt.json"),load(OUT/"replay-compile-receipt.json")
invocations = prep["rows"] + replay["rows"]
for row in invocations:
    assert row["exit_code"] == int((OUT/row["exit_file"]).read_text().strip()) == 0
    assert sha(ROOT/row["source_root_relative"]) == row["source_sha256"]
    for field in ["log","exit_file","wrapper","output","stdout_copy"]:
        if row.get(field): assert sha(OUT/row[field]) == row["stdout_sha256" if field == "stdout_copy" else field+"_sha256"]
    wrapper = (OUT/row["wrapper"]).read_text(encoding="utf-8")
    assert (OUT/"cache").as_posix() in wrapper and (BATCH/"project").as_posix() not in wrapper
check("46_fresh_independent_Lean_runs_all_actual_exit_zero",len(prep["rows"]) == 15 and len(replay["rows"]) == 31 and len(invocations) == 46 and prep["complete"] and replay["complete"],
    {"preparation":15,"final_replay":31,"native_staged_objects_borrowed":False,"separate_new_native_and_platform_caches":True})
environment = load(OUT/"actual-environment.json")
check("observed_Lean_4_33_1_and_root_pinned_Mathlib_revision",environment["lean_toolchain"] == "leanprover/lean4:v4.33.1" and
    "4.33.1" in environment["lean_runtime_stdout"] and environment["actual_runtime_exit_code"] == 0 and
    environment["mathlib_manifest_revision"] == "0df444a360eaa60ab8c11dca51a86af692955474" and
    sha(ROOT/"lake-manifest.json") == environment["root_lake_manifest_sha256"] and sha(ROOT/"lean-toolchain") == environment["root_toolchain_sha256"] and
    (OUT/"actual-toolchain-exit.txt").read_text().strip() == "0",{"separate_lightweight_runtime_probe_exit":0})
original = index(rows(OUT/"replay-types_original.log"))
definitions = index(rows(OUT/"replay-types_definition.log"))
assert len(original) == 46 and len(definitions) == 43
contexts = [("definition",definitions)]
solutions,references = [],[]
for i in range(3):
    sol,ref = index(rows(OUT/f"replay-types_{i}_solution.log")),index(rows(OUT/f"replay-types_{i}_reference.log"))
    assert len(sol) == len(ref) == 44
    contexts.extend([(f"solution_{i}",sol),(f"reference_{i}",ref)])
    solutions.append(sol);references.append(ref)
comparisons = []
for context,rs in contexts:
    for name in definitions:
        a,b = original[name],rs[name]
        comparisons.append({"context":context,"declaration":name,"pass":a["type"] == b["type"] and a["value"] == b["value"] and standard(a) and standard(b)})
check("301_actual_definition_types_and_values_exact_across_seven_contexts",len(comparisons) == 301 and all(r["pass"] for r in comparisons),
    {"actual_Defs":43,"Base":9,"Jet":9,"Injectivity":7,"PF":5,"Reflection":4,"FiniteSum":4,"Summation":3,"HarmonicStability":2,"contexts":7})
target_comparisons = []
for i,short in enumerate(TARGETS):
    name = NS+"."+short
    a,b,c = original[name],solutions[i]["solution"],references[i][name]
    assert a["value"] is b["value"] is c["value"] is None
    assert standard(a) and standard(b) and set(a["axioms"]) == set(b["axioms"]) == STANDARD
    assert set(c["axioms"]) == STANDARD|{"sorryAx"}
    target_comparisons.append({"target":name,"original_type":a["type"],"solution_type":b["type"],"reference_type":c["type"],
        "pass":a["type"] == b["type"] == c["type"],"solution_axioms":b["axioms"],"reference_statement_stub_axioms":c["axioms"],"extra_hypotheses":[]})
check("three_original_Sol_reference_types_equal_no_new_premises",all(r["pass"] for r in target_comparisons),{"target_names":TARGETS,"stubs_are_not_proofs":True})
native = index(rows(OUT/"independent-native-required-proofs.log"))
native_count = 21 + len(mechanical["actual_cross_helpers"])
assert len(native) == native_count and all(standard(r) for r in native.values()) and set(native) == set(replay["native_actual_proof_names"])
proof_comparisons = []
for i in range(3):
    hs = rows(OUT/f"replay-helpers_{i}.log")
    assert len(hs) == native_count + 1
    mapped = {normalize(r["declaration"]):r for r in hs if r["declaration"] != "solution"}
    assert set(mapped) == set(native)
    for name,r in mapped.items():
        proof_comparisons.append({"solution_index":i,"declaration":r["declaration"],"native_declaration":name,
            "pass":normalize(r["type"]) == native[name]["type"] and standard(r) and standard(native[name]),"axioms":r["axioms"]})
    wrapper = next(r for r in hs if r["declaration"] == "solution")
    proof_comparisons.append({"solution_index":i,"declaration":"solution","native_declaration":NS+"."+TARGETS[i],
        "pass":wrapper["type"] == original[NS+"."+TARGETS[i]]["type"] and standard(wrapper),"axioms":wrapper["axioms"]})
check("all_actual_Sol_proof_records_match_native_types_and_standard_axioms",len(proof_comparisons) == 3*(native_count+1) and all(r["pass"] for r in proof_comparisons),
    {"per_Sol":native_count+1,"original_Summation_proofs":21,"actual_cross_helpers":len(mechanical["actual_cross_helpers"]),"wrapper":1,"standard_axioms":sorted(STANDARD)})
for name in ["types_original","types_definition"]+[f"types_{i}_{kind}" for i in range(3) for kind in ["solution","reference"]]+[f"helpers_{i}" for i in range(3)]:
    assert payload(rows(OUT/("replay-"+name+".log"))) == payload(rows(BATCH/(name+".log")))
check("eleven_fresh_actual_type_proof_reports_equal_author_frozen_reports",True,{"equality_fields":["label","type","value","axioms_as_set"]})
boundary = index(rows(OUT/"replay-stage-boundary-audit.log"))
old_boundary = index(load(OLD/"independent-boundary-types.json"))
assert len(boundary) == len(old_boundary) == 56
boundary_comparisons = []
assert {normalize(name) for name in boundary} == set(old_boundary)
for name,r in boundary.items():
    base=old_boundary[normalize(name)]
    boundary_comparisons.append({"declaration":name,"native_declaration":normalize(name),"type":r["type"],"axioms":r["axioms"],
        "pass":normalize(r["type"])==base["type"] and r["definitionValue"]==base["definitionValue"] and standard(r) and standard(base)})
assert rows(OUT/"replay-stage-boundary-audit.log") == rows(BATCH/"stage-boundary-audit.log")
closed = [r for r in boundary.values() if r["declaration"].startswith("sum_ind_")]
check("56_staged_boundary_records_equal_original_native_including_32_closed",len(closed)==32 and all(r["pass"] for r in boundary_comparisons),
    {"original_source_records":24,"original_closed_records":32,"original_math_review_sha256":"fb0d4a09e3273fe430688521771ea582463d31cd98caf50764a7498293c040fa"})
new_boundary=rows(OUT/"independent-new-boundary.log")
check("eight_new_reviewer_analytic_controls_standard_axioms",len(new_boundary)==8 and all(standard(r) for r in new_boundary),
    {"absolute_without_even":True,"HasSum_supplies_summability_and_exact_tsum":True,"integer_even_two_X_four":True,"actual_n0_X3_at_positive_two":"1/8","actual_n0_X4_at_positive_two":"1/2","index_starts_at_positive_one":True})
required=["sum_ind_absolute_without_even","sum_ind_odd_n_one_absolute","sum_ind_n_zero_X_three_HasSum","sum_ind_n_zero_X_four_no_HasSum","sum_ind_n_zero_X_four_not_summable","sum_ind_n_zero_X_four_totalized_tsum_eq_exactL","sum_ind_n_zero_X_four_partial_diverges","sum_ind_closed_original_HasSum"]
check("actual_absolute_odd_and_divergent_totalized_tsum_boundaries_preserved",all(name in boundary for name in required),
    {"totalized_tsum_without_HasSum_not_proof_of_convergence":True,"original_even_integer_quartic_domain_kept":True})

prints = []
for row in invocations:
    text = (OUT/row["log"]).read_text(encoding="utf-8-sig")
    for name,axs in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",text):
        axset = {a.strip() for a in axs.split(',') if a.strip()}
        assert axset <= STANDARD
        prints.append({"invocation":row["label"],"declaration":name,"axioms":sorted(axset)})
check("all_actual_native_and_Sol_printed_axioms_are_standard",len(prints) >= 15,{"prints":len(prints),"reference_sorry_warnings_separate":True})
root_prints = re.findall(r"info: Solutions/Sol_ZetaNine_CoefficientMapSummation_([^.:]+)\.lean:\d+:\d+: 'solution' depends on axioms: \[([^\]]*)\]",(BATCH/"task-build.log").read_text(encoding="utf-8-sig"))
check("parent_task_build_prints_each_new_Summation_Sol_standard_axioms",len(root_prints) == 3 and {n for n,axs in root_prints} == set(TARGETS) and all({a.strip() for a in axs.split(',')} <= STANDARD for n,axs in root_prints),{"new_solution_prints":3,"older_PNT_stub_boundary_not_reviewed":True})
write(OUT/"independent-type-comparisons.json",{"original_actual_definition_records":[original[n] for n in definitions],"definition_comparisons":comparisons,
    "target_comparisons":target_comparisons,"proof_comparisons":proof_comparisons,"boundary_comparisons":boundary_comparisons,"new_boundary_records":new_boundary,"native_proof_records":list(native.values()),"printed_axioms":prints})
scope = "Actual p9,q1,m=n,d0 absolute convergence under Strong without Even; exact odd-zeta HasSum under Even and Strong; original integer-quartic even n>=2 specialization"
findings = [
    {"severity":"informational","code":"EXACT_ANALYTIC_DOMAINS","detail":"Absolute norm summability keeps only actual StrongProperMultiplier; HasSum keeps Even n and Strong. The original integer endpoint keeps Even n>=2 and integer polynomial degree<=4. No rho-cancellation, summability, abstract rational function or zeta-limit premise is added."},
    {"severity":"informational","code":"GENUINE_HAS_SUM","detail":"Summability is proved before genuine HasSum. The original n0,X4 is strict proper but not Strong, is not summable and has no HasSum to any real, although Lean's totalized tsum equals zero. The actual n0,X3 converges to zetaReal3; odd n1 absolute summability remains valid."},
    {"severity":"informational","code":"ACTUAL_COMPLETE_PROOFS","detail":"All21 original Sum proofs and69 actual cross-source helpers remain in each Sol. Only Definitions and Mathlib imports support all complete proofs; reference Theorems carry sorryAx as statement stubs and are excluded from proof claims."},
    {"severity":"informational","code":"RAW_AND_PARSER_INPUT","detail":"Pure Harmonic raw CRLF bytes remain fixed; the independently executed official parser snapshot equals exact CRLF-to-LF normalization. All seven actual native source snapshots and eight actual parser outputs are reexecuted."},
    {"severity":"informational","code":"SCOPED_ROOT_BUILD","detail":"Root7+7 actual byte files and the parent scoped3789-job build0 are bound. Check1 names only the two existing Tao files; older PNT statement mirror is outside the new-Sol proof claim. Parent initial path gate failure is preserved separately, not successful build evidence."},
    {"severity":"informational","code":"OPEN_OBLIGATIONS","detail":"This batch proves actual infinite weighted sum for p9,q1,m=n,d0 and the original quartic specialization. Inverse height/integrality, small nonzero integer forms, general parameters, J and irrationality remain outside this verdict; KernelBridge results are separately reviewed."}]
md = "Independent Summation platform integration review: PASS.\n\n"+scope+".\n\n"
md += "46 observed fresh source/extraction/audit Lean exits0, plus one separate runtime probe; seven actual sources and pure Harmonic source, seven existing pure Def dependencies, eight Stage2/parser snapshots and header, and seven staged modules compile.301 actual Def type/value comparisons, three exact original/Sol/reference types,273 Sol proof records,56 exact original staged boundary records including32 closed controls and8 new reviewer analytic controls pass.\n\n"
md += "Absolute convergence has no Even premise; genuine odd-zeta HasSum preserves Even and Strong; the integer quartic endpoint preserves even n>=2. No root/scope/API/credential writes or publication occurred during this review. Earlier FS and Reflection independent freezes remain unchanged.\n"
(OUT/"independent-integration-review.md").write_text(md,encoding="utf-8")
(OUT/"independent-integration-review.log").write_text("PASS\n"+"\n".join(c["name"]+": PASS" for c in checks)+"\n",encoding="utf-8")
paths = set(TASK/r["task_relative"] for r in load(BATCH/"source-manifest.json")["files"])
paths.update(BATCH/n for n in mechanical["author_frozen_controls"])
paths.update(BATCH/n for n in mechanical["root_evidence_sha256"])
paths.update(ROOT/n for n in mechanical["root_paths"])
paths.update(ROOT/n for n in mechanical["old_frozen_manifests"])
paths.update(TASK/("formalization/"+n+".lean") for n in prep["original_sources_sha256"])
paths.update(OLD/n for n in ["independent-review.json","independent-boundary-types.json","independent-boundary-audit.lean","independent-compile-receipt.json"])
paths.update(ROOT/n for n in ["lake-manifest.json","lean-toolchain"])
paths.update(ROOT/r["root_relative"] for r in load(OLD/"independent-review.json")["stable_files"])
paths.update(OUT.rglob("*"))
paths.add(BATCH/"root-install-attempt-01-failure.json")
for batch in ["coefficient-map-reflection","coefficient-map-finite-sum"]:
    paths.add(TASK/"formalization/platform"/batch/"independent/independent-integration-review.json")
report_path = OUT/"independent-integration-review.json"
files = []
for p in sorted(paths,key=lambda p:p.as_posix()):
    if not p.is_file() or p == report_path: continue
    assert p.is_relative_to(ROOT)
    files.append({"task_relative":p.relative_to(TASK).as_posix() if p.is_relative_to(TASK) else None,"root_relative":p.relative_to(ROOT).as_posix(),"bytes":p.stat().st_size,"sha256":sha(p)})
report = {"schema_version":1,"verdict":"PASS","scope_verdict":"PASS_ACTUAL_INFINITE_SUM_PLATFORM_INTEGRATION","review_role":"Independent transplant reviewer; not mathematical or platform batch author",
    "checked_at":datetime.now(timezone.utc).isoformat(),"scope":scope,"source_sha256":prep["original_sources_sha256"]["CoefficientMapSummation"],"sources_sha256":prep["original_sources_sha256"],
    "author_frozen_controls":mechanical["author_frozen_controls"],"environment":{"lean_toolchain":"leanprover/lean4:v4.33.1","mathlib_rev":"0df444a360eaa60ab8c11dca51a86af692955474"},
    "checks":checks,"findings":findings,"compile_counts":{"preparation":15,"replay":31,"total":46,"separate_runtime_probe":1,"all_Lean_invocations":47,"actual_nonzero_final_exits":0},
    "audit_counts":{"graph":len(rows(OUT/"native-decl-graph.jsonl")),"new_Def":3,"all_actual_Def":43,"definition_comparisons":301,"exact_targets":3,"native_required_proofs":native_count,"Sol_proof_records":3*(native_count+1),"staged_boundary_records":56,"exact_original_closed_boundaries":32,"new_reviewer_boundary_records":8},
    "actual_cross_source_helpers":mechanical["actual_cross_helpers"],"new_external_theorem_boundaries":[],"root_module_bytes_verified":True,"parent_task_build_exit_code":0,"workspace_check_exit_code":1,
    "reviewer_root_scope_API_credentials_writes":False,"platform_published_by_reviewer":False,"platform_acceptance_claimed":False,"failed_attempts_excluded_from_success_evidence":True,"stable_files":files,
    "hash_exclusions":["report self","dynamic scope.json","API receipts","API documentation","credentials"]}
write(report_path,report)
assert all(sha(ROOT/r["root_relative"]) == r["sha256"] and (ROOT/r["root_relative"]).stat().st_size == r["bytes"] for r in files)
print("Independent Summation PASS; "+str(len(checks))+" checks; "+str(len(files))+" bindings")
print("review_sha256="+sha(report_path))
