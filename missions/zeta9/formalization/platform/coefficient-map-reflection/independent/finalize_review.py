"""Freeze an independent Reflection transplant verdict from actual fresh runs."""
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
OLD = TASK / "verification/formalization-coefficient-map-reflection-2026-10-03"
NS = "ZetaNine.CoefficientMapReflection"
STANDARD = {"propext","Classical.choice","Quot.sound"}
TARGETS = ["local_coefficient_reflection","rho_even_order_zero","rho_one_zero_of_strong_proper"]
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
check("37_fresh_independent_Lean_runs_all_actual_exit_zero",len(prep["rows"]) == 9 and len(replay["rows"]) == 28 and len(invocations) == 37 and prep["complete"] and replay["complete"],
    {"preparation":9,"final_replay":28,"native_staged_objects_borrowed":False,"separate_new_native_and_platform_caches":True})
environment = load(OUT/"actual-environment.json")
check("observed_Lean_4_33_1_and_root_pinned_Mathlib_revision",environment["lean_toolchain"] == "leanprover/lean4:v4.33.1" and
    "4.33.1" in environment["lean_runtime_stdout"] and environment["actual_runtime_exit_code"] == 0 and
    environment["mathlib_manifest_revision"] == "0df444a360eaa60ab8c11dca51a86af692955474" and
    sha(ROOT/"lake-manifest.json") == environment["root_lake_manifest_sha256"] and sha(ROOT/"lean-toolchain") == environment["root_toolchain_sha256"] and
    (OUT/"actual-toolchain-exit.txt").read_text().strip() == "0",{"separate_lightweight_runtime_probe_exit":0})
original = index(rows(OUT/"replay-types_original.log"))
definitions = index(rows(OUT/"replay-types_definition.log"))
assert len(original) == 37 and len(definitions) == 34
contexts = [("definition",definitions)]
solutions,references = [],[]
for i in range(3):
    sol,ref = index(rows(OUT/f"replay-types_{i}_solution.log")),index(rows(OUT/f"replay-types_{i}_reference.log"))
    assert len(sol) == len(ref) == 35
    contexts.extend([(f"solution_{i}",sol),(f"reference_{i}",ref)])
    solutions.append(sol);references.append(ref)
comparisons = []
for context,rs in contexts:
    for name in definitions:
        a,b = original[name],rs[name]
        comparisons.append({"context":context,"declaration":name,"pass":a["type"] == b["type"] and a["value"] == b["value"] and standard(a) and standard(b)})
check("238_actual_definition_types_and_values_exact_across_seven_contexts",len(comparisons) == 238 and all(r["pass"] for r in comparisons),
    {"actual_Defs":34,"Base":9,"Jet":9,"Injectivity":7,"PF":5,"Reflection":4,"contexts":7})
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
assert len(native) == 64 and all(standard(r) for r in native.values())
proof_comparisons = []
for i in range(3):
    hs = rows(OUT/f"replay-helpers_{i}.log")
    assert len(hs) == 65
    mapped = {normalize(r["declaration"]):r for r in hs if r["declaration"] != "solution"}
    assert set(mapped) == set(native)
    for name,r in mapped.items():
        proof_comparisons.append({"solution_index":i,"declaration":r["declaration"],"native_declaration":name,
            "pass":normalize(r["type"]) == native[name]["type"] and standard(r) and standard(native[name]),"axioms":r["axioms"]})
    wrapper = next(r for r in hs if r["declaration"] == "solution")
    proof_comparisons.append({"solution_index":i,"declaration":"solution","native_declaration":NS+"."+TARGETS[i],
        "pass":wrapper["type"] == original[NS+"."+TARGETS[i]]["type"] and standard(wrapper),"axioms":wrapper["axioms"]})
check("195_actual_Sol_proof_records_match_native_types_and_standard_axioms",len(proof_comparisons) == 195 and all(r["pass"] for r in proof_comparisons),
    {"per_Sol":65,"original_Reflection_proofs":30,"actual_cross_helpers":34,"wrapper":1,"standard_axioms":sorted(STANDARD)})
for name in ["types_original","types_definition"]+[f"types_{i}_{kind}" for i in range(3) for kind in ["solution","reference"]]+[f"helpers_{i}" for i in range(3)]:
    assert payload(rows(OUT/("replay-"+name+".log"))) == payload(rows(BATCH/(name+".log")))
check("eleven_fresh_actual_type_proof_reports_equal_author_frozen_reports",True,{"equality_fields":["label","type","value","axioms_as_set"]})
boundary = index(rows(OUT/"replay-stage-boundary-audit.log"))
old_boundary = index(load(OLD/"independent-boundary-types.json"))
assert len(boundary) == 59 and len([n for n in boundary if n.startswith("refl_ind_")]) == 25
boundary_comparisons = []
for name,r in boundary.items():
    base = old_boundary[normalize(name)]
    boundary_comparisons.append({"declaration":name,"native_declaration":normalize(name),"type":r["type"],"axioms":r["axioms"],
        "pass":normalize(r["type"]) == base["type"] and r["definitionValue"] == base["definitionValue"] and standard(r) and standard(base)})
assert rows(OUT/"replay-stage-boundary-audit.log") == rows(BATCH/"stage-boundary-audit.log")
check("59_staged_boundary_records_and_25_original_exact_boundaries",all(r["pass"] for r in boundary_comparisons),
    {"source_records":34,"closed_boundary_records":25,"original_math_review_sha256":"ac3d8f135cb3c69b39074548bea712f418fa6d0273ad27e33805374c1db20123"})
new_boundary = rows(OUT/"independent-new-boundary.log")
check("nine_new_reviewer_boundaries_proven_with_only_standard_axioms",len(new_boundary) == 9 and all(standard(r) for r in new_boundary),
    {"actual_n0_X4_rho1":1,"n0_X4":"Proper and not Strong","n0_X5":"even totals vanish without Proper","n1_quartic":"Strong and rho1=0 without Even","n1_antireflection":"actual rational counterexample","Strong_vs_Proper":"two-degree-gap condition proved equivalent; implies strict proper"})
required = ["refl_ind_n_zero_X_four_rho_one","refl_ind_n_zero_X_four_proper_not_strong","refl_ind_n_zero_X_four_actual_simple_pole","refl_ind_n_zero_X_four_even_cancellations","refl_ind_odd_n_one_simple_zero","refl_ind_odd_n_anti_reflection_fails"]
check("actual_zero_and_odd_boundary_domains_preserved",all(name in boundary for name in required),{"simple_total_zero_requires_Strong":True,"sign_reflection_keeps_Even":True})
prints = []
for row in invocations:
    text = (OUT/row["log"]).read_text(encoding="utf-8-sig")
    for name,axs in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",text):
        axset = {a.strip() for a in axs.split(',') if a.strip()}
        assert axset <= STANDARD
        prints.append({"invocation":row["label"],"declaration":name,"axioms":sorted(axset)})
check("all_actual_native_and_Sol_printed_axioms_are_standard",len(prints) >= 15,{"prints":len(prints),"reference_sorry_warnings_separate":True})
root_prints = re.findall(r"info: Solutions/Sol_ZetaNine_CoefficientMapReflection_([^.:]+)\.lean:\d+:\d+: 'solution' depends on axioms: \[([^\]]*)\]",(BATCH/"task-build.log").read_text(encoding="utf-8-sig"))
check("parent_task_build_prints_each_new_Reflection_Sol_standard_axioms",len(root_prints) == 3 and {n for n,axs in root_prints} == set(TARGETS) and all({a.strip() for a in axs.split(',')} <= STANDARD for n,axs in root_prints),{"new_solution_prints":3,"older_PNT_stub_boundary_not_reviewed":True})
write(OUT/"independent-type-comparisons.json",{"original_actual_definition_records":[original[n] for n in definitions],"definition_comparisons":comparisons,
    "target_comparisons":target_comparisons,"proof_comparisons":proof_comparisons,"boundary_comparisons":boundary_comparisons,"new_boundary_records":new_boundary,"native_proof_records":list(native.values()),"printed_axioms":prints})
scope = "Actual finite reflection and coefficient totals: even n for signs/even rho; exact stronger two-degree gap for rho1, without Even premise"
findings = [
    {"severity":"informational","code":"EXACT_DOMAINS","detail":"First two endpoints retain Even n and need no properness. rho1 needs 2*n+2*W.natDegree<=9*(n+1)-2, not Even n. No cancellation hypotheses were introduced."},
    {"severity":"informational","code":"ACTUAL_BOUNDARIES","detail":"n0,X4 is Proper but not Strong, its actual rho1=1 and weightedR=1/t, yet even-order totals vanish. n1 quartics are Strong and have rho1=0 although anti-reflection fails for odd n. Fresh closed boundary proofs preserve these distinctions."},
    {"severity":"informational","code":"STATEMENT_STUBS","detail":"Three Theorems files intentionally use sorryAx as statement stubs. No complete Sol imports them; all195 real Sol proof records and68 boundary records use only standard axioms."},
    {"severity":"informational","code":"FROZEN_MEMBERS","detail":"All170 manifest members and172 SHA256SUMS entries match, as do515 prior batch frozen members. Author's retained parser-snapshot gate failure is separate from successful actual Reflection parser replay."},
    {"severity":"informational","code":"SCOPED_ROOT_BUILD","detail":"Parent supported task build is3775 jobs exit0. Scope check exit1 identifies only two pre-existing Tao unassigned solutions. Older PNT MediumPNT statement mirror is outside this review's axiom claim."},
    {"severity":"informational","code":"FINITE_SCOPE","detail":"This transplant does not assert numerical infinite-series convergence, original aggregate F or its inverse, prescribed L, denominator integrality, J or irrationality. Other later native modules are outside the exact scope of this three-endpoint batch."},
    {"severity":"informational","code":"RETAINED_REVIEWER_METADATA_FAILURE","detail":"Reviewer initially asserted3776 parent build jobs from the handoff. The bound unchanged log actually says3775 jobs. Own failed assertion/script are retained separately and corrected to the observed count. No Lean, mathematical-source or staged-proof failure is inferred from this metadata correction."}]
md = "Independent Reflection platform integration review: PASS.\n\n"+scope+".\n\n"
md += "37 observed fresh Lean exits0; five actual sources, four pure Def dependencies,169 actual graph records and all five parser/header snapshots; seven staged modules compile.238 actual Def type/value comparisons, three exact original/Sol/reference types,195 proof records,59 staged boundary records and9 new reviewer boundary proofs pass. Root7+4 source bytes and supported parent3775-job task build are verified.\n\n"
md += "The Even and Strong conditions remain distinct. n0,X4 has actual rho1=1 despite even cancellation and strict properness. n1 quartics satisfy Strong and rho1 cancellation without Even; actual anti-reflection still fails. Complete solutions use only standard axioms; reference stubs are statements.\n\n"
md += "All170 author manifest members and172 SHA entries remain fixed. Old515 freeze members remain fixed. The two workspace check errors concern older Tao files. No root/scope/API/credential writes or publication occurred during this review.\n"
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
paths.update(OUT.rglob("*"))
report_path = OUT/"independent-integration-review.json"
files = []
for p in sorted(paths,key=lambda p:p.as_posix()):
    if not p.is_file() or p == report_path: continue
    assert p.is_relative_to(ROOT)
    files.append({"task_relative":p.relative_to(TASK).as_posix() if p.is_relative_to(TASK) else None,"root_relative":p.relative_to(ROOT).as_posix(),"bytes":p.stat().st_size,"sha256":sha(p)})
report = {"schema_version":1,"verdict":"PASS","scope_verdict":"PASS_ACTUAL_REFLECTION_PLATFORM_INTEGRATION","review_role":"Independent transplant reviewer; not mathematical or platform batch author",
    "checked_at":datetime.now(timezone.utc).isoformat(),"scope":scope,"source_sha256":prep["original_sources_sha256"]["CoefficientMapReflection"],"sources_sha256":prep["original_sources_sha256"],
    "author_frozen_controls":mechanical["author_frozen_controls"],"environment":{"lean_toolchain":"leanprover/lean4:v4.33.1","mathlib_rev":"0df444a360eaa60ab8c11dca51a86af692955474"},
    "checks":checks,"findings":findings,"compile_counts":{"preparation":9,"replay":28,"total":37,"separate_runtime_probe":1,"all_Lean_invocations":38,"actual_nonzero_final_exits":0},
    "audit_counts":{"graph":169,"new_Def":4,"all_actual_Def":34,"definition_comparisons":238,"exact_targets":3,"native_required_proofs":64,"Sol_proof_records":195,"staged_boundary_records":59,"exact_original_closed_boundaries":25,"new_reviewer_boundary_records":9},
    "actual_cross_source_helpers":mechanical["actual_cross_helpers"],"new_external_theorem_boundaries":[],"root_module_bytes_verified":True,"parent_task_build_exit_code":0,"workspace_check_exit_code":1,
    "reviewer_root_scope_API_credentials_writes":False,"platform_published_by_reviewer":False,"platform_acceptance_claimed":False,"failed_attempts_excluded_from_success_evidence":True,"stable_files":files,
    "hash_exclusions":["report self","dynamic scope.json","API receipts","API documentation","credentials"]}
write(report_path,report)
assert all(sha(ROOT/r["root_relative"]) == r["sha256"] and (ROOT/r["root_relative"]).stat().st_size == r["bytes"] for r in files)
print("Independent Reflection PASS; "+str(len(checks))+" checks; "+str(len(files))+" bindings")
print("review_sha256="+sha(report_path))
