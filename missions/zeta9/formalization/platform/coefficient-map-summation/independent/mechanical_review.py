"""Independent actual graph/parser reconstruction and frozen-root audit."""
from pathlib import Path
import hashlib
import json
import re
import sys

sys.stdout.reconfigure(encoding="utf-8")
OUT = Path(__file__).resolve().parent
BATCH = OUT.parent
TASK = OUT.parents[3]
ROOT = TASK.parents[1]
NS = "ZetaNine.CoefficientMapSummation"
REV = "0df444a360eaa60ab8c11dca51a86af692955474"
MATHLIB = ["Mathlib.NumberTheory.LSeries.RiemannZeta","Mathlib.Analysis.PSeries","Mathlib.Analysis.Normed.Group.InfiniteSum","Mathlib.Analysis.Normed.Module.FiniteDimension"]
# Enrollment is read after helper functions are defined; no unfrozen author records serve as controls.
CONTROLS = None
ROOT_EVIDENCE = None

TARGETS = ["actualSeries_norm_summable", "actualSeries_hasSum_exactL", "original_integer_quartic_exact_infinite_L"]
DEF_NAMES = ["zetaReal", "exactL", "actualSeries"]

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def load(path): return json.loads(path.read_text(encoding="utf-8-sig"))
def rows(path): return [json.loads(line) for line in path.read_text(encoding="utf-8-sig").splitlines() if line.startswith("{")]
def write(path, obj): path.write_text(json.dumps(obj, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
def lean_code(text): return re.sub(r"--[^\n]*", "", re.sub(r"/\-.*?\-/", "", text, flags=re.S))
def edit(data, edits):
    edge = len(data)
    for a,b,value in sorted(set(edits), reverse=True):
        assert 0 <= a <= b <= edge
        data = data[:a] + value + data[b:]
        edge = a
    return data
checks = []
def check(name, passed, detail=None):
    checks.append({"name":name,"pass":bool(passed),"detail":detail})
    write(OUT / "mechanical-development-checks.json", {"checks":checks,"complete":False})
    assert passed, name

enrollment = load(OUT / "frozen-controls.json")
assert enrollment["status"] == "PARENT_FROZEN_AUTHOR_HANDOFF"
CONTROLS = enrollment["controls"]
root_enrollment = load(OUT / "root-evidence-handoff.json")
assert root_enrollment["status"] == "PARENT_INSTALLED_AND_SCOPED_BUILD_OBSERVED"
ROOT_EVIDENCE = root_enrollment["hashes"]
check("fixed_four_author_controls_match", all(sha(BATCH/n) == h for n,h in CONTROLS.items()), CONTROLS)
manifest = load(BATCH / "source-manifest.json")
check("all_author_manifest_member_bytes_and_hashes_match", all(
    sha(TASK/r["task_relative"]) == r["sha256"] and (TASK/r["task_relative"]).stat().st_size == r["bytes"] for r in manifest["files"]),
    {"members":len(manifest["files"]),"independent_files_frozen_by_author":False})
sha_lines = [line.split("  ",1) for line in (BATCH/"SHA256SUMS.txt").read_text(encoding="utf-8-sig").splitlines() if line.strip()]
check("all_SHA256SUMS_entries_match", len(sha_lines) == len(manifest["files"])+2 and all(sha(BATCH/n) == h for h,n in sha_lines),len(sha_lines))
prep = load(OUT / "prepare-compile-receipt.json")
check("seven_actual_sources_and_seven_pure_Defs_match_fixed_hashes", all(sha(TASK/("formalization/"+n+".lean")) == h for n,h in prep["original_sources_sha256"].items()) and
    all(sha(ROOT/("Definitions/"+n+".lean")) == h for n,h in prep["existing_pure_Def_sources_sha256"].items()),
    {"sources":prep["original_sources_sha256"],"Defs":prep["existing_pure_Def_sources_sha256"]})
graph = rows(OUT / "native-decl-graph.jsonl")
def normalized_graph(rs): return {r["name"]:dict(r,typeDeps=sorted(r["typeDeps"]),valueDeps=sorted(r["valueDeps"])) for r in rs}
check("fresh_actual_Stage1_all_records_equal_frozen_graph", normalized_graph(graph) == normalized_graph(rows(BATCH/"decl_graph.jsonl")),len(graph))
by_name = {g["name"]:g for g in graph}
sources, facts = {}, {}
for module in prep["original_sources_sha256"]:
    sources[module] = (OUT/(module+"-native-snapshot.lean")).read_bytes()
    old_input = "oracle-input.lean" if module == "CoefficientMapPartialFractions" else module+"-oracle-input.lean"
    old_facts = "CoefficientMapSummation-sketch_info.jsonl" if module == "CoefficientMapSummation" else "sketch_info.jsonl" if module == "CoefficientMapPartialFractions" else module+"-sketch_info.jsonl"
    facts[module] = rows(OUT/(module+"-native-facts.jsonl"))
    assert sources[module] == (BATCH/old_input).read_bytes() == (TASK/("formalization/"+module+".lean")).read_bytes()
    assert facts[module] == rows(BATCH/old_facts)
harmonic_raw = (ROOT / "Definitions/Def_ZetaNine_HarmonicStability.lean").read_bytes()
sources["Def_ZetaNine_HarmonicStability"] = (OUT / "Def_ZetaNine_HarmonicStability-native-snapshot.lean").read_bytes()
facts["Def_ZetaNine_HarmonicStability"] = rows(OUT / "Def_ZetaNine_HarmonicStability-native-facts.jsonl")
assert hashlib.sha256(harmonic_raw).hexdigest() == "5ff9d83ca177893db1eb149da985ff29b85dbe83614650a995e28066f9bd3e92"
assert sources["Def_ZetaNine_HarmonicStability"] == harmonic_raw.replace(b"\r\n",b"\n") == (BATCH / "Def_ZetaNine_HarmonicStability-oracle-input.lean").read_bytes()
assert facts["Def_ZetaNine_HarmonicStability"] == rows(BATCH / "Def_ZetaNine_HarmonicStability-sketch_info.jsonl")
check("actual_Harmonic_raw_hash_and_official_parser_CRLF_normalization_exact",True,{"raw_source_unchanged":True,"only_CRLF_to_LF_input_normalization":True,"parser_decl_count":sum(f["kind"] == "decl" for f in facts["Def_ZetaNine_HarmonicStability"])})
check("all_eight_actual_Stage2_input_and_command_decl_ref_spans_equal", True,
    {m:{k:sum(f["kind"] == k for f in fs) for k in ["decl","ref","command"]} for m,fs in facts.items()})
header = rows(OUT / "native-header.jsonl")
source = sources["CoefficientMapSummation"]
assert len(header) == 1 and header == rows(BATCH/"header_info.jsonl")
he = header[0]["end"]["offset"]
check("actual_Summation_parser_header_has_six_actual_imports", source[:he].decode().strip().splitlines() == ["import missions.zeta9.formalization.CoefficientMapReflection","import missions.zeta9.formalization.CoefficientMapFiniteSum"]+["import "+m for m in MATHLIB], header[0])

def declaration(name):
    g = by_name[name]
    ds = [f for f in facts[g["module"].split(".")[-1]] if f["kind"] == "decl" and f["declStart"]["line"] <= g["startLine"] <= f["declEnd"]["line"]]
    assert g["startLine"] > 0 and len(ds) == 1 and ds[0]["valStart"] is not None
    return ds[0]

core = [g for g in graph if g["module"].endswith(".CoefficientMapSummation") and g["startLine"] > 0]
reached, work = set(), [g["name"] for g in core] + [g["name"] for g in graph if g["isInstance"]]
while work:
    name = work.pop()
    if name in reached: continue
    reached.add(name)
    work.extend(by_name[name]["typeDeps"] + by_name[name]["valueDeps"])
prov = load(BATCH / "integration-provenance.json")
bridge, helpers, helper_facts, opens = "", [], [], []
for module in ["CoefficientMap","CoefficientMapJet","CoefficientMapInjectivity","CoefficientMapPartialFractions","CoefficientMapReflection","CoefficientMapFiniteSum"]:
    hs = sorted([by_name[n] for n in reached if by_name[n]["module"].endswith("."+module) and by_name[n]["kind"] == "theorem" and by_name[n]["startLine"] > 0],key=lambda g:g["startLine"])
    if not hs: continue
    first = min(declaration(g["name"])["declStart"]["offset"] for g in hs)
    cmdopens = [f for f in facts[module] if f["kind"] == "command" and f["syntaxKind"] == "Lean.Parser.Command.open" and f["span"]["end"]["offset"] < first]
    bridge += "open scoped BigOperators\nopen Finset Polynomial\n\nnamespace ZetaNine."+module+"\n\n"
    for f in cmdopens:
        opens.append({"module":module,"fact":f})
        bridge += sources[module][f["span"]["start"]["offset"]:f["span"]["end"]["offset"]].decode()+"\n"
    if cmdopens: bridge += "\n"
    for g in hs:
        f = declaration(g["name"])
        bridge += sources[module][f["declStart"]["offset"]:f["declEnd"]["offset"]].decode()+"\n\n"
        helpers.append(g["name"])
        helper_facts.append({"module":module,"name":g["name"],"fact":f})
    bridge += "end ZetaNine."+module+"\n\n"
check("actual_cross_helpers_and_entire_core_closure_exact", len(core) == 24 and helpers == prov["inline_helper_names"] and
    helper_facts == prov["inline_helper_facts"] and sorted(reached) == prov["cross_module_core_closure"],
    {"source_defs":3,"source_proofs":21,"cross_helpers":helpers})
check("real_parser_open_context_spans_and_bridge_bytes_exact", opens == prov["bridge_open_context_facts"] and bridge.encode() == (BATCH/"actual-proof-bridge.lean.inc").read_bytes(),opens)
check("actual_graph_has_no_axiom_or_unproved_external_boundary", not any(g["kind"] == "axiom" for g in graph) and not prov["new_external_theorem_boundaries"])

dfacts = [declaration(NS+"."+n) for n in DEF_NAMES]
first_def = min(f["declStart"]["offset"] for f in dfacts)
def_opens = [f for f in facts["CoefficientMapSummation"] if f["kind"] == "command" and f["syntaxKind"] == "Lean.Parser.Command.open" and f["span"]["end"]["offset"] < first_def]
check("three_Def_spans_and_three_actual_open_spans_exact", dfacts == prov["definition_facts"] and len(def_opens) == 3 and def_opens == prov["definition_open_context_facts"])
definition = "import Definitions.Def_ZetaNine_CoefficientMapReflection\nimport Definitions.Def_ZetaNine_CoefficientMapFiniteSum\n"+"\n".join("import "+m for m in MATHLIB)+"\n\nset_option autoImplicit false\nnoncomputable section\nopen scoped BigOperators\nopen Finset Polynomial\n\nnamespace "+NS+"\n\n"
definition += "\n".join(source[f["span"]["start"]["offset"]:f["span"]["end"]["offset"]].decode() for f in def_opens)+"\n\n"
definition += "\n\n".join(source[f["declStart"]["offset"]:f["declEnd"]["offset"]].decode() for f in dfacts)+"\n\nend "+NS+"\n"
check("lightweight_three_actual_Def_reconstructed_bytes_exact", definition.encode() == (BATCH/"staged/Definitions/Def_ZetaNine_CoefficientMapSummation.lean").read_bytes() and not re.search(r"\b(theorem|lemma|axiom|sorry|admit)\b",lean_code(definition)),DEF_NAMES)
reflection_facts = facts["CoefficientMapSummation"]
refs = [f for f in reflection_facts if f["kind"] == "ref"]
diagnostics = [f for f in reflection_facts if f["kind"] == "command" and f["syntaxKind"] == "Lean.Parser.Command.printAxioms"]
assert len(diagnostics) == 12 and diagnostics == prov["deleted_diagnostic_facts"]
cuts = [(f["declStart"]["offset"],f["declEnd"]["offset"],b"") for f in dfacts]+[(f["span"]["start"]["offset"],f["span"]["end"]["offset"],b"") for f in diagnostics]+[(0,he,b"")]
plan = load(BATCH/"target-plan.json")
request = load(BATCH/"problems-request.json")
preamble = "import Definitions.Def_ZetaNine_CoefficientMapSummation\n\nset_option autoImplicit false\nopen scoped BigOperators\nopen Finset Polynomial\nopen ZetaNine "+NS+" ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapFiniteSum ZetaNine.HarmonicStability\n"
for i,short in enumerate(TARGETS):
    full = NS+"."+short
    d = declaration(full)
    a,v = d["declStart"]["offset"],d["valStart"]["offset"]
    rs = [r for r in refs if r["const"] == full]
    bindings = [r for r in rs if a <= r["start"]["offset"] < v]
    assert len(bindings) == 1
    bs,be = bindings[0]["start"]["offset"],bindings[0]["end"]["offset"]
    assert source[bs:be].decode() == short
    sig = source[be:v].decode()
    renames = []
    for r in rs:
        x,y = r["start"]["offset"],r["end"]["offset"]
        if any(ca <= x and y <= cb for ca,cb,_ in cuts): continue
        old = source[x:y].decode()
        assert old in [short,full]
        renames.append((x,y,("checked_"+short if old == short else NS+".checked_"+short).encode()))
    sol = "import Definitions.Def_ZetaNine_CoefficientMapSummation\nimport Mathlib.Tactic\n"+"\n".join("import "+m for m in MATHLIB)+"\n\nset_option autoImplicit false\nset_option maxHeartbeats 2000000\nnoncomputable section\n"+bridge+"\n"+edit(source,cuts+renames).decode()+"\n\nopen ZetaNine "+NS+" ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapFiniteSum ZetaNine.HarmonicStability\n\ntheorem solution"+sig+":= by\n  exact "+NS+".checked_"+short+" "+plan["targets"][i]["wrapper_arguments"]+"\n\n#print axioms solution\n"
    assert sol.encode() == (BATCH/"staged"/plan["targets"][i]["local_solution"]).read_bytes()
    assert not re.search(r"\b(sorry|admit|axiom|unsafe)\b",lean_code(sol)) and not re.search(r"(?m)^import (Theorems|Solutions|missions)\.",sol)
    formal_edits = [(bs-a,be-a,full.encode())]
    if d["docstring"]:
        ds = d["docstring"]
        formal_edits.append((ds["start"]["offset"]-a,ds["end"]["offset"]-a,b""))
    formal = edit(source[a:v],formal_edits).decode().strip()+":= by sorry"
    ref = preamble+"\n"+formal+"\n"
    assert ref.encode() == (BATCH/"staged"/plan["targets"][i]["local_reference"]).read_bytes()
    req = request["problems"][i]
    assert req["formal_statement"] == formal and req["preamble"] == preamble and req["theorem_name"] == full
    pr = prov["targets"][full]
    assert pr["declaration_fact"] == d and pr["binding_fact"] == bindings[0] and pr["target_refs"] == rs and pr["original_signature"] == sig and not pr["extra_hypotheses"] and pr["rename_spans"] == [[x,y] for x,y,_ in renames]
check("three_actual_Sol_reference_and_request_splices_exact_without_new_premises",True,{"original_proofs_per_Sol":21,"cross_proofs_per_Sol":len(helpers),"wrapper":1,"only_actual_target_binding_and_resolved_refs_renamed":True})
check("three_Sols_use_only_pure_Def_and_Mathlib_imports_and_no_holes",True,{"external_proof_imports":[],"new_axioms":[],"stubs_sorry_only":True})
dreq = load(BATCH/"definitions-request.json")
allowed_d = {"definition_name","definition_title","definition","natural_language_statement","source","tags","env","private"}
allowed_p = {"theorem_name","theorem_title","formal_statement","natural_language_statement","preamble","source","tags"}
check("strict_offline_request_fields_env_and_actual_Def_bytes",len(dreq) == 1 and set(dreq[0]) <= allowed_d and dreq[0]["definition"] == definition and dreq[0]["definition_name"] == "ZetaNine_CoefficientMapSummation" and dreq[0]["env"] == REV and dreq[0]["private"] is False and set(request) == {"env","private","problems"} and request["env"] == REV and request["private"] is False and len(request["problems"]) == len(plan["targets"]) == 3 and all(set(p) <= allowed_p and 0 < len(p["theorem_title"]) <= 200 for p in request["problems"]),{"API_called":False})
nl = [p["natural_language_statement"] for p in request["problems"]]
check("strong_absolute_even_HasSum_and_integer_quartic_domains_in_prose", all(text in nl[i] for i,text in [(0,"No Even n premise"),(0,"stronger degree gap"),(0,"divergent harmonic"),(1,"Let $n$ be even"),(1,"genuine HasSum"),(1,"no HasSum"),(1,"totalized Lean tsum"),(2,"n\\ge2"),(2,"degree at most4"),(2,"Integer W is not a claim")]), "Absolute convergence has Strong without Even; actual odd-zeta HasSum keeps Even; integer quartic keeps even n>=2 and degree<=4.")
old_math = TASK/"verification/formalization-coefficient-map-summation-independent-2026-10-04/independent-review.json"
math = load(old_math)
check("independent_native_mathematical_review_exact_hash_and_scope",sha(old_math) == "fb0d4a09e3273fe430688521771ea582463d31cd98caf50764a7498293c040fa" and math["verdict"] == "PASS" and len(math["checks"]) == 16,old_math.relative_to(TASK).as_posix())
check("all_94_prior_native_math_review_bindings_unchanged",len(math["stable_files"])==94 and all(sha(ROOT/r["root_relative"])==r["sha256"] and (ROOT/r["root_relative"]).stat().st_size==r["bytes"] for r in math["stable_files"]),{"prior_cache_only_hash_bound_not_used_as_our_objects":True})
check("bound_parent_root_install_build_and_check_evidence_unchanged",all(sha(BATCH/n) == h for n,h in ROOT_EVIDENCE.items()),ROOT_EVIDENCE)
copyplan, install = load(BATCH/"root-copy-plan.json"),load(BATCH/"root-install-receipt.json")
root_paths = []
for row in copyplan["files"]:
    staged,root = TASK/row["staged_task_relative"],ROOT/row["root_relative_destination"]
    assert root.read_bytes() == staged.read_bytes() and sha(root) == row["sha256"] and root.stat().st_size == row["bytes"]
    root_paths.append(root)
for row in copyplan["required_existing_Definitions"]:
    root,staged = ROOT/row["root_relative"],TASK/row["task_relative"]
    assert root.read_bytes() == staged.read_bytes() and sha(root) == row["sha256"]
    root_paths.append(root)
check("seven_installed_root_modules_and_seven_existing_Defs_match_stage",len(copyplan["files"]) == 7 and len(copyplan["required_existing_Definitions"]) == 7 and install["frozen_author_audit_sha256"] == CONTROLS["author-audit.json"] and install["frozen_root_copy_plan_sha256"] == CONTROLS["root-copy-plan.json"] and install["root_bytes_match_frozen_stage"] and install["results"] == {"check":1,"build":0},{"root_paths":[p.relative_to(ROOT).as_posix() for p in root_paths]})
build = (BATCH/"task-build.log").read_text(encoding="utf-8-sig")
match = re.search(r"Build completed successfully \((\d+) jobs\)\.",build)
assert match is not None
jobs = int(match.group(1))
check("parent_supported_scoped_task_build_actual_exit_zero",(BATCH/"task-build-exit.txt").read_text().strip() == "0" and jobs == root_enrollment["observed_build_jobs"] and all("Sol_ZetaNine_CoefficientMapSummation_"+n in build for n in TARGETS),{"root_build_role":"parent scoped type integration; separate fresh actual proof audit","jobs":jobs})
scope = load(TASK/"scope.json")
check("all_three_new_Sols_owned_by_current_task_build",all("Solutions/Sol_ZetaNine_CoefficientMapSummation_"+n+".lean" in scope["build"] for n in TARGETS),{"scope_not_modified_or_hashed":True})
issues = [s for s in (BATCH/"task-check.log").read_text(encoding="utf-8-sig").splitlines() if s.strip()]
check("workspace_check_only_two_preexisting_other_mission_entries",(BATCH/"task-check-exit.txt").read_text().strip() == "1" and len(issues) == 2 and all("Sol_TaoFivePrimes_" in s and "Unassigned solution" in s for s in issues),issues)
old_manifests,old_counts = [],[]
for batch in ["coefficient-map","coefficient-map-jet","coefficient-map-injectivity","coefficient-map-partial-fractions","coefficient-map-reflection","coefficient-map-finite-sum"]:
    m = TASK/"formalization/platform"/batch/"SHA256SUMS.txt"
    ls = [line.split("  ",1) for line in m.read_text(encoding="utf-8-sig").splitlines() if line.strip()]
    assert all(sha(m.parent/n) == h for h,n in ls)
    old_counts.append(len(ls)); old_manifests.append(m)
check("all_907_prior_platform_freeze_members_unchanged",old_counts == [96,111,134,174,172,220],old_counts)
failure = load(BATCH/"root-install-attempt-01-failure.json")
check("parent_initial_path_gate_failure_preserved_separate_from_success",failure["actual_exit_code"]==1 and failure["failed_before_copy_or_scope_change"] and not failure["mathematical_or_Lean_failure"] and failure["excluded_from_success_evidence"] and failure["correct_review"]==old_math.relative_to(TASK).as_posix(),{"failure_file":"root-install-attempt-01-failure.json","final_native_review_path_is_correct":True,"failure_not_success_evidence":True})
prior_reviews = {
    "coefficient-map-reflection":"954a72aeed9af3188e62ed16030cdae9212da68d3c1d93eb6b75c2e854d50241",
    "coefficient-map-finite-sum":"dea9dff29978c2576d9a3955bf7aa4a265a70edb60e4b6a9a7f9acd31815df50"}
for batch,h in prior_reviews.items():
    p=TASK/"formalization/platform"/batch/"independent/independent-integration-review.json"
    prior=load(p)
    assert sha(p)==h and prior["verdict"]=="PASS"
    assert all(sha(ROOT/r["root_relative"])==r["sha256"] and (ROOT/r["root_relative"]).stat().st_size==r["bytes"] for r in prior["stable_files"])
check("two_earlier_independent_transplant_freezes_unchanged",True,prior_reviews)
write(OUT/"mechanical-checks.json",{"checks":checks,"author_frozen_controls":CONTROLS,"root_evidence_sha256":ROOT_EVIDENCE,"actual_core_declarations":core,"actual_cross_helpers":helpers,"actual_core_closure":sorted(reached),"root_paths":[p.relative_to(ROOT).as_posix() for p in root_paths],"old_frozen_manifests":[p.relative_to(ROOT).as_posix() for p in old_manifests],"complete":True,"actual_type_proof_checks_pending":True})
print("Mechanical review PASS: "+str(len(checks))+" checks")
