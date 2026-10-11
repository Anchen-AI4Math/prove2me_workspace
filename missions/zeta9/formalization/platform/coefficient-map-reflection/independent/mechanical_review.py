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
NS = "ZetaNine.CoefficientMapReflection"
REV = "0df444a360eaa60ab8c11dca51a86af692955474"
CONTROLS = {
    "author-audit.json": "7d48c5b7197fc9d9543b35063c256aa73bea606a59866ea81df227f731105651",
    "root-copy-plan.json": "d8a5022833267eba1884f519a2f61b80343dfae4f53820e80ae57c2c9a6e5ad6",
    "source-manifest.json": "fe3ec5bf2de4944eb186c72ad299c1b52e51fbe04f9b68f512253d4e34d9812a",
    "SHA256SUMS.txt": "d7e497dd9e6d69f538dd77390b4b516c0ec8ecdbcb93cdc1eb5a3490e93eaba3"}
ROOT_EVIDENCE = {
    "root-install-receipt.json":"74d3236310cb0bacc07d7faa33fc3c495629e8545cc932d13d51cc0cd6e847f4",
    "task-build.log":"311587c53ac92e1030be459b1c537cd03520f253d8365e7df3a119658420baab",
    "task-build-exit.txt":"13bf7b3039c63bf5a50491fa3cfd8eb4e699d1ba1436315aef9cbe5711530354",
    "task-check.log":"01a8be04d7e8271bbb089327220d24f487ddca4d688419fd1bcead7f081a02bb",
    "task-check-exit.txt":"f1b2f662800122bed0ff255693df89c4487fbdcf453d3524a42d4ec20c3d9c04"}
TARGETS = ["local_coefficient_reflection", "rho_even_order_zero", "rho_one_zero_of_strong_proper"]
DEF_NAMES = ["reflectionVariable", "rho", "StrongProperMultiplier", "partialBasis"]

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

check("fixed_four_author_controls_match", all(sha(BATCH/n) == h for n,h in CONTROLS.items()), CONTROLS)
manifest = load(BATCH / "source-manifest.json")
check("all_170_manifest_member_bytes_and_hashes_match", len(manifest["files"]) == 170 and all(
    sha(TASK/r["task_relative"]) == r["sha256"] and (TASK/r["task_relative"]).stat().st_size == r["bytes"] for r in manifest["files"]),
    {"members":170,"independent_files_frozen_by_author":False})
sha_lines = [line.split("  ",1) for line in (BATCH/"SHA256SUMS.txt").read_text(encoding="utf-8-sig").splitlines() if line.strip()]
check("all_172_SHA256SUMS_entries_match", len(sha_lines) == 172 and all(sha(BATCH/n) == h for h,n in sha_lines),172)
prep = load(OUT / "prepare-compile-receipt.json")
check("five_actual_sources_and_four_pure_Defs_match_fixed_hashes", all(sha(TASK/("formalization/"+n+".lean")) == h for n,h in prep["original_sources_sha256"].items()) and
    all(sha(ROOT/("Definitions/"+n+".lean")) == h for n,h in prep["existing_pure_Def_sources_sha256"].items()),
    {"sources":prep["original_sources_sha256"],"Defs":prep["existing_pure_Def_sources_sha256"]})
graph = rows(OUT / "native-decl-graph.jsonl")
def normalized_graph(rs): return {r["name"]:dict(r,typeDeps=sorted(r["typeDeps"]),valueDeps=sorted(r["valueDeps"])) for r in rs}
check("fresh_actual_Stage1_169_records_equal_frozen_graph", len(graph) == 169 and normalized_graph(graph) == normalized_graph(rows(BATCH/"decl_graph.jsonl")),169)
by_name = {g["name"]:g for g in graph}
sources, facts = {}, {}
for module in prep["original_sources_sha256"]:
    sources[module] = (OUT/(module+"-native-snapshot.lean")).read_bytes()
    old_input = "oracle-input.lean" if module == "CoefficientMapPartialFractions" else module+"-oracle-input.lean"
    old_facts = "CoefficientMapReflection-sketch_info.jsonl" if module == "CoefficientMapReflection" else "sketch_info.jsonl" if module == "CoefficientMapPartialFractions" else module+"-sketch_info.jsonl"
    facts[module] = rows(OUT/(module+"-native-facts.jsonl"))
    assert sources[module] == (BATCH/old_input).read_bytes() == (TASK/("formalization/"+module+".lean")).read_bytes()
    assert facts[module] == rows(BATCH/old_facts)
check("all_five_actual_Stage2_input_and_command_decl_ref_spans_equal", True,
    {m:{k:sum(f["kind"] == k for f in fs) for k in ["decl","ref","command"]} for m,fs in facts.items()})
header = rows(OUT / "native-header.jsonl")
source = sources["CoefficientMapReflection"]
assert len(header) == 1 and header == rows(BATCH/"header_info.jsonl")
he = header[0]["end"]["offset"]
check("actual_Reflection_parser_header_is_only_actual_PF_import", source[:he].decode().strip() == "import missions.zeta9.formalization.CoefficientMapPartialFractions", header[0])

def declaration(name):
    g = by_name[name]
    ds = [f for f in facts[g["module"].split(".")[-1]] if f["kind"] == "decl" and f["declStart"]["line"] <= g["startLine"] <= f["declEnd"]["line"]]
    assert g["startLine"] > 0 and len(ds) == 1 and ds[0]["valStart"] is not None
    return ds[0]

core = [g for g in graph if g["module"].endswith(".CoefficientMapReflection") and g["startLine"] > 0]
reached, work = set(), [g["name"] for g in core] + [g["name"] for g in graph if g["isInstance"]]
while work:
    name = work.pop()
    if name in reached: continue
    reached.add(name)
    work.extend(by_name[name]["typeDeps"] + by_name[name]["valueDeps"])
prov = load(BATCH / "integration-provenance.json")
bridge, helpers, helper_facts, opens = "", [], [], []
for module in ["CoefficientMap","CoefficientMapJet","CoefficientMapInjectivity","CoefficientMapPartialFractions"]:
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
check("actual_34_cross_helpers_and_entire_core_closure_exact", len(core) == 34 and len(helpers) == 34 and helpers == prov["inline_helper_names"] and
    helper_facts == prov["inline_helper_facts"] and sorted(reached) == prov["cross_module_core_closure"],
    {"source_defs":4,"source_proofs":30,"cross_helpers":helpers})
check("ten_real_parser_open_context_spans_and_bridge_bytes_exact", len(opens) == 10 and opens == prov["bridge_open_context_facts"] and bridge.encode() == (BATCH/"actual-proof-bridge.lean.inc").read_bytes(),opens)
check("actual_graph_has_no_axiom_or_unproved_external_boundary", not any(g["kind"] == "axiom" for g in graph) and not prov["new_external_theorem_boundaries"])

dfacts = [declaration(NS+"."+n) for n in DEF_NAMES]
first_def = min(f["declStart"]["offset"] for f in dfacts)
def_opens = [f for f in facts["CoefficientMapReflection"] if f["kind"] == "command" and f["syntaxKind"] == "Lean.Parser.Command.open" and f["span"]["end"]["offset"] < first_def]
check("four_Def_spans_and_three_actual_open_spans_exact", dfacts == prov["definition_facts"] and len(def_opens) == 3 and def_opens == prov["definition_open_context_facts"])
definition = "import Definitions.Def_ZetaNine_CoefficientMapPartialFractions\n\n\nset_option autoImplicit false\nnoncomputable section\nopen scoped BigOperators\nopen Finset Polynomial\n\nnamespace "+NS+"\n\n"
definition += "\n".join(source[f["span"]["start"]["offset"]:f["span"]["end"]["offset"]].decode() for f in def_opens)+"\n\n"
definition += "\n\n".join(source[f["declStart"]["offset"]:f["declEnd"]["offset"]].decode() for f in dfacts)+"\n\nend "+NS+"\n"
check("lightweight_four_actual_Def_reconstructed_bytes_exact", definition.encode() == (BATCH/"staged/Definitions/Def_ZetaNine_CoefficientMapReflection.lean").read_bytes() and not re.search(r"\b(theorem|lemma|axiom|sorry|admit)\b",lean_code(definition)),DEF_NAMES)
reflection_facts = facts["CoefficientMapReflection"]
refs = [f for f in reflection_facts if f["kind"] == "ref"]
diagnostics = [f for f in reflection_facts if f["kind"] == "command" and f["syntaxKind"] == "Lean.Parser.Command.printAxioms"]
assert len(diagnostics) == 11 and diagnostics == prov["deleted_diagnostic_facts"]
cuts = [(f["declStart"]["offset"],f["declEnd"]["offset"],b"") for f in dfacts]+[(f["span"]["start"]["offset"],f["span"]["end"]["offset"],b"") for f in diagnostics]+[(0,he,b"")]
plan = load(BATCH/"target-plan.json")
request = load(BATCH/"problems-request.json")
preamble = "import Definitions.Def_ZetaNine_CoefficientMapReflection\n\nset_option autoImplicit false\nopen scoped BigOperators\nopen Finset Polynomial\nopen ZetaNine "+NS+" ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions\n"
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
    sol = "import Definitions.Def_ZetaNine_CoefficientMapReflection\nimport Mathlib.Tactic\n\n\n"+bridge+"\n"+edit(source,cuts+renames).decode()+"\n\nopen ZetaNine "+NS+" ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions\n\ntheorem solution"+sig+":= by\n  exact "+NS+".checked_"+short+" "+plan["targets"][i]["wrapper_arguments"]+"\n\n#print axioms solution\n"
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
check("three_actual_Sol_reference_and_request_splices_exact_without_new_premises",True,{"original_proofs_per_Sol":30,"cross_proofs_per_Sol":34,"wrapper":1,"only_actual_target_binding_and_resolved_refs_renamed":True})
check("three_Sols_use_only_pure_Def_and_Mathlib_imports_and_no_holes",True,{"external_proof_imports":[],"new_axioms":[],"stubs_sorry_only":True})
dreq = load(BATCH/"definitions-request.json")
allowed_d = {"definition_name","definition_title","definition","natural_language_statement","source","tags","env","private"}
allowed_p = {"theorem_name","theorem_title","formal_statement","natural_language_statement","preamble","source","tags"}
check("strict_offline_request_fields_env_and_actual_Def_bytes",len(dreq) == 1 and set(dreq[0]) <= allowed_d and dreq[0]["definition"] == definition and dreq[0]["definition_name"] == "ZetaNine_CoefficientMapReflection" and dreq[0]["env"] == REV and dreq[0]["private"] is False and set(request) == {"env","private","problems"} and request["env"] == REV and request["private"] is False and len(request["problems"]) == len(plan["targets"]) == 3 and all(set(p) <= allowed_p and 0 < len(p["theorem_title"]) <= 200 for p in request["problems"]),{"API_called":False})
nl = [p["natural_language_statement"] for p in request["problems"]]
check("Even_and_Strong_premises_and_zero_odd_boundaries_faithful_in_prose",all(text in nl[i] for i,text in [(0,"$n$ is even"),(1,"$s$ even"),(1,"simple-pole total is one"),(2,"does not require Even n"),(2,"$n=1$"),(2,"proper but not StrongProper")]),"No rho cancellation assumption; proper does not entail Strong. Infinite series and F are excluded from this batch scope.")
old_math = TASK/"verification/formalization-coefficient-map-reflection-2026-10-03/independent-review.json"
math = load(old_math)
check("independent_native_mathematical_review_exact_hash_and_scope",sha(old_math) == "ac3d8f135cb3c69b39074548bea712f418fa6d0273ad27e33805374c1db20123" and math["verdict"] == "PASS" and len(math["checks"]) == 17 and math["rho1_zero_from_strict_proper_alone_closed"] is False and math["original_aggregate_F_injectivity_closed"] is False,old_math.relative_to(TASK).as_posix())
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
check("seven_installed_root_modules_and_four_existing_Defs_match_stage",len(copyplan["files"]) == 7 and len(copyplan["required_existing_Definitions"]) == 4 and install["frozen_author_audit_sha256"] == CONTROLS["author-audit.json"] and install["frozen_root_copy_plan_sha256"] == CONTROLS["root-copy-plan.json"] and install["root_bytes_match_frozen_stage"] and install["results"] == {"check":1,"build":0},{"root_paths":[p.relative_to(ROOT).as_posix() for p in root_paths]})
build = (BATCH/"task-build.log").read_text(encoding="utf-8-sig")
check("parent_supported_scoped_task_build_actual_exit_zero_3775_jobs",(BATCH/"task-build-exit.txt").read_text().strip() == "0" and "Build completed successfully (3775 jobs)." in build and all("Sol_ZetaNine_CoefficientMapReflection_"+n in build for n in TARGETS),{"root_build_role":"parent scoped type integration; separate fresh actual proof audit","jobs":3775})
scope = load(TASK/"scope.json")
check("all_three_new_Sols_owned_by_current_task_build",all("Solutions/Sol_ZetaNine_CoefficientMapReflection_"+n+".lean" in scope["build"] for n in TARGETS),{"scope_not_modified_or_hashed":True})
issues = [s for s in (BATCH/"task-check.log").read_text(encoding="utf-8-sig").splitlines() if s.strip()]
check("workspace_check_only_two_preexisting_other_mission_entries",(BATCH/"task-check-exit.txt").read_text().strip() == "1" and len(issues) == 2 and all("Sol_TaoFivePrimes_" in s and "Unassigned solution" in s for s in issues),issues)
old_manifests,old_counts = [],[]
for batch in ["coefficient-map","coefficient-map-jet","coefficient-map-injectivity","coefficient-map-partial-fractions"]:
    m = TASK/"formalization/platform"/batch/"SHA256SUMS.txt"
    ls = [line.split("  ",1) for line in m.read_text(encoding="utf-8-sig").splitlines() if line.strip()]
    assert all(sha(m.parent/n) == h for h,n in ls)
    old_counts.append(len(ls)); old_manifests.append(m)
check("all_515_prior_platform_freeze_members_unchanged",old_counts == [96,111,134,174],old_counts)
failed = load(BATCH/"audit-gate-failed-attempt.json")
check("author_snapshot_gate_failure_preserved_separately",failed["verdict"] == "FAIL" and failed["actual_proof_source_modified"] is False and sha(BATCH/"audit_and_freeze.py.before-splice-oracle-fix") == failed["original_audit_script_sha256"],{"failed_gate_not_success_evidence":True,"correct_Reflection_snapshot_independently_reexecuted":True})
write(OUT/"mechanical-checks.json",{"checks":checks,"author_frozen_controls":CONTROLS,"root_evidence_sha256":ROOT_EVIDENCE,"actual_core_declarations":core,"actual_cross_helpers":helpers,"actual_core_closure":sorted(reached),"root_paths":[p.relative_to(ROOT).as_posix() for p in root_paths],"old_frozen_manifests":[p.relative_to(ROOT).as_posix() for p in old_manifests],"complete":True,"actual_type_proof_checks_pending":True})
print("Mechanical review PASS: "+str(len(checks))+" checks")
