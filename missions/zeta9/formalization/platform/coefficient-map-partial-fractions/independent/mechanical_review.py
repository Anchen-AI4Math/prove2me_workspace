"""Independent frozen-byte, actual-oracle splice, request and root audit."""
from pathlib import Path
import hashlib
import json
import re

OUT = Path(__file__).resolve().parent
BATCH = OUT.parent
TASK = OUT.parents[3]
ROOT = TASK.parents[1]
NS = "ZetaNine.CoefficientMapPartialFractions"
REV = "0df444a360eaa60ab8c11dca51a86af692955474"
CONTROLS = {
    "author-audit.json": "d416ad774d2f4a7b599151aef4f460a42395f116cf5e13d577d311ca2a9aa20f",
    "root-copy-plan.json": "6d60147f78b8463471c32fb257c9fd3fbad22c970733487c469dfb821650b847",
    "source-manifest.json": "7ee6aa8437cdaa046a3a24f2e9c0f0033e89a51fc64b389ba992d342ad104208",
    "SHA256SUMS.txt": "f59940eca0b4b749bd363bc46b7b9fb99b79f1faf3022c2ae82b0d802992d32d"}
ROOT_EVIDENCE = {"root-install-receipt.json": "b505753655cd87c6b0d63d9fbeababe97c718e08daf367aac73599349d8ac10d",
    "task-build.log": "b5e4c7d473b5a12a5ac00ae4665e2df849c09add09fc3ea8be775ee30d7e2218",
    "task-build-exit.txt": "13bf7b3039c63bf5a50491fa3cfd8eb4e699d1ba1436315aef9cbe5711530354",
    "task-check.log": "01a8be04d7e8271bbb089327220d24f487ddca4d688419fd1bcead7f081a02bb",
    "task-check-exit.txt": "f1b2f662800122bed0ff255693df89c4487fbdcf453d3524a42d4ec20c3d9c04"}
TARGETS = ["candidate_local_coefficients", "actual_global_polynomial_partial_fractions", "actual_global_partial_fractions"]
ARGS = ["n j s W hj hs1 hs9", "n W hproper", "n W hproper t hregular"]
DEF_NAMES = ["clearedPolePolynomial", "localTruncation", "partialBlock", "partialNumerator", "candidateClearedSeries"]
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def load(path): return json.loads(path.read_text(encoding="utf-8-sig"))
def rows(path): return [json.loads(s) for s in path.read_text(encoding="utf-8-sig").splitlines() if s.startswith("{")]
def write(path, obj): path.write_text(json.dumps(obj, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
def lean_code(text): return re.sub(r"--[^\n]*", "", re.sub(r"/\-.*?\-/", "", text, flags=re.S))
def edit(data, edits):
    bound = len(data)
    for a,b,value in sorted(set(edits), reverse=True):
        assert 0 <= a <= b <= bound
        data = data[:a] + value + data[b:]
        bound = a
    return data
checks = []
def check(name, passed, detail):
    checks.append({"name": name, "pass": bool(passed), "detail": detail})
    assert passed, name
check("fixed_author_controls_match_parent_freeze", all(sha(BATCH / n) == h for n,h in CONTROLS.items()), CONTROLS)
manifest = load(BATCH / "source-manifest.json")
check("all_172_manifest_members_and_174_SHA_entries_unchanged", len(manifest["files"]) == 172 and
    all(sha(TASK / r["task_relative"]) == r["sha256"] and (TASK / r["task_relative"]).stat().st_size == r["bytes"] for r in manifest["files"]),
    {"manifest_members": 172, "SHA256SUMS_entries":174, "no_independent_files_in_author_freeze": not any("/independent/" in r["task_relative"] for r in manifest["files"])})
sha_lines = [s.split("  ",1) for s in (BATCH / "SHA256SUMS.txt").read_text(encoding="utf-8").splitlines() if s.strip()]
assert len(sha_lines) == 174 and all(sha(BATCH / name) == h for h,name in sha_lines)
prep = load(OUT / "prepare-compile-receipt.json")
check("frozen_four_actual_sources_and_three_existing_Definitions", all(sha(TASK / ("formalization/" + n + ".lean")) == h for n,h in prep["original_sources_sha256"].items()) and
    all(sha(ROOT / ("Definitions/" + n + ".lean")) == h for n,h in prep["existing_pure_Def_sources_sha256"].items()),
    {"actual_sources_sha256": prep["original_sources_sha256"], "existing_Def_sha256": prep["existing_pure_Def_sources_sha256"]})
graph, old_graph = [rows(p) for p in [OUT / "native-decl-graph.jsonl", BATCH / "decl_graph.jsonl"]]
def graph_map(rs):
    return {r["name"]: dict(r, typeDeps=sorted(r["typeDeps"]), valueDeps=sorted(r["valueDeps"])) for r in rs}
check("independent_actual_Stage1_across_four_sources_exact", len(graph) == 133 and graph_map(graph) == graph_map(old_graph),
    {"records": 133, "dependency_arrays_compared_as_sets": True})
byname = {g["name"]: g for g in graph}
sources, facts = {}, {}
for module in prep["original_sources_sha256"]:
    sources[module] = (OUT / (module + "-native-snapshot.lean")).read_bytes()
    old_source = BATCH / ("oracle-input.lean" if module.endswith("PartialFractions") else module + "-oracle-input.lean")
    old_facts = BATCH / ("sketch_info.jsonl" if module.endswith("PartialFractions") else module + "-sketch_info.jsonl")
    facts[module] = rows(OUT / (module + "-native-facts.jsonl"))
    assert sources[module] == old_source.read_bytes() == (TASK / ("formalization/" + module + ".lean")).read_bytes()
    assert facts[module] == rows(old_facts)
check("independent_actual_four_Stage2_snapshots_and_ref_spans_exact", True,
    {module: {kind: sum(f["kind"] == kind for f in facts[module]) for kind in ["decl","ref","command"]} for module in facts})
header = rows(OUT / "native-header.jsonl")
assert header == rows(BATCH / "header_info.jsonl") and len(header) == 1
source = sources["CoefficientMapPartialFractions"]
he = header[0]["end"]["offset"]
check("actual_Stage2_header_exact_two_original_imports", header[0]["start"]["offset"] == 0 and
    source[:he].decode().strip().splitlines() == ["import missions.zeta9.formalization.CoefficientMapInjectivity", "import Mathlib.RingTheory.PowerSeries.Trunc"], header[0])
def declaration(name):
    g = byname[name]
    ds = [f for f in facts[g["module"].split(".")[-1]] if f["kind"] == "decl" and f["declStart"]["line"] <= g["startLine"] <= f["declEnd"]["line"]]
    assert g["startLine"] > 0 and len(ds) == 1 and ds[0]["valStart"] is not None
    return ds[0]
core = [g for g in graph if g["module"].endswith(".CoefficientMapPartialFractions") and g["startLine"] > 0]
reached, work = set(), [g["name"] for g in core] + [g["name"] for g in graph if g["isInstance"]]
while work:
    name = work.pop()
    if name in reached: continue
    reached.add(name)
    work.extend(byname[name]["typeDeps"] + byname[name]["valueDeps"])
bridge, helpers, helper_facts = "", [], []
for module in ["CoefficientMap", "CoefficientMapJet", "CoefficientMapInjectivity"]:
    hs = sorted([byname[n] for n in reached if byname[n]["module"].endswith("." + module) and byname[n]["kind"] == "theorem" and byname[n]["startLine"] > 0], key=lambda g:g["startLine"])
    if not hs: continue
    bridge += "open scoped BigOperators\nopen Finset Polynomial\n\nnamespace ZetaNine." + module + "\n\n"
    for g in hs:
        f = declaration(g["name"])
        bridge += sources[module][f["declStart"]["offset"]:f["declEnd"]["offset"]].decode() + "\n\n"
        helpers.append(g["name"])
        helper_facts.append({"module": module, "name": g["name"], "fact": f})
    bridge += "end ZetaNine." + module + "\n\n"
prov = load(BATCH / "integration-provenance.json")
check("real_cross_source_closure_and_all_15_proof_splices_exact", len(core) == 32 and len(helpers) == 15 and
    sorted(reached) == prov["cross_module_core_closure"] and helpers == prov["inline_helper_names"] and helper_facts == prov["inline_helper_facts"] and
    bridge.encode() == (BATCH / "actual-proof-bridge.lean.inc").read_bytes(),
    {"all_source_defs": 5, "all_source_proofs": 27, "cross_helpers": helpers, "no_spanless_declaration_copied": True,
     "all_instance_roots_from_actual_Stage1_flags": True})
dfacts = [declaration(NS + "." + n) for n in DEF_NAMES]
assert dfacts == prov["definition_facts"]
definition = "import Definitions.Def_ZetaNine_CoefficientMapInjectivity\nimport Mathlib.RingTheory.PowerSeries.Trunc\n\nset_option autoImplicit false\nnoncomputable section\nopen scoped BigOperators\nopen Finset Polynomial\n\nnamespace " + NS + "\n\n"
definition += "\n\n".join(source[f["declStart"]["offset"]:f["declEnd"]["offset"]].decode() for f in dfacts) + "\n\nend " + NS + "\n"
check("pure_five_actual_Def_spans_reconstructed_exactly", definition.encode() == (BATCH / "staged/Definitions/Def_ZetaNine_CoefficientMapPartialFractions.lean").read_bytes() and
    len([g for g in core if g["kind"] == "def"]) == 5 and not re.search(r"\b(theorem|lemma|axiom|sorry|admit)\b", lean_code(definition)), DEF_NAMES)
pf_facts = facts["CoefficientMapPartialFractions"]
refs = [f for f in pf_facts if f["kind"] == "ref"]
diagnostics = [f for f in pf_facts if f["kind"] == "command" and f["syntaxKind"] == "Lean.Parser.Command.printAxioms"]
cuts = [(f["declStart"]["offset"], f["declEnd"]["offset"], b"") for f in dfacts] + [(f["span"]["start"]["offset"], f["span"]["end"]["offset"], b"") for f in diagnostics] + [(0,he,b"")]
assert len(diagnostics) == 12 and diagnostics == prov["deleted_diagnostic_facts"]
preamble = "import Definitions.Def_ZetaNine_CoefficientMapPartialFractions\n\nset_option autoImplicit false\nopen scoped BigOperators\nopen Finset Polynomial\nopen ZetaNine " + NS + " ZetaNine.CoefficientMapInjectivity\n"
solheader = "import Definitions.Def_ZetaNine_CoefficientMapPartialFractions\nimport Mathlib.Tactic\nimport Mathlib.RingTheory.PowerSeries.Trunc\n\n" + bridge
problem_request = load(BATCH / "problems-request.json")
for i,short in enumerate(TARGETS):
    full = NS + "." + short
    d = declaration(full)
    a,v = d["declStart"]["offset"], d["valStart"]["offset"]
    rs = [r for r in refs if r["const"] == full]
    bindings = [r for r in rs if a <= r["start"]["offset"] < v]
    assert len(bindings) == 1
    bs,be = bindings[0]["start"]["offset"], bindings[0]["end"]["offset"]
    assert source[bs:be].decode() == short
    sig = source[be:v].decode()
    renames = []
    for r in rs:
        x,y = r["start"]["offset"],r["end"]["offset"]
        if any(ca <= x and y <= cb for ca,cb,_ in cuts): continue
        old = source[x:y].decode()
        assert old in [short,full]
        renames.append((x,y,("checked_"+short if old == short else NS+".checked_"+short).encode()))
    sol = solheader + "\n" + edit(source,cuts + renames).decode() + "\n\nopen ZetaNine " + NS + " ZetaNine.CoefficientMapInjectivity\n\ntheorem solution" + sig + ":= by\n  exact " + NS + ".checked_" + short + " " + ARGS[i] + "\n\n#print axioms solution\n"
    solpath = BATCH / ("staged/Solutions/Sol_ZetaNine_CoefficientMapPartialFractions_" + short + ".lean")
    assert sol.encode() == solpath.read_bytes()
    assert not re.search(r"\b(sorry|admit|axiom|unsafe)\b", lean_code(sol))
    assert not re.search(r"(?m)^import (Theorems|Solutions|missions)\.", sol)
    formal_edits = [(bs-a,be-a,full.encode())]
    if d["docstring"]:
        ds = d["docstring"]
        formal_edits.append((ds["start"]["offset"]-a,ds["end"]["offset"]-a,b""))
    formal = edit(source[a:v], formal_edits).decode().strip() + ":= by sorry"
    ref = preamble + "\n" + formal + "\n"
    refpath = BATCH / ("staged/Theorems/Thm_ZetaNine_CoefficientMapPartialFractions_" + short + ".lean")
    assert ref.encode() == refpath.read_bytes()
    req = problem_request["problems"][i]
    assert req["formal_statement"] == formal and req["preamble"] == preamble and req["theorem_name"] == full
    pt = prov["targets"][full]
    assert pt["declaration_fact"] == d and pt["binding_fact"] == bindings[0] and pt["target_refs"] == rs and pt["original_signature"] == sig and not pt["extra_hypotheses"]
    assert pt["rename_spans"] == [[x,y] for x,y,_ in renames]
check("all_three_actual_parser_Sol_ref_request_splices_exact", True,
    {"target_roots": TARGETS, "proofs_per_Sol": 43, "source_proofs_per_Sol": 27, "cross_proofs_per_Sol": 15,
     "removed_defs": 5, "removed_actual_diagnostic_commands": 12, "extra_hypotheses": [], "own_target_reference_renames_only": True})
check("canonical_solutions_have_no_holes_or_external_proof_imports", not prov["new_external_theorem_boundaries"],
    {"Theorems_imports": [], "Solutions_imports": [], "native_mission_imports": [], "sorryAx_allowed_in_reference_stubs_only": True})
defs_req = load(BATCH / "definitions-request.json")
allowed_definition = {"definition_name","definition_title","definition","natural_language_statement","source","tags","env","private"}
allowed_problem = {"theorem_name","theorem_title","formal_statement","natural_language_statement","preamble","source","tags"}
check("strict_documented_offline_request_schema_and_definition_bytes", len(defs_req) == 1 and set(defs_req[0]) <= allowed_definition and
    defs_req[0]["definition"] == definition and defs_req[0]["definition_name"] == "ZetaNine_CoefficientMapPartialFractions" and
    defs_req[0]["env"] == REV and defs_req[0]["private"] is False and set(problem_request) == {"env","private","problems"} and
    problem_request["env"] == REV and problem_request["private"] is False and len(problem_request["problems"]) == 3 and
    all(set(p) <= allowed_problem and p["formal_statement"].endswith(":= by sorry") and p["source"] and p["theorem_title"] for p in problem_request["problems"]),
    {"documentation_read": "readback-2026-10-03/api-docs/references/contribute.md", "API_called": False})
nl = [p["natural_language_statement"] for p in problem_request["problems"]]
check("prose_states_actual_nine_coefficients_proper_regular_and_simple_pole_limits", "properness" in nl[0] and "outside" in nl[0] and
    "Strict properness is essential" in nl[1] and "X^5" in nl[1] and "t+k" in nl[2] and "X^4" in nl[2] and "simple pole" in nl[2] and
    "invertibility" in nl[2] and all("arbitrary coefficient" not in p or "neither" in p or "nor" in p for p in nl),
    "Candidate local match has no proper input; polynomial and regular-Q global identities retain strict properness. n0X4 simple1/t is allowed; n0X5 is excluded. Infinite L and aggregate F conclusions are explicitly excluded.")
check("root_install_receipt_build_and_check_evidence_hash_bound", all(sha(BATCH / n) == h for n,h in ROOT_EVIDENCE.items()), ROOT_EVIDENCE)
plan, install = load(BATCH / "root-copy-plan.json"), load(BATCH / "root-install-receipt.json")
assert plan["source_sha256"] == prep["original_sources_sha256"]["CoefficientMapPartialFractions"]
root_paths = []
for r in plan["files"]:
    staged, root = TASK / r["staged_task_relative"], ROOT / r["root_relative_destination"]
    assert root.read_bytes() == staged.read_bytes() and sha(root) == r["sha256"] and root.stat().st_size == r["bytes"]
    root_paths.append(root)
for r in plan["required_existing_Definitions"]:
    root, staged = ROOT / r["root_relative"], TASK / r["task_relative"]
    assert root.read_bytes() == staged.read_bytes() and sha(root) == r["sha256"]
    root_paths.append(root)
check("seven_installed_root_modules_and_three_existing_Defs_identical_to_stage", len(plan["files"]) == 7 and
    install["frozen_author_audit_sha256"] == CONTROLS["author-audit.json"] and install["frozen_root_copy_plan_sha256"] == CONTROLS["root-copy-plan.json"] and
    install["root_bytes_match_frozen_stage"] and install["results"] == {"check":1,"build":0},
    {"root_paths": [p.relative_to(ROOT).as_posix() for p in root_paths], "reviewer_root_writes": False})
build_text = (BATCH / "task-build.log").read_text(encoding="utf-8-sig")
check("parent_observed_supported_task_build_exit_zero", int((BATCH / "task-build-exit.txt").read_text().strip()) == 0 and
    "Build completed successfully (3768 jobs)." in build_text and all("Sol_ZetaNine_CoefficientMapPartialFractions_" + name in build_text for name in TARGETS),
    {"execution_role": "parent ran supported scoped task build; reviewer verifies bound stable log/exit and installed bytes",
     "jobs":3768, "root_reference_sorry_is_statement_only":True, "independent_proof_compilation_is_separate":True})
scope = load(TASK / "scope.json")
check("all_three_new_Solutions_have_actual_task_scope_ownership", all("Solutions/Sol_ZetaNine_CoefficientMapPartialFractions_" + n + ".lean" in scope["build"] for n in TARGETS),
    {"scope_read_only":True,"scope_not_hashed":True})
check_text = (BATCH / "task-check.log").read_text(encoding="utf-8-sig")
scope_issues = [s for s in check_text.splitlines() if s.strip()]
check("workspace_check_failure_is_only_two_preexisting_other_mission_entries", int((BATCH / "task-check-exit.txt").read_text().strip()) == 1 and
    len(scope_issues) == 2 and all("Sol_TaoFivePrimes_" in s and "Unassigned solution" in s for s in scope_issues), scope_issues)
old_manifests = []
counts = []
for batch_name in ["coefficient-map", "coefficient-map-jet", "coefficient-map-injectivity"]:
    mpath = TASK / ("formalization/platform/" + batch_name + "/SHA256SUMS.txt")
    lines = [s.split("  ",1) for s in mpath.read_text(encoding="utf-8").splitlines() if s.strip()]
    for h,path in lines:
        candidate = mpath.parent / path
        if not candidate.exists(): candidate = TASK / path
        assert sha(candidate) == h
    counts.append(len(lines))
    old_manifests.append(mpath)
check("all_341_previous_platform_frozen_members_unchanged", counts == [96,111,134], {"counts":counts, "manifest_hashes":{p.relative_to(TASK).as_posix():sha(p) for p in old_manifests}})
write(OUT / "mechanical-checks.json", {"checks": checks, "actual_core_declarations": core, "actual_cross_helpers": helpers,
    "actual_native_reachability": sorted(reached), "author_frozen_controls":CONTROLS,"root_evidence_sha256":ROOT_EVIDENCE,
    "root_paths":[p.relative_to(ROOT).as_posix() for p in root_paths],"old_frozen_manifests":[p.relative_to(ROOT).as_posix() for p in old_manifests],
    "final_type_and_proof_audit_pending":True})
print("Mechanical independent checks PASS: " + str(len(checks)))
