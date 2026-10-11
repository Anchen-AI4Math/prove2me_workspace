"""Independent offline review; no author scripts imported or proof files edited."""
from pathlib import Path
import hashlib
import json
import re
import sys

OUT = Path(__file__).resolve().parent
TASK = OUT.parents[2]
ROOT = TASK.parents[1]
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
REV = "0df444a360eaa60ab8c11dca51a86af692955474"
PNT_ID = "7cfa31c8-4063-4b52-81fc-8b2f2a59495e"
ORIGINAL_HASH = "6c56d052ae48b44e76d40e7a08fcfd6ca8d232b5bc7882430bfbf48b85bb2c8b"
NS = "ZetaNine.HarmonicStability"
NAMES = ["psi_pnt_rate", "harmonic_log_den_rate", "harmonic_nine_double_log_den_rate", "harmonic_perturbed_log_den_rate"]
TARGETS = [NS + "." + name for name in NAMES]
ARGS = ["", "s hs", "", "s hs r hr"]
OBJECTS = sorted(NS + "." + n for n in ["logDen", "harmonicPower", "primeRemainder", "harmonicExceptionalProduct"])
ORDER = ["Solutions.Sol_ZetaNine_HarmonicStability_harmonic_den_dvd_lcm_power", "missions.zeta9.formalization.HarmonicPrimeValuation", "missions.zeta9.formalization.HarmonicAsymptotic", "missions.zeta9.formalization.PNTTransfer"]
checks = []
hashes = {}
findings = []

def load(path):
    return json.loads(path.read_text(encoding="utf-8-sig"))

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def resolve_recorded(path):
    p = Path(path)
    if p.is_absolute():
        return p
    return OUT / p

def freeze(path):
    path = path.resolve()
    root_relative = path.relative_to(ROOT.resolve()).as_posix()
    try:
        task_relative = path.relative_to(TASK.resolve()).as_posix()
    except ValueError:
        task_relative = None
    key = "task:" + task_relative if task_relative else "root:" + root_relative
    hashes[key] = {"sha256": digest(path), "root_relative": root_relative, "task_relative": task_relative}

def equal_hash(path, expected):
    assert digest(path) == expected, str(path)
    freeze(path)

def jsonlines(path):
    return [json.loads(line) for line in path.read_text(encoding="utf-8-sig").splitlines() if line.startswith("{")]

def report_records(path):
    rows = jsonlines(path)
    assert rows, "No actual type rows: " + str(path)
    assert "error:" not in path.read_text(encoding="utf-8-sig"), str(path)
    assert len({r["label"] for r in rows}) == len(rows)
    freeze(path)
    return {r["label"]: r for r in rows}

def check(name, fn):
    try:
        evidence = fn()
        checks.append({"id": name, "pass": True, "evidence": evidence})
    except Exception as exc:
        checks.append({"id": name, "pass": False, "error": repr(exc)})

def splice(data, edits):
    edits = sorted(set(edits), reverse=True)
    edge = len(data)
    for start, end, value in edits:
        assert 0 <= start <= end <= edge
        data = data[:start] + value + data[end:]
        edge = start
    return data

def source_code(text):
    # Lexical guard only; never used to choose mathematical cuts or positions.
    result = []
    i, depth = 0, 0
    while i < len(text):
        if depth:
            if text[i:i+2] == "/-":
                depth += 1
                i += 2
            elif text[i:i+2] == "-/":
                depth -= 1
                i += 2
            else:
                i += 1
        elif text[i:i+2] == "/-":
            depth = 1
            i += 2
        elif text[i:i+2] == "--":
            newline = text.find("\n", i)
            i = len(text) if newline < 0 else newline
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        else:
            result.append(text[i])
            i += 1
    assert depth == 0
    return "".join(result)

request = load(OUT / "problems-request.json")
plan = load(OUT / "decl-plan.json")
provenance = load(OUT / "integration-provenance.json")
original_review = load(OUT / "independent-original-review.json")
readback = load(OUT / "medium-pnt-proved-readback.json")
graph_rows = jsonlines(OUT / "decl-graph.jsonl")
graph = {r["name"]: r for r in graph_rows}
sources, facts, joined, reachable = {}, {}, {}, set()

def original_fidelity():
    assert original_review["verdict"] == "PASS"
    assert original_review["proof_authorship_in_this_review"] is False
    equal_hash(TASK / "formalization/PNTTransfer.lean", ORIGINAL_HASH)
    assert original_review["reviewed_source"]["sha256"] == ORIGINAL_HASH
    for name, expected in original_review["reviewed_hashes"].items():
        # API readback is a saved boundary fact, deliberately excluded from freeze.
        if name.endswith("medium-pnt-proved-readback.json"):
            continue
        base = ROOT if name.startswith(("Definitions/", "Solutions/", "Theorems/")) else TASK
        if name.endswith(".md"):
            assert digest(base / name) == expected
        else:
            equal_hash(base / name, expected)
    freeze(OUT / "independent-original-review.json")
    source = (TASK / "formalization/PNTTransfer.lean").read_text(encoding="utf-8")
    assert "theorem psi_pnt_rate :" in source
    assert "theorem harmonic_log_den_rate (s : ℕ) (hs : 0 < s) :" in source
    assert "(hr : Tendsto (fun N => logDen (r N) / (N : ℝ)) atTop (nhds 0))" in source
    assert "harmonic_perturbed_log_den_rate_of_pnt s hs theta_pnt lcm_pnt r hr" in source
    return {"source_sha256": ORIGINAL_HASH, "actual_objects": True, "positive_fixed_order": True, "full_natural_sequence": True, "real_small_denominator_hr_retained": True, "double_nine_rate": 18, "new_PNT_or_baseline_premises": []}

check("original_statement_and_mathematical_review_fidelity", original_fidelity)

def actual_upstream_replay():
    replay = TASK / "verification/formalization-pnt-dependency-2026-10-02"
    receipt = load(replay / "kernel-replay-receipt.json")
    manifest = load(replay / "kernel-source-manifest.json")
    assert receipt["verdict"] == "PASS" and receipt["build_exit"] == 0
    assert receipt["explicit_statement_audit_exit"] == 0
    assert set(receipt["axioms"]) == STANDARD
    assert receipt["sorryAx_found"] is False
    assert receipt["lean_version"] == "4.33.1" and receipt["mathlib_revision"] == REV
    assert receipt["pnt_commit"] == "55270df807213fc3584523d09e0311d7dc073ff5"
    assert receipt["mathematical_source_edits"] == []
    assert len(manifest["sources"]) == 23
    for row in manifest["sources"]:
        base = replay / ("external" if row["module"].startswith("PrimeNumberTheoremAnd") else "architect")
        equal_hash(base / row["path"], row["sha256"])
        equal_hash(replay / "project" / row["path"], row["sha256"])
    for name, expected in receipt["hashes"].items():
        equal_hash(replay / name, expected)
    freeze(replay / "kernel-replay-receipt.json")
    log = (replay / "kernel-axiom-audit.log").read_text(encoding="utf-8-sig")
    assert "sorryAx" not in log and "checked_medium_pnt" in log
    return {"verified_original_source_modules": 23, "full_replay_repeated": False, "retained_build_jobs": receipt["build_jobs"], "actual_cache_hash": receipt["hashes"]["project/.lake/build/lib/lean/PrimeNumberTheoremAnd/MediumPNT.olean"], "standard_three_axioms": True}

check("actual_original_PNT_cache_and_complete_replay_evidence", actual_upstream_replay)

def parser_closure():
    assert len(graph) == len(graph_rows)
    old_plan = load(OUT / "reachable-local-graph.json")
    instance_roots = [r["name"] for r in graph_rows if r["isInstance"] and r["module"] in old_plan["participating_source_modules"]]
    work = TARGETS + instance_roots
    while work:
        name = work.pop()
        if name in reachable:
            continue
        assert name in graph
        reachable.add(name)
        if name != "MediumPNT":
            work.extend(graph[name]["typeDeps"] + graph[name]["valueDeps"])
    selected = {n: graph[n] for n in reachable if n != "MediumPNT" and graph[n]["startLine"] > 0}
    assert len(reachable) == 56 and len(selected) == 55
    assert plan["reachable_with_boundary"] == 56 and plan["selected_source_declarations"] == 55
    assert set(selected) == set(plan["selected_declarations"])
    assert plan["targets"] == TARGETS and plan["all_instance_roots"] == instance_roots
    receipts = load(OUT / "stage2-extract-receipt.json")
    for row in receipts:
        assert row["exit_code"] == 0
        source = Path(row["source"])
        snapshot = Path(row["oracle_input"])
        equal_hash(source, row["source_sha256"])
        equal_hash(snapshot, row["oracle_input_sha256"])
        assert snapshot.read_bytes() == source.read_bytes().replace(b"\r\n", b"\n")
        module = row["module"]
        sources[module] = snapshot.read_bytes()
        fp = OUT / (module.replace(".", "_") + "-sketch.jsonl")
        facts[module] = jsonlines(fp)
        freeze(fp)
        for kind, count in row["fact_counts"].items():
            assert sum(f["kind"] == kind for f in facts[module]) == count
        for name, decl in selected.items():
            if decl["module"] != module:
                continue
            matches = [f for f in facts[module] if f["kind"] == "decl" and f["declStart"]["line"] <= decl["startLine"] <= f["declEnd"]["line"]]
            assert len(matches) == 1 and matches[0]["valStart"] is not None
            joined[name] = matches[0]
            assert plan["selected_declarations"][name]["graph"] == decl
            assert plan["selected_declarations"][name]["stage2"] == matches[0]
    assert set(joined) == set(selected)
    assert plan["regex_source_position_queries"] is False
    for name in ["decl-graph.jsonl", "reachable-local-graph.json", "stage2-extract-receipt.json", "decl-plan.json", "extract_pnt_decl_graph.lean", "extract_pnt_sketch_info.lean"]:
        freeze(OUT / name)
    return {"independently_recomputed_reachable": 56, "selected_source_declarations": 55, "instance_roots": instance_roots, "actual_oracle_snapshots_verified": len(receipts), "source_positions_from_executed_Lean_parser": True}

check("executed_official_parser_snapshot_and_55_declaration_closure", parser_closure)

def reconstruct_payloads():
    assert joined
    imports = set()
    fragments = []
    for module in ORDER:
        keep = {(joined[n]["declStart"]["offset"], joined[n]["declEnd"]["offset"]) for n in reachable if n in joined and graph[n]["module"] == module and graph[n]["userName"] not in OBJECTS}
        edits = []
        for f in facts[module]:
            if f["kind"] == "decl":
                span = (f["declStart"]["offset"], f["declEnd"]["offset"])
                if span not in keep:
                    edits.append((*span, b""))
            elif f["kind"] == "import":
                if f["module"].startswith("Mathlib."):
                    imports.add(f["module"])
                else:
                    assert f["module"] in ORDER + ["Definitions.Def_ZetaNine_HarmonicStability", "PrimeNumberTheoremAnd.MediumPNT"]
                span = f["span"]
                edits.append((span["start"]["offset"], span["end"]["offset"], b""))
            elif f["kind"] == "command" and f["syntaxKind"] == "Lean.Parser.Command.printAxioms":
                span = f["span"]
                edits.append((span["start"]["offset"], span["end"]["offset"], b""))
        fragments.append(splice(sources[module], edits).decode("utf-8"))
    headers = ["Definitions.Def_ZetaNine_HarmonicStability", "Definitions.Def_ZetaNine_HarmonicPrimeValuation", "Theorems.Thm_MediumPNT"] + sorted(imports)
    core = "\n".join("import " + h for h in headers) + "\n\n" + "\n\n".join(fragments)
    assert (OUT / "proof-core.lean").read_bytes() == core.encode()
    assert headers == provenance["imports"]
    assert [h for h in headers if h.startswith("Theorems.")] == ["Theorems.Thm_MediumPNT"]
    assert not re.search(r"\b(?:sorry|sorryAx|admit|axiom)\b", source_code(core))
    assert "theorem checked_harmonic_den_dvd_lcm_power (s N : ℕ)" in core
    assert "theorem log_den_rate_stability" in core and "theorem log_denominator_stability" in core
    assert "theorem solution" not in source_code(core)
    assert len(request["problems"]) == 4 and request["env"] == REV and request["private"] is False
    assert load(OUT / "definitions-request.json") == []
    assert provenance["extra_pnt_assumptions"] == [] and provenance["new_public_definitions"] == []
    source = sources["missions.zeta9.formalization.PNTTransfer"]
    endpoint_fidelity = []
    for i, p in enumerate(request["problems"]):
        full = p["theorem_name"]
        assert full == TARGETS[i]
        f = joined[full]
        a, b, v = [f[k]["offset"] for k in ["declStart", "declEnd", "valStart"]]
        bindings = [r for r in facts["missions.zeta9.formalization.PNTTransfer"] if r["kind"] == "ref" and r["const"] == full and a <= r["start"]["offset"] < v]
        assert len(bindings) == 1
        binding = bindings[0]
        bs, be = binding["start"]["offset"], binding["end"]["offset"]
        assert source[bs:be].decode() == NAMES[i]
        signature = source[be:v].decode()
        edits = [(bs-a, be-a, full.encode())]
        if f["docstring"]:
            doc = f["docstring"]
            edits.append((doc["start"]["offset"]-a, doc["end"]["offset"]-a, b""))
        formal = splice(source[a:v], edits).decode().strip() + ":= by sorry"
        expected_solution = core + "\n\nopen " + NS + "\n\ntheorem solution" + signature + ":= by\n  exact " + full + (" " + ARGS[i] if ARGS[i] else "") + "\n\n#print axioms solution\n"
        sol, ref = OUT / "staged" / p["local_solution"], OUT / "staged" / p["local_reference"]
        assert p["formal_statement"] == formal
        assert sol.read_bytes() == expected_solution.encode()
        assert ref.read_bytes() == (p["preamble"] + "\n" + formal + "\n").encode()
        assert p["proved_theorem_dependencies"] == [{"theorem_name": "MediumPNT", "theorem_id": PNT_ID}]
        for file, key in [(sol, "solution_sha256"), (ref, "reference_sha256")]:
            equal_hash(file, provenance["targets"][full][key])
        assert provenance["targets"][full]["binding_fact"] == binding
        assert provenance["targets"][full]["stage2_declaration_fact"] == f
        assert not re.search(r"\b(?:sorry|sorryAx|admit|axiom)\b", source_code(sol.read_text(encoding="utf-8")))
        endpoint_fidelity.append({"theorem_name": full, "original_signature_preserved": True, "wrapper_arguments": ARGS[i]})
    for name in ["proof-core.lean", "problems-request.json", "definitions-request.json", "integration-provenance.json", "boundary-policy.json"]:
        freeze(OUT / name)
    return {"proof_core_reconstructed_byte_exactly": True, "all_math_proof_spans_preserved": True, "complete_clearing_and_perturbation_proofs_inline": True, "canonical_Solutions_own_no_sorry_or_axiom": True, "endpoints": endpoint_fidelity}

check("source_span_exact_payloads_and_only_Proved_boundary", reconstruct_payloads)

def type_and_definition_matrix():
    original = report_records(OUT / "types-original.log")
    assert set(original) == set(TARGETS + OBJECTS + ["MediumPNT"])
    native = report_records(OUT / "types-boundary-native.log")["MediumPNT"]
    stub = report_records(OUT / "types-boundary-stub.log")["MediumPNT"]
    assert native["type"] == stub["type"] == original["MediumPNT"]["type"]
    assert set(native["axioms"]) == set(original["MediumPNT"]["axioms"]) == STANDARD
    assert set(stub["axioms"]) == STANDARD | {"sorryAx"}
    assert (readback["theorem_id"], readback["status"], readback["visibility"], readback["mathlib_rev"]) == (PNT_ID, "Proved", "public", REV)
    forward = OUT / "boundary-mirror/native/Theorems/Thm_MediumPNT.lean"
    assert forward.read_bytes() == b"import PrimeNumberTheoremAnd.MediumPNT\n"
    stub_file = OUT / "boundary-mirror/stub/Theorems/Thm_MediumPNT.lean"
    assert readback["formal_statement"] in stub_file.read_text(encoding="utf-8")
    freeze(forward)
    freeze(stub_file)
    rows = []
    for i, p in enumerate(request["problems"]):
        full = p["theorem_name"]
        nr = report_records(OUT / f"types-native-{i}-solution.log")
        sr = report_records(OUT / f"types-stub-{i}-solution.log")
        rr = report_records(OUT / f"types-{i}-reference.log")
        assert set(nr) == set(sr) == set([full, "MediumPNT"] + OBJECTS)
        assert set(rr) == set([full] + OBJECTS)
        assert original[full]["type"] == nr[full]["type"] == sr[full]["type"] == rr[full]["type"]
        assert set(original[full]["axioms"]) == set(nr[full]["axioms"]) == STANDARD
        assert set(sr[full]["axioms"]) == STANDARD | {"sorryAx"}
        assert "sorryAx" in rr[full]["axioms"]
        for obj in OBJECTS:
            for r in [nr[obj], sr[obj], rr[obj]]:
                assert r["type"] == original[obj]["type"]
                assert r["definitionValue"] == original[obj]["definitionValue"]
                assert r["definitionValue"] is not None
                assert set(r["axioms"]) <= STANDARD
        rows.append({"theorem_name": full, "exact_original_native_stub_reference_type_equal": True, "all_four_public_definition_types_and_values_equal": True, "native_axioms": nr[full]["axioms"], "stub_axioms": sr[full]["axioms"]})
    return {"exact_elaborated_type_equality": True, "boundary_native_proof": True, "boundary_stub_is_proof": False, "checks": rows}

check("actual_native_stub_original_reference_types_and_public_definition_values", type_and_definition_matrix)

def independent_actual_compile():
    log = OUT / "independent-native-perturbed.log"
    assert (OUT / "independent-native-perturbed-exit.txt").read_text(encoding="utf-8-sig").strip() == "0"
    text = log.read_text(encoding="utf-8-sig")
    assert "error:" not in text and "sorryAx" not in text
    assert "'solution' depends on axioms: [propext, Classical.choice, Quot.sound]" in text
    for name in ["independent-integration-compile.ps1", "independent-native-perturbed.log", "independent-native-perturbed-exit.txt", "independent-native-perturbed.olean"]:
        freeze(OUT / name)
    return {"fresh_independent_exact_canonical_Solution_compile": True, "endpoint": TARGETS[3], "command": "lake env pwsh -NoProfile -ExecutionPolicy Bypass -File missions/zeta9/formalization/platform/pnt/independent-integration-compile.ps1", "working_directory": str(ROOT), "source": "formalization/platform/pnt/staged/" + request["problems"][3]["local_solution"], "source_sha256": provenance["targets"][TARGETS[3]]["solution_sha256"], "log": "formalization/platform/pnt/independent-native-perturbed.log", "output": "formalization/platform/pnt/independent-native-perturbed.olean", "exit_code": 0, "axioms": sorted(STANDARD), "full_23_module_rebuild_repeated": False, "source_bytes_unchanged_during_compile": True}

check("fresh_independent_genuine_cache_Solution_compile", independent_actual_compile)

def final_author_receipts_and_freeze():
    receipt = load(OUT / "staged-compile-receipt.json")
    audit = load(OUT / "integration-audit.json")
    assert receipt["canonical_solution_bytes_identical_across_modes"] is True
    assert receipt["stub_mirror_is_proof"] is False
    assert receipt["completion"] == "complete"
    assert audit["native_identical_canonical_solution_bytes_standard_three_axioms"] is True
    assert audit["canonical_stub_build_standard_three_axioms"] is False
    assert audit["root_formal_build_with_type_only_medium_pnt_mirror_is_closed_proof"] is False
    assert audit["new_pnt_or_harmonic_baseline_assumptions"] == []
    assert audit["only_external_proved_theorem_boundary"]["id"] == PNT_ID
    assert audit["only_external_proved_theorem_boundary"]["stub_is_proof"] is False
    retained, successful = [], []
    by_label = {row["label"]: row for row in receipt["rows"]}
    assert len(by_label) == len(receipt["rows"]) == 29
    for row in receipt["rows"]:
        equal_hash(resolve_recorded(row["source"]), row["source_sha256"])
        equal_hash(resolve_recorded(row["log"]), row["log_sha256"])
        if row.get("output"):
            equal_hash(resolve_recorded(row["output"]), row["output_sha256"])
        if row["exit_code"] is None:
            assert row["evidence_kind"] in ["retained_build_object", "retained_type_report"]
            assert "Reconstructed" in row["command_provenance"]
            chain, node = [], row
            while node["exit_code"] is None:
                assert node["label"] not in chain
                chain.append(node["label"])
                node = by_label[node["verification_report"]]
            assert node["exit_code"] == 0
            assert node["evidence_kind"] == "fresh_type_report"
            retained.append(row["label"])
        else:
            assert row["exit_code"] == 0, row["label"]
            assert row["evidence_kind"] == "fresh_type_report"
            successful.append(row["label"])
    assert "types-original" in successful
    assert len(successful) == 13 and len(retained) == 16
    assert by_label["types-original"]["search_path_prefix"] is None
    for i in range(4):
        assert f"types-native-{i}-solution" in successful
        assert f"types-stub-{i}-solution" in successful
        assert f"types-{i}-reference" in successful
    manifest = (OUT / "SHA256SUMS.txt").read_text(encoding="utf-8-sig")
    for line in manifest.splitlines():
        expected, name = line.split("  ", 1)
        equal_hash(OUT / name, expected)
    copy_plan = load(OUT / "root-copy-plan.json")
    assert copy_plan["root_shared_paths_written_by_this_offline_batch"] == []
    assert len(copy_plan["files"]) == 8
    for row in copy_plan["files"]:
        assert Path(row["destination"]) == ROOT / row["relative_destination"]
        assert Path(row["source"]) == OUT / "staged" / row["relative_destination"]
        equal_hash(Path(row["source"]), row["sha256"])
    for name in ["staged-compile-receipt.json", "integration-audit.json", "SHA256SUMS.txt", "root-copy-plan.json", "review_pnt_integration_independent.py"]:
        freeze(OUT / name)
    return {"successful_current_type_import_processes": len(successful), "honestly_unrecorded_old_process_exits": retained, "retained_to_fresh_exit_zero_verification_chains_acyclic": True, "all_retained_sources_logs_and_oleans_hash_verified": True, "frozen_payload_manifest_matches": True, "staged_batch_only_root_copy_plan_verified": True, "server_acceptance_claimed": False}

check("final_author_receipts_and_payload_freeze", final_author_receipts_and_freeze)

def parent_root_byte_integration():
    receipt = load(OUT / "root-install-receipt.json")
    assert receipt["frozen_audit_sha256"] == digest(OUT / "integration-audit.json")
    assert receipt["shared_source_bytes_match_frozen_stage"] is True
    assert receipt["medium_pnt_mirror_is_proof"] is False
    assert receipt["native_same_bytes_proof_evidence_preserved"] is True
    expected = {p[k] for p in request["problems"] for k in ["local_solution", "local_reference"]} | {"Theorems/Thm_MediumPNT.lean"}
    assert len(receipt["copies"]) == 9
    assert {row["destination"] for row in receipt["copies"]} == expected
    for row in receipt["copies"]:
        source, destination = TASK / row["source"], ROOT / row["destination"]
        assert source.read_bytes() == destination.read_bytes()
        equal_hash(source, row["sha256"])
        equal_hash(destination, row["sha256"])
    freeze(OUT / "root-install-receipt.json")
    return {"installed_root_Solutions_and_references_byte_equal_frozen_stage": 8, "explicit_installed_MediumPNT_stub_byte_equal_reviewed_type_mirror": True, "root_stub_is_closed_proof": False, "root_build_result_not_claimed_by_this_review": True, "root_scope_and_dynamic_build_logs_not_hashed": True}

check("parent_root_installed_bytes_equal_frozen_staged_payloads", parent_root_byte_integration)

findings.extend([
    {"severity": "informational", "id": "platform_and_native_source_commits_differ", "finding": "Saved public Proved MediumPNT source references f55e85551ac10e96d98262a354cfcaac2825f2da; genuine local unchanged replay is 55270df807213fc3584523d09e0311d7dc073ff5. Exact elaborated statements and Mathlib revision agree; no cross-commit byte equality is asserted.", "affects_pass": False},
    {"severity": "informational", "id": "stub_is_type_compatibility_evidence_only", "finding": "The platform local MediumPNT declaration mirror intentionally uses sorry and causes sorryAx in stub builds. The unchanged canonical Solutions contain no sorry; their genuine-cache builds use exactly the three standard axioms.", "affects_pass": False},
    {"severity": "informational", "id": "proof_boundary", "finding": "This offline audit verifies four harmonic/PNT endpoints and mechanical transplantation. Platform proof acceptance remains a separate live operation. J, S, and zeta(9) irrationality are not closed by this batch.", "affects_pass": False},
    {"severity": "informational", "id": "retained_process_exit_statuses_are_unknown", "finding": "Fourteen earlier compiled objects and two boundary type logs have honestly unknown historical process exit codes. Their frozen receipt keeps null exits and provides acyclic links to thirteen fresh actual-exit-zero type imports. This reviewer independently compiled the unchanged full perturbation Solution with actual exit zero and standard-three axioms.", "affects_pass": False},
    {"severity": "informational", "id": "root_integration_and_build_boundary", "finding": "The frozen author batch writes no shared root sources; the parent's subsequent root installation receipt and all nine installed source byte hashes were independently verified. The root MediumPNT mirror remains a statement stub. The parent owns task scope/check/build and live platform acceptance; this review does not claim a running root stub build as a closed proof.", "affects_pass": False},
])
passed = all(row["pass"] for row in checks)
review = {"schema_version": 1, "date": "2026-10-03", "reviewer": "/root/pnt_integration_review_1003", "proof_authorship_in_this_review": False, "review_kind": "Independent offline integration, source-span fidelity, genuine-cache and platform-stub distinction review", "verdict": "PASS" if passed else "FAIL", "checks": checks, "findings": findings, "reviewed_hashes": hashes, "review_method": {"author_scripts_imported_or_executed": False, "actual_original_sources_read": True, "independent_source_span_reconstruction": True, "fresh_independent_Solution_compile": True, "full_upstream_rebuild_repeated": False, "credentials_read": False, "network_or_API_calls": False, "existing_source_or_frozen_batches_modified": False, "dynamic_API_receipts_scope_and_docs_hashed": False}}
if "--write" in sys.argv:
    (OUT / "independent-integration-review.json").write_text(json.dumps(review, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"verdict": review["verdict"], "checks": [{k: r[k] for k in ("id", "pass", "error") if k in r} for r in checks], "hash_bound_files": len(hashes)}, ensure_ascii=False, indent=2))
sys.exit(0 if passed else 1)
