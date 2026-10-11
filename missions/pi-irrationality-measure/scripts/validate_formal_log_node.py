"""Replay exact FormalLog proof-node evidence without Lean or network calls.

The original four-file stage stays frozen. Its generated snapshot may have a
separate byte-prefix-preserving WithRefs companion, certified by its own actual
preflight. Companion certificates never mutate the preview manifest.
"""
from __future__ import annotations

import argparse
from bisect import bisect_right
from difflib import SequenceMatcher
import hashlib
import json
from pathlib import Path
from unittest.mock import patch

import generate_platform_provider_nodes as nodegen
import generate_namespace_context_providers as sourcegen
import generate_formal_log_truncation_provider as formal
import validate_formal_log_truncation_provider as formalcert
import validate_namespace_context_providers as context
import validate_standalone_platform_node as standalone
import stage_formal_log_base_node_short as shortstage
from certify_command_emission_probe import checked_expr, normalized

TASK, ROOT, V = formal.TASK, formal.ROOT, formal.V
NODE_ROOT = V / "flp3"
SELF = Path(__file__).resolve()
sha, read, rel, fail, file = context.sha, context.read, context.rel, context.fail, context.file
NODE_KEYS = {formal.MODULE + ":" + str(n) for n in [356, 12753, 14165, 17060]}
CERT_NAME = "formal-node-validation.json"
SHORT_PRODUCER_SHA = "1fbe55781015b5cadded0b1fc3b964ba393d05c3dfa20ddf9f0c42fe5219060d"


def stage_path(value):
    p = Path(value)
    if not p.is_absolute():
        p = TASK / p if p.parts[0] == "verification" else NODE_ROOT / p
    p = p.resolve()
    fail(p != shortstage.STAGE.resolve() or not p.is_dir(), "Only the actual short FormalLog base stage flp3/f1 is supported")
    return p


def implementation_pins():
    paths = [SELF, Path(nodegen.__file__), Path(sourcegen.__file__), Path(formalcert.__file__),
             Path(context.__file__), Path(standalone.__file__),
             TASK / "scripts/plan_formal_log_proof_nodes.py", TASK / "scripts/certify_command_emission_probe.py",
             TASK / "scripts/stage_formal_log_base_node.py",
             Path(shortstage.__file__),
             TASK / "scripts/preflight_staged_module.py", TASK / "scripts/validate_shared_source_snapshot.py"]
    return {rel(p): sha(p) for p in paths}


def readonly_generator(manifest):
    # The ordinary constructor writes live-import-inventory.json. Reproduce its
    # checked state using the already existing pure builder, then remove only
    # that builder's explicit extra consumer pins absent from the producer.
    g = sourcegen.readonly_generator()
    for p in [V / "extraction-state.json", Path(sourcegen.__file__), sourcegen.CATALOG, sourcegen.SOURCE_SUBSET]:
        g.input_hashes.pop(rel(p), None)
    fail(g.input_hashes != manifest["input_hashes"], "Exact current provider-node global input domain differs")
    n = nodegen.ProviderNodeGenerator.__new__(nodegen.ProviderNodeGenerator)
    n.preview, n.g = True, g
    n.runtime_sha = formal.runner.validate_runtime()[1]
    n.core_path = V / "TypeOnlyTheoremSnapshotCore.inc"
    n.core_sha = sha(n.core_path)
    n.cache, n.layout_cache, n.inventory_cache = {}, {}, {}
    if manifest["node"] == formal.MODULE + ":17060":
        cert = formalcert.validate_equation_certificate()
        equation = cert["data"]["required_source_equation"]
        preserved = g.unit_plan["preserved_generated_commands"]
        if equation not in preserved:
            g.unit_plan = dict(g.unit_plan)
            g.unit_plan["preserved_generated_commands"] = [*preserved, equation]
    return n


def reconstruct(stage, manifest, n):
    captured = {}
    def capture_bytes(path, data):
        fail(path.resolve().parent != stage or path.name in captured, "Unexpected generator write during readonly reconstruction")
        captured[path.name] = bytes(data)
        return len(data)
    def capture_text(path, text, encoding=None, errors=None, newline=None):
        return capture_bytes(path, text.encode(encoding or "utf-8", errors or "strict"))
    old_sha = nodegen.sha
    def captured_sha(path):
        if path.resolve().parent == stage and path.name in captured:
            return hashlib.sha256(captured[path.name]).hexdigest()
        return old_sha(path)
    with patch.object(nodegen, "DEST", shortstage.ShortDestination()), patch.object(Path, "write_bytes", capture_bytes), \
         patch.object(Path, "write_text", capture_text), patch.object(Path, "mkdir", lambda *a, **k: None), \
         patch.object(nodegen, "sha", captured_sha):
        result = n.generate(manifest["node"])
    fail((TASK / result["stage"]).resolve() != stage, "Node stage does not match its exact authority name")
    expected_manifest = json.loads(captured.pop("manifest.json"))
    fail(expected_manifest != manifest, "Manifest differs from exact readonly AST reconstruction")
    fail(set(captured) != set(manifest["outputs_sha256"]) or len(captured) != 4, "Expected exactly four original stage files")
    for name, data in captured.items():
        fail((stage / name).read_bytes() != data or sha(stage / name) != manifest["outputs_sha256"][name],
             "Original staged bytes differ from source/AST reconstruction: " + name)
    return n.import_collision_inventory(manifest["node"])


def setup(stage):
    fail(sha(Path(shortstage.__file__)) != SHORT_PRODUCER_SHA, "Frozen short-stage producer changed")
    m = read(stage / "manifest.json")
    fail(m["node"] not in NODE_KEYS or m["source_commit"] != formalcert.SOURCE_COMMIT,
         "Wrong exact FormalLog proof frontier/commit")
    fail(m["validated"] is not False or m["submission_ready"] is not False or m["full_tree_ready"] is not False
         or m["lean_started"] is not False or m["api_used"] is not False, "Preview manifest flags were mutated")
    fail(m["node_generated_names"] or m["source_to_generated_private_kernel_names"] is not None
         or m["restored_local_instances"] or m["definition_certificates"], "Private aliases/local instances require a separate actual kernel-map validator")
    fail(m["child_nodes"], "Child-bearing nodes require an actual proved-child certificate adapter")
    fail(m["theorem_name"] != m["source_graph_name"] or m["top_level_literal_theorem_solution"] is not True,
         "Only original public theorem and literal root solution supported")
    for relative, digest in m["input_hashes"].items():
        fail(sha(file(relative)) != digest, "Frozen node input changed: " + relative)
    for name, digest in m["implementation_sha256"].items():
        fail(sha(TASK / "scripts" / name) != digest, "Frozen node producer changed: " + name)
    fail(sha(file(m["snapshot_core"])) != m["snapshot_core_sha256"]
         or sha(V / "decl_graph.jsonl") != m["source_graph_sha256"], "Core/Graph changed")
    n = readonly_generator(m)
    inventory = reconstruct(stage, m, n)
    fail(inventory != m["whole_import_closure_inventory"] or inventory["collisions"], "Whole import public CI collision inventory differs")
    target = n.g.units[m["node"]]
    fail(target["private"] or target["deprivate"] or target["graph_kinds"] != ["theorem"]
         or target["graph_names"] != [m["source_graph_name"]], "Target must be one atomic unchanged public theorem")
    for r in m["public_inline_ci_requests"]:
        u = n.g.units[r["source_unit"]]
        fail(u["private"] or u["deprivate"] or u["graph_kinds"] != ["theorem"]
             or r["source_graph_name"] != r["generated_name"] or r["source_graph_name"] not in u["graph_names"],
             "Only atomic unchanged public inline theorem CIs supported")
    return m, n, inventory


def definition_interfaces(m):
    # Replay the full four-module source/generated context once; it includes
    # actual PolynomialFrameDegree validation via the frozen Windows adapter.
    old = formal.frozen_fast.checked_fast_generated_snapshot
    try:
        formal.frozen_fast.checked_fast_generated_snapshot = formal.windows_fast.checked_fast_generated_snapshot
        g, results = context.setup()
        validated = context.certify_generated(g, results, write=False)
    finally:
        formal.frozen_fast.checked_fast_generated_snapshot = old
    certs = {module: entry for module, entry in validated["certificates"].items()}
    degree = validated["certificates"][sourcegen.MODULES[0]]["data"]["external_provider"]
    degree_path = file(degree["certificate"])
    certs["OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree"] = {
        "path": rel(degree_path), "sha256": sha(degree_path), "data": read(degree_path)}
    if any(x["source_module"] == formal.MODULE for x in m["definition_dependency_witnesses"]):
        certs[formal.MODULE] = formalcert.validate_formal_log_provider()["certificate"]
    direct, provided = [], {}
    for witness in m["definition_dependency_witnesses"]:
        module = witness["source_module"]
        fail(module not in certs, "No exact actual Definition interface supported: " + module)
        entry = certs[module]; c = entry["data"]
        fail(c["source_module"] != module or c["platform_module"] != witness["platform_module"]
             or c["validated"] is not True or c["proof_axioms"] != "Std3", "Imported Definition certificate identity differs")
        if "comparisons" in c:
            names = [x["name"] for x in c["comparisons"]]
        else:
            fail(not all(c["snapshot_comparison"].get(x) is True for x in ["types_equal", "values_equal", "axioms_equal_and_std3"]),
                 "Definition exact type/value/axiom comparison missing")
            names = c["snapshot_comparison"]["compared_names"]
        olean = V / "staged-build/lib/lean" / Path(*witness["platform_module"].split(".")).with_suffix(".olean")
        pf = c.get("bundle_preflight")
        if pf is None:
            pf = next(x for x in c["preflights"] if x["role"] == "provider-bundle")
            expected_olean = read(file(pf["record"]))["output_olean_sha256"]
        else:
            expected_olean = pf["data"]["output_olean_sha256"]
        fail(sha(olean) != expected_olean, "Direct imported Definition OLean differs from actual emitted artifact")
        direct.append({"source_module": module, "platform_module": witness["platform_module"],
            "certificate": entry["path"], "certificate_sha256": entry["sha256"],
            "output_olean": rel(olean), "output_lean_sha256": sha(olean), "validated": True, "proof_axioms": "Std3"})
        for name in names:
            fail(name in provided, "Duplicate actual public provided CI across direct Definitions: " + name)
            provided[name] = module
    return direct, provided


def compile_records(stage, m, definitions):
    expected_inputs = {"schema_version": 1, "artifact_kind": "formal-log-base-node-certified-inputs", "node": m["node"],
        "definition_certificates": definitions, "child_certificates": [],
        "validated_node": False, "Lean_started": False, "submission_ready": False}
    fail(read(stage / "certified-inputs.json") != expected_inputs, "Frozen actual input interfaces differ from full readonly replay")
    preparation = read(stage / "preparation.json")
    common = {rel(stage / "manifest.json"): sha(stage / "manifest.json"),
              rel(stage / "certified-inputs.json"): sha(stage / "certified-inputs.json"),
              rel(TASK / "scripts/plan_formal_log_proof_nodes.py"): sha(TASK / "scripts/plan_formal_log_proof_nodes.py"),
              rel(TASK / "scripts/stage_formal_log_base_node.py"): sha(TASK / "scripts/stage_formal_log_base_node.py"),
              rel(Path(shortstage.__file__)): sha(Path(shortstage.__file__))}
    for row in definitions:
        common[row["certificate"]] = row["certificate_sha256"]
        common[row["output_olean"]] = row["output_lean_sha256"]
    records = {}
    actual_files = [Path(m["statement"]).name, Path(m["solution"]).name, "SnapshotOriginal.lean", "SnapshotGeneratedWithRefs.lean"]
    fail(set(preparation["compile_manifests"]) != set(actual_files), "Actual four-file preflight domain differs")
    for index, filename in enumerate(actual_files, 1):
        source = stage / filename
        imports = ["Lean", m["source_components"][0]["source_module"]] if filename == "SnapshotOriginal.lean" else m["imports"]
        mp = stage / (f"c{index}.json")
        expected = {"schema_version": 1, "artifact_kind": "formal-log-proof-node-file-import-certificate",
            "output": source.relative_to(ROOT).as_posix(), "output_sha256": sha(source), "imports": imports,
            "input_hashes": common, "runtime_sha256": m["runtime_sha256"], "node": m["node"], "node_validated": False,
            "timeout_seconds": 300, "Lean_started": False, "submission_ready": False}
        fail(read(mp) != expected or preparation["compile_manifests"][filename]
             != {"manifest": rel(mp), "manifest_sha256": sha(mp)}, "Frozen four-file compilation manifest differs")
        if filename != "SnapshotGeneratedWithRefs.lean":
            records[filename] = context.record(source, mp, "modecheck", source.stem, stage)
    return records


def kernel_rows(path, names, pf):
    formalcert.written_during(path, pf)
    rows = read(path)
    fail(not isinstance(rows, list) or [x["name"] for x in rows] != names or len(set(names)) != len(names),
         "Exact snapshot CI names/order differs: " + rel(path))
    for row in rows:
        fail(set(row) != {"name", "levelParams", "type", "value", "prettyType"} or row["value"] is not None
             or not isinstance(row["prettyType"], str), "Only null-value theorem type snapshots supported")
        levels = row["levelParams"]
        fail(not isinstance(levels, list) or any(not isinstance(p, str) for p in levels)
             or len(set(levels)) != len(levels), "Invalid theorem universe binders")
        checked_expr(row["type"], set(levels))
    return rows


def same_type(left, right):
    fail(len(left["levelParams"]) != len(right["levelParams"])
         or normalized(left["type"], {p:i for i,p in enumerate(left["levelParams"])}, {})
         != normalized(right["type"], {p:i for i,p in enumerate(right["levelParams"])}, {}),
         "Exact theorem kernel types differ: " + left["name"] + " / " + right["name"])


def source_command_witness(m, n):
    """Keep original and port commands separately, including version edits.

    AST coordinates authenticate the port command. Its unchanged boundary
    lines map to the original source using full-file line correspondence; no
    declaration is identified from a guessed private name or proof prefix.
    """
    unit = n.g.units[m["node"]]
    origin = next(x for x in m["source_components"] if x["source_module"] == unit["module"])
    port, original = (ROOT / origin["source"]).read_bytes(), (ROOT / origin["original_source"]).read_bytes()
    old_lines, new_lines = original.splitlines(keepends=True), port.splitlines(keepends=True)
    def offsets(lines):
        out = [0]
        for line in lines: out.append(out[-1] + len(line))
        return out
    old_offsets, new_offsets = offsets(old_lines), offsets(new_lines)
    # Source download and port retain their original line ending variants.
    # Compare only line contents to locate boundaries, then use raw offsets for
    # both preserved hashes. No theorem content is normalized or rewritten.
    old_contents = [line.rstrip(b"\r\n") for line in old_lines]
    new_contents = [line.rstrip(b"\r\n") for line in new_lines]
    matching = SequenceMatcher(None, old_contents, new_contents, autojunk=False).get_matching_blocks()
    def original_boundary(position):
        line = bisect_right(new_offsets, position) - 1
        for match in matching:
            if match.b <= line < match.b + match.size:
                delta = position - new_offsets[line]
                fail(delta > len(new_contents[line]), "Command boundary occurs inside line ending bytes")
                return old_offsets[match.a + line - match.b] + delta
        raise ValueError("Original source command boundary lacks an exact unchanged line witness")
    a, b = unit["start"]["offset"], unit["end"]["offset"]
    oa, ob = original_boundary(a), original_boundary(b)
    fail(not 0 <= oa < ob <= len(original), "Invalid original command boundary mapping")
    return {"source_module": unit["module"], "source_graph_name": m["source_graph_name"],
        "port_source": origin["source"], "port_source_sha256": origin["source_sha256"],
        "original_source": origin["original_source"], "original_source_sha256": origin["original_source_sha256"],
        "port_command_range": {"start": a, "end": b}, "original_command_range": {"start": oa, "end": ob},
        "port_command_sha256": hashlib.sha256(port[a:b]).hexdigest(),
        "original_command_sha256": hashlib.sha256(original[oa:ob]).hexdigest(),
        "port_and_original_command_bytes_equal": port[a:b] == original[oa:ob],
        "port_kernel_type_actual_source_snapshot_verified": True,
        "original_command_boundaries_from_full_file_equal_line_correspondence": True}


def certify(stage):
    # WithRefs preparation consumer is intentionally separate from all frozen
    # producers. Its checker is loaded only once the actual companion exists.
    import formal_log_node_refs_repaired as refs
    m, n, inventory = setup(stage)
    definitions, provided = definition_interfaces(m)
    records = compile_records(stage, m, definitions)
    generated_source, generated_manifest, references_path = refs.checked_preparation(stage)
    generated_pf = context.record(generated_source, generated_manifest, "modecheck", generated_source.stem, stage)
    records[generated_source.name] = generated_pf
    for pf in records.values():
        if pf["data"]["actual_module_identity"] == "SnapshotOriginal": continue
        for interface in definitions:
            dep = next(d for d in pf["data"]["dependency_oleans"] if d["module"] == interface["platform_module"])
            fail(dep["sha256_before"] != interface["output_lean_sha256"], "Node actual imported Def OLean differs from certified current artifact")
    original = kernel_rows(stage / "original-type.json", [m["source_graph_name"]], records["SnapshotOriginal.lean"])
    generated = kernel_rows(stage / "generated-type.json", [m["theorem_name"], "solution"], generated_pf)
    for row in generated: same_type(original[0], row)
    source_public = [r["source_graph_name"] for r in m["public_inline_ci_requests"]]
    generated_public = [r["generated_name"] for r in m["public_inline_ci_requests"]]
    source_inline = kernel_rows(ROOT / m["public_inline_type_json_outputs"]["original"], source_public, records["SnapshotOriginal.lean"])
    generated_inline = kernel_rows(ROOT / m["public_inline_type_json_outputs"]["generated"], generated_public, generated_pf)
    for a, b in zip(source_inline, generated_inline, strict=True): same_type(a, b)
    for side, pf in [("original", records["SnapshotOriginal.lean"]), ("generated", generated_pf)]:
        fail(kernel_rows(ROOT / m["inline_type_json_outputs"][side], [], pf) != [], "Unexpected private CI maps/exports")
    audits = {"source": standalone.audit_axioms(file(records["SnapshotOriginal.lean"]["data"]["log"]), m["source_graph_name"]),
              "snapshot_solution": standalone.audit_axioms(file(generated_pf["data"]["log"]), "solution"),
              "exact_solution": standalone.audit_axioms(file(records[Path(m["solution"]).name]["data"]["log"]), "solution")}
    actual_refs = refs.checked_output(stage, m, generated_pf, references_path)
    fail([x["name"] for x in actual_refs] != ["solution", *generated_public], "Exact proof reference request domain differs")
    fail(set(actual_refs[0]["axioms"]) != set(audits["snapshot_solution"]),
         "Actual proof-reference axioms differ from same-run solution axiom audit")
    allowed = set(provided) | set(generated_public)
    graph_names = set(n.g.graph)
    reference_audits = []
    for row in actual_refs:
        names = set(row["typeRefs"]) | set(row["valueRefs"])
        fail(m["theorem_name"] in names or "solution" in names, "Generated proof uses its target stub or solution itself")
        project = {name for name in names if name in graph_names or name.startswith(("OAI.", "Definitions.", "Theorems.", "Solutions.", "_private.OAI."))}
        fail(not project <= allowed, "Generated proof uses unavailable project CI: " + str(sorted(project - allowed)))
        reference_audits.append({"name": row["name"], "actual_project_refs": sorted(project), "available_project_refs_only": True,
            "closed_type_and_proof": True, "axioms": row["axioms"], "actual_owner": row["owner"]})
    pins = implementation_pins()
    pins[rel(Path(refs.__file__))] = sha(Path(refs.__file__))
    for producer in [refs.original, refs.repair]:
        pins[rel(Path(producer.__file__))] = sha(Path(producer.__file__))
    hashes = {p.name: sha(p) for p in [stage / "original-type.json", stage / "generated-type.json", references_path,
        ROOT / m["public_inline_type_json_outputs"]["original"], ROOT / m["public_inline_type_json_outputs"]["generated"],
        ROOT / m["inline_type_json_outputs"]["original"], ROOT / m["inline_type_json_outputs"]["generated"]]}
    return {"schema_version": 1, "artifact_kind": "formal-log-proof-node-kernel-certificate", "validated": True,
        "node": m["node"], "theorem_name": m["theorem_name"], "source_commit": m["source_commit"],
        "manifest": rel(stage / "manifest.json"), "manifest_sha256": sha(stage / "manifest.json"),
        "statement_sha256": m["statement_sha256"], "solution_sha256": m["solution_sha256"],
        "original_four_files_sha256": m["outputs_sha256"], "generated_with_refs": rel(generated_source),
        "generated_with_refs_sha256": sha(generated_source), "generated_with_refs_manifest_sha256": sha(generated_manifest),
        "generated_reference_exporter_repair": refs.lineage_evidence(),
        "definition_certificates": definitions, "actual_definition_provided_names": provided,
        "child_certificates": [], "source_components": m["source_components"], "source_graph_sha256": m["source_graph_sha256"],
        "source_command_witness": source_command_witness(m, n),
        "source_skeleton_and_inventory_reconstructed": True, "public_import_duplicate_constants": [],
        "kernel_types_equal": True, "inline_kernel_types_equal": True, "source_target_solution_universes_equal": True,
        "only_universe_parameter_names_normalized": True, "theorem_values_null": True,
        "solution_proof_reference_evidence": reference_audits, "target_stub_unused": True,
        "actual_project_reference_coverage_complete": True, "allowed_project_names": sorted(allowed),
        "proof_reference_getter": "Lean.Expr.getUsedConstants", "theorem_proof_values_exported": False,
        "Std3_only": True, "proof_axioms": "Std3", "axioms": audits, "preflights": records,
        "max_file_seconds": max(p["data"]["seconds"] for p in records.values()), "output_json_sha256": hashes,
        "input_hashes": m["input_hashes"], "implementation_hashes": pins,
        "submission_ready": False, "full_tree_ready": False, "source_scope_partial": True}


def validate_formal_node(stage):
    """Read-only publisher/child-consumer interface. Returns exact reviewed bytes."""
    stage = stage_path(stage)
    cert = certify(stage)
    path = stage / CERT_NAME
    fail(not path.is_file() or read(path) != cert, "Formal proof-node certificate missing/stale after full readonly replay")
    m = read(stage / "manifest.json")
    return {"stage": stage, "manifest": stage / "manifest.json", "manifest_data": m,
        "certificate": {"path": rel(path), "sha256": sha(path), "data": cert},
        "statement_bytes": (ROOT / m["statement"]).read_bytes(), "solution_bytes": (ROOT / m["solution"]).read_bytes(),
        "source_command_witness": cert["source_command_witness"],
        "validated": True, "submission_ready": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("stage")
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check-only", action="store_true")
    mode.add_argument("--certify-existing", action="store_true")
    mode.add_argument("--validate-only", action="store_true")
    args = parser.parse_args()
    try:
        stage = stage_path(args.stage)
        if args.check_only:
            m, *_ = setup(stage)
            out = {"node": m["node"], "source_and_exact_bytes_checked": True, "validated": False, "submission_ready": False}
        elif args.certify_existing:
            cert = certify(stage); path = stage / CERT_NAME
            context.write_exact(path, cert)
            out = {"validated": True, "certificate": rel(path), "sha256": sha(path), "max_file_seconds": cert["max_file_seconds"], "submission_ready": False}
        else:
            result = validate_formal_node(stage)
            out = {"validated": True, "certificate": result["certificate"]["path"], "sha256": result["certificate"]["sha256"], "submission_ready": False}
        print(json.dumps(out, indent=2))
    except (ValueError, KeyError, FileNotFoundError, TypeError, StopIteration) as error:
        print(json.dumps({"validated": False, "status": "rejected", "error": str(error)})); raise SystemExit(2)


if __name__ == "__main__": main()
