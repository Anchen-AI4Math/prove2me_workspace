#!/usr/bin/env python3
"""Offline structural and staged-evidence validator for provider bundles.

Only ordinary, public theorem/definition command units are currently accepted.
The script keeps preview generation provenance separate from Lean evidence:
``--check-only`` never starts Lean, ``--certify-existing`` only checks captured
preflight records, and ``--run-preflights`` explicitly invokes the bounded
staged preflight runner for this one provider.  It never contacts the platform.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from typing import Any

from prepare_fast_provider_snapshot import checked_fast_generated_snapshot, stage_fast_generated_snapshot
from provider_source_subset_cache_windows import validate_provider_source_subset_cache
from shared_source_certificate_cache import validate_complete_source_cache

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
VERIFICATION = TASK / "verification"
PREVIEW = VERIFICATION / "providers-preview"
COMPLETE_PREVIEW = VERIFICATION / "providers-complete-preview"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
MAX_SECONDS = 300
COMMIT = "adc7f1241b42e322a6451854ab7e4b4c146bf78a"


def sha_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def sha(path: Path) -> str:
    return sha_bytes(path.read_bytes())


def read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def resolve_provider_root(value=None) -> Path:
    """Only the historical root or the complete 875-module mission root."""
    path = PREVIEW if value is None else Path(value)
    if not path.is_absolute():
        path = TASK / path
    path = path.resolve()
    allowed = {PREVIEW.resolve(), COMPLETE_PREVIEW.resolve()}
    if not path.is_relative_to(TASK.resolve()) or path not in allowed:
        raise ValueError("Provider root must be mission-local verification/providers-preview or verification/providers-complete-preview")
    return path


def check_complete_provider_basis(provider_root: Path) -> dict[str, Any] | None:
    if provider_root != COMPLETE_PREVIEW.resolve():
        return None
    manifest_path = VERIFICATION / "provider-plans/all-shared-public/provider-plan-manifest.json"
    manifest = read_json(manifest_path)
    if manifest.get("basis") != "verified complete 875-module preview":
        raise ValueError("Complete provider root lacks the verified 875-module provider-plan basis")
    for filename in ("platform-unit-plan-preview.json", "platform-artifact-plan-preview.json"):
        path = VERIFICATION / filename
        expected = manifest.get("input_hashes", {}).get(path.relative_to(TASK).as_posix())
        if not expected or sha(path) != expected:
            raise ValueError("Complete provider basis base-plan pin changed: " + filename)
        plan = read_json(path)
        if plan.get("complete_extraction") is not True:
            raise ValueError("Complete provider base plan is not based on full extraction")
        if filename == "platform-unit-plan-preview.json" and plan.get("source_declarations_pending_ast") != []:
            raise ValueError("Complete provider base plan has pending AST declaration owners")
    inventory_path = VERIFICATION / "ast-unit-inventory.json"
    inventory = read_json(inventory_path)
    if (sha(inventory_path) != manifest.get("input_hashes", {}).get(inventory_path.relative_to(TASK).as_posix())
            or inventory.get("complete_extraction") is not True or inventory.get("extracted_modules") != 875
            or inventory.get("unmatched")):
        raise ValueError("Complete provider basis has not verified exactly 875 AST modules")
    return {"basis": manifest["basis"], "provider_plan_manifest":manifest_path.relative_to(TASK).as_posix(),
            "provider_plan_manifest_sha256":sha(manifest_path), "extracted_modules":875,
            "source_declarations_pending_ast":[]}


def mission_path(value: str, label: str) -> Path:
    p = (TASK / value).resolve()
    if not p.is_relative_to(TASK.resolve()) or not p.is_file():
        raise ValueError(f"{label} is absent or escapes the mission: {value}")
    return p


def workspace_path(value: str, label: str) -> Path:
    p = Path(value)
    p = p.resolve() if p.is_absolute() else (ROOT / p).resolve()
    if not p.is_relative_to(ROOT.resolve()) or not p.is_file():
        raise ValueError(f"{label} is absent or escapes the workspace: {value}")
    return p


def module_path(module: str, root: Path) -> Path:
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*(\.[A-Za-z_][A-Za-z0-9_']*)*", module):
        raise ValueError(f"Invalid Lean module name: {module}")
    return root.joinpath(*module.split(".")).with_suffix(".lean")


def fail_if(condition: bool, message: str) -> None:
    if condition:
        raise ValueError(message)


def exact_import_header(source: bytes, imports: list[str]) -> bool:
    statements = "".join(f"import {name}\n" for name in imports).encode("utf-8")
    # The generator splices an LF-authored import replacement into source
    # bytes that may retain CRLF at the splice boundary.  Every import line is
    # still fixed by the manifest; tolerate only that final line terminator.
    return source.startswith(statements) or source.startswith(statements[:-1] + b"\r\n")


def norm_expr(value: Any, levels: list[str]) -> Any:
    indices = {name: i for i, name in enumerate(levels)}
    if isinstance(value, list):
        if len(value) == 2 and value[0] == "param":
            if value[1] not in indices:
                raise ValueError("Snapshot has an undeclared universe parameter")
            return ["param", indices[value[1]]]
        return [norm_expr(v, levels) for v in value]
    return value


def graph_rows() -> tuple[dict[str, dict[str, Any]], str]:
    path = VERIFICATION / "decl_graph.jsonl"
    rows: dict[str, dict[str, Any]] = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        row = json.loads(line)
        name = row.get("name") or row.get("graph_name")
        if name:
            rows[name] = row
    return rows, sha(path)


def syntax_kinds(node: Any) -> list[str]:
    found = []
    if isinstance(node, dict):
        k = node.get("syntaxKind")
        if isinstance(k, str):
            found.append(k)
        for child in node.get("children", []):
            found.extend(syntax_kinds(child))
    elif isinstance(node, list):
        for child in node:
            found.extend(syntax_kinds(child))
    return found


def verify_fact_command(facts_path: Path, offset: int, expected_kind: str) -> dict[str, Any]:
    rows = [json.loads(line) for line in facts_path.read_text(encoding="utf-8").splitlines() if line.strip()]
    matches = []
    if expected_kind == "theorem":
        allowed_commands = {"Lean.Parser.Command.theorem", "Lean.Parser.Command.lemma", "theorem", "lemma"}
    elif expected_kind in {"def", "definition", "abbrev"}:
        allowed_commands = {"Lean.Parser.Command.definition", "Lean.Parser.Command.def", "Lean.Parser.Command.abbrev"}
    else:
        raise ValueError(f"Unsupported provider graph kind: {expected_kind}")
    for row in rows:
        rng = (row.get("syntax") or {}).get("range") or {}
        start = (rng.get("start") or {}).get("offset")
        if row.get("kind") == "command" and row.get("isDeclaration") is True and start == offset:
            kinds = syntax_kinds(row.get("syntax"))
            if allowed_commands.intersection(kinds):
                matches.append((row, kinds))
    if len(matches) != 1:
        raise ValueError(f"Expected one authoritative {expected_kind} command at source byte {offset}; found {len(matches)}")
    row, kinds = matches[0]
    forbidden = [k for k in kinds if k.startswith("Lean.Parser.Command.")
                 and any(x in k.lower() for x in ("macro", "mutual", "inductive", "structure", "instance"))]
    if forbidden:
        raise ValueError(f"Unsupported syntax wrapper(s): {forbidden}")
    return row


def derive_expected_imports(manifest: dict[str, Any], batch_root: Path, stem: str, provider_root: Path = PREVIEW) -> None:
    # The live import inventory captures source import commands.  The per-module
    # import ledger records the exact complete rewritten closure used by the
    # generator; compare both its external leaves and provider dependencies to
    # the manifest, then compare the byte-authenticated header to that list.
    inventory = read_json(provider_root / "live-import-inventory.json")
    module = manifest["source_module"]
    info = inventory.get("modules", {}).get(module)
    if not info:
        raise ValueError(f"No captured live import record for {module}")
    ledger = read_json(batch_root / "ledgers" / stem / "import-ledger.json")
    if ledger.get("source_module") != module:
        raise ValueError("Import ledger belongs to a different source module")
    inv_modules = [x.get("module") for x in info.get("imports", [])]
    ledger_modules = [x.get("module") for x in ledger.get("parser_reported_original_imports", [])]
    if inv_modules != ledger_modules:
        raise ValueError("Import ledger source imports differ from captured live import inventory")
    rewritten = ledger.get("rewritten_imports")
    if not isinstance(rewritten, list) or rewritten != sorted(set(rewritten)):
        raise ValueError("Import ledger rewritten closure is absent, duplicated, or unsorted")
    if manifest.get("imports") != rewritten:
        raise ValueError("Manifest imports differ from import-ledger complete rewritten closure")


def structural_check(batch: str, module_or_stem: str, provider_root: Path = PREVIEW) -> dict[str, Any]:
    provider_root = resolve_provider_root(provider_root)
    if batch not in {"minimum-statement", "all-shared-safe-leaves"}:
        raise ValueError("Unsupported provider batch")
    complete_basis = check_complete_provider_basis(provider_root)
    batch_root = provider_root / batch
    if not batch_root.resolve().is_relative_to(provider_root):
        raise ValueError("Provider batch escapes its selected provider root")
    if not batch_root.is_dir():
        raise ValueError(f"Provider batch missing: {batch}")
    report = read_json(batch_root / "generation-report.json")
    if report.get("batch") != batch or not report.get("preview_only") or report.get("lean_started") or report.get("api_used"):
        raise ValueError("Generation report is not an untouched preview")
    manifests = list((batch_root / "Definitions").glob("*.manifest.json"))
    selected = []
    for mp in manifests:
        m = read_json(mp)
        if module_or_stem in (m.get("source_module"), m.get("platform_module"), mp.name.removesuffix(".manifest.json")):
            selected.append((mp, m))
    if len(selected) != 1:
        raise ValueError(f"Expected exactly one provider manifest for {module_or_stem}; found {len(selected)}")
    mp, m = selected[0]
    source = workspace_path(m["source"], "ported source")
    original = workspace_path(m["original_source"], "original source")
    output = workspace_path(m["output"], "provider source")
    facts = workspace_path(m["facts"], "Stage2 facts")
    if provider_root == COMPLETE_PREVIEW.resolve() and output.resolve() != mp.with_suffix("").with_suffix(".lean").resolve():
        raise ValueError("Complete provider source output is not the exact selected new-root bundle path")
    if m.get("source_commit") != COMMIT:
        raise ValueError("Provider source commit is not the pinned OpenAI source commit")
    for field, path in (("source_sha256", source), ("original_source_sha256", original), ("output_sha256", output), ("facts_sha256", facts)):
        if sha(path) != m.get(field):
            raise ValueError(f"Provider manifest {field} mismatch")
    if not m.get("preview_only") or not m.get("provisional") or m.get("validated") or m.get("submission_ready") or m.get("lean_started") or m.get("api_used"):
        raise ValueError("Provider manifest has unsafe or inconsistent status flags")
    if not m.get("source_unchanged") or not m.get("source_skeleton_preserved") or not m.get("full_definition_proofs_preserved") or not m.get("independent_byte_reconstruction_equal"):
        raise ValueError("Source preservation/reconstruction attestations are absent")
    if m.get("renames") or m.get("deprivate_units") or m.get("elaboration_only_helpers") or m.get("kept_local_instances"):
        raise ValueError("Unsupported private/deprivate/rename/helper/local-instance provider case")
    if report.get("input_hashes") != m.get("input_hashes"):
        raise ValueError("Generation report and provider manifest input hash maps differ")
    historical_inputs = []
    for rel, expected in m.get("input_hashes", {}).items():
        p = mission_path(rel, "captured generation input")
        if sha(p) != expected:
            # The provider preview predates the in-progress full Stage2 index
            # refresh.  Its extraction-state digest is retained by both the
            # report and manifest, but the old state bytes were not archived.
            # Keep this explicit historical exception non-final; all other
            # captured inputs remain exact-current requirements.
            if provider_root == PREVIEW.resolve() and rel in {"verification/extraction-state.json",
                       "scripts/generate_platform_provider_bundles.py",
                       "verification/providers-preview/live-import-inventory.json"}:
                historical_inputs.append({"path": rel, "captured_sha256": expected,
                                          "current_sha256": sha(p), "recovered": False})
            else:
                raise ValueError(f"Captured provider-generation input changed: {rel}")
    for key, digest in (("provider_plan", "provider_plan_sha256"), ("provider_artifact_plan", "provider_artifact_plan_sha256")):
        p = mission_path(m[key], key)
        if sha(p) != m[digest]:
            raise ValueError(f"{key} hash mismatch")
    stem = mp.name.removesuffix(".manifest.json")
    derive_expected_imports(m, batch_root, stem, provider_root)
    if m.get("import_provenance") is not None:
        ledger = read_json(batch_root / "ledgers" / stem / "import-ledger.json")
        provenance = m["import_provenance"]
        if provenance != ledger.get("project_import_closure_provenance"):
            raise ValueError("Manifest and import-ledger project-closure provenance differ")
        for entry in provenance:
            src = workspace_path(entry["source"], "project import source")
            fact = workspace_path(entry["facts"], "project import Stage2 facts")
            if sha(src) != entry["source_sha256"] or sha(fact) != entry["facts_sha256"]:
                raise ValueError(f"Project import closure source/facts hash mismatch: {entry.get('module')}")
    if not exact_import_header(output.read_bytes(), m["imports"]):
        raise ValueError("Provider header does not exactly match authenticated imports")
    selected_units = m.get("selected_units", [])
    if not selected_units or len(set(selected_units)) != len(selected_units):
        raise ValueError("Selected unit list is empty or duplicated")
    graph, graph_hash = graph_rows()
    provider_plan = read_json(mission_path(m["provider_plan"], "provider unit plan"))
    plan_units = {row.get("id"): row for row in provider_plan.get("units", []) if isinstance(row, dict)}
    declarations = []
    for uid in selected_units:
        module, sep, offset_s = uid.rpartition(":")
        if not sep or module != m["source_module"]:
            raise ValueError(f"Invalid selected provider unit identity: {uid}")
        offset = int(offset_s)
        # Each unit must map to exactly one ordinary public theorem/definition
        # graph declaration, and exactly one authoritative parser command.
        unit = plan_units.get(uid)
        if not unit or unit.get("module") != module or (unit.get("start") or {}).get("offset") != offset:
            raise ValueError(f"Selected unit is absent or mismatched in the pinned provider unit plan: {uid}")
        names = unit.get("graph_names", [])
        if len(names) != 1:
            raise ValueError(f"Unit {uid} does not map to exactly one graph name: {names}")
        name = names[0]
        row = graph[name]
        kind = row.get("kind") or row.get("envKind") or row.get("env_kind")
        if kind not in ("theorem", "def", "definition", "abbrev"):
            raise ValueError(f"Unsupported provider graph kind for {name}: {kind}")
        for flag in ("private", "is_private", "isPrivate", "is_instance", "isInstance", "local"):
            if row.get(flag) is True:
                raise ValueError(f"Unsupported private/local/instance declaration {name}")
        if unit.get("private") or unit.get("deprivate") or unit.get("is_instance_command") or unit.get("is_local_instance"):
            raise ValueError(f"Unsupported private/deprivate/instance command unit {uid}")
        fact = verify_fact_command(facts, offset, kind)
        declarations.append({"name": name, "kind": kind, "unit": uid, "offset": offset,
                             "graph_row_sha256": sha_bytes((json.dumps(row, sort_keys=True, ensure_ascii=False) + "\n").encode()),
                             "fact_range": (fact.get("syntax") or {}).get("range")})
    if not m.get("imports") == sorted(set(m["imports"])):
        raise ValueError("Import list is not sorted and duplicate-free")
    snap_dir = batch_root / "snapshots" / stem
    if provider_root == COMPLETE_PREVIEW.resolve() and not snap_dir.resolve().is_relative_to(provider_root):
        raise ValueError("Complete provider snapshots escape their selected root")
    plan = read_json(snap_dir / "snapshot-comparison-plan.json")
    req = read_json(snap_dir / "snapshot-requests.json")
    expected_names = [x["name"] for x in declarations]
    if plan.get("source_module") != m["source_module"] or plan.get("generated_module") != m["platform_module"] or plan.get("source_graph_names") != expected_names:
        raise ValueError("Snapshot comparison plan does not match selected graph declarations")
    if plan.get("validated") or plan.get("lean_started"):
        raise ValueError("Snapshot plan falsely claims Lean validation")
    if [x.get("source_graph_name") for x in req.get("original", [])] != expected_names or [x.get("source_graph_name") for x in req.get("generated", [])] != expected_names:
        raise ValueError("Snapshot requests do not match selected graph declaration order")
    for filename, key in (("SnapshotOriginal.lean", "original_exporter_sha256"), ("SnapshotGenerated.lean", "generated_exporter_sha256")):
        if sha(snap_dir / filename) != plan.get(key):
            raise ValueError(f"Snapshot exporter hash mismatch: {filename}")
    if sha(output) != plan.get("generated_bundle_sha256"):
        raise ValueError("Snapshot plan generated bundle hash mismatch")
    return {"batch": batch, "provider_root":provider_root.relative_to(TASK).as_posix(),
            "complete_provider_basis":complete_basis,
            "source_module": m["source_module"], "platform_module": m["platform_module"],
            "manifest": str(mp.relative_to(TASK)), "manifest_sha256": sha(mp), "provider_source": str(output.relative_to(TASK)),
            "provider_source_sha256": sha(output), "graph_sha256": graph_hash, "imports": m["imports"],
            "declarations": declarations, "snapshot_dir": str(snap_dir.relative_to(TASK)),
            "historical_inputs": historical_inputs,
            "supported": True, "preview_only": True, "lean_evidence": False}


def stage_manifests(result: dict[str, Any], include_original_snapshot: bool = True,
                    include_generated_snapshot: bool = True) -> list[dict[str, Any]]:
    """Write only validation-local import certificates for the existing runner."""
    stem = Path(result["manifest"]).name.removesuffix(".manifest.json")
    provider_root = resolve_provider_root(result.get("provider_root", PREVIEW))
    batch_root = provider_root / result["batch"]
    compact_names = provider_root == COMPLETE_PREVIEW.resolve()
    bundle_manifest = read_json(TASK / result["manifest"])
    snap_dir = TASK / result["snapshot_dir"]
    validation_dir = batch_root / "validation" / stem
    validation_dir.mkdir(parents=True, exist_ok=True)
    legacy_paths = {
        "provider-bundle": validation_dir / "bundle-imports.manifest.json",
        "original-snapshot": validation_dir / "original-snapshot-imports.manifest.json",
        "generated-snapshot": validation_dir / "generated-snapshot-imports.manifest.json",
    }
    # Complete-root certificates created before compact naming keep their exact
    # manifest paths and hashes.  New modules use short names for Windows.
    preserve_existing_complete_layout = (compact_names
                                         and all(path.is_file() for path in legacy_paths.values()))
    base = {
        "runtime_sha256": sha(VERIFICATION / "lean-runtime.json"),
        "input_hashes": {},
        "source": bundle_manifest["source"],
        "source_sha256": bundle_manifest["source_sha256"],
        "original_source": bundle_manifest["original_source"],
        "original_source_sha256": bundle_manifest["original_source_sha256"],
    }
    stages = []
    bundle = dict(base, output=bundle_manifest["output"], output_sha256=bundle_manifest["output_sha256"],
                  imports=bundle_manifest["imports"])
    bundle_manifest_path = (legacy_paths["provider-bundle"]
                            if preserve_existing_complete_layout else
                            validation_dir / ("b.json" if compact_names else "bundle-imports.manifest.json"))
    bundle_manifest_path.write_text(json.dumps(bundle, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    bundle_source = workspace_path(bundle_manifest["output"], "provider source")
    stages.append({"source": bundle_source.relative_to(VERIFICATION).as_posix(),
                   "root": batch_root.relative_to(VERIFICATION).as_posix(), "manifest": bundle_manifest_path,
                   "module": result["platform_module"], "imports": bundle_manifest["imports"],
                   "mode": "emit-olean", "role": "provider-bundle"})
    snapshot_specs = []
    if include_original_snapshot:
        snapshot_specs.append(("original-snapshot", "SnapshotOriginal.lean",
                               ["Lean", result["source_module"]], "SnapshotOriginal.lean"))
    if include_generated_snapshot:
        snapshot_specs.append(("generated-snapshot", "SnapshotGenerated.lean",
                               ["Lean", result["platform_module"]], "SnapshotGenerated.lean"))
    for role, filename, imports, snap_name in snapshot_specs:
        snapshot = snap_dir / filename
        sm = dict(base, statement=bundle_manifest["source"], statement_sha256=bundle_manifest["source_sha256"],
                  imports=[bundle_manifest["source_module"] if role == "original-snapshot" else result["platform_module"]],
                  source_components=[{"source_module": result["source_module"]}],
                  snapshot_sha256={snap_name: sha(snapshot)})
        compact = {"original-snapshot": "oi.json", "generated-snapshot": "gi.json"}
        mp = (legacy_paths[role] if preserve_existing_complete_layout else
              validation_dir / (compact[role] if compact_names else f"{role}-imports.manifest.json"))
        mp.write_text(json.dumps(sm, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
        stages.append({"source": (snap_dir.relative_to(VERIFICATION) / filename).as_posix(),
                       "root": (snap_dir.relative_to(VERIFICATION)).as_posix(), "manifest": mp,
                       "module": "SnapshotOriginal" if role == "original-snapshot" else "SnapshotGenerated",
                       "imports": imports,
                       "mode": "modecheck", "role": role})
    return stages


def verify_preflight_record(stage: dict[str, Any]) -> dict[str, Any]:
    source = VERIFICATION / stage["source"]
    record_path = source.with_suffix(source.suffix + ".preflight.json")
    if not record_path.is_file():
        raise ValueError(f"Missing preflight sidecar for {stage['role']}")
    record = read_json(record_path)
    if record.get("success") is not True or record.get("exit_code") != 0 or record.get("timed_out"):
        raise ValueError(f"Preflight failed for {stage['role']}")
    if not 0 < record.get("seconds", 0) <= MAX_SECONDS or record.get("timeout_seconds", 0) > MAX_SECONDS:
        raise ValueError(f"Preflight exceeded 300 seconds for {stage['role']}")
    if record.get("source_sha256_before") != sha(source) or record.get("source_sha256_after") != sha(source) or not record.get("source_unchanged"):
        raise ValueError(f"Preflight source bytes changed for {stage['role']}")
    if record.get("runtime_sha256") != sha(VERIFICATION / "lean-runtime.json") or not record.get("runtime_unchanged"):
        raise ValueError(f"Preflight runtime is stale/unstable for {stage['role']}")
    log = mission_path(record.get("log", ""), "compiler log")
    if sha(log) != record.get("log_sha256") or record.get("stdout_and_stderr_sha256") != record.get("log_sha256"):
        raise ValueError(f"Compiler log hash mismatch for {stage['role']}")
    expected_mode = "emit-olean" if stage["mode"] == "emit-olean" else "modecheck"
    if record.get("mode") != expected_mode or record.get("actual_module_identity") != stage["module"]:
        raise ValueError(f"Preflight module identity or mode mismatch for {stage['role']}")
    if record.get("imports") != stage["imports"]:
        raise ValueError(f"Preflight exact imports differ for {stage['role']}")
    if record.get("manifest_sha256_before") != sha(stage["manifest"]) or record.get("manifest_sha256_after") != sha(stage["manifest"]):
        raise ValueError(f"Preflight manifest changed for {stage['role']}")
    deps = record.get("dependency_oleans")
    if not isinstance(deps, list) or not deps or not all(d.get("stable_during_compile") is True and d.get("sha256_before") == d.get("sha256_after") for d in deps):
        raise ValueError(f"Unstable or missing dependency OLean certificates for {stage['role']}")
    search_roots = [Path(p).resolve() for p in record.get("effective_lean_path", [])]
    seen_deps = set()
    for dep in deps:
        dep_path = Path(dep.get("path", "")).resolve()
        module = dep.get("module", "")
        if not dep_path.is_file() or not module:
            raise ValueError(f"Missing imported OLean for {stage['role']}")
        if sha(dep_path) != dep.get("sha256_after"):
            raise ValueError(f"Imported OLean bytes differ from recorded hash for {module}")
        relative = Path(*module.split(".")).with_suffix(".olean")
        first = next((root / relative for root in search_roots if (root / relative).is_file()), None)
        if first is None or first.resolve() != dep_path or Path(dep.get("resolved_search_root", "")).resolve() not in search_roots:
            raise ValueError(f"Imported OLean resolution is not the recorded first search-path match for {module}")
        seen_deps.add(module)
    if not set(stage["imports"]).issubset(seen_deps):
        raise ValueError(f"Some exact imports lack actual OLean certificates for {stage['role']}")
    output_path, output_hash = record.get("output_olean"), record.get("output_olean_sha256")
    if expected_mode == "emit-olean":
        p = mission_path(output_path or "", "provider emitted OLean")
        expected_olean = (VERIFICATION / "staged-build" / "lib" / "lean" /
                          Path(*stage["module"].split(".")).with_suffix(".olean")).resolve()
        if p.resolve() != expected_olean or not output_hash or sha(p) != output_hash:
            raise ValueError("Emitted provider OLean hash mismatch")
    elif output_path is not None or output_hash is not None:
        raise ValueError(f"Unexpected OLean output in modecheck {stage['role']}")
    return {"role": stage["role"], "record": str(record_path.relative_to(TASK)),
            "record_sha256": sha(record_path), "log": record["log"], "log_sha256": sha(log),
            "actual_module_identity": record["actual_module_identity"], "mode": record["mode"],
            "seconds": record["seconds"], "output_olean": output_path,
            "output_olean_sha256": output_hash, "dependency_oleans": deps}


def compare_snapshots(result: dict[str, Any], stages: list[dict[str, Any]],
                      shared_source: dict[str, Any] | None = None,
                      source_cache_kind: str | None = None,
                      fast_generated: dict[str, Any] | None = None) -> dict[str, Any]:
    stem = Path(result["manifest"]).name.removesuffix(".manifest.json")
    snap_dir = TASK / result["snapshot_dir"]
    plan = read_json(snap_dir / "snapshot-comparison-plan.json")
    req = read_json(snap_dir / "snapshot-requests.json")
    originals = list(shared_source["rows"]) if shared_source is not None else []
    generated = []
    generated_path = (Path(fast_generated["generated_jsonl"]).resolve()
                      if fast_generated is not None else snap_dir / "generated.jsonl")
    paths = [(generated_path, generated)]
    if shared_source is None:
        paths.insert(0, (snap_dir / "original.jsonl", originals))
    for path, target in paths:
        if not path.is_file():
            raise ValueError(f"Snapshot exporter did not create {path.name}")
        target.extend(json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip())
    if len(originals) != len(req["original"]) or len(generated) != len(req["generated"]):
        raise ValueError("Snapshot row counts differ from authenticated request lists")
    compared = []
    for old, new, old_req, new_req in zip(originals, generated, req["original"], req["generated"]):
        for row, request, expected_module in ((old, old_req, result["source_module"]), (new, new_req, result["platform_module"])):
            if row.get("sourceGraphName", row.get("sourceName")) != request["source_graph_name"]:
                raise ValueError("Snapshot graph declaration name differs from request")
            if row.get("module", row.get("sourceModule")) != expected_module:
                raise ValueError("Snapshot declaration module identity differs")
            if (request.get("expected_module") != expected_module or
                    request.get("expected_public_name") != request.get("source_graph_name") or
                    request.get("source_was_private") is not False or
                    row.get("sourceWasPrivate", False) is not False):
                raise ValueError("Snapshot request/public-name/private status mismatch")
            if row.get("resolvedName", request["source_graph_name"]) != request["expected_public_name"]:
                raise ValueError("Snapshot resolved declaration name differs from requested public name")
            if row.get("declGraphSha256") != request["decl_graph_sha256"] or row.get("declGraphRowSha256") != request["decl_graph_row_sha256"]:
                raise ValueError("Snapshot declaration graph witness differs")
            if row.get("closedType") is not True:
                raise ValueError("Snapshot declaration type is not closed")
            kind = request["expected_kind"]
            if kind == "theorem":
                if row.get("value") is not None or row.get("closedValue") is not None:
                    raise ValueError("Theorem proof value must be omitted from interface snapshot")
            elif kind == "def":
                if row.get("closedValue") is not True or row.get("value") is None:
                    raise ValueError("Ordinary definition value is absent or not closed")
            else:
                raise ValueError(f"Unsupported snapshot declaration kind {kind}")
            axioms = row.get("axioms")
            if not isinstance(axioms, list) or not set(axioms).issubset(ALLOWED_AXIOMS):
                raise ValueError("Snapshot axioms are not a subset of Std3")
        if old.get("envKind") != new.get("envKind"):
            raise ValueError("Kernel environment declaration kinds differ")
        for key in ("type", "value"):
            if old.get(key) is None and new.get(key) is None:
                continue
            if norm_expr(old.get(key), old.get("levelParams", [])) != norm_expr(new.get(key), new.get("levelParams", [])):
                raise ValueError(f"Kernel {key} differs for {old_req['source_graph_name']}")
        if set(old.get("axioms", [])) != set(new.get("axioms", [])):
            raise ValueError("Source and generated declaration axiom sets differ")
        compared.append(old_req["source_graph_name"])
    snapshots = ({"original": sha(snap_dir / "original.jsonl"),
                  "generated": sha(snap_dir / "generated.jsonl")}
                 if shared_source is None else
                 {"generated": sha(generated_path)})
    comparison = {"compared_names": compared, "snapshot_jsonl_sha256": snapshots,
                  "types_equal": True, "values_equal": True, "axioms_equal_and_std3": True}
    if shared_source is not None:
        if source_cache_kind == "provider-source-subset":
            comparison["source_snapshot_strategy"] = "provider-source-subset-cache"
            comparison["source_subset_evidence"] = shared_source["evidence"]
        else:
            comparison["source_snapshot_strategy"] = "complete-source-cache"
            comparison["shared_source_evidence"] = shared_source["evidence"]
    if fast_generated is not None:
        comparison["generated_snapshot_strategy"] = "exact-public-Name-direct-env-lookup"
        comparison["fast_generated_jsonl"] = str(generated_path.relative_to(TASK)).replace("\\", "/")
        comparison["fast_generated_provenance"] = fast_generated["fast_generated_provenance"]
        comparison["fast_generated_provenance_sha256"] = fast_generated["fast_generated_provenance_sha256"]
    return comparison


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--batch", required=True, choices=("minimum-statement", "all-shared-safe-leaves"))
    ap.add_argument("--module", required=True, help="Source module, platform module, or manifest stem")
    ap.add_argument("--provider-root", default=str(PREVIEW),
                    help="Mission-relative or absolute provider output root; default retains historical providers-preview")
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check-only", action="store_true")
    mode.add_argument("--run-preflights", action="store_true")
    mode.add_argument("--certify-existing", action="store_true")
    source_cache = ap.add_mutually_exclusive_group()
    source_cache.add_argument("--shared-source-certificate", help="Optional full shared-source certificate; pilot certificates are rejected")
    source_cache.add_argument("--source-subset-certificate", help="Optional certified partial source cache for the exact 174 provider declarations")
    ap.add_argument("--fast-generated-snapshot", action="store_true",
                    help="Use the separately authenticated direct public-Name generated snapshot; requires --source-subset-certificate")
    args = ap.parse_args()
    try:
        provider_root = resolve_provider_root(args.provider_root)
        if args.fast_generated_snapshot and not args.source_subset_certificate:
            raise ValueError("--fast-generated-snapshot requires --source-subset-certificate")
        if args.source_subset_certificate:
            batch_root = provider_root / args.batch
            candidates = []
            for manifest_path in (batch_root / "Definitions").glob("*.manifest.json"):
                manifest = read_json(manifest_path)
                if args.module in (manifest.get("source_module"), manifest.get("platform_module"),
                                    manifest_path.name.removesuffix(".manifest.json")):
                    candidates.append(manifest_path)
            if len(candidates) == 1:
                stem = candidates[0].name.removesuffix(".manifest.json")
                request_doc = read_json(batch_root / "snapshots" / stem / "snapshot-requests.json")
                unsupported = sorted({request.get("expected_kind") for request in request_doc["original"]
                                      if request.get("expected_kind") not in {"theorem", "def"}})
                if unsupported:
                    raise ValueError(
                        "Provider source-subset cache integration currently supports only theorem/def "
                        "comparisons; structural declaration kinds require exact kindMetadata comparison: "
                        + ", ".join(unsupported))
        result = structural_check(args.batch, args.module, provider_root)
        result["mode"] = "check-only" if args.check_only else ("run-preflights" if args.run_preflights else "certify-existing")
        shared_source = None
        source_cache_kind = None
        if args.shared_source_certificate:
            source_cache_kind = "complete-source"
            result["source_snapshot_strategy"] = "complete-source-cache; skip original snapshot compile"
            certp = mission_path(args.shared_source_certificate, "shared source certificate")
            request_doc = read_json(TASK / result["snapshot_dir"] / "snapshot-requests.json")
            shared_source = validate_complete_source_cache(certp, request_doc["original"])
            helper = TASK / "scripts" / "shared_source_certificate_cache.py"
            result["shared_source_certificate"] = dict(
                shared_source["evidence"], cache_validator=helper.relative_to(TASK).as_posix(),
                cache_validator_sha256=sha(helper))
        elif args.source_subset_certificate:
            source_cache_kind = "provider-source-subset"
            result["source_snapshot_strategy"] = "provider-source-subset-cache; skip original snapshot compile"
            certp = mission_path(args.source_subset_certificate, "provider source-subset certificate")
            request_doc = read_json(TASK / result["snapshot_dir"] / "snapshot-requests.json")
            unsupported = sorted({request.get("expected_kind") for request in request_doc["original"]
                                  if request.get("expected_kind") not in {"theorem", "def"}})
            if unsupported:
                raise ValueError(
                    "Provider source-subset cache integration currently supports only theorem/def "
                    "comparisons; structural declaration kinds require exact kindMetadata comparison: "
                    + ", ".join(unsupported))
            shared_source = validate_provider_source_subset_cache(certp, request_doc["original"])
            helper = TASK / "scripts" / "provider_source_subset_cache_windows.py"
            result["source_subset_certificate"] = dict(
                shared_source["evidence"], cache_validator=helper.relative_to(TASK).as_posix(),
                cache_validator_sha256=sha(helper))
        fast_generated = None
        if args.fast_generated_snapshot and args.check_only:
            fast_generated = checked_fast_generated_snapshot(result)
            helper = TASK / "scripts" / "prepare_fast_provider_snapshot.py"
            result["fast_generated_snapshot"] = {
                "strategy": "exact-public-Name-direct-env-lookup",
                "helper": helper.relative_to(TASK).as_posix(),
                "helper_sha256": sha(helper),
                "source": fast_generated["source"],
                "source_sha256": sha(VERIFICATION / fast_generated["source"]),
                "generated_jsonl": str(Path(fast_generated["generated_jsonl"]).resolve().relative_to(TASK)).replace("\\", "/"),
                "generated_jsonl_sha256": sha(Path(fast_generated["generated_jsonl"])),
                "provenance": fast_generated["fast_generated_provenance"],
                "provenance_sha256": fast_generated["fast_generated_provenance_sha256"],
                "ordinary_public_requests_only": True,
                "private_branch_eligible": False,
            }
        if args.check_only:
            result.update({"validated": False, "status": "structural-preview-only", "reason": "No Lean/type/value/axiom preflight evidence was checked"})
            print(json.dumps(result, ensure_ascii=False, indent=2))
            return 0
        stages = stage_manifests(
            result, include_original_snapshot=shared_source is None,
            include_generated_snapshot=not args.fast_generated_snapshot)
        if args.run_preflights:
            runner = TASK / "scripts" / "preflight_staged_module.py"
            for stage in stages:
                command = [sys.executable, str(runner), stage["source"], "--root", stage["root"],
                           "--imports-manifest", stage["manifest"].relative_to(VERIFICATION).as_posix(),
                           "--timeout-seconds", str(MAX_SECONDS)]
                if stage["mode"] == "emit-olean":
                    command.append("--emit-olean")
                completed = subprocess.run(command, cwd=ROOT, check=False)
                if completed.returncode != 0:
                    raise ValueError(f"Preflight runner failed for {stage['role']} with exit {completed.returncode}")
            if args.fast_generated_snapshot:
                fast_generated = stage_fast_generated_snapshot(result)
                fast_stage = {key: fast_generated[key] for key in (
                    "source", "root", "manifest", "module", "imports", "mode", "role")}
                stages.append(fast_stage)
                command = [sys.executable, str(runner), fast_stage["source"], "--root", fast_stage["root"],
                           "--imports-manifest", fast_stage["manifest"].relative_to(VERIFICATION).as_posix(),
                           "--timeout-seconds", str(MAX_SECONDS)]
                completed = subprocess.run(command, cwd=ROOT, check=False)
                if completed.returncode != 0:
                    raise ValueError(f"Preflight runner failed for generated-snapshot with exit {completed.returncode}")
        elif args.fast_generated_snapshot:
            fast_generated = checked_fast_generated_snapshot(result)
            stages.append({key: fast_generated[key] for key in (
                "source", "root", "manifest", "module", "imports", "mode", "role")})
        if fast_generated is not None:
            helper = TASK / "scripts" / "prepare_fast_provider_snapshot.py"
            result["fast_generated_snapshot"] = {
                "strategy": "exact-public-Name-direct-env-lookup",
                "helper": helper.relative_to(TASK).as_posix(),
                "helper_sha256": sha(helper),
                "source": fast_generated["source"],
                "source_sha256": sha(VERIFICATION / fast_generated["source"]),
                "generated_jsonl": str(Path(fast_generated["generated_jsonl"]).resolve().relative_to(TASK)).replace("\\", "/"),
                "generated_jsonl_sha256": sha(Path(fast_generated["generated_jsonl"])),
                "provenance": fast_generated["fast_generated_provenance"],
                "provenance_sha256": fast_generated["fast_generated_provenance_sha256"],
                "ordinary_public_requests_only": True,
                "private_branch_eligible": False,
            }
        preflights = [verify_preflight_record(stage) for stage in stages]
        comparison = compare_snapshots(result, stages, shared_source, source_cache_kind, fast_generated)
        result.update({"validated": True, "status": "local-kernel-provider-validated",
                       "preflights": preflights, "snapshot_comparison": comparison,
                       "proof_axioms": "Std3", "preview_only": True,
                       "submission_ready": False, "current_final_generation_eligible": False})
        validation_dir = provider_root / args.batch / "validation" / Path(result["manifest"]).name.removesuffix(".manifest.json")
        validation_dir.mkdir(parents=True, exist_ok=True)
        cert = validation_dir / ("provider-validation-fast.json" if args.fast_generated_snapshot
                                 else "provider-validation.json")
        cert.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
        print(json.dumps({"validated": True, "certificate": str(cert.relative_to(TASK)),
                          "certificate_sha256": sha(cert), "preflights": preflights,
                          "snapshot_comparison": comparison}, ensure_ascii=False, indent=2))
        return 0
    except Exception as exc:
        print(json.dumps({"validated": False, "status": "rejected", "error": str(exc)}, ensure_ascii=False, indent=2), file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
