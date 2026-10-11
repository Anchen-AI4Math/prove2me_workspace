"""Construct scope restoration evidence and a source-only Lean probe.

The probe imports the original source module. It tests scope reconstruction,
not platform dependency closure, and is never eligible for submission.
"""
import hashlib
import json
from pathlib import Path

from generate_platform_nodes import NodeGenerator
from platform_statement import declaration_fragment
from restore_node_context import restore_context

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]


def main():
    base = NodeGenerator(True)
    records, rejected = [], []
    probe_name = "OAI.PiExponent.AmpleGlobalGeneration.ample_eventual_global_generators"
    stage = TASK / "verification/context-restoration"
    stage.mkdir(parents=True, exist_ok=True)
    probe = None
    for key in base.g.artifact_plan["node_order"]:
        unit = base.g.units[key]
        scope = base.g.scope_for(unit)
        raw, facts, wrappers, origin = base.load_module(unit["module"])
        try:
            restored = restore_context(raw, facts, scope, origin["source_sha256"])
            records.append({"node": key, "source_module": unit["module"],
                            "names": unit["graph_names"], "restoration": restored})
            if unit["graph_names"] == [probe_name]:
                fragment, hoisted, ledger = declaration_fragment(
                    raw, unit, wrappers[unit["start"]["offset"]], "scope_probe",
                    origin["source_sha256"], stub=False)
                content = ("import Lean\nimport " + unit["module"] + "\n\n" + restored["preamble"]
                           + "\n".join(row["text"] for row in hoisted) + "\n"
                           + fragment.decode("utf-8") + restored["closing"]
                           + (TASK / "verification/TypedSnapshotCore.inc").read_text(encoding="utf-8")
                           + "\nrun_meta do\n"
                           + "  PiExponentInterfaceSnapshot.exportSnapshot #[`" + probe_name
                           + ", `scope_probe] " + json.dumps((stage / "types.json").relative_to(ROOT).as_posix())
                           + "\n#print axioms scope_probe\n")
                path = stage / "ContextScopeProbe.lean"
                path.write_bytes(content.encode("utf-8"))
                probe = {"output": path.relative_to(ROOT).as_posix(),
                         "output_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
                         "source": origin["source"], "source_sha256": origin["source_sha256"],
                         "original_source": origin["original_source"],
                         "original_source_sha256": origin["original_source_sha256"],
                         "source_commit": "adc7f1241b42e322a6451854ab7e4b4c146bf78a",
                         "original_declaration": probe_name, "generated_declaration": "scope_probe",
                         "origin": origin, "restoration": restored, "fragment_edits": ledger,
                         "imports": ["Lean", unit["module"]],
                         "input_hashes": {path: value for path, value in base.g.input_hashes.items()
                                          if path != "verification/extraction-state.json"},
                         "append_only_extraction_state_at_generation_sha256":
                             base.g.input_hashes["verification/extraction-state.json"],
                         "dependency_policy": "Probe depends on exact source/fact bytes and frozen inventories; unrelated append-only extraction entries are not compilation inputs.",
                         "snapshot_core_sha256": base.core_sha,
                         "runtime_sha256": base.runtime_sha,
                         "validated": False, "submission_ready": False,
                         "source_only_scope_probe": True}
        except ValueError as error:
            rejected.append({"node": key, "reason": str(error)})
    report = {"input_hashes": base.g.input_hashes, "total_nodes": len(records)+len(rejected),
              "constructed_contexts": len(records), "rejected": rejected, "nodes": records,
              "validated": False, "submission_ready": False,
              "meaning": "AST construction only; source-only probe is not a platform proof."}
    (stage / "audit.json").write_bytes((json.dumps(report, ensure_ascii=False, indent=2)+"\n").encode("utf-8"))
    if probe is None:
        raise ValueError("The chosen source scope probe was absent from the frozen plan")
    (stage / "probe-manifest.json").write_bytes((json.dumps(probe, indent=2)+"\n").encode("utf-8"))
    print(json.dumps({"total_nodes": report["total_nodes"], "constructed_contexts": len(records),
                      "rejected": rejected, "probe": probe["output"], "source_only": True}))


if __name__ == "__main__":
    main()
