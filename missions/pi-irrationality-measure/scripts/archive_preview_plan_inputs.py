"""Preserve immutable 799-module generation inputs before final inventory refresh."""
import hashlib
import json
from pathlib import Path

TASK = Path(__file__).resolve().parents[1]


def main():
    stage = TASK / "verification/plan-history/799-publication"
    paths = {
        "verification/ast-unit-inventory.json", "verification/ast-scope-inventory.json",
        "verification/ast-wrapper-inventory.json", "verification/ast-import-inventory.json",
        "verification/platform-unit-plan-preview.json", "verification/platform-artifact-plan-preview.json",
        "verification/TypedSnapshotCore.inc", "scripts/generate_platform_bundles.py",
        "scripts/generate_platform_nodes.py", "scripts/plan_platform_units.py",
        "scripts/plan_platform_artifacts.py", "platform/deprivate-name-overrides.json",
        "platform/source-theorem-name-overrides.json", "platform/definition-reuse-candidates.json",
        "platform/upload-route.json", "verification/decl_graph.jsonl", "verification/lean-runtime.json",
    }
    for stem in ("Collision", "AnalyticCollision"):
        manifest_path = TASK / ("verification/definition-validation/Def_OAI_NumberTheory_PiExponent_Analysis_"
                                + stem + "/manifest.json")
        if manifest_path.exists():
            manifest = json.loads(manifest_path.read_bytes())
            paths.update(path for path in manifest.get("input_hashes", {})
                         if path != "verification/extraction-state.json")
    inventory = json.loads((TASK / "verification/ast-unit-inventory.json").read_bytes())
    count = len(inventory["modules"])
    if count != 799:
        raise ValueError("Archive is specifically for the existing 799-module publication lineage")
    records = {}
    for relative in sorted(paths):
        source = (TASK / relative).resolve()
        if not source.is_relative_to(TASK.resolve()) or not source.is_file():
            raise ValueError("Invalid frozen input path: " + relative)
        raw = source.read_bytes()
        digest = hashlib.sha256(raw).hexdigest()
        output = stage / relative
        if output.exists() and output.read_bytes() != raw:
            raise ValueError("A prior immutable archive differs: " + relative)
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_bytes(raw)
        if source.read_bytes() != raw:
            raise ValueError("Frozen generation input changed while archiving: " + relative)
        records[relative] = {"sha256": digest, "bytes": len(raw),
                             "archive": output.relative_to(TASK).as_posix()}
    report = {"indexed_modules": count, "input_files": records,
              "source_commit": "adc7f1241b42e322a6451854ab7e4b4c146bf78a",
              "extraction_state_not_archived": True,
              "reason": "Live append-only extraction state is not the historical 799-module state. Exact module source/AST witnesses remain separately pinned in each stage.",
              "validated": False, "meaning": "Byte preservation of existing inputs, not a new proof certificate."}
    data = (json.dumps(report, indent=2)+"\n").encode("utf-8")
    output = stage / "archive-manifest.json"
    if output.exists() and output.read_bytes() != data:
        raise ValueError("Refusing to change immutable archive manifest")
    output.write_bytes(data)
    print(json.dumps({"archived_files": len(records), "indexed_modules": count,
                      "bytes": sum(row["bytes"] for row in records.values()),
                      "manifest": output.relative_to(TASK).as_posix()}))


if __name__ == "__main__":
    main()
