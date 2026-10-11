"""Preserve the existing exporter and disable unused theorem proof serialization."""
import hashlib
import json
from pathlib import Path

TASK = Path(__file__).resolve().parents[1]


def main():
    source = TASK / "verification/TypedSnapshotCore.inc"
    output = TASK / "verification/TypeOnlyTheoremSnapshotCore.inc"
    original = source.read_bytes()
    old = b"      | .thmInfo t => some t.value"
    new = b"      | .thmInfo _ => none"
    if original.count(old) != 1:
        raise ValueError("The preserved exporter has no unique expected theorem-value branch")
    transformed = original.replace(old, new)
    if output.exists() and output.read_bytes() != transformed:
        raise ValueError("Refusing to overwrite a different theorem-type-only exporter")
    output.write_bytes(transformed)
    report = {"source": source.relative_to(TASK).as_posix(),
              "source_sha256": hashlib.sha256(original).hexdigest(),
              "output": output.relative_to(TASK).as_posix(),
              "output_sha256": hashlib.sha256(transformed).hexdigest(),
              "edit": {"offset": original.index(old), "original": old.decode(), "replacement": new.decode()},
              "preserved": ["closed kernel types", "all universe/binder information", "ordinary definition values"],
              "theorem_values": None, "lean_validated": False,
              "why": "Proof values are not part of theorem interface equality. Actual compiler and axiom checks certify the proof; serializing them can expand a short source proof to hundreds of MB."}
    manifest = output.with_suffix(".lineage.json")
    data = (json.dumps(report, indent=2)+"\n").encode("utf-8")
    if manifest.exists() and manifest.read_bytes() != data:
        raise ValueError("Refusing to overwrite an exporter lineage witness")
    manifest.write_bytes(data)
    print(json.dumps({"output": report["output"], "output_sha256": report["output_sha256"],
                      "source_unchanged": source.read_bytes() == original, "lean_validated": False}))


if __name__ == "__main__":
    main()
