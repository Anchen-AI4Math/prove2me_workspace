"""Replay the frozen p1j consumer with four exact task-relative path bindings."""
import json
from pathlib import Path
from unittest.mock import patch

import certify_pi_parameters_p1j_existing as consumer

SELF = Path(__file__).resolve()
TASK, V, STAGE = consumer.TASK, consumer.V, consumer.STAGE
FINAL = consumer.CERT
BASE = STAGE / "p1j-validation.base.json"


def certify():
    manifest = consumer.read(STAGE / "manifest.json")
    bindings = {}
    for section, keys in (
        ("definition_dependency", ("structural_certificate", "first_search_olean")),
        ("proved_child_dependency", ("actual_child_certificate", "olean")),
    ):
        row = manifest[section]
        for key in keys:
            relative, digest = row[key], row[key + "_sha256"]
            expected = (TASK / relative).resolve()
            if (not relative.startswith("verification/")
                    or not expected.is_relative_to(V.resolve())
                    or not expected.is_file() or consumer.sha(expected) != digest):
                raise ValueError("Exact task-relative dependency pin differs: " + relative)
            bindings[relative] = {"path": expected, "sha256": digest}

    class ExactDependencyRoot:
        def __truediv__(self, value):
            if value not in bindings:
                raise ValueError("Consumer requested an unbound dependency path: " + str(value))
            item = bindings[value]
            if consumer.sha(item["path"]) != item["sha256"]:
                raise ValueError("Dependency changed during consumer replay")
            return item["path"]

    with patch.object(consumer, "V", ExactDependencyRoot()), patch.object(consumer, "CERT", BASE):
        report = consumer.certify()
    report["implementation_hashes"][consumer.rel(SELF)] = consumer.sha(SELF)
    report["path_resolution_bridge"] = {
        "scope": "four frozen manifest dependency paths already prefixed verification/",
        "bindings": {key: {"path": consumer.rel(value["path"]), "sha256": value["sha256"]}
                     for key, value in bindings.items()},
        "base_consumer_report": consumer.rel(BASE),
        "base_consumer_report_sha256": consumer.sha(BASE),
        "frozen_consumer_sha256": consumer.sha(Path(consumer.__file__)),
        "all_kernel_preflight_owner_axiom_and_type_gates_unchanged": True,
        "Lean_started": False, "API_used": False,
    }
    raw = (json.dumps(report, ensure_ascii=False, indent=2) + "\n").encode()
    if FINAL.exists() and FINAL.read_bytes() != raw:
        raise ValueError("Existing final certificate differs; preserve it")
    if not FINAL.exists():
        FINAL.write_bytes(raw)
    return {"validated": report["validated"], "certificate": consumer.rel(FINAL),
            "certificate_sha256": consumer.sha(FINAL), "max_file_seconds": report["max_file_seconds"]}


if __name__ == "__main__":
    print(json.dumps(certify(), ensure_ascii=False))
