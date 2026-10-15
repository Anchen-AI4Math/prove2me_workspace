"""Prepare the AP19 four-definition analytic-remainder provider offline.

There is no pending publication mode.  Final preparation requires all three
actual compiler witnesses and their strict full-ConstantInfo certificate.  A
single ``--check-only`` invocation performs one complete strict replay, writes
the immutable publication bundle, and then checks every frozen hash.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import certify_analytic_remainder_data_existing as consumer
import publish_closed_definition_bundle as payload_driver
import stage_analytic_remainder_data_provider as stage


TASK, ROOT, STAGE = stage.TASK, stage.ROOT, stage.STAGE
KEY = "remainder"
DEST = STAGE / "publication-v2"
CERT = STAGE / "actual-provider-validation.json"
SELF = Path(__file__).resolve()
ONLINE = TASK / "scripts/publish_analytic_remainder_data_definition.py"
API_REVIEW = TASK / "verification/api-review-20261011-v0.12.4"
API_REVIEW_MANIFEST = API_REVIEW / "manifest.json"
ENV = payload_driver.ENV
STD3 = {"propext", "Classical.choice", "Quot.sound"}


def sha_bytes(raw): return hashlib.sha256(raw).hexdigest()
def sha(path): return sha_bytes(Path(path).read_bytes())
def read(path): return json.loads(Path(path).read_text(encoding="utf-8"))
def encode(value):
    return (json.dumps(value, ensure_ascii=False, sort_keys=True,
                       separators=(",", ":")) + "\n").encode("utf-8")
def need(ok, message):
    if not ok: raise ValueError(message)


def exact(path, raw):
    path = Path(path)
    if path.exists() and path.read_bytes() != raw:
        raise ValueError("Frozen AP19 publication artifact differs: " + str(path))
    if not path.exists():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)


def definition_name(config):
    prefix = "Definitions.Def_"
    need(config["platform_module"].startswith(prefix),
         "AP19 Definition module prefix differs")
    return config["platform_module"][len(prefix):]


def static():
    config = stage.config(KEY)
    need(STAGE == config["stage"] and (STAGE / "preparation.json").is_file(),
         "AP19 final provider preparation is pending")
    prep = read(STAGE / "preparation.json")
    academic = read(STAGE / "academic-metadata.json")
    need(set(academic) == {"definition_title", "natural_language_statement",
                           "source_commit", "source_url", "tags"}
         and academic["source_commit"] == stage.COMMIT
         and "$$" in academic["natural_language_statement"],
         "AP19 academic metadata/provenance differs")
    need(prep["artifact_kind"] == "ap19-analytic-remainder-four-Def-preparation"
         and prep["source_commit"] == stage.COMMIT
         and prep["source_modules"] == config["source_modules"]
         and prep["platform_module"] == config["platform_module"]
         and prep["provided_names"] == config["names"] == stage.NAMES
         and prep["provider_file"] == config["provider_file"]
         and prep["imports"] == config["imports"]
         and prep["contains_theorems"] is False
         and prep["own_structures_constructors_recursors"] == []
         and prep["raw_owned_CI_inventory_exported_before_classification"] is True
         and prep["source_theorem_values_not_requested"] is True
         and prep["canonical_CoreData_definition_id"] ==
             "03bc0316-3599-4c4d-97a8-3fce8ad984af"
         and prep["validated"] is False and prep["submission_ready"] is False
         and prep["proposal_status"] == "Draft",
         "AP19 exact four-Definition preparation differs")
    units = prep["exact_source_units"]
    expected = [(name, start, end, [first, last])
                for name, _, start, end, first, last in stage.SPECS]
    need(len(units) == 4
         and [(row["name"], row["start"], row["end"], row["source_lines"])
              for row in units] == expected
         and all(row["ast"]["graph_names"] == [row["name"]]
                 and row["ast"]["graph_kinds"] == ["def"]
                 and row["ast"]["privateTok"] is None
                 for row in units),
         "AP19 original four AST commands/ranges differ")

    provider = STAGE / config["provider_file"]
    raw = provider.read_bytes()
    need(sha(provider) == read(STAGE / "c1.json")["output_sha256"]
         and b"sorry" not in raw and b"theorem " not in raw
         and raw.count(b"def ") == 4,
         "AP19 provider bytes contain proof or non-original declarations")
    expected_imports = [config["imports"], ["Lean"] + config["source_modules"],
                        ["Lean", config["platform_module"]]]
    need([read(STAGE / f"c{i}.json")["imports"] for i in range(1, 4)] ==
             expected_imports,
         "AP19 ordered compiler imports differ")

    metadata = {"definition_title": academic["definition_title"],
                "natural_language_statement": academic["natural_language_statement"],
                "source": academic["source_url"], "tags": academic["tags"]}
    payload = {"definition_name": definition_name(config),
               "definition_title": metadata["definition_title"],
               "definition": raw.decode("utf-8"),
               "natural_language_statement": metadata["natural_language_statement"],
               "source": metadata["source"], "tags": metadata["tags"],
               "env": ENV, "private": False}
    payload_bytes = json.dumps(payload, ensure_ascii=False).encode("utf-8")
    need(payload["definition"].encode("utf-8") == raw,
         "AP19 payload changes exact provider bytes")
    manifest = {"schema_version": 1,
        "artifact_kind": "ap19-analytic-remainder-four-Def-publication-manifest",
        "provider_key": KEY, "definition_name": definition_name(config),
        "definition_module": config["platform_module"],
        "provided_names": config["names"], "environment": ENV,
        "visibility": "public", "source_commit": stage.COMMIT,
        "source_modules": config["source_modules"],
        "source_url": academic["source_url"],
        "provider_source": stage.rel(provider),
        "provider_source_sha256": sha(provider),
        "stage_preparation_sha256": sha(STAGE / "preparation.json"),
        "metadata_sha256": sha_bytes(encode(metadata)),
        "payload_sha256": sha_bytes(payload_bytes),
        "uploaded_definition_sha256": sha_bytes(raw),
        "definition_bytes_equal_provider_source": True,
        "exact_source_definition_count": 4,
        "structural_declaration_domain": [],
        "canonical_CoreData_definition_id": prep["canonical_CoreData_definition_id"],
        "route": "/submit-definition", "expected_readback_status": "Definition",
        "validated": CERT.is_file(), "submission_ready": False,
        "proposal_status": "Draft"}
    return config, prep, provider, raw, metadata, payload, payload_bytes, manifest


def replay(config, prep, cert):
    actual = consumer.validate(KEY)
    need(stage.encode(actual) == CERT.read_bytes() and actual == cert,
         "AP19 certificate differs from its one complete strict replay")
    need(cert["schema_version"] == 1
         and cert["artifact_kind"] ==
             "ap19-analytic-remainder-four-Def-actual-provider-validation"
         and cert["source_commit"] == stage.COMMIT
         and cert["source_modules"] == config["source_modules"]
         and cert["platform_module"] == config["platform_module"]
         and cert["provided_names"] == config["names"]
         and cert["validated"] is True and cert["Std3_only"] is True
         and cert["source_and_generated_types_equal"] is True
         and cert["contains_theorems"] is False
         and cert["submission_ready"] is False
         and cert["proposal_status"] == "Draft"
         and cert["Lean_started_by_consumer"] is False
         and cert["API_used"] is False
         and cert["provider_source_sha256"] == sha(STAGE / config["provider_file"])
         and cert["preparation_sha256"] == sha(STAGE / "preparation.json")
         and cert["compiler_manifest_sha256"] ==
             {f"c{i}.json": sha(STAGE / f"c{i}.json") for i in range(1, 4)}
         and set(cert["preflights"]) ==
             {config["provider_file"], stage.SOURCE_SNAPSHOT, stage.GENERATED_SNAPSHOT}
         and 0 < cert["max_file_seconds"] <= 300,
         "AP19 type/value/owner/Std3 certificate contract differs")
    differences = cert["actual_definition_value_proof_cache_differences"]
    inherited_pair = read(stage.CORE_CERT)["certified_actual_helper_pair"]
    expected_pair = [inherited_pair["source_name"], inherited_pair["generated_name"]]
    need(cert["raw_definition_values_equal"] is (not differences)
         and cert["definition_values_equal_and_exported"] is (not differences)
         and cert["raw_equal_definition_count"] + len(differences) == 4
         and cert["definition_values_equal_after_exact_inherited_closed_Prop_substitution"] is True
         and len({row["name"] for row in differences}) == len(differences)
         and all(row["name"] in config["names"]
                 and row["exact_inherited_closed_Prop_helper_pair"] == expected_pair
                 and isinstance(row["source_value_sha256"], str)
                 and isinstance(row["generated_value_sha256"], str)
                 for row in differences)
         and cert["canonical_CoreData_certificate_sha256"] == sha(stage.CORE_CERT)
         and cert["canonical_CoreData_definition_id"] ==
             "03bc0316-3599-4c4d-97a8-3fce8ad984af"
         and cert["canonical_CoreData_OLean_sha256"] == stage.CORE_OLEAN_SHA
         and cert["canonical_CoreData_raw_equal_definitions"] == 12
         and cert["canonical_CoreData_actual_closed_Prop_substitution_defs"] == 2
         and cert["raw_owned_CI_inventory_exact"] is True
         and cert["actual_owned_public_names"] == sorted(config["names"])
         and len(cert["actual_owned_public_names"]) ==
             len(set(cert["actual_owned_public_names"])),
         "AP19 finite inherited proof-cache substitution or owned CI inventory differs")
    need(cert["source_module_by_name"] ==
             {name: next(row["source_module"] for row in prep["exact_source_units"]
                         if row["name"] == name) for name in config["names"]}
         and cert["actual_owners"]["source"] == cert["source_module_by_name"]
         and cert["actual_owners"]["generated"] ==
             {name: config["platform_module"] for name in config["names"]},
         "AP19 source/generated Definition owners differ")
    for axioms in cert["axioms"].values():
        need(set(axioms) <= STD3, "AP19 nonstandard axiom")
    for path, expected in cert["implementation_hashes"].items():
        need(sha(TASK / path) == expected, "AP19 implementation changed: " + path)
    for path, expected in cert["output_json_sha256"].items():
        need(sha(TASK / path) == expected, "AP19 full-CI JSON changed: " + path)
    need(sha(TASK / cert["provider_olean"]) == cert["provider_olean_sha256"],
         "AP19 provider OLean changed")


def preflight_hashes(cert):
    found = {}
    for row in cert["preflights"].values():
        found[row["record"]] = row["record_sha256"]
        for key in ("source", "manifest", "log"):
            value = row["data"][key]
            found[value] = sha(consumer.context.file(value))
    return dict(sorted(found.items()))


def dependency_oleans(cert):
    found = {}
    for row in cert["preflights"].values():
        for dep in row["data"]["dependency_oleans"]:
            need(dep["stable_during_compile"] is True
                 and dep["sha256_before"] == dep["sha256_after"],
                 "AP19 dependency OLean changed during actual compilation")
            found[dep["module"] + "|" + dep["path"]] = dep["sha256_before"]
    return dict(sorted(found.items()))


def api_review():
    review = read(API_REVIEW_MANIFEST)
    docs = {row["name"]: row["sha256"] for row in review["documents"]}
    need(review["official_tag"] == "v0.12.4"
         and review["official_commit"] == "78989800ba0b3149ee34205257025bd0f617e8ef"
         and all(sha(API_REVIEW / name) == expected for name, expected in docs.items()),
         "Reviewed official API docs differ")
    return {"official_tag": review["official_tag"],
            "official_commit": review["official_commit"],
            "manifest_sha256": sha(API_REVIEW_MANIFEST), "documents": docs}


def prepare():
    config, prep, provider, raw, metadata, payload, payload_bytes, manifest = static()
    need(CERT.is_file(), "AP19 actual three-context certificate is pending")
    cert = read(CERT)
    replay(config, prep, cert)
    pins = {"schema_version": 1,
        "artifact_kind": "ap19-analytic-remainder-four-Def-publication-preparation",
        "provider_key": KEY, "definition_name": definition_name(config),
        "definition_module": config["platform_module"],
        "environment": ENV, "visibility": "public",
        "offline_wrapper_sha256": sha(SELF),
        "online_wrapper_sha256": sha(ONLINE),
        "publisher_script_sha256": sha(Path(payload_driver.__file__)),
        "api_client_sha256": sha(ROOT / "scripts/p2m_api.py"),
        "stage_producer_sha256": sha(Path(stage.__file__)),
        "strict_consumer_sha256": sha(Path(consumer.__file__)),
        "stage_preparation_sha256": sha(STAGE / "preparation.json"),
        "validation_sha256": sha(CERT),
        "manifest_sha256": sha_bytes(encode(manifest)),
        "metadata_sha256": sha_bytes(encode(metadata)),
        "payload_sha256": sha_bytes(payload_bytes),
        "provider_source_sha256": sha(provider),
        "uploaded_definition_sha256": sha_bytes(raw),
        "exact_source_definition_count": 4,
        "structural_declaration_domain": [],
        "ordered_imports": {config["provider_file"]: read(STAGE / "c1.json")["imports"],
                            stage.SOURCE_SNAPSHOT: read(STAGE / "c2.json")["imports"],
                            stage.GENERATED_SNAPSHOT: read(STAGE / "c3.json")["imports"]},
        "compiler_manifest_sha256": cert["compiler_manifest_sha256"],
        "stage_input_hashes": prep["input_hashes"],
        "preflight_artifact_sha256": preflight_hashes(cert),
        "dependency_olean_sha256": dependency_oleans(cert),
        "implementation_hashes": cert["implementation_hashes"],
        "kernel_type_value_snapshots": cert["output_json_sha256"],
        "actual_definition_value_proof_cache_differences":
            cert["actual_definition_value_proof_cache_differences"],
        "raw_definition_values_equal": cert["raw_definition_values_equal"],
        "definition_values_equal_after_exact_inherited_closed_Prop_substitution": True,
        "provider_olean": cert["provider_olean"],
        "provider_olean_sha256": cert["provider_olean_sha256"],
        "canonical_CoreData_definition_id": prep["canonical_CoreData_definition_id"],
        "canonical_CoreData_certificate_sha256":
            prep["canonical_CoreData_certificate_sha256"],
        "published30_coverage_sha256": prep["published_coverage_sha256"],
        "frozen_actual_Published30_baseline_sha256":
            prep["frozen_actual_Published30_baseline_sha256"],
        "route": "/submit-definition", "expected_readback_status": "Definition",
        "official_api_review": api_review(),
        "one_complete_strict_replay_performed": True,
        "subsequent_HTTP_guards_are_hash_only": True,
        "at_most_once_policy": "durable publish_intent before POST; never repeat a recorded intent",
        "API_used": False, "submission_ready": False, "proposal_status": "Draft"}
    exact(DEST / "manifest.json", encode(manifest))
    exact(DEST / "validation.json", CERT.read_bytes())
    exact(DEST / "metadata.json", encode(metadata))
    exact(DEST / "publish-payload.json", payload_bytes)
    exact(DEST / "wire-definition-source.lean", raw)
    exact(DEST / "preparation.json", encode(pins))
    return {"prepared": True, "provider": KEY, "network_used": False,
            "one_complete_strict_replay_performed": True,
            "payload_sha256": pins["payload_sha256"], "proposal_status": "Draft"}


def hash_gate(pins):
    config = stage.config(KEY)
    direct = {SELF: pins["offline_wrapper_sha256"],
              ONLINE: pins["online_wrapper_sha256"],
              Path(payload_driver.__file__): pins["publisher_script_sha256"],
              ROOT / "scripts/p2m_api.py": pins["api_client_sha256"],
              Path(stage.__file__): pins["stage_producer_sha256"],
              Path(consumer.__file__): pins["strict_consumer_sha256"],
              STAGE / "preparation.json": pins["stage_preparation_sha256"],
              CERT: pins["validation_sha256"],
              STAGE / config["provider_file"]: pins["provider_source_sha256"]}
    for path, expected in direct.items():
        need(sha(path) == expected, "AP19 frozen implementation/evidence changed: " + str(path))
    for path, expected in pins["implementation_hashes"].items():
        need(sha(TASK / path) == expected, "AP19 strict implementation changed: " + path)
    for path, expected in pins["stage_input_hashes"].items():
        need(sha(TASK / path) == expected, "AP19 stage input changed: " + path)
    for filename, expected in pins["compiler_manifest_sha256"].items():
        need(sha(STAGE / filename) == expected, "AP19 compiler manifest changed: " + filename)
    for path, expected in pins["preflight_artifact_sha256"].items():
        need(sha(consumer.context.file(path)) == expected,
             "AP19 preflight artifact changed: " + path)
    for key, expected in pins["dependency_olean_sha256"].items():
        need(sha(Path(key.split("|", 1)[1])) == expected,
             "AP19 imported OLean changed: " + key)
    for path, expected in pins["kernel_type_value_snapshots"].items():
        need(sha(TASK / path) == expected, "AP19 full-CI JSON changed: " + path)
    need(sha(TASK / pins["provider_olean"]) == pins["provider_olean_sha256"],
         "AP19 provider OLean changed")
    need((DEST / "preparation.json").read_bytes() == encode(pins)
         and sha(DEST / "manifest.json") == pins["manifest_sha256"]
         and sha(DEST / "validation.json") == pins["validation_sha256"]
         and sha(DEST / "metadata.json") == pins["metadata_sha256"]
         and sha(DEST / "publish-payload.json") == pins["payload_sha256"]
         and sha(DEST / "wire-definition-source.lean") ==
             pins["uploaded_definition_sha256"],
         "AP19 frozen publication artifacts changed")
    need(api_review() == pins["official_api_review"], "AP19 API review pins changed")


def frozen():
    pins = read(DEST / "preparation.json")
    hash_gate(pins)
    return pins, read(DEST / "metadata.json"), read(DEST / "publish-payload.json"), \
        (DEST / "publish-payload.json").read_bytes()


def check():
    result = prepare()
    frozen()
    return {"checked": True, **{k: v for k, v in result.items() if k != "prepared"}}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--provider", choices=stage.CONFIGS, default=KEY)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--prepare-only", action="store_true")
    modes.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    print(json.dumps(prepare() if args.prepare_only else check(),
                     ensure_ascii=False, indent=2))
