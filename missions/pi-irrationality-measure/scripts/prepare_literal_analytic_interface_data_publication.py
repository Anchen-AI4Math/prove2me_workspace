"""Prepare AP20's exact seventeen-Def interface package without networking.

Final preparation requires the genuine three-context certificate.  Its one
strict replay is performed here once; every later HTTP guard is hash-only.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import certify_literal_analytic_interface_data_existing as consumer
import stage_literal_analytic_interface_data_provider as stage


TASK, ROOT, STAGE = stage.TASK, stage.ROOT, stage.STAGE
SELF = Path(__file__).resolve()
ONLINE = TASK / "scripts/publish_literal_analytic_interface_data_definition.py"
CERT = stage.CERTIFICATE
DEST = STAGE / "publication"
KEY = "interface"
ENV = "0df444a360eaa60ab8c11dca51a86af692955474"
API = ROOT / "scripts/p2m_api.py"
API_REVIEW = TASK / "verification/api-review-20261011-v0.12.4"
STD3 = {"propext", "Classical.choice", "Quot.sound"}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha_bytes(raw): return hashlib.sha256(raw).hexdigest()
def sha(path): return sha_bytes(Path(path).read_bytes())
def read(path): return json.loads(Path(path).read_text(encoding="utf-8"))
def encode(value):
    return (json.dumps(value, ensure_ascii=False, sort_keys=True,
                       separators=(",", ":")) + "\n").encode("utf-8")


def exact(path, raw):
    path = Path(path)
    if path.exists() and path.read_bytes() != raw:
        raise ValueError("Frozen AP20 publication artifact differs: " + str(path))
    if not path.exists():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)


def resolved(path):
    p = Path(path)
    return p if p.is_absolute() else TASK / p


def definition_name(config):
    prefix = "Definitions.Def_"
    need(config["platform_module"].startswith(prefix),
         "AP20 Definition module prefix differs")
    return config["platform_module"][len(prefix):]


def static_artifacts():
    stage.check_only(KEY)
    config = stage.config(KEY)
    prep = read(STAGE / "preparation.json")
    academic = read(STAGE / "academic-metadata.json")
    need(set(academic) == {"definition_title", "natural_language_statement",
                           "source_commit", "source_url", "tags"}
         and academic["source_commit"] == stage.COMMIT
         and academic["source_url"].startswith(
             "https://github.com/openai/math/blob/" + stage.COMMIT + "/")
         and all(token in academic["natural_language_statement"]
                 for token in ("seventeen definitions", "$w=", "$\\omega=2\\pi i$", "asserts no estimate")),
         "AP20 academic metadata/source provenance differs")
    need(prep["artifact_kind"] == "ap20-literal-interface-original17Def-preparation"
         and prep["source_commit"] == stage.COMMIT
         and prep["platform_module"] == config["platform_module"]
         and prep["provider_file"] == config["provider_file"]
         and prep["provided_names"] == config["names"] == stage.NAMES
         and prep["source_modules"] == config["source_modules"]
         and prep["imports"] == config["imports"]
         and prep["original17_source_lines"] == 49
         and prep["candidate_provider_bytes_unchanged"] is True
         and prep["raw_owned_CI_inventory_exported_before_classification"] is True
         and prep["complete_environment_inventory_owner_index_first"] is True
         and prep["actual_used_proof_CI_inventory_no_guessed_names"] is True
         and prep["contains_theorems"] is False
         and prep["own_structures_constructors_recursors"] == []
         and prep["validated"] is False and prep["submission_ready"] is False
         and prep["proposal_status"] == "Draft",
         "AP20 exact source/module/preparation contract differs")
    units = prep["exact_source_units"]
    need(len(units) == 17 and [row["name"] for row in units] == stage.NAMES
         and all(row["ast"]["graph_names"] == [row["name"]]
                 and row["ast"]["graph_kinds"] == ["def"]
                 and row["finite_source_port_version_adaptation"] is None
                 and sha(TASK / row["source"]) == row["source_sha256"]
                 and sha(TASK / row["original"]) == row["original_sha256"]
                 for row in units),
         "AP20 exact seventeen original AST/source rows differ")
    provider = STAGE / config["provider_file"]
    raw = provider.read_bytes()
    need(sha(provider) == read(STAGE / "c1.json")["output_sha256"]
         and b"sorry" not in raw and b"theorem " not in raw,
         "AP20 provider bytes contain proof material or differ from c1")
    for row in units:
        source = (TASK / row["source"]).read_bytes()
        command = source[row["start"]:row["end"]]
        need(sha_bytes(command) == row["command_sha256"] and raw.count(command) == 1,
             "AP20 original command is not preserved exactly once: " + row["name"])
    metadata = {"definition_title": academic["definition_title"],
                "natural_language_statement": academic["natural_language_statement"],
                "source": academic["source_url"], "tags": academic["tags"]}
    payload = {"definition_name": definition_name(config),
               "definition_title": metadata["definition_title"],
               "definition": raw.decode("utf-8"),
               "natural_language_statement": metadata["natural_language_statement"],
               "source": metadata["source"], "tags": metadata["tags"],
               "env": ENV, "private": False}
    payload_raw = json.dumps(payload, ensure_ascii=False).encode("utf-8")
    need(payload["definition"].encode("utf-8") == raw,
         "AP20 payload changes provider source bytes")
    manifest = {"schema_version": 1,
        "artifact_kind": "ap20-literal-interface-seventeen-Def-publication-manifest",
        "provider_key": KEY, "definition_name": payload["definition_name"],
        "definition_module": config["platform_module"],
        "provided_names": config["names"], "source_modules": config["source_modules"],
        "environment": ENV, "visibility": "public", "source_commit": stage.COMMIT,
        "source_url": academic["source_url"], "provider_source": stage.rel(provider),
        "provider_source_sha256": sha(provider),
        "stage_preparation_sha256": sha(STAGE / "preparation.json"),
        "metadata_sha256": sha_bytes(encode(metadata)),
        "payload_sha256": sha_bytes(payload_raw),
        "uploaded_definition_sha256": sha_bytes(raw),
        "definition_bytes_equal_provider_source": True,
        "exact_source_definition_count": 17, "exact_source_lines": 49,
        "contains_theorems": False, "structural_declaration_domain": [],
        "route": "/submit-definition", "expected_readback_status": "Definition",
        "validated": CERT.is_file(), "submission_ready": False,
        "proposal_status": "Draft"}
    return config, prep, provider, raw, metadata, payload, payload_raw, manifest


def historical_witness_hashes(cert):
    found, deps = {}, {}
    for witness in cert["preflights"].values():
        data = witness["data"]
        need(sha(resolved(witness["record"])) == witness["record_sha256"],
             "AP20 compiler record changed")
        found[witness["record"]] = witness["record_sha256"]
        need(data["source_unchanged"] is True
             and data["source_sha256_before"] == data["source_sha256_after"]
             and sha(resolved(data["source"])) == data["source_sha256_before"],
             "AP20 source differs from historical before/after witness")
        need(data["manifest_unchanged"] is True
             and data["manifest_sha256_before"] == data["manifest_sha256_after"]
             and sha(resolved(data["manifest"])) == data["manifest_sha256_before"],
             "AP20 manifest differs from historical before/after witness")
        need(sha(resolved(data["log"])) == data["log_sha256"] == data["stdout_and_stderr_sha256"],
             "AP20 log differs from historical compiler witness")
        found[data["source"]] = data["source_sha256_before"]
        found[data["manifest"]] = data["manifest_sha256_before"]
        found[data["log"]] = data["log_sha256"]
        for dep in data["dependency_oleans"]:
            need(dep["stable_during_compile"] is True
                 and dep["sha256_before"] == dep["sha256_after"]
                 and sha(Path(dep["path"])) == dep["sha256_before"],
                 "AP20 dependency OLean differs from historical witness")
            deps[dep["path"]] = dep["sha256_before"]
        if data["output_olean"] is not None:
            need(sha(resolved(data["output_olean"])) == data["output_olean_sha256"],
                 "AP20 emitted OLean differs")
            deps[data["output_olean"]] = data["output_olean_sha256"]
    return dict(sorted(found.items())), dict(sorted(deps.items()))


def replay(cert, config, prep, provider):
    actual = consumer.validate(KEY)
    need(stage.encode(actual) == CERT.read_bytes() and actual == cert,
         "AP20 certificate differs from its one strict full replay")
    differences = cert["actual_definition_value_proof_cache_differences"]
    pairs = cert["actual_source_generated_closed_Prop_CI_pairs"]
    owned = cert["actual_owned_CI_names"]
    need(cert["schema_version"] == 1
         and cert["artifact_kind"] ==
             "ap20-literal-interface-seventeen-Def-actual-provider-validation"
         and cert["source_commit"] == stage.COMMIT
         and cert["platform_module"] == config["platform_module"]
         and cert["provided_names"] == config["names"]
         and cert["provider_source_sha256"] == sha(provider)
         and cert["preparation_sha256"] == sha(STAGE / "preparation.json")
         and cert["source_and_generated_types_equal"] is True
         and cert["raw_definition_values_equal"] is cert["definition_values_equal_and_exported"]
         and cert["raw_equal_definition_count"] + len(differences) == 17
         and cert["definition_values_equal_after_exact_observed_closed_Prop_substitution"] is True
         and isinstance(pairs, list)
         and all(row["actual_kernel_isProp"] is True
                 and row["closedType"] is True and row["closedValue"] is True
                 and set(row["axioms"]) <= STD3 for row in pairs)
         and owned == sorted(set(owned)) and set(stage.NAMES) <= set(owned)
         and cert["actual_owned_public_names"] == sorted(set(cert["actual_owned_public_names"]))
         and cert["raw_owned_CI_inventory_exact"] is True
         and cert["complete_environment_owner_index_first"] is True
         and cert["contains_theorems"] is False
         and cert["own_structures_constructors_recursors"] == []
         and cert["Std3_only"] is True and cert["validated"] is True
         and cert["submission_ready"] is False and cert["proposal_status"] == "Draft"
         and cert["Lean_started_by_consumer"] is False and cert["API_used"] is False
         and 0 < cert["max_file_seconds"] <= 300,
         "AP20 strict seventeen-Def/actual-CI contract differs")
    need(cert["compiler_manifest_sha256"] ==
             {f"c{i}.json": sha(STAGE / f"c{i}.json") for i in range(1, 4)}
         and set(cert["preflights"]) ==
             {stage.PROVIDER_FILE, stage.SOURCE_SNAPSHOT, stage.GENERATED_SNAPSHOT}
         and cert["provider_olean_sha256"] == sha(resolved(cert["provider_olean"])),
         "AP20 actual compiler/OLean evidence differs")
    need(cert["actual_owners"]["generated"] ==
             {name: stage.PLATFORM_MODULE for name in stage.NAMES}
         and set(cert["axioms"]) == {side + ":" + name
             for side in ("source", "generated") for name in stage.NAMES}
         and all(set(ax) <= STD3 for ax in cert["axioms"].values()),
         "AP20 actual owner/axiom domain differs")
    for collection in (cert["implementation_hashes"], cert["output_json_sha256"]):
        for path, expected in collection.items():
            need(sha(resolved(path)) == expected, "AP20 certified evidence changed: " + path)
    return historical_witness_hashes(cert)


def api_review():
    review = read(API_REVIEW / "manifest.json")
    docs = {row["name"]: row["sha256"] for row in review["documents"]}
    need(review["official_tag"] == "v0.12.4"
         and review["official_commit"] == "78989800ba0b3149ee34205257025bd0f617e8ef"
         and all(sha(API_REVIEW / name) == expected for name, expected in docs.items()),
         "AP20 reviewed official API documents differ")
    return {"official_tag": review["official_tag"],
            "official_commit": review["official_commit"],
            "manifest_sha256": sha(API_REVIEW / "manifest.json"), "documents": docs}


def prepare():
    need(CERT.is_file(), "AP20 genuine three-context certificate is pending")
    config, prep, provider, raw, metadata, payload, payload_raw, manifest = static_artifacts()
    cert = read(CERT)
    witness_hashes, dependency_hashes = replay(cert, config, prep, provider)
    pins = {"schema_version": 1,
        "artifact_kind": "ap20-literal-interface-seventeen-Def-publication-preparation",
        "provider_key": KEY, "definition_name": payload["definition_name"],
        "definition_module": config["platform_module"],
        "environment": ENV, "visibility": "public",
        "offline_wrapper_sha256": sha(SELF), "online_wrapper_sha256": sha(ONLINE),
        "api_client_sha256": sha(API), "stage_producer_sha256": sha(Path(stage.__file__)),
        "strict_consumer_sha256": sha(Path(consumer.__file__)),
        "stage_preparation_sha256": sha(STAGE / "preparation.json"),
        "validation_sha256": sha(CERT), "manifest_sha256": sha_bytes(encode(manifest)),
        "metadata_sha256": sha_bytes(encode(metadata)), "payload_sha256": sha_bytes(payload_raw),
        "provider_source_sha256": sha(provider), "uploaded_definition_sha256": sha_bytes(raw),
        "stage_input_hashes": prep["input_hashes"],
        "external_dependency_olean_hashes": prep["external_dependency_olean_hashes"],
        "compiler_manifest_sha256": cert["compiler_manifest_sha256"],
        "historical_preflight_artifact_sha256": witness_hashes,
        "actual_dependency_and_emitted_olean_sha256": dependency_hashes,
        "implementation_hashes": cert["implementation_hashes"],
        "kernel_and_inventory_json_sha256": cert["output_json_sha256"],
        "provider_olean": cert["provider_olean"],
        "provider_olean_sha256": cert["provider_olean_sha256"],
        "actual_owned_CI_names": cert["actual_owned_CI_names"],
        "actual_source_generated_closed_Prop_CI_pairs":
            cert["actual_source_generated_closed_Prop_CI_pairs"],
        "actual_definition_value_proof_cache_differences":
            cert["actual_definition_value_proof_cache_differences"],
        "official_api_review": api_review(), "route": "/submit-definition",
        "expected_readback_status": "Definition",
        "one_complete_strict_replay_performed_by_offline_preparation": True,
        "subsequent_HTTP_guards_are_hash_only": True,
        "durable_policy": "write intent before POST; never repeat an uncertain POST; poll only a known id",
        "API_used": False, "submission_ready": False, "proposal_status": "Draft"}
    exact(DEST / "manifest.json", encode(manifest))
    exact(DEST / "validation.json", CERT.read_bytes())
    exact(DEST / "metadata.json", encode(metadata))
    exact(DEST / "publish-payload.json", payload_raw)
    exact(DEST / "wire-definition-source.lean", raw)
    exact(DEST / "preparation.json", encode(pins))
    return {"prepared": True, "provider": KEY, "network_used": False,
            "one_complete_strict_replay_performed": True,
            "payload_sha256": pins["payload_sha256"], "proposal_status": "Draft"}


def hash_gate(pins):
    direct = {SELF: pins["offline_wrapper_sha256"], ONLINE: pins["online_wrapper_sha256"],
        API: pins["api_client_sha256"], Path(stage.__file__): pins["stage_producer_sha256"],
        Path(consumer.__file__): pins["strict_consumer_sha256"],
        STAGE / "preparation.json": pins["stage_preparation_sha256"],
        CERT: pins["validation_sha256"], STAGE / stage.PROVIDER_FILE: pins["provider_source_sha256"],
        resolved(pins["provider_olean"]): pins["provider_olean_sha256"]}
    for path, expected in direct.items():
        need(sha(path) == expected, "AP20 frozen direct evidence changed: " + str(path))
    for collection in (pins["stage_input_hashes"], pins["external_dependency_olean_hashes"],
                       pins["historical_preflight_artifact_sha256"],
                       pins["actual_dependency_and_emitted_olean_sha256"],
                       pins["implementation_hashes"], pins["kernel_and_inventory_json_sha256"]):
        for path, expected in collection.items():
            need(sha(resolved(path)) == expected, "AP20 frozen evidence changed: " + path)
    for name, expected in pins["compiler_manifest_sha256"].items():
        need(sha(STAGE / name) == expected, "AP20 compiler manifest changed: " + name)
    need((DEST / "preparation.json").read_bytes() == encode(pins)
         and sha(DEST / "manifest.json") == pins["manifest_sha256"]
         and sha(DEST / "validation.json") == pins["validation_sha256"]
         and sha(DEST / "metadata.json") == pins["metadata_sha256"]
         and sha(DEST / "publish-payload.json") == pins["payload_sha256"]
         and sha(DEST / "wire-definition-source.lean") == pins["uploaded_definition_sha256"],
         "AP20 frozen publication artifacts changed")
    need(api_review() == pins["official_api_review"], "AP20 API review pins changed")


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
