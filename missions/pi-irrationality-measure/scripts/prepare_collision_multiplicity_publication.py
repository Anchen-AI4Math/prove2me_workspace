"""Freeze the AP18 Collision multiplicity Definition payload without networking.

Pending preparation is available before the three bounded compiler witnesses.
Final preparation additionally requires the strict full-ConstantInfo
type/value/Std3 certificate produced from those existing witnesses.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import certify_collision_multiplicity_existing as consumer
import publish_closed_definition_bundle as driver
import stage_collision_multiplicity_provider as stage


TASK, ROOT = stage.TASK, stage.ROOT
SELF = Path(__file__).resolve()
ONLINE = TASK / "scripts/publish_collision_multiplicity_definition.py"
ENV = driver.ENV
API_REVIEW = TASK / "verification/api-review-20261011-v0.12.4"
KEY = "multiplicity"


def sha_bytes(raw): return hashlib.sha256(raw).hexdigest()
def sha(path): return sha_bytes(Path(path).read_bytes())
def read(path): return json.loads(Path(path).read_text(encoding="utf-8"))
def encode(value): return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode()
def need(ok, message):
    if not ok: raise ValueError(message)


def exact(path, raw):
    path = Path(path)
    if path.exists() and path.read_bytes() != raw:
        raise ValueError("Frozen AP18 publication artifact differs: " + str(path))
    if not path.exists():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)


def name(c):
    prefix = "Definitions.Def_"
    need(c["platform_module"].startswith(prefix), "AP18 Definition module prefix differs")
    return c["platform_module"][len(prefix):]


def static():
    stage.check_only(KEY)
    c = stage.config(KEY); root = c["stage"]
    prep = read(root / "preparation.json")
    academic = read(root / "academic-metadata.json")
    need(set(academic) == {"definition_title", "natural_language_statement",
                           "source_commit", "source_url", "tags"}
         and academic["source_commit"] == stage.COMMIT
         and all(token in academic["natural_language_statement"]
                 for token in ("$\\iota$", "$\\kappa$", "$$", "m_s", "\\#", "\\to\\kappa")),
         "AP18 academic metadata/provenance differs")
    order = [c["provider_file"], stage.SOURCE_SNAPSHOT, stage.GENERATED_SNAPSHOT]
    need(prep["artifact_kind"] == "ap18-collision-multiplicity-data-preparation"
         and prep["source_commit"] == stage.COMMIT
         and prep["source_module"] == c["source_module"]
         and prep["platform_module"] == c["platform_module"]
         and prep["provided_names"] == c["names"]
         and prep["provider_file"] == c["provider_file"]
         and prep["imports"] == c["imports"]
         and prep["contains_theorems"] is False
         and prep["own_structures_constructors_recursors"] == []
         and prep["source_context_commands"] == ["open scoped BigOperators"],
         "AP18 source/module/section preparation differs")
    units = prep["exact_source_units"]
    need(len(units) == 1 and [u["name"] for u in units] == c["names"]
         and [(u["start"], u["end"], u["source_lines"]) for u in units] == [
             (1120, 1274, [34, 36])]
         and all(u["ast"]["graph_names"] == [u["name"]]
                 and u["ast"]["graph_kinds"] == ["def"]
                 and u["ast"]["privateTok"] is None
                 and u["graph"]["typeDeps"] == []
                 and set(u["graph"]["valueDeps"]) <= set(c["names"])
                 for u in units),
         "AP18 exact source Def AST or empty structural domain differs")
    expected_imports = [c["imports"], ["Lean", c["source_module"]],
                        ["Lean", c["platform_module"]]]
    need([read(root / f"c{i}.json")["imports"] for i in range(1, 4)] == expected_imports,
         "AP18 ordered imports differ")
    provider = root / c["provider_file"]
    raw = provider.read_bytes()
    need(sha(provider) == read(root / "c1.json")["output_sha256"]
         and b"sorry" not in raw and b"theorem " not in raw
         and raw.count(b"def multiplicity ") == 1,
         "AP18 provider changed or contains proof/extra declaration material")
    metadata = {"definition_title": academic["definition_title"],
                "natural_language_statement": academic["natural_language_statement"],
                "source": academic["source_url"], "tags": academic["tags"]}
    payload = {"definition_name": name(c), "definition_title": metadata["definition_title"],
               "definition": raw.decode("utf-8"),
               "natural_language_statement": metadata["natural_language_statement"],
               "source": metadata["source"], "tags": metadata["tags"],
               "env": ENV, "private": False}
    payload_bytes = json.dumps(payload, ensure_ascii=False).encode("utf-8")
    need(payload["definition"].encode("utf-8") == raw,
         "AP18 payload changes provider bytes")
    cert = root / "actual-provider-validation.json"
    manifest = {"schema_version": 1,
        "artifact_kind": "ap18-collision-multiplicity-definition-publication-manifest",
        "provider_key": KEY, "definition_name": name(c),
        "definition_module": c["platform_module"], "provided_names": c["names"],
        "environment": ENV, "visibility": "public", "source_commit": stage.COMMIT,
        "source_module": c["source_module"], "source_url": academic["source_url"],
        "provider_source": stage.rel(provider), "provider_source_sha256": sha(provider),
        "stage_preparation_sha256": sha(root / "preparation.json"),
        "metadata_sha256": sha_bytes(encode(metadata)), "payload_sha256": sha_bytes(payload_bytes),
        "uploaded_definition_sha256": sha_bytes(raw), "definition_bytes_equal_provider_source": True,
        "exact_source_definition_count": 1, "structural_declaration_domain": [],
        "route": "/submit-definition", "expected_readback_status": "Definition",
        "validated": cert.is_file(), "submission_ready": False, "proposal_status": "Draft"}
    return c, root, prep, provider, raw, metadata, payload, payload_bytes, manifest, cert


def replay(c, root, prep, cert):
    need(consumer.validate(KEY) == cert,
         "AP18 certificate differs from strict saved-evidence replay")
    need(cert["schema_version"] == 1
         and cert["artifact_kind"] == "ap18-collision-multiplicity-actual-provider-validation"
         and cert["source_commit"] == stage.COMMIT
         and cert["source_module"] == c["source_module"]
         and cert["platform_module"] == c["platform_module"]
         and cert["provided_names"] == c["names"],
         "AP18 certificate identity differs")
    need(cert["validated"] is True and cert["Lean_started_by_consumer"] is False
         and cert["API_used"] is False and cert["submission_ready"] is False
         and cert["proposal_status"] == "Draft" and cert["Std3_only"] is True
         and cert["source_and_generated_types_equal"] is True
         and cert["definition_values_equal_and_exported"] is True
         and cert["contains_theorems"] is False,
         "AP18 actual type/value/axiom/state gates differ")
    need(cert["provider_source_sha256"] == sha(root / c["provider_file"])
         and cert["preparation_sha256"] == sha(root / "preparation.json")
         and cert["compiler_manifest_sha256"] ==
             {f"c{i}.json": sha(root / f"c{i}.json") for i in range(1, 4)}
         and set(cert["preflights"]) == set(order := [c["provider_file"], stage.SOURCE_SNAPSHOT, stage.GENERATED_SNAPSHOT])
         and 0 < cert["max_file_seconds"] <= 300,
         "AP18 compiler evidence differs")
    need(cert["actual_owners"]["source"] == {n: c["source_module"] for n in c["names"]}
         and cert["actual_owners"]["generated"] == {n: c["platform_module"] for n in c["names"]}
         and set(cert["axioms"]) == {side + ":" + n for side in ("source", "generated")
                                       for n in c["names"]},
         "AP18 actual owners or complete Def axiom domain differs")
    for axioms in cert["axioms"].values():
        need(set(axioms) <= {"propext", "Classical.choice", "Quot.sound"},
             "AP18 nonstandard axiom")
    for path, expected in cert["implementation_hashes"].items():
        need(sha(TASK / path) == expected, "AP18 implementation changed: " + path)
    for path, expected in cert["output_json_sha256"].items():
        need(sha(TASK / path) == expected, "AP18 full-CI output changed: " + path)
    need(sha(TASK / cert["provider_olean"]) == cert["provider_olean_sha256"],
         "AP18 provider OLean changed")


def artifacts():
    values = static(); c, root, prep, provider, raw, metadata, payload, payload_bytes, manifest, cert_path = values
    need(cert_path.is_file(), "Actual AP18 Collision multiplicity certificate is pending")
    cert = read(cert_path); replay(c, root, prep, cert)
    return (*values, cert)


def api_review():
    m = read(API_REVIEW / "manifest.json")
    docs = {x["name"]: x["sha256"] for x in m["documents"]}
    need(m["official_tag"] == "v0.12.4"
         and m["official_commit"] == "78989800ba0b3149ee34205257025bd0f617e8ef"
         and sha(API_REVIEW / "references/contribute.md") == docs["references/contribute.md"],
         "Official Definition API review changed")
    return {"official_tag": m["official_tag"], "official_commit": m["official_commit"],
            "manifest_sha256": sha(API_REVIEW / "manifest.json"),
            "contribute_sha256": docs["references/contribute.md"]}


def preflight_hashes(cert):
    found = {}
    for row in cert["preflights"].values():
        record = row["record"]
        need(sha(TASK / record) == row["record_sha256"],
             "AP18 actual preflight sidecar changed")
        found[record] = row["record_sha256"]
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
                 "AP18 dependency OLean changed during actual compilation")
            found[dep["module"] + "|" + dep["path"]] = dep["sha256_before"]
    return dict(sorted(found.items()))


def pins(c, root, prep, provider, raw, metadata, payload_bytes, manifest, cert_path, cert):
    return {"schema_version": 1,
        "artifact_kind": "ap18-collision-multiplicity-definition-publication-preparation",
        "provider_key": KEY, "offline_prepare_only": True,
        "publisher_script_sha256": sha(Path(driver.__file__)),
        "offline_wrapper_sha256": sha(SELF), "online_wrapper_sha256": sha(ONLINE),
        "api_client_sha256": sha(ROOT / "scripts/p2m_api.py"),
        "stage_producer_sha256": sha(Path(stage.__file__)),
        "strict_consumer_sha256": sha(Path(consumer.__file__)),
        "definition_name": name(c), "definition_module": c["platform_module"],
        "environment": ENV, "visibility": "public",
        "metadata_sha256": sha_bytes(encode(metadata)), "payload_sha256": sha_bytes(payload_bytes),
        "payload_encoding": "Exact UTF-8 JSON bytes saved and sent unchanged",
        "wire_body_sha256": sha_bytes(payload_bytes), "bundle_source_sha256": sha(provider),
        "uploaded_definition_sha256": sha_bytes(raw), "uploaded_definition_bytes": len(raw),
        "definition_bytes_equal_bundle_source": True,
        "bundle_manifest_sha256": sha_bytes(encode(manifest)),
        "stage_preparation_sha256": sha(root / "preparation.json"),
        "validation_sha256": sha(cert_path), "source_commit": stage.COMMIT,
        "exact_source_definition_count": 1, "structural_declaration_domain": [],
        "source_section_contexts": prep["source_context_commands"],
        "ordered_imports": {n: read(root / f"c{i}.json")["imports"]
                            for i, n in enumerate(
                                [c["provider_file"], stage.SOURCE_SNAPSHOT,
                                 stage.GENERATED_SNAPSHOT], 1)},
        "compiler_manifest_sha256": cert["compiler_manifest_sha256"],
        "stage_input_hashes": prep["input_hashes"],
        "preflight_artifact_sha256": preflight_hashes(cert),
        "dependency_olean_sha256": dependency_oleans(cert),
        "implementation_hashes": cert["implementation_hashes"],
        "preflight_count": len(cert["preflights"]),
        "max_preflight_seconds": cert["max_file_seconds"],
        "olean_sha256": cert["provider_olean_sha256"],
        "kernel_type_value_snapshots": cert["output_json_sha256"],
        "route": "/submit-definition", "expected_readback_status": "Definition",
        "official_api_review": api_review(),
        "at_most_once_policy": "durable publish_intent before POST; never repeat a recorded intent",
        "API_used": False, "submission_ready": False, "proposal_status": "Draft"}


def hash_gate(frozen):
    c = stage.config(KEY); root = c["stage"]
    dest = root / "publication"
    cert_path = root / "actual-provider-validation.json"
    direct = {SELF: frozen["offline_wrapper_sha256"],
              ONLINE: frozen["online_wrapper_sha256"],
              Path(driver.__file__): frozen["publisher_script_sha256"],
              ROOT / "scripts/p2m_api.py": frozen["api_client_sha256"],
              Path(stage.__file__): frozen["stage_producer_sha256"],
              Path(consumer.__file__): frozen["strict_consumer_sha256"],
              root / "preparation.json": frozen["stage_preparation_sha256"],
              cert_path: frozen["validation_sha256"],
              root / c["provider_file"]: frozen["bundle_source_sha256"]}
    for path, expected in direct.items():
        need(sha(path) == expected, "AP18 frozen implementation/evidence changed: " + str(path))
    for path, expected in frozen["implementation_hashes"].items():
        need(sha(TASK / path) == expected, "AP18 certificate implementation changed: " + path)
    for path, expected in frozen["stage_input_hashes"].items():
        need(sha(TASK / path) == expected, "AP18 stage input changed: " + path)
    for filename, expected in frozen["compiler_manifest_sha256"].items():
        need(sha(root / filename) == expected, "AP18 compiler manifest changed: " + filename)
    for path, expected in frozen["preflight_artifact_sha256"].items():
        need(sha(consumer.context.file(path)) == expected, "AP18 preflight artifact changed: " + path)
    for key, expected in frozen["dependency_olean_sha256"].items():
        need(sha(Path(key.split("|", 1)[1])) == expected, "AP18 dependency OLean changed: " + key)
    for path, expected in frozen["kernel_type_value_snapshots"].items():
        need(sha(TASK / path) == expected, "AP18 kernel full-CI output changed: " + path)
    need(sha(TASK / read(cert_path)["provider_olean"]) == frozen["olean_sha256"],
         "AP18 provider OLean changed")
    need((dest / "prepare-record.json").read_bytes() == encode(frozen)
         and sha(dest / "manifest.json") == frozen["bundle_manifest_sha256"]
         and sha(dest / "validation.json") == frozen["validation_sha256"]
         and sha(dest / "metadata.json") == frozen["metadata_sha256"]
         and sha(dest / "publish-payload.json") == frozen["payload_sha256"]
         and sha(dest / "wire-definition-source.lean") == frozen["uploaded_definition_sha256"],
         "AP18 frozen publication artifacts changed")
    need(api_review() == frozen["official_api_review"], "AP18 reviewed API docs changed")


def pending():
    c, root, prep, provider, raw, metadata, payload, payload_bytes, manifest, cert = static()
    dest = root / "publication"
    exact(dest / "metadata.json", encode(metadata)); exact(dest / "publish-payload.json", payload_bytes)
    exact(dest / "wire-definition-source.lean", raw)
    record = {"schema_version": 1,
        "artifact_kind": "ap18-collision-multiplicity-pending-publication",
        "provider_key": KEY, "definition_name": payload["definition_name"],
        "publication_manifest_sha256": sha_bytes(encode(manifest)),
        "stage_preparation_sha256": sha(root / "preparation.json"),
        "metadata_sha256": sha_bytes(encode(metadata)), "payload_sha256": sha_bytes(payload_bytes),
        "provider_source_sha256": sha(provider), "strict_validation_pending": not cert.is_file(),
        "network_used": False, "API_used": False, "submission_ready": False,
        "proposal_status": "Draft"}
    exact(dest / "pending-preparation.json", encode(record))
    return {"prepared": True, "provider": KEY, "validation_pending": not cert.is_file(),
            "network_used": False, "payload_sha256": record["payload_sha256"]}


def prepare():
    c, root, prep, provider, raw, metadata, payload, payload_bytes, manifest, cert_path, cert = artifacts()
    dest = root / "publication"
    frozen = pins(c, root, prep, provider, raw, metadata, payload_bytes, manifest, cert_path, cert)
    exact(dest / "manifest.json", encode(manifest)); exact(dest / "validation.json", cert_path.read_bytes())
    exact(dest / "metadata.json", encode(metadata)); exact(dest / "publish-payload.json", payload_bytes)
    exact(dest / "wire-definition-source.lean", raw); exact(dest / "prepare-record.json", encode(frozen))
    return {"prepared": True, "provider": KEY, "network_used": False,
            "payload_sha256": frozen["payload_sha256"], "proposal_status": "Draft"}


def check():
    c, root, prep, provider, raw, metadata, payload, payload_bytes, manifest, cert_path, cert = artifacts()
    dest = root / "publication"
    frozen = pins(c, root, prep, provider, raw, metadata, payload_bytes, manifest, cert_path, cert)
    need((dest / "manifest.json").read_bytes() == encode(manifest)
         and (dest / "validation.json").read_bytes() == cert_path.read_bytes()
         and (dest / "metadata.json").read_bytes() == encode(metadata)
         and (dest / "publish-payload.json").read_bytes() == payload_bytes
         and (dest / "wire-definition-source.lean").read_bytes() == raw
         and (dest / "prepare-record.json").read_bytes() == encode(frozen),
         "Frozen AP18 publication evidence differs")
    need(read(dest / "publish-payload.json") == payload, "Saved AP18 payload differs")
    return {"checked": True, "provider": KEY, "network_used": False,
            "payload_sha256": frozen["payload_sha256"], "proposal_status": "Draft"}


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--provider", choices=list(stage.CONFIGS), default=KEY)
    g = p.add_mutually_exclusive_group(required=True)
    g.add_argument("--prepare-pending", action="store_true")
    g.add_argument("--prepare-only", action="store_true")
    g.add_argument("--check-only", action="store_true")
    a = p.parse_args()
    result = pending() if a.prepare_pending else prepare() if a.prepare_only else check()
    print(json.dumps(result, ensure_ascii=False, indent=2))
