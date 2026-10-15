"""Prepare proof-only AP21 publications for two existing analytic Open leaves.

`--prepare-pending` writes review candidates only and never imports a strict
consumer.  `--prepare-only` is intentionally unavailable until each derived
consumer/certificate locator is frozen below; it then performs exactly one full
strict replay and freezes every compiler/evidence hash for hash-only HTTP use.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib
import importlib.util
import json
from pathlib import Path

import stage_actual_row_count_pos_node as row_stage
import stage_index_weight_nonneg_node as index_stage


TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
SELF = Path(__file__).resolve()
ONLINE = TASK / "scripts/publish_ap21_analytic_small_leaf.py"
API = ROOT / "scripts/p2m_api.py"
API_REVIEW = TASK / "verification/api-review-20261011-v0.12.4"
API_REVIEW_MANIFEST = API_REVIEW / "manifest.json"
ENV = "0df444a360eaa60ab8c11dca51a86af692955474"
STD3 = {"propext", "Classical.choice", "Quot.sound"}


def config(node: str):
    if node == "index":
        return {
            "node": node, "stage": index_stage,
            "stage_dir": index_stage.STAGE,
            "target": index_stage.TARGET, "theorem_id": index_stage.THEOREM_ID,
            "readback_key": "norm-child-" + index_stage.TARGET,
            "candidate_dir": TASK / "verification/ap20/analytic-small-leaf-candidates/indexWeight_nonneg/candidate",
            "candidate_theorem": "Theorems/Thm_OAI_PiExponent_LiteralAnalytic_indexWeight_nonneg.lean",
            "candidate_solution": "Solutions/Sol_OAI_PiExponent_LiteralAnalytic_indexWeight_nonneg_small_leaf_ap20.lean",
            "route": TASK / "verification/ap20/analytic-small-leaf-candidates/indexWeight_nonneg/source-route.json",
            "ast_count": 3, "source_lines": 12,
            "title": "Nonnegativity of the logarithmic index weight",
            "statement": (
                "For fixed source data $d$, height $H$, and a transverse multi-index $a$, "
                "the logarithmic index weight is nonnegative:"
                "\n\n$$\\operatorname{indexWeight}_d(a)\\ge 0.$$\n\n"
                "Each summand is a nonnegative natural multiplicity times a positive "
                "logarithmic source weight."),
            "explanation": (
                "The original source identities rewrite every fixed weight as the "
                "corresponding logarithmic row weight.  Source admissibility makes each "
                "weight positive, while all multi-index coordinates are natural numbers; "
                "the defining finite sum is therefore nonnegative."),
            "consumer_module": "certify_index_weight_nonneg_node",
            "certificate_path": index_stage.CERTIFICATE,
            "artifact_kind": "ap21-indexWeight-nonneg-actual-closed-node-validation",
        }
    if node == "row":
        return {
            "node": node, "stage": row_stage,
            "stage_dir": row_stage.STAGE,
            "target": row_stage.TARGET, "theorem_id": row_stage.TARGET_ID,
            "readback_key": "actual-child-" + row_stage.TARGET,
            "candidate_dir": TASK / "verification/ap20/analytic-small-leaf-candidates/actualRowCount_pos/candidate",
            "candidate_theorem": "Theorems/Thm_OAI_PiExponent_LiteralAnalytic_actualRowCount_pos.lean",
            "candidate_solution": "Solutions/Sol_OAI_PiExponent_LiteralAnalytic_actualRowCount_pos_small_leaf_ap20.lean",
            "route": TASK / "verification/ap20/analytic-small-leaf-candidates/actualRowCount_pos/source-route.json",
            "ast_count": 7, "source_lines": 53,
            "title": "Positivity of the actual interpolation-row count",
            "statement": (
                "For fixed source data $d$ and every height $H>0$, the finite set of "
                "actual interpolation rows is nonempty, and hence"
                "\n\n$$\\operatorname{actualRowCount}_d(H)>0.$$\n\n"
                "The zero multi-index together with the first row label gives an explicit "
                "row because the row weights and structural parameters are positive."),
            "explanation": (
                "The source proof constructs a concrete row: use the first of the positive "
                "number of row labels and the zero multi-index.  Positivity of the fixed "
                "weights, base height, and interpolation parameters verifies the strict "
                "weighted-simplex inequality, so the finite row type has positive cardinality."),
            # This v3 successor locator is fixed before freezing the shared
            # scripts; its genuine certificate is still required by prepare().
            "consumer_module": "certify_actual_row_count_pos_node_v3",
            "certificate_path": (TASK / "verification/ap21/"
                                 "actual-row-count-pos-node-validation-v3/"
                                 "node-validation-v3.json"),
            "artifact_kind": "ap21-actual-row-count-seven-original-AST-closed-validation-v3",
        }
    raise ValueError("Unknown AP21 leaf: " + node)


def need(ok, message):
    if not ok:
        raise ValueError(message)


def digest(raw): return hashlib.sha256(raw).hexdigest()
def sha(path): return digest(Path(path).read_bytes())
def read(path): return json.loads(Path(path).read_text(encoding="utf-8"))
def encode(value):
    return (json.dumps(value, ensure_ascii=False, sort_keys=True,
                       separators=(",", ":")) + "\n").encode()


def resolve(path):
    p = Path(path)
    return p if p.is_absolute() else TASK / p


def pin_key(path):
    p = Path(path).resolve()
    try:
        return p.relative_to(TASK.resolve()).as_posix()
    except ValueError:
        return str(p)


def exact(path, raw):
    path = Path(path)
    if path.exists():
        need(path.read_bytes() == raw, "Frozen AP21 leaf artifact differs: " + str(path))
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)


def api_review_pins():
    review = read(API_REVIEW_MANIFEST)
    docs = {row["name"]: row["sha256"] for row in review["documents"]}
    need(review["official_tag"] == "v0.12.4"
         and review["official_commit"] == "78989800ba0b3149ee34205257025bd0f617e8ef"
         and docs["references/prove.md"] == sha(API_REVIEW / "references/prove.md")
         and docs["references/contribute.md"] == sha(API_REVIEW / "references/contribute.md"),
         "Reviewed official API v0.12.4 files differ")
    return {"official_tag": review["official_tag"],
            "official_commit": review["official_commit"],
            "manifest_sha256": sha(API_REVIEW_MANIFEST),
            "prove_sha256": docs["references/prove.md"],
            "contribute_sha256": docs["references/contribute.md"]}


def publication_record(cfg):
    path = TASK / "verification/ap20/analytic-translated-two-layer-reduction-final-v3/publication-v4/publication.json"
    doc = read(path)
    row = doc["readbacks"][cfg["readback_key"]]
    body = row["body"]
    need(row["http_status"] == 200
         and body["theorem_id"] == cfg["theorem_id"]
         and body["theorem_name"] == cfg["target"]
         and body["status"] == "Open" and body["mathlib_rev"] == ENV
         and body["visibility"] == "public" and body["deprecated_at"] is None
         and body["deprecated_by"] is None,
         "Exact historical AP21 Open target differs: " + cfg["target"])
    return path, body


def candidate_paths(cfg):
    # The route candidate deliberately labels its comparator as non-publishable.
    # Use the exact historical public wire captured by the AP20 graph stage even
    # for pending review; only the closed solution comes from the leaf route.
    return (TASK / "verification/ap20/analytic-translated-two-layer-reduction-final" /
            cfg["stage"].TARGET_OUTPUT,
            cfg["candidate_dir"] / cfg["candidate_solution"])


def final_paths(cfg):
    stage = cfg["stage"]
    return cfg["stage_dir"] / stage.TARGET_OUTPUT, cfg["stage_dir"] / stage.SOLUTION_OUTPUT


def source_url(cfg, route):
    unit = next(row for row in route["source_units"] if row["name"] == cfg["target"])
    original = unit["original"]
    need(original.startswith("source/lean/"), "Original source path is not under source/lean")
    commit = read(cfg["stage_dir"] / "preparation.json")["source_commit"]
    return "https://github.com/openai/math/blob/" + commit + "/" + original.removeprefix("source/")


def multipart(descriptor, solution):
    spec = importlib.util.spec_from_file_location("p2m_api_ap21_offline", API)
    api = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(api)
    return api._multipart(
        {"theorem_id": descriptor["theorem_id"], "proof_type": "prove",
         "explanation": descriptor["explanation"]},
        {"file": (descriptor["file"]["filename"], solution)})


def static(node: str, final: bool = False):
    cfg = config(node)
    route = read(cfg["route"])
    public_path, body = publication_record(cfg)
    stage_prep = read(cfg["stage_dir"] / "preparation.json")
    need(route["target"] == cfg["target"]
         and route["proof_AST_count"] == cfg["ast_count"]
         and route["source_line_count"] == cfg["source_lines"]
         and route["target_source_proof_suffix_unchanged_except_solution_name"] is True
         and route["all_helpers_original_AST_inline"] is True
         and route["uses_unProved_platform_boundaries"] is False
         and route["missing_data_names"] == []
         and route["finite_port_adaptations"] == [],
         "Source-faithful AP21 leaf route differs")
    theorem, solution = final_paths(cfg) if final else candidate_paths(cfg)
    if final:
        cfg["stage"].check_only()
    wire, proof = theorem.read_bytes(), solution.read_bytes()
    need(wire == (body["preamble"] + body["formal_statement"]).encode()
         and proof.count(b"theorem solution ") == 1 and b"sorry" not in proof
         and b"#print" not in proof and b"#check" not in proof and b"#eval" not in proof
         and ("import " + cfg["stage"].MODULE).encode() not in proof,
         "Exact existing target wire or global closed solution differs")
    metadata = {"theorem_title": cfg["title"],
                "natural_language_statement": cfg["statement"],
                "source": source_url(cfg, route),
                "tags": ["pi", "number theory", "finite combinatorics", "source faithful"]}
    descriptor = {
        "theorem_id": cfg["theorem_id"], "target_theorem_name": cfg["target"],
        "proof_type": "prove", "env": ENV, "explanation": cfg["explanation"],
        "file": {"filename": Path(solution).name,
                 "source": pin_key(solution), "sha256": sha(solution),
                 "utf8": proof.decode("utf-8")}}
    request, content_type = multipart(descriptor, proof)
    manifest = {
        "schema_version": 1,
        "artifact_kind": "ap21-analytic-small-leaf-proof-publication-candidate",
        "node": node, "theorem_id": cfg["theorem_id"], "theorem_name": cfg["target"],
        "environment": ENV, "existing_target_only": True,
        "creates_theorem_or_proposal": False, "proof_type": "prove",
        "source_commit": stage_prep["source_commit"], "original_AST_count": cfg["ast_count"],
        "original_source_lines": cfg["source_lines"], "source_units": route["source_units"],
        "historical_publication": pin_key(public_path),
        "historical_publication_sha256": sha(public_path),
        "wire_sha256": sha(theorem), "solution_sha256": sha(solution),
        "strict_certificate_pending": not final,
        "validated": False, "submission_ready": False, "proposal_status": "Draft"}
    return cfg, route, body, theorem, solution, metadata, descriptor, request, content_type, manifest


def pending(node: str):
    cfg, route, body, theorem, solution, metadata, descriptor, request, ctype, manifest = static(node)
    dest = cfg["stage_dir"] / "publication"
    files = {
        "pending-metadata.json": encode(metadata),
        "pending-wire-theorem-source.lean": theorem.read_bytes(),
        "pending-verification-payload.json": encode(descriptor),
        "pending-verification-request.multipart": request,
        "pending-manifest.json": encode(manifest),
    }
    preparation = {
        "schema_version": 1,
        "artifact_kind": "ap21-analytic-small-leaf-pending-publication",
        "node": node, "theorem_id": cfg["theorem_id"], "theorem_name": cfg["target"],
        "environment": ENV, "route": "/verify", "proof_type": "prove",
        "existing_target_only": True, "creates_theorem_or_proposal": False,
        "historical_target_status": body["status"],
        "source_route_sha256": sha(cfg["route"]),
        "candidate_theorem_sha256": sha(theorem),
        "candidate_solution_sha256": sha(solution),
        "payload_sha256": {name: digest(raw) for name, raw in files.items()},
        "multipart_content_type": ctype,
        "strict_consumer_locator_pending": (cfg["consumer_module"] is None or
                                               cfg["certificate_path"] is None),
        "strict_certificate_pending": True,
        "full_replay_performed": False,
        "network_used": False, "API_used": False,
        "submission_ready": False, "proposal_status": "Draft"}
    files["pending-preparation.json"] = encode(preparation)
    for name, raw in files.items():
        exact(dest / name, raw)
    return {"prepared": True, "pending": True, "node": node,
            "strict_replay_performed": False, "network_used": False,
            "creates_theorem_or_proposal": False,
            "descriptor_sha256": digest(encode(descriptor)),
            "multipart_sha256": digest(request)}


def historical(cert, cfg, prep):
    stage = cfg["stage"]
    artifacts, deps = {}, {}
    preflights = cert["preflights"]
    for output, record in preflights.items():
        data = record["data"] if "data" in record else record
        record_path = record.get("record")
        if record_path:
            expected = record.get("record_sha256")
            need(expected and sha(resolve(record_path)) == expected,
                 "Actual preflight sidecar differs: " + output)
            artifacts[pin_key(resolve(record_path))] = expected
        else:
            # Some derived consumers intentionally expose the compiler's raw
            # sidecar object.  Bind that object to the actual sidecar bytes so
            # the later HTTP-only gate cannot silently lose the c1--c4 record.
            sidecar = resolve(data["source"]).with_suffix(".lean.preflight.json")
            need(sidecar.is_file() and read(sidecar) == data,
                 "Actual raw preflight does not equal its sidecar: " + output)
            artifacts[pin_key(sidecar)] = sha(sidecar)
        need(data["success"] is True and data["exit_code"] == 0
             and data["timed_out"] is False and 0 < data["seconds"] <= 300
             and data["source_sha256_before"] == data["source_sha256_after"] == sha(resolve(data["source"]))
             and data["manifest_sha256_before"] == data["manifest_sha256_after"] == sha(resolve(data["manifest"]))
             and data["log_sha256"] == data["stdout_and_stderr_sha256"] == sha(resolve(data["log"])),
             "Actual bounded source/manifest/log evidence differs: " + output)
        for field, key in (("source", "source_sha256_before"),
                           ("manifest", "manifest_sha256_before"),
                           ("log", "log_sha256")):
            artifacts[pin_key(resolve(data[field]))] = data[key]
        for dep in data["dependency_oleans"]:
            need(dep["stable_during_compile"] is True
                 and dep["sha256_before"] == dep["sha256_after"] == sha(Path(dep["path"])),
                 "Actual imported OLean changed: " + dep["module"])
            deps[dep["module"] + "|" + dep["path"]] = dep["sha256_before"]
        if data.get("output_olean"):
            need(sha(resolve(data["output_olean"])) == data["output_olean_sha256"],
                 "Actual emitted OLean changed: " + output)
            deps[output + "|" + str(resolve(data["output_olean"]))] = data["output_olean_sha256"]
    return dict(sorted(artifacts.items())), dict(sorted(deps.items()))


def certificate_evidence(cert, cfg, consumer):
    """Extract path/hash witnesses that the strict report says it consumed."""
    files = {}

    def add(path, expected, label):
        p = resolve(path)
        need(isinstance(expected, str) and len(expected) == 64 and p.is_file()
             and sha(p) == expected, "Strict certificate evidence differs: " + label)
        files[pin_key(p)] = expected

    # These report fields are deliberately path -> SHA maps.
    for field in ("implementation_hashes", "output_json_sha256",
                  "source_only_provider_certificate_hashes",
                  "source_auxiliary_closed_Prop_witness_hashes"):
        for path, expected in cert.get(field, {}).items():
            add(path, expected, field + ":" + path)
            if field == "source_only_provider_certificate_hashes":
                child = read(resolve(path))
                for child_path, child_sha in child.get("output_json_sha256", {}).items():
                    add(child_path, child_sha, path + ":certified output")
                if child.get("provider_olean") and child.get("provider_olean_sha256"):
                    add(child["provider_olean"], child["provider_olean_sha256"],
                        path + ":provider OLean")
    for name, expected in cert.get("compiler_manifest_hashes", {}).items():
        add(cfg["stage_dir"] / name, expected, "compiler_manifest:" + name)

    # Both consumers expose these path/SHA records when present.  Pin the
    # certified provider, its exact imported OLean, and any full-Def equation
    # JSON used to justify an automatically generated Eq theorem.
    for module, row in cert.get("actual_direct_provider_olean_bridges", {}).items():
        add(row["certificate"], row["certificate_sha256"], module + ":certificate")
        add(row["c1_imported_path"], row["actual_olean_sha256"], module + ":c1 OLean")
    for name, row in cert.get("unused_actual_closed_data_equations", {}).items():
        full_ci = resolve(row["primary_generated_full_CI"])
        add(full_ci, row["primary_generated_full_CI_sha256"], name + ":full Def CI")
        provider_cert = full_ci.parent / "actual-provider-validation.json"
        add(provider_cert, row["primary_provider_certificate_sha256"],
            name + ":provider certificate")
    for module, row in cert.get("emitted_oleans", {}).items():
        add(row["path"], row["sha256"], module + ":emitted OLean")

    # The row successor exposes its exact finite Published provider domain as
    # constants on the frozen consumer and as hashes in the certificate.
    provider_records = cert.get("typed_published_external_provider_records", {})
    if provider_records:
        for jsonl_rel, cert_rel, publication_rel, _kind in consumer.PROJECT_PROVIDERS:
            record = provider_records[cert_rel]
            add(cfg["stage"].V / jsonl_rel, record["full_CI_jsonl_sha256"],
                cert_rel + ":full CI")
            add(cfg["stage"].V / cert_rel, record["certificate_sha256"],
                cert_rel + ":certificate")
            add(cfg["stage"].V / publication_rel, record["public_readback_sha256"],
                cert_rel + ":public readback")
    if cert.get("actual_import_closure_sha256"):
        add(cfg["stage"].CLOSURE, cert["actual_import_closure_sha256"],
            "actual import closure")
    if cert.get("original_finite_domain_audit_sha256"):
        add(cfg["stage_dir"] / "actual-ci-audit.json",
            cert["original_finite_domain_audit_sha256"], "actual CI audit")
    if cert.get("v2_actual_failure_record_sha256"):
        add(consumer.V2_FAILURE, cert["v2_actual_failure_record_sha256"],
            "preserved v2 failure")

    return dict(sorted(files.items()))


def prepare(node: str):
    cfg = config(node)
    need(cfg["consumer_module"] and cfg["certificate_path"] and cfg["artifact_kind"],
         "Derived strict consumer/certificate locator is not frozen for " + node)
    consumer = importlib.import_module(cfg["consumer_module"])
    cert_path = Path(cfg["certificate_path"])
    need(cert_path.is_file(), "Genuine derived strict certificate is pending: " + str(cert_path))
    cfg, route, body, theorem, solution, metadata, descriptor, request, ctype, manifest = static(node, True)
    cert = read(cert_path)
    replay = consumer.validate()
    need(replay == cert and cert_path.read_bytes() == cfg["stage"].encode(replay),
         "Single complete derived strict replay/certificate bytes differ")
    need(cert["artifact_kind"] == cfg["artifact_kind"]
         and cert["validated"] is True and cert["Std3_only"] is True
         and cert["submission_ready"] is False and cert["proposal_status"] == "Draft"
         and cert["Lean_started_by_consumer"] is False and cert["API_used"] is False
         and 0 < cert["max_file_seconds"] <= 300,
         "Derived strict certificate semantics differ")
    prep = read(cfg["stage_dir"] / "preparation.json")
    artifacts, deps = historical(cert, cfg, prep)
    for path, expected in prep.get("external_dependency_olean_hashes", {}).items():
        p = Path(path)
        need(p.is_absolute() and p.is_file() and sha(p) == expected,
             "Frozen external dependency OLean differs: " + path)
        deps["external|" + str(p)] = expected
    pin_files = {pin_key(p): sha(p) for p in [
        SELF, ONLINE, API, API_REVIEW_MANIFEST, Path(cfg["stage"].__file__),
        Path(consumer.__file__), cert_path, cfg["stage_dir"] / "preparation.json",
        theorem, solution, cfg["route"],
        TASK / "verification/ap20/analytic-translated-two-layer-reduction-final-v3/publication-v4/publication.json",
    ]}
    pin_files.update(prep["input_hashes"])
    pin_files.update(cert.get("implementation_hashes", {}))
    pin_files.update(cert.get("output_json_sha256", {}))
    pin_files.update(certificate_evidence(cert, cfg, consumer))
    pin_files.update(artifacts)
    dest = cfg["stage_dir"] / "publication"
    final_files = {
        "manifest.json": encode({**manifest, "strict_certificate_pending": False,
                                  "validated": True}),
        "metadata.json": encode(metadata),
        "validation.json": cert_path.read_bytes(),
        "wire-theorem-source.lean": theorem.read_bytes(),
        "verification-payload.json": encode(descriptor),
        "verification-request.multipart": request,
    }
    pins = {
        "schema_version": 1,
        "artifact_kind": "ap21-analytic-small-leaf-frozen-proof-publication",
        "node": node, "theorem_id": cfg["theorem_id"], "theorem_name": cfg["target"],
        "environment": ENV, "route": "/verify", "proof_type": "prove",
        "existing_target_only": True, "creates_theorem_or_proposal": False,
        "validation_sha256": sha(cert_path),
        "wire_source_sha256": sha(theorem),
        "solution_source_sha256": sha(solution),
        "offline_wrapper_sha256": sha(SELF), "online_wrapper_sha256": sha(ONLINE),
        "stage_preparation_sha256": sha(cfg["stage_dir"] / "preparation.json"),
        "historical_and_input_hashes": dict(sorted(pin_files.items())),
        "dependency_olean_hashes": deps,
        "artifact_sha256": {name: digest(raw) for name, raw in final_files.items()},
        "multipart_content_type": ctype,
        "official_api_review": api_review_pins(),
        "one_complete_strict_replay_performed": True,
        "strict_replay_count": 1,
        "subsequent_HTTP_guards_hash_only": True,
        "actual_max_file_seconds": cert["max_file_seconds"],
        "durable_post_policy": "write verify_intent before POST; never repeat an uncertain POST",
        "first_seen_Proved_without_own_submission_policy":
            "record reuse_existing_Proved and do not count it as this campaign's ACCEPTED proof",
        "submission_ready": False, "proposal_status": "Draft", "API_used": False,
    }
    for name, raw in final_files.items():
        exact(dest / name, raw)
    exact(dest / "preparation.json", encode(pins))
    hash_gate(node, pins)
    return {"prepared": True, "pending": False, "node": node,
            "strict_replay_count": 1, "network_used": False,
            "creates_theorem_or_proposal": False,
            "descriptor_sha256": pins["artifact_sha256"]["verification-payload.json"],
            "multipart_sha256": pins["artifact_sha256"]["verification-request.multipart"]}


def hash_gate(node: str, pins=None):
    cfg = config(node)
    dest = cfg["stage_dir"] / "publication"
    pins = pins or read(dest / "preparation.json")
    need(pins["node"] == node and pins["theorem_id"] == cfg["theorem_id"]
         and pins["theorem_name"] == cfg["target"]
         and pins["one_complete_strict_replay_performed"] is True
         and pins["strict_replay_count"] == 1
         and pins["subsequent_HTTP_guards_hash_only"] is True,
         "Frozen AP21 leaf preparation identity differs")
    for path, expected in pins["historical_and_input_hashes"].items():
        need(sha(resolve(path)) == expected, "Frozen AP21 input changed: " + path)
    for key, expected in pins["dependency_olean_hashes"].items():
        need(sha(Path(key.split("|", 1)[1])) == expected,
             "Frozen AP21 imported OLean changed: " + key)
    for name, expected in pins["artifact_sha256"].items():
        need(sha(dest / name) == expected, "Frozen AP21 publication artifact changed: " + name)
    need(api_review_pins() == pins["official_api_review"],
         "Reviewed API v0.12.4 evidence changed")
    return pins


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--node", choices=("index", "row"), required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--prepare-pending", action="store_true")
    mode.add_argument("--prepare-only", action="store_true")
    args = parser.parse_args()
    result = pending(args.node) if args.prepare_pending else prepare(args.node)
    print(json.dumps(result, ensure_ascii=False, indent=2))
