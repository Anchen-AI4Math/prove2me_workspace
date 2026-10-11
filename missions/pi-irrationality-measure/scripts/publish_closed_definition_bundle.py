"""Prepare or explicitly advance one of the audited closed definition bundles.

The default mode is offline and writes only beneath the corresponding
verification/definition-validation stage.  Network access is reachable only
with --advance.  Once a POST intent has been recorded, this tool never repeats
that POST; it can only poll the recorded job or verify its exact readback.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys
from urllib.parse import quote

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
VERIFICATION = TASK / "verification"
ENV = "0df444a360eaa60ab8c11dca51a86af692955474"
COMMIT = "adc7f1241b42e322a6451854ab7e4b4c146bf78a"
PREFIX = "Definitions.Def_"


def sha_bytes(data):
    return hashlib.sha256(data).hexdigest()


def sha_file(path):
    return sha_bytes(path.read_bytes())


def read_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def task_path(relative, label):
    path = (TASK / relative).resolve()
    if not path.is_relative_to(TASK.resolve()):
        raise ValueError(label + " path escapes the task")
    return path


def root_path(relative, label):
    path = (ROOT / relative).resolve()
    if not path.is_relative_to(ROOT.resolve()):
        raise ValueError(label + " path escapes the workspace")
    return path


def normalized(row, key):
    levels = {name: index for index, name in enumerate(row["levelParams"])}

    def walk(value):
        if not isinstance(value, list):
            return value
        if len(value) == 2 and value[0] == "param":
            if value[1] not in levels:
                raise ValueError("Snapshot refers to an unknown universe parameter")
            return ["param", levels[value[1]]]
        return [walk(item) for item in value]

    return walk(row[key])


def metadata_for(key):
    tag_set = ["number-theory", "complex-analysis", "pi", "openai-pi-exponent-017"]
    if key == "Collision":
        return {
            "definition_title": "Holomorphic error term in the determinant estimate",
            "natural_language_statement": (
                "For a natural number $K$ and real parameters $w_0$, $v_0$, and $w_\\star$, "
                "this definition assigns the real quantity\n\n"
                "$$E_{\\mathrm{hol}}(K,w_0,v_0,w_\\star)="
                "\\frac{100K}{w_0}+\\frac{\\log 2}{v_0}"
                "+\\frac{\\log(200K)}{w_\\star}.$$\n\n"
                "The declaration itself imposes no positivity, nonzero, or size conditions "
                "on these inputs; such hypotheses belong to any later estimate that uses "
                "the expression. In the source development it packages the holomorphic "
                "contribution appearing in a determinant upper bound."
            ),
            "tags": tag_set,
            "source": ("OpenAI math, source commit " + COMMIT + ", "
                       "Analysis/Collision.lean, definition holomorphicError, lines 12-13: "
                       "https://github.com/openai/math/blob/" + COMMIT +
                       "/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean#L12-L13"),
            "explanation": "A real error-term expression used in the determinant exponent; the definition has no built-in domain hypotheses.",
        }
    if key == "AnalyticCollision":
        return {
            "definition_title": "Analytic coefficient and row-test constructions",
            "natural_language_statement": (
                "This module defines three complex-valued constructions used in the "
                "analytic determinant estimates. For $b,h,z\\in\\mathbb C$ and "
                "$d\\in\\mathbb N$, the exponential monomial is\n\n"
                "$$M_{b,h,d}(z)=b\\,e^{hz}z^d.$$\n\n"
                "For a function $f:\\mathbb C\\to\\mathbb C$, a real radius $R$, and "
                "$d\\in\\mathbb N$, the normalized Taylor coefficient is the "
                "Cauchy-power-series coefficient of $f$ about $0$ at radius $R$, evaluated "
                "on the constant vector with value $R$. For $\\ell\\in\\mathbb N$, "
                "the row test is the same construction at radius $1/2$, evaluated on the "
                "constant vector with value $1$. These are definitions and assume no "
                "analyticity or radius-positivity hypotheses on $f$ or $R$; later analytic "
                "bounds state the conditions they need."
            ),
            "tags": tag_set,
            "source": (
                "OpenAI math, source commit " + COMMIT + ", definitions in "
                "Analysis/AnalyticCollision.lean: exponentialMonomial, lines 10-11 "
                "(https://github.com/openai/math/blob/" + COMMIT +
                "/lean/OAI/NumberTheory/PiExponent/Analysis/AnalyticCollision.lean#L10-L11); "
                "normalizedTaylorCoeff, lines 31-32 (https://github.com/openai/math/blob/" + COMMIT +
                "/lean/OAI/NumberTheory/PiExponent/Analysis/AnalyticCollision.lean#L31-L32); "
                "rowTest, lines 88-89 (https://github.com/openai/math/blob/" + COMMIT +
                "/lean/OAI/NumberTheory/PiExponent/Analysis/AnalyticCollision.lean#L88-L89)"
            ),
            "explanation": "The bundle preserves the three source definitions used to build normalized analytic coefficient rows.",
        }
    raise ValueError("Unsupported bundle key")


BUNDLES = {
    "Collision": {
        "stem": "Def_OAI_NumberTheory_PiExponent_Analysis_Collision",
    },
    "AnalyticCollision": {
        "stem": "Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticCollision",
    },
}


def selected_graph_names(manifest):
    """Resolve expected declaration names only through the authoritative unit plan and graph."""
    unit_rows = read_json(VERIFICATION / "platform-unit-plan-preview.json")["units"]
    units = {row["id"]: row for row in unit_rows}
    graph = {}
    graph_path = VERIFICATION / "decl_graph.jsonl"
    for line in graph_path.read_text(encoding="utf-8").splitlines():
        if line.strip():
            row = json.loads(line)
            graph[row["name"]] = row
    names = []
    for unit_id in manifest["selected_units"]:
        unit = units.get(unit_id)
        if unit is None or unit.get("is_instance_command") or unit.get("deprivate"):
            raise ValueError("Selected unit is absent, an instance command, or requires deprivatization")
        graph_names = unit.get("graph_names")
        if not isinstance(graph_names, list) or len(graph_names) != 1:
            raise ValueError("Selected definition unit does not resolve to one authoritative graph name")
        name = graph_names[0]
        row = graph.get(name)
        if (row is None or row.get("kind") not in {"def", "definition", "abbrev"}
                or row.get("module") != manifest.get("source_module")
                or row.get("isPrivate") is not False or row.get("isInstance") is not False):
            raise ValueError("Selected graph declaration is not an ordinary public definition: " + name)
        names.append(name)
    if len(names) != len(set(names)):
        raise ValueError("Selected units duplicate a graph declaration name")
    return names


def validate_certificates(key, source, manifest, stage, graph_names):
    validation_path = stage / "validation.json"
    validation = read_json(validation_path)
    if not validation.get("validated"):
        raise ValueError("Closed-definition validation has not succeeded")
    equal_field = ("kernel_types_and_values_equal" if "kernel_types_and_values_equal" in validation
                   else "kernel_types_equal")
    if validation.get(equal_field) is not True:
        raise ValueError("Validation certificate does not affirm kernel type/value equality")
    if validation.get("standard_axioms_only") is not True:
        raise ValueError("Validation certificate does not affirm the standard-axiom audit")
    if validation.get("source_manifest_sha256") != sha_file(source.with_suffix(".manifest.json")):
        raise ValueError("Validation refers to a different bundle manifest")
    if validation.get("output_sha256") != sha_file(source):
        raise ValueError("Validation refers to different Definition source bytes")

    provided_names = validation.get("provided_names")
    if (not isinstance(provided_names, list) or len(provided_names) != len(set(provided_names))
            or set(provided_names) != set(graph_names)):
        raise ValueError("Validated declaration names differ from the authoritative graph-name set")
    # The validator preserves selected-unit order in provided_names.  Use that
    # recorded order for all row-by-row type/value checks below.
    expected_names = provided_names
    for variant in ("source", "generated"):
        axiom_rows = validation.get("axioms", {}).get(variant, {})
        if not isinstance(axiom_rows, dict) or set(axiom_rows) != set(expected_names):
            raise ValueError("Axiom certificate names do not exactly match provided_names")
    expected_core = VERIFICATION / "TypedSnapshotCore.inc"
    if validation.get("snapshot_core_sha256") != sha_file(expected_core):
        raise ValueError("Typed snapshot core changed after validation")

    # Verify the actual serialized kernel type and value snapshots, including
    # their certified hashes.  The validator's universe-parameter display-name
    # normalization is reproduced here before checking equality.
    tv_hashes = validation.get("type_value_snapshots", {})
    if set(tv_hashes) != {"original-definitions.json", "generated-definitions.json"}:
        raise ValueError("Missing original/generated type-value snapshot certificates")
    original_path = stage / "original-definitions.json"
    generated_path = stage / "generated-definitions.json"
    for path in (original_path, generated_path):
        if not path.is_file() or sha_file(path) != tv_hashes[path.name]:
            raise ValueError("A kernel type/value snapshot is absent or has changed: " + path.name)
    original, generated = read_json(original_path), read_json(generated_path)
    if ([row.get("name") for row in original] != expected_names
            or [row.get("name") for row in generated] != expected_names):
        raise ValueError("Snapshot declaration list differs from expected exact names")
    for left, right in zip(original, generated):
        if (len(left.get("levelParams", [])) != len(right.get("levelParams", []))
                or normalized(left, "type") != normalized(right, "type")
                or normalized(left, "value") != normalized(right, "value")):
            raise ValueError("Original/generated kernel type or value differs: " + left["name"])

    snapshots = validation.get("snapshots", {})
    if set(snapshots) != {"SnapshotOriginal.lean", "SnapshotGenerated.lean"}:
        raise ValueError("Missing exact source/generated snapshot file certificates")
    for filename, digest in snapshots.items():
        if sha_file(stage / filename) != digest:
            raise ValueError("A certified snapshot source changed: " + filename)

    preflights = validation.get("preflights")
    if not isinstance(preflights, list) or len(preflights) != 3:
        raise ValueError("Expected exactly three successful strict preflight records")
    runtime_sha = sha_file(VERIFICATION / "lean-runtime.json")
    bundle_relative = source.relative_to(TASK).as_posix()
    source_records = [r for r in preflights if r.get("source") == bundle_relative]
    snapshot_records = [r for r in preflights if r.get("source") != bundle_relative]
    if len(source_records) != 1 or len(snapshot_records) != 2:
        raise ValueError("Preflight records do not contain one bundle and two snapshot runs")
    expected_snapshot_hashes = {
        (stage / "SnapshotOriginal.lean").relative_to(TASK).as_posix(): sha_file(stage / "SnapshotOriginal.lean"),
        (stage / "SnapshotGenerated.lean").relative_to(TASK).as_posix(): sha_file(stage / "SnapshotGenerated.lean"),
    }
    seen_snapshots = set()
    for index, record in enumerate(preflights):
        record_source = record.get("source")
        source_path = task_path(record_source, "preflight source")
        log_path = task_path(record.get("log", ""), "preflight log")
        if (not source_path.is_file() or not log_path.is_file()
                or record.get("exit_code") != 0 or record.get("timed_out") is not False
                or record.get("success") is not True or record.get("source_unchanged") is not True
                or record.get("dependencies_stable_during_compile") is not True
                or record.get("input_certificates_stable") is not True
                or record.get("manifest_unchanged") is not True
                or record.get("source_certificate_stable") is not True
                or record.get("runtime_unchanged") is not True
                or not isinstance(record.get("timeout_seconds"), (int, float))
                or not 0 < record["timeout_seconds"] <= 300
                or not isinstance(record.get("seconds"), (int, float))
                or not 0 < record["seconds"] <= 300
                or record.get("runtime_sha256") != runtime_sha
                or record.get("source_sha256_before") != sha_file(source_path)
                or record.get("source_sha256_after") != sha_file(source_path)
                or record.get("log_sha256") != sha_file(log_path)
                or record.get("stdout_and_stderr_sha256") != record.get("log_sha256")):
            raise ValueError("A preflight is stale, failed, over budget, or not fully certified")
        if index == 0 and record.get("mode") != "emit-olean":
            raise ValueError("First preflight must compile the bundle and emit its staged OLean")
        if index > 0 and record.get("mode") != "modecheck":
            raise ValueError("Snapshot preflight unexpectedly emitted an OLean")
        if record_source != bundle_relative:
            expected_hash = expected_snapshot_hashes.get(record_source)
            if expected_hash is None or record_source in seen_snapshots:
                raise ValueError("Snapshot preflight source is unexpected or duplicated")
            seen_snapshots.add(record_source)
            if record.get("source_sha256_before") != expected_hash:
                raise ValueError("Snapshot preflight does not certify the exact snapshot bytes")
            expected_snapshot_name = Path(record_source).stem
            if (record.get("actual_module_identity") != expected_snapshot_name
                    or record.get("module_root") !=
                    (Path("verification") / stage.relative_to(VERIFICATION)).as_posix()):
                raise ValueError("Snapshot preflight module identity/root is not exact")
        elif record.get("actual_module_identity") != manifest.get("platform_module"):
            raise ValueError("Bundle preflight module identity differs from the manifest")
        elif record.get("module_root") != "verification/bundles-preview":
            raise ValueError("Bundle preflight used an unexpected Lean module root")
    if seen_snapshots != set(expected_snapshot_hashes):
        raise ValueError("One of the exact original/generated snapshot sources was not preflighted")

    bundle_record = source_records[0]
    if bundle_record.get("actual_module_identity") != manifest.get("platform_module"):
        raise ValueError("Bundle preflight module identity differs from the manifest")
    olean_rel = bundle_record.get("output_olean")
    if not olean_rel or not bundle_record.get("output_olean_sha256"):
        raise ValueError("Bundle preflight has no emitted OLean certificate")
    olean = task_path(olean_rel, "staged OLean")
    expected_olean = (VERIFICATION / "staged-build/lib/lean" /
                      Path(*manifest["platform_module"].split(".")).with_suffix(".olean"))
    if (olean != expected_olean.resolve() or not olean.is_file()
            or sha_file(olean) != bundle_record["output_olean_sha256"]):
        raise ValueError("Staged OLean is absent or has changed")
    return validation, preflights, bundle_record


def write_json(path, obj):
    # Write explicit LF bytes so certified metadata hashes are platform-stable.
    path.write_bytes((json.dumps(obj, ensure_ascii=False, indent=2) + "\n").encode("utf-8"))


def prepare(key):
    info = BUNDLES[key]
    source = VERIFICATION / "bundles-preview/Definitions" / (info["stem"] + ".lean")
    manifest_path = source.with_suffix(".manifest.json")
    if not source.is_file() or not manifest_path.is_file():
        raise ValueError("Expected source bundle and its exact manifest")
    manifest = read_json(manifest_path)
    expected_source_module = "OAI.NumberTheory.PiExponent.Analysis." + key
    if (manifest.get("source_module") != expected_source_module or
            manifest.get("platform_module") != PREFIX + info["stem"][len("Def_"):] or
            manifest.get("output") != source.relative_to(ROOT).as_posix() or
            manifest.get("output_sha256") != sha_file(source) or
            manifest.get("source_commit") != COMMIT or
            manifest.get("source_skeleton_preserved") is not True or
            manifest.get("full_definition_proofs_preserved") is not True or
            manifest.get("independent_byte_reconstruction_equal") is not True or
            manifest.get("source_unchanged") is not True or manifest.get("renames") or
            manifest.get("elaboration_only_helpers") or manifest.get("kept_local_instances")):
        raise ValueError("Bundle identity, lineage, or closed ordinary-definition scope differs")
    for field in ("source", "original_source", "facts"):
        certified = root_path(manifest[field], "manifest " + field)
        if not certified.is_file() or sha_file(certified) != manifest.get(field + "_sha256"):
            raise ValueError("Bundle lineage certificate is stale: " + field)
    for relative, expected in manifest.get("input_hashes", {}).items():
        certified = task_path(relative, "manifest input")
        if not certified.is_file() or sha_file(certified) != expected:
            raise ValueError("Bundle generation input changed: " + relative)
    if manifest.get("imports") != sorted(manifest.get("imports", [])):
        raise ValueError("Bundle imports are not in the exact canonical sorted order")
    if any(name.startswith(("OAI.", "Definitions.", "Theorems.", "Solutions."))
           for name in manifest["imports"]):
        raise ValueError("Closed bundle unexpectedly imports a project/platform module")
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", info["stem"][len("Def_"):]):
        raise ValueError("Platform definition name violates the API identifier rule")

    stage = VERIFICATION / "definition-validation" / info["stem"]
    graph_names = selected_graph_names(manifest)
    validation, preflights, bundle_record = validate_certificates(key, source, manifest, stage, graph_names)
    metadata = metadata_for(key)
    payload = {
        "definition_name": info["stem"][len("Def_"):],
        "definition_title": metadata["definition_title"],
        # Decode raw bytes without text-mode newline normalization: the JSON
        # string must round-trip to precisely the staged Lean source bytes.
        "definition": source.read_bytes().decode("utf-8"),
        "natural_language_statement": metadata["natural_language_statement"],
        "source": metadata["source"],
        "tags": metadata["tags"],
        "env": ENV,
        "private": False,
    }
    payload_bytes = json.dumps(payload, ensure_ascii=False).encode("utf-8")
    definition_bytes = payload["definition"].encode("utf-8")
    prep = {
        "schema_version": 1,
        "prepared_at_utc": datetime.now(timezone.utc).isoformat(),
        "offline_prepare_only": True,
        "publisher_script_sha256": sha_file(Path(__file__).resolve()),
        "definition_name": payload["definition_name"],
        "definition_module": manifest["platform_module"],
        "environment": ENV,
        "visibility": "public",
        "metadata_sha256": sha_bytes(json.dumps(metadata, ensure_ascii=False, indent=2).encode("utf-8") + b"\n"),
        "payload_sha256": sha_bytes(payload_bytes),
        "payload_encoding": "Exact UTF-8 JSON bytes saved to publish-payload.json and sent unchanged",
        "wire_body_sha256": sha_bytes(payload_bytes),
        "bundle_source_sha256": sha_file(source),
        "uploaded_definition_sha256": sha_bytes(definition_bytes),
        "uploaded_definition_bytes": len(definition_bytes),
        "definition_bytes_equal_bundle_source": definition_bytes == source.read_bytes(),
        "bundle_manifest_sha256": sha_file(manifest_path),
        "validation_sha256": sha_file(stage / "validation.json"),
        "source_commit": COMMIT,
        "preflight_count": len(preflights),
        "max_preflight_seconds": max(r["seconds"] for r in preflights),
        "olean_sha256": bundle_record["output_olean_sha256"],
        "kernel_type_value_snapshots": validation["type_value_snapshots"],
    }
    pub_record = stage / "publication.json"
    if pub_record.exists():
        previous = read_json(pub_record)
        if ((previous.get("publish_intent") or previous.get("definition_id")
             or previous.get("publish_payload_sha256"))
                and previous.get("publish_payload_sha256") != prep["payload_sha256"]):
            raise ValueError("Recorded publish intent is immutable; refusing to change payload")
    write_json(stage / "metadata.json", metadata)
    (stage / "publish-payload.json").write_bytes(payload_bytes)
    write_json(stage / "prepare-record.json", prep)
    return stage, metadata, payload, prep


def advance(stage, metadata, payload, prep):
    spec = importlib.util.spec_from_file_location("p2m_api", ROOT / "scripts/p2m_api.py")
    p2m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(p2m)
    record_path = stage / "publication.json"
    record = read_json(record_path) if record_path.exists() else {
        "definition_name": payload["definition_name"],
        "environment": ENV,
        "visibility": "public",
    }
    if record.get("environment", ENV) != ENV or record.get("definition_name") != payload["definition_name"]:
        raise ValueError("Existing publication record refers to a different target")
    if record.get("publish_payload_sha256", prep["payload_sha256"]) != prep["payload_sha256"]:
        raise ValueError("Publish payload changed after the recorded intent")

    def save():
        record["updated_at_utc"] = datetime.now(timezone.utc).isoformat()
        write_json(record_path, record)

    token = None

    def request(method, path, **kwargs):
        nonlocal token
        if token is None:
            token = p2m.get_token()
        status, body = p2m._request(method, path, token=token, **kwargs)
        try:
            return status, json.loads(body)
        except json.JSONDecodeError:
            return status, {"raw_body": body}

    def exact_readback(definition_id):
        status, body = request("GET", "/theorems/" + quote(definition_id, safe=""))
        record["target_readback"] = {"http_status": status, "body": body}
        save()
        if (status != 200 or body.get("theorem_id") != definition_id
                or body.get("theorem_name") != payload["definition_name"]
                or body.get("status") != "Definition"
                or body.get("mathlib_rev") != ENV or body.get("visibility") != "public"
                or body.get("definition") != payload["definition"]):
            raise ValueError("Definition readback identity, environment, visibility, or body differs")
        return body

    # A prior intent is an at-most-once boundary.  Resume only by polling its
    # recorded job; an ambiguous response without a job id is never reposted.
    if record.get("publish_intent"):
        job_id = record.get("job_id")
        if record.get("definition_id"):
            exact_readback(record["definition_id"])
            return record
        if not record.get("definition_id") and not job_id:
            raise ValueError("A POST intent exists without a known job id; inspect manually, never retry POST")
    elif record.get("definition_id"):
        exact_readback(record["definition_id"])
        return record
    else:
        # Exact-name listing in the selected environment; never reuse a name
        # based only on a substring or a row from another environment.
        matches, offset = [], 0
        while True:
            status, body = request(
                "GET", "/theorems?theorem_name=" + quote(payload["definition_name"]) +
                f"&env={ENV}&limit=100&offset={offset}")
            if status != 200 or not isinstance(body.get("theorems"), list):
                raise ValueError(f"Exact environment/name query failed: HTTP {status}")
            page = body["theorems"]
            matches.extend(row for row in page
                           if row.get("theorem_name") == payload["definition_name"])
            total = body.get("total")
            if not isinstance(total, int) or total < 0:
                raise ValueError("Name lookup omitted a reliable pagination total")
            offset += len(page)
            if offset >= total:
                break
            if not page:
                raise ValueError("Name lookup pagination ended before total rows were reached")
        if matches:
            if len(matches) != 1 or not matches[0].get("theorem_id"):
                raise ValueError("Duplicate exact name exists in the target environment")
            # Never silently adopt a same-name Definition with a different
            # environment, visibility, or source text.
            result = exact_readback(matches[0]["theorem_id"])
            record["definition_id"] = result["theorem_id"]
            record["publish_payload_sha256"] = prep["payload_sha256"]
            record["reused_exact_existing_definition"] = True
            save()
            return record

        status, environments = request("GET", "/environments")
        if (status != 200 or not any(row.get("mathlib_rev") == ENV
                                     and row.get("toolchain") == "leanprover/lean4:v4.33.1"
                                     for row in environments.get("environments", []))):
            raise ValueError("Pinned public platform environment unavailable; no POST sent")
        record["publish_payload_sha256"] = prep["payload_sha256"]
        record["publish_intent"] = {
            "at_utc": datetime.now(timezone.utc).isoformat(),
            "endpoint": "/submit-definition",
            "definition_name": payload["definition_name"],
            "environment": ENV,
            "visibility": "public",
            "payload": payload,
            "payload_sha256": prep["payload_sha256"],
            "bundle_source_sha256": prep["bundle_source_sha256"],
            "bundle_manifest_sha256": prep["bundle_manifest_sha256"],
            "validation_sha256": prep["validation_sha256"],
        }
        save()  # Durable intent before the one and only POST.
        raw = (stage / "publish-payload.json").read_bytes()
        if (sha_bytes(raw) != prep["wire_body_sha256"]
                or json.loads(raw.decode("utf-8")) != payload):
            raise ValueError("Prepared wire payload bytes changed before POST")
        status, body = request("POST", "/submit-definition", raw_body=raw, ctype="application/json")
        record["publish_response"] = {"http_status": status, "body": body,
                                       "response_sha256": sha_bytes(json.dumps(body, ensure_ascii=False).encode("utf-8"))}
        if (status == 202 and body.get("definition_name") == payload["definition_name"]
                and body.get("job_id")):
            record["job_id"] = body["job_id"]
        save()
        if not record.get("job_id"):
            raise ValueError("POST response is uncertain or malformed; it is recorded and will not be retried")
        return record

    # One bounded polling request per invocation.  No automatic tight loop.
    status, body = request("GET", "/publish-jobs/" + quote(record["job_id"], safe=""))
    record["last_publish_verdict"] = {"http_status": status, "body": body}
    save()
    if status != 200 or body.get("status") not in {"PUBLISHED", "FAILED", "ERROR", "PENDING", "COMPILING"}:
        raise ValueError("Publish job response is not a recognized job state")
    if (body.get("job_id", record["job_id"]) != record["job_id"]
            or body.get("definition_name", payload["definition_name"]) != payload["definition_name"]
            or body.get("mathlib_rev", ENV) != ENV):
        raise ValueError("Publish job identity, definition name, or environment differs")
    if body.get("status") == "PUBLISHED":
        definition_id = body.get("definition_id") or body.get("theorem_id")
        if not definition_id:
            raise ValueError("Published job has no definition identifier")
        record["definition_id"] = definition_id
        save()
        exact_readback(definition_id)
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("bundle", choices=sorted(BUNDLES),
                        help="Closed source bundle key: Collision or AnalyticCollision")
    parser.add_argument("--advance", action="store_true",
                        help="Explicitly perform duplicate-check GETs and at most one submit-definition POST")
    parser.add_argument("--prepare-only", action="store_true",
                        help="Explicitly select offline preparation (the default)")
    args = parser.parse_args()
    if args.advance and args.prepare_only:
        parser.error("choose --advance or --prepare-only, not both")
    stage, metadata, payload, prep = prepare(args.bundle)
    if args.advance:
        record = advance(stage, metadata, payload, prep)
        print(json.dumps({"advanced": True, "definition_name": payload["definition_name"],
                          "job_id": record.get("job_id"), "definition_id": record.get("definition_id"),
                          "status": record.get("last_publish_verdict", {}).get("body", {}).get("status")},
                         ensure_ascii=False))
    else:
        print(json.dumps({"prepared_offline": True, "stage": stage.relative_to(TASK).as_posix(),
                          "definition_name": payload["definition_name"],
                          "payload_sha256": prep["payload_sha256"]}, ensure_ascii=False))


if __name__ == "__main__":
    try:
        main()
    except (OSError, KeyError, ValueError, TypeError, json.JSONDecodeError) as exc:
        raise SystemExit("definition publisher refused to proceed: " + str(exc))
