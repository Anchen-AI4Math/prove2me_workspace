"""Read-only consumer of the separately preserved exact WithRefs identifier repair."""
from pathlib import Path

import formal_log_node_refs as original
import repair_formal_log_base_refs as repair
import generate_formal_log_truncation_provider as formal
import validate_namespace_context_providers as context

sha, read, rel, fail, file = context.sha, context.read, context.rel, context.fail, context.file
checked_output = original.checked_output
REPAIR_PRODUCER_SHA = "e8b587f1da8aa391ce632a25a4223103db6d3188ec3da6ef75dfdc22a69390cc"


def checked_preparation(stage):
    fail(stage.resolve() != repair.STAGE.resolve() or sha(Path(repair.__file__)) != REPAIR_PRODUCER_SHA,
         "Only exact immutable f1 two-identifier repair is supported")
    old, old_manifest, output = original.checked_preparation(stage)
    old_document = read(old_manifest)
    before, after = old.read_bytes(), old.read_bytes()
    ledger = []
    for source, replacement in repair.REPAIRS:
        fail(after.count(source) != 1 or after.count(replacement) != 0, "Repair identifier anchors are not exact unique fresh matches")
        offset = after.index(source)
        ledger.append({"start": offset, "end": offset + len(source), "source": source.decode(), "replacement": replacement.decode()})
        after = after[:offset] + replacement + after[offset + len(source):]
    new, mp = repair.NEW, repair.NEW_MANIFEST
    fail(len(after) - len(before) != 18 or new.read_bytes() != after, "Repaired snapshot differs from exact two identifier edits")
    rp = repair.OLD_RECORD; r = read(rp)
    log = file(r["log"])
    fail(r.get("success") is not False or r.get("exit_code") == 0 or r.get("timed_out") is not False
         or r.get("mode") != "modecheck" or r.get("actual_module_identity") != old.stem
         or r.get("source") != rel(old) or r.get("manifest") != rel(old_manifest)
         or r.get("module_root") != rel(stage) or r.get("imports") != old_document["imports"]
         or r.get("runtime_sha256") != old_document["runtime_sha256"]
         or not 0 < r["seconds"] <= r["timeout_seconds"] <= 300, "Preserved failure is not the exact bounded old WithRefs attempt")
    for field in ["source_unchanged", "manifest_unchanged", "source_certificate_stable", "input_certificates_stable", "dependencies_stable_during_compile"]:
        fail(r.get(field) is not True, "Preserved failure input stability gate failed: " + field)
    for field in ["source_sha256_before", "source_sha256_after"]:
        fail(r[field] != sha(old), "Preserved failed source bytes changed")
    for field in ["manifest_sha256_before", "manifest_sha256_after"]:
        fail(r[field] != sha(old_manifest), "Preserved failed manifest bytes changed")
    fail(sha(log) != r["log_sha256"] or sha(log) != r["stdout_and_stderr_sha256"], "Preserved failed log bytes changed")
    fail("unexpected token 'export'; expected identifier" not in log.read_text(encoding="utf-8"), "Preserved failure does not contain the exact exporter identifier parser error")
    formal.runner.verify_manifest_inputs(old_document)
    fail(r["source_certificate"] != formal.runner.verify_source_certificate(old, old_document), "Preserved failed source certificate differs")
    for which in ["manifest_input_hashes_before", "manifest_input_hashes_after"]:
        captured = r[which]
        fail(set(captured) != set(old_document["input_hashes"]), "Preserved failed actual input domain differs")
        for p, digest in old_document["input_hashes"].items():
            fail(captured[p] != {"expected_sha256": digest, "actual_sha256": digest, "matches": True}, "Preserved failed actual input hash differs")
    runtime = formal.runner.validate_runtime()[0]
    current = formal.runner.dependency_certificates(old_document["imports"], formal.runner.effective_search_path(runtime["environment"]["LEAN_PATH"]), {old.stem})
    context.match_dependencies([{k:d[k] for k in ["module", "path", "resolved_search_root", "sha256_before"]}
                               for d in r["dependency_oleans"]], current)
    for d in r["dependency_oleans"]:
        fail(d["sha256_after"] != d["sha256_before"] or d["stable_during_compile"] is not True, "Preserved failed actual OLean input was unstable")
    archive = repair.OLD_GENERATED_ARCHIVE
    fail(not isinstance(read(archive), list), "Preserved failed type export archive schema differs")
    pins = dict(old_document["input_hashes"])
    pins.update({rel(Path(repair.__file__)): sha(Path(repair.__file__)), rel(old): sha(old), rel(old_manifest): sha(old_manifest),
        rel(rp): sha(rp), rel(log): sha(log), rel(archive): sha(archive), rel(stage / "preparation.json"): sha(stage / "preparation.json")})
    expected = dict(old_document)
    expected.update(output=new.relative_to(formal.ROOT).as_posix(), output_sha256=sha(new), input_hashes=pins,
        repair_of=rel(old), repair_of_sha256=sha(old), repair_ledger=ledger,
        prior_failed_preflight=rel(rp), prior_failed_preflight_sha256=sha(rp),
        node_validated=False, Lean_started=False, submission_ready=False)
    fail(read(mp) != expected, "Exact repaired actual compiler manifest reconstruction differs")
    preparation = {"schema_version": 1, "artifact_kind": "formal-log-proof-ref-keyword-repair", "source": rel(old), "source_sha256": sha(old),
        "output": rel(new), "output_sha256": sha(new), "manifest": rel(mp), "manifest_sha256": sha(mp), "repair_ledger": ledger,
        "prior_failed_preflight": rel(rp), "prior_failed_preflight_sha256": sha(rp), "prior_failed_log": rel(log), "prior_failed_log_sha256": sha(log),
        "only_function_identifier_renamed": True, "prior_failed_generated_type_archive": rel(archive), "prior_failed_generated_type_archive_sha256": sha(archive),
        "old_source_and_evidence_preserved": True, "Lean_started": False, "validated": False, "submission_ready": False}
    fail(read(repair.PREPARATION) != preparation, "Exact immutable repair preparation differs")
    return new, mp, output


def lineage_evidence():
    return {"preparation": rel(repair.PREPARATION), "preparation_sha256": sha(repair.PREPARATION),
        "source": rel(repair.OLD), "source_sha256": sha(repair.OLD),
        "failed_preflight": rel(repair.OLD_RECORD), "failed_preflight_sha256": sha(repair.OLD_RECORD),
        "failed_generated_type_archive": rel(repair.OLD_GENERATED_ARCHIVE), "failed_generated_type_archive_sha256": sha(repair.OLD_GENERATED_ARCHIVE),
        "failed_outputs_used_as_success_evidence": False, "exact_two_identifier_edits": True}
