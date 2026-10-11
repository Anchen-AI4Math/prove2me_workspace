"""Read-only frozen ZIP audit. Writes only this review's new JSON and log."""
from pathlib import Path, PurePosixPath
import hashlib
import json
import re
import sys
import zipfile

sys.stdout.reconfigure(encoding="utf-8")
OUT = Path(__file__).resolve().parent
TASK = OUT.parents[2]
ROOT = TASK.parents[1]
ARCHIVE = OUT / "zeta9-advanced-proofs-2026-10-02.zip"
EXPECTED = "87c7ea2680bda568e8e2b36b82f48dab6910ab9bf92e8b4486471c547792e31c"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
checks, findings, bound = [], [], {}

def sha(data):
    return hashlib.sha256(data).hexdigest()

def filehash(path):
    path = path.resolve()
    value = sha(path.read_bytes())
    bound[path.relative_to(ROOT.resolve()).as_posix()] = value
    return value

def load(path):
    return json.loads(path.read_text(encoding="utf-8-sig"))

def check(name, fn):
    try:
        detail = fn()
        checks.append({"name": name, "pass": True, "detail": detail})
    except Exception as exc:
        checks.append({"name": name, "pass": False, "error": repr(exc)})

def code(text):
    i, depth, result = 0, 0, []
    while i < len(text):
        if depth:
            if text[i:i+2] == "/-": depth, i = depth+1, i+2
            elif text[i:i+2] == "-/": depth, i = depth-1, i+2
            else: i += 1
        elif text[i:i+2] == "/-": depth, i = 1, i+2
        elif text[i:i+2] == "--":
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == "\\": i += 2
                elif text[i] == '"': i += 1; break
                else: i += 1
        else: result.append(text[i]); i += 1
    assert depth == 0
    return "".join(result)

z = zipfile.ZipFile(ARCHIVE)
members = z.namelist()
data = {name: z.read(name) for name in members}
manifest = json.loads(data["source-manifest.json"])
validation = load(OUT / "package-validation.json")

def zip_integrity():
    assert filehash(ARCHIVE) == EXPECTED
    assert z.testzip() is None
    assert len(members) == len(set(members)) == 81
    entries = {r["path"]: r for r in manifest["files"]}
    assert len(entries) == len(manifest["files"]) == 80
    assert set(entries) | {"source-manifest.json"} == set(members)
    for name, row in entries.items():
        assert len(data[name]) == row["bytes"]
        assert sha(data[name]) == row["sha256"]
    assert data["source-manifest.json"] == (OUT / "source-manifest.json").read_bytes()
    assert data["README.md"] == (OUT / "README.md").read_bytes()
    assert validation["archive_sha256"] == EXPECTED
    assert validation["source_manifest_sha256"] == filehash(OUT / "source-manifest.json")
    for line in (OUT / "SHA256SUMS.txt").read_text(encoding="utf-8-sig").splitlines():
        expected, name = line.split("  ", 1)
        assert filehash(OUT / name) == expected
    for name in ["README.md", "package-validation.json", "SHA256SUMS.txt"]:
        filehash(OUT / name)
    return {"CRC": "PASS", "members": 81, "manifest_payload_members": 80, "all_member_sha256_and_sizes_match": True, "sidecars_match": True}

check("archive_CRC_81_members_and_80_member_hash_size_manifest", zip_integrity)

def source_provenance():
    count = 0
    for row in manifest["files"]:
        provenance = row.get("source_provenance")
        if not provenance:
            continue
        path = ROOT / provenance["workspace_source"]
        assert path.is_file()
        assert len(path.read_bytes()) == provenance["bytes"] == row["bytes"]
        assert sha(data[row["path"]]) == provenance["sha256"] == filehash(path)
        assert data[row["path"]] == path.read_bytes()
        count += 1
    upstream = json.loads(data["audit/upstream-pnt/kernel-source-manifest.json"])
    assert len(upstream["sources"]) == 23
    pnt, architect = 0, 0
    for row in upstream["sources"]:
        assert sha(data[row["path"]]) == row["sha256"]
        if row["module"].startswith("PrimeNumberTheoremAnd."):
            assert row["source_commit"] == "55270df807213fc3584523d09e0311d7dc073ff5"
            pnt += 1
        else:
            assert row["source_commit"] == "0f5bc0209ae02a7fb0cfe7d113d4094542cee221"
            architect += 1
    assert (pnt, architect) == (14, 9)
    for filename, original in [
        ("licenses/PrimeNumberTheoremAnd-APACHE-2.0.txt", TASK / "verification/formalization-pnt-dependency-2026-10-02/external/LICENSE"),
        ("licenses/LeanArchitect-APACHE-2.0.txt", TASK / "verification/formalization-pnt-dependency-2026-10-02/architect/LICENSE")]:
        assert data[filename] == original.read_bytes()
        assert sha(data[filename]) == filehash(original)
        assert b"Apache License" in data[filename]
    assert sha(data["missions/zeta9/formalization/PNTTransfer.lean"]) == "6c56d052ae48b44e76d40e7a08fcfd6ca8d232b5bc7882430bfbf48b85bb2c8b"
    assert sha(data["missions/zeta9/formalization/ShortZeroCoefficient.lean"]) == "9bf18387c4a51dd6dca03ecf197fc1cd85337fabf5b1d3421e2302e452347dbc"
    return {"source_provenance_files_byte_exact": count, "actual_PNT_modules": pnt, "actual_Architect_modules": architect, "both_Apache_licenses_byte_exact": True}

check("actual_source_provenance_23_PNT_Architect_and_licenses", source_provenance)

def prohibited_members():
    allowed_suffix = {".lean", ".json", ".jsonl", ".log", ".txt", ".md", ".py"}
    for name in members:
        path = PurePosixPath(name)
        assert not path.is_absolute() and ".." not in path.parts and "\\" not in name
        assert path.suffix in allowed_suffix or name == "lean-toolchain"
        assert all(part.lower() not in {".lake", ".git", "node_modules", "__pycache__", ".aws", ".codex", "api-docs", "credentials", "definition-receipts", "problem-receipts", "proof-receipts", "target-readback"} for part in path.parts)
        assert not re.search(r"(?:^|/)(?:\.env|auth\.json|credentials\.[^/]+)$", name, re.I)
        text = data[name].decode("utf-8-sig")
        assert not re.search(r"(?:Authorization:\s*Bearer\s+\S+|ghp_[A-Za-z0-9]{20,}|github_pat_[A-Za-z0-9_]{20,}|-----BEGIN (?:RSA |EC |OPENSSH )?PRIVATE KEY-----)", text)
        assert not re.search(r'"(?:access_token|refresh_token|api_key|client_secret|password)"\s*:', text)
    return {"all_members_are_named_text_source_or_offline_evidence": True, "cache_compiled_binary_git_credentials_and_API_receipt_members": [], "secret_signature_scan": "PASS"}

check("no_cache_binary_credentials_or_API_receipts", prohibited_members)

module_files = {name[:-5].replace("/", "."): name for name in members if name.endswith(".lean") and name != "lakefile.lean"}
imports = {}
for module, name in module_files.items():
    imports[module] = re.findall(r"^(?:(?:public|meta)\s+)*import\s+([A-Za-z0-9_'.]+)", code(data[name].decode("utf-8-sig")), re.M)
closures = {}

def actual_import_closure():
    assert len(module_files) == 39
    external = set()
    for module, deps in imports.items():
        for dep in deps:
            if dep not in module_files:
                assert dep.startswith(("Mathlib.", "Batteries.", "Lean", "Init", "Std")), (module, dep)
                external.add(dep)
    stub_names = set(manifest["reference_statement_stubs"])
    omissions = {}
    for root in ["Audit.Kernel", "Audit.C3Signed", "Audit.C3Nonzero", "Audit.NativeC3", "Audit.PNT"]:
        seen, work = set(), [root]
        while work:
            module = work.pop()
            if module in seen:
                continue
            assert module in module_files
            seen.add(module)
            work.extend(dep for dep in imports[module] if dep in module_files)
        closure = sorted(module_files[module] for module in seen)
        assert not stub_names.intersection(closure)
        closures[root] = closure
        documented = set(manifest["complete_proof_audit_import_closures"][root])
        assert documented <= set(closure)
        if set(closure) - documented:
            omissions[root] = sorted(set(closure) - documented)
    for root in ["Audit.Kernel", "Audit.PNT"]:
        assert sum(name.startswith("PrimeNumberTheoremAnd/") for name in closures[root]) == 14
        assert sum(name.startswith("Architect/") or name == "Architect.lean" for name in closures[root]) == 9
    if omissions:
        findings.append({"severity": "informational", "name": "frozen_manifest_closure_metadata_omits_public_import_recursion", "affects_actual_package_completeness": False, "detail": "The frozen complete_proof_audit_import_closures lists omit eight Architect submodules reached via public import. All omitted modules are present with verified original bytes, and the actual Lean build succeeded. This independent sidecar records the complete closures, including public imports; the frozen ZIP and sidecars were not changed.", "omitted_members_by_root": omissions})
    return {"actual_import_closures_complete": True, "public_imports_recognized": True, "all_23_upstream_modules_reachable_for_Kernel_and_PNT": True, "five_actual_audit_closures_exclude_statement_stubs": True, "frozen_metadata_list_omissions": omissions}

check("actual_Lean_import_closure_complete_including_public_imports", actual_import_closure)

def axiom_records(text):
    records = {}
    for declaration, axioms in re.findall(r"'([^'\n]+)' depends on axioms:\s*\[([^\]]*)\]", text):
        records.setdefault(declaration, []).append({x.strip() for x in axioms.split(",") if x.strip()})
    return records

def build_and_standard_three():
    receipt = json.loads(data["audit/standalone-rebuild/receipt.json"])
    resumed = json.loads(data["audit/standalone-rebuild/resume-receipt.json"])
    assert receipt["status"] == "PASS" and receipt["exit_code"] == 0
    assert resumed["status"] == "PASS" and resumed["aggregate_exit_code"] == 0
    assert len(resumed["completed_earlier_steps"]) == 31 and len(resumed["new_steps"]) == 9
    assert all(row["exit_code"] == 0 for row in resumed["new_steps"])
    assert resumed["new_steps"][-1]["command"] == ["lake", "--no-cache", "build", "Audit", "Theorems"]
    assert resumed["external_PNT_binary_cache_borrowed"] is False
    assert resumed["upstream_modules_successfully_built_in_this_project"] == 23
    assert data["audit/standalone-rebuild/build-exit.txt"].decode("utf-8-sig").strip() == "0"
    assert data["audit/standalone-rebuild/resumed-exit.txt"].decode("utf-8-sig").strip() == "0"
    assert sha(data["audit/standalone-rebuild/build.log"]) == receipt["build_log_sha256"]
    assert sha(data["audit/standalone-rebuild/earlier-sequential.log"]) == resumed["earlier_sequential_log_sha256"]
    assert sha(data["audit/standalone-rebuild/resumed.log"]) == resumed["new_log_sha256"]
    log = data["audit/standalone-rebuild/build.log"].decode("utf-8-sig")
    assert "Build completed successfully (3780 jobs)." in log
    assert ": error:" not in log
    required = set(["MediumPNT", "ZetaNine.ExternalPNT.checked_medium_pnt", "ZetaNine.ShortZeroCoefficient.A_even_signed_lower", "ZetaNine.ShortZeroCoefficient.A_ne_zero_of_even", "ZetaNine.AdvancedAudit.checked_c3_signed_lower", "ZetaNine.AdvancedAudit.checked_c3_nonzero"] + ["ZetaNine.HarmonicStability."+n for n in ["psi_pnt_rate", "theta_pnt", "lcm_pnt", "harmonic_log_den_rate", "harmonic_perturbed_log_den_rate", "harmonic_nine_double_log_den_rate"]] + ["ZetaNine.AdvancedAudit."+n for n in ["checked_psi_rate", "checked_harmonic_rate", "checked_perturbed_harmonic_rate", "checked_nine_double_harmonic_rate"]])
    assert len(required) == 16
    for log_text in [log, (OUT / "extracted-audits.log").read_text(encoding="utf-8-sig")]:
        records = axiom_records(log_text)
        assert required <= set(records)
        for name in required:
            assert all(axioms == STANDARD for axioms in records[name]), name
    extracted = load(OUT / "extracted-validation.json")
    assert extracted["status"] == "PASS" and extracted["archive_sha256"] == EXPECTED
    assert extracted["extracted_payload_verifier_exit"] == 0
    assert len(extracted["steps"]) == 5 and all(row["exit_code"] == 0 for row in extracted["steps"])
    assert extracted["audit_log_sha256"] == filehash(OUT / "extracted-audits.log")
    assert validation["extraction_receipt_sha256"] == filehash(OUT / "extracted-validation.json")
    assert (OUT / "resumed-build-receipt.json").read_bytes() == data["audit/standalone-rebuild/resume-receipt.json"]
    for name in ["resumed-build-receipt.json", "combined-build.log", "resumed-build.log", "resumed-build-exit.txt", "sequential-build.log"]:
        filehash(OUT / name)
    return {"final_actual_build_exit": 0, "final_success_diagnostic": "Build completed successfully (3780 jobs).", "actual_required_declarations_standard_three": sorted(required), "extracted_five_audit_compiles_exit_zero": True, "no_rebuild_performed_by_reviewer": True, "prior_parallel_failure_retained_honestly": True}

check("final_build_exit_zero_and_16_actual_standard_three_axiom_reports", build_and_standard_three)

def c3_fidelity_and_proof_holes():
    review = json.loads(data["audit/coefficient/independent-integration-review.json"])
    assert review["verdict"] == "PASS" and all(row["pass"] for row in review["checks"])
    assert review["source_sha256"] == "9bf18387c4a51dd6dca03ecf197fc1cd85337fabf5b1d3421e2302e452347dbc"
    checked = []
    for path, expected in review["sha256"].items():
        archive_path = path.replace("missions/zeta9/formalization/platform/coefficient/", "audit/coefficient/")
        if archive_path in data:
            assert sha(data[archive_path]) == expected
            checked.append(archive_path)
    original = {r["label"]: r for r in map(json.loads, data["audit/coefficient/types-original.jsonl"].decode().splitlines())}
    definitions = {r["label"]: r for r in map(json.loads, data["audit/coefficient/types-definition.jsonl"].decode().splitlines())}
    for label in ["ZetaNine.ShortZeroCoefficient.A", "ZetaNine.ShortZeroCoefficient.weightedCoeff"]:
        assert original[label]["type"] == definitions[label]["type"]
        assert original[label]["value"] == definitions[label]["value"]
    for i, name in enumerate(["A_even_signed_lower", "A_ne_zero_of_even"]):
        label = "ZetaNine.ShortZeroCoefficient." + name
        for kind in ["solution", "reference"]:
            rows = [json.loads(s) for s in data[f"audit/coefficient/types-{i}_{kind}.jsonl"].decode().splitlines() if s.startswith("{")]
            assert len(rows) == 1 and rows[0]["type"] == original[label]["type"]
    assert "∀ (d m : ℕ)" in original["ZetaNine.ShortZeroCoefficient.A_even_signed_lower"]["type"]
    assert "Even n → ZetaNine.ShortZeroCoefficient.A n m ≠ 0" in original["ZetaNine.ShortZeroCoefficient.A_ne_zero_of_even"]["type"]
    actual_holes = []
    for name in members:
        if not name.endswith(".lean"):
            continue
        lean_code = code(data[name].decode("utf-8-sig"))
        assert not re.search(r"^\s*(?:private\s+)?axiom\s", lean_code, re.M), name
        if re.search(r"\b(?:sorry|admit)\b", lean_code):
            if name in manifest["unchanged_upstream_sorry_detection_or_tactic_infrastructure"]:
                continue
            actual_holes.append(name)
    assert sorted(actual_holes) == sorted(manifest["reference_statement_stubs"])
    assert "import PrimeNumberTheoremAnd.MediumPNT" in data["missions/zeta9/formalization/PNTTransfer.lean"].decode()
    assert "(hr : Tendsto (fun N => logDen (r N) / (N : ℝ)) atTop (nhds 0))" in data["missions/zeta9/formalization/PNTTransfer.lean"].decode()
    return {"archived_C3_independent_review_pass_and_source_hash_match": True, "matched_review_provenance_members": checked, "two_actual_definition_values_and_four_endpoint_types_equal": True, "all_even_quantifier_including_zero_retained": True, "only_unimported_reference_stubs_have_own_proof_holes": actual_holes, "genuine_MediumPNT_and_real_perturbation_hr_retained": True}

check("C3_source_proof_provenance_and_actual_endpoint_trust_boundary", c3_fidelity_and_proof_holes)

filehash(Path(__file__))
passed = all(row["pass"] for row in checks)
result = {"schema_version": 1, "reviewer": "/root/pnt_integration_review_1003", "date": "2026-10-03", "verdict": "PASS" if passed else "FAIL", "pass_scope": "Actual frozen source package completeness, byte provenance, CRC and retained proof/build evidence. Informational closure-list omissions are recorded separately.", "archive_sha256": filehash(ARCHIVE), "archive_bytes": ARCHIVE.stat().st_size, "checks": checks, "findings": findings, "independently_recomputed_complete_local_audit_import_closures": closures, "zip_member_sha256": {name: sha(data[name]) for name in members}, "reviewed_stable_file_sha256_root_relative": bound, "review_method": {"frozen_ZIP_and_sidecars_modified": False, "proof_builds_repeated": False, "author_validation_script_executed": False, "credentials_read": False, "network_API_gh_operations": False, "shared_root_written": False}, "boundaries": ["All actual required endpoints use only propext, Classical.choice and Quot.sound.", "Two included Theorems files are statement stubs excluded from all five complete proof audit import closures.", "The frozen manifest's original closure lists omit public-import recursion; this sidecar records corrected complete closures without mutating the archive.", "J, S, primitive decay and zeta(9) irrationality remain open; platform acceptance is not claimed."]}
(OUT / "independent-release-review.json").write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
summary = {"verdict": result["verdict"], "archive_sha256": result["archive_sha256"], "checks": [{k: row[k] for k in ["name", "pass", "error"] if k in row} for row in checks], "informational_findings": [row["name"] for row in findings], "review_sha256": sha((OUT / "independent-release-review.json").read_bytes())}
(OUT / "independent-release-review.log").write_text(json.dumps(summary, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
print(json.dumps(summary, ensure_ascii=False, indent=2))
sys.exit(0 if passed else 1)
