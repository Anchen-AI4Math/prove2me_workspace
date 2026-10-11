"""Package and verify the explicit advanced proof source/audit allow-list.

No API, gh, credential access, shared workspace writes, or dependency downloads.
The earlier research ZIP and nine-proof ZIP are only hashed against their baselines.
"""
from pathlib import Path, PurePosixPath
import hashlib
import importlib.util
import json
import re
import shutil
import zipfile

OUT = Path(__file__).resolve().parent
PROJECT = OUT / "project"
TASK = OUT.parents[2]
PIN = "0df444a360eaa60ab8c11dca51a86af692955474"
ARCHIVE = OUT / "zeta9-advanced-proofs-2026-10-02.zip"

def load(p):
    return json.loads(p.read_text(encoding="utf-8-sig"))

def sha(data):
    return hashlib.sha256(data).hexdigest()

prepared = load(OUT / "prepared-source-manifest.json")
build = load(PROJECT / "audit/standalone-rebuild/receipt.json")
resume = load(OUT / "resumed-build-receipt.json")
assert build["status"] == "PASS" and build["exit_code"] == 0
assert build["required_declarations"] == 16 and not build["missing_reports"] and not build["unexpected_axioms"]
assert resume["status"] == "PASS" and resume["aggregate_exit_code"] == 0
assert resume["upstream_modules_successfully_built_in_this_project"] == 23
assert resume["upstream_modules_rebuilt_during_resume"] == 0
assert not resume["external_PNT_binary_cache_borrowed"]
assert len(resume["completed_earlier_steps"]) == 31 and len(resume["new_steps"]) == 9
assert all(x["exit_code"] == 0 for x in resume["completed_earlier_steps"] + resume["new_steps"])
assert resume["new_steps"][-1]["command"] == ["lake", "--no-cache", "build", "Audit", "Theorems"]
assert sha((PROJECT / "audit/standalone-rebuild/build.log").read_bytes()) == build["build_log_sha256"]
assert sha((OUT / "sequential-build.log").read_bytes()) == resume["earlier_sequential_log_sha256"]
assert sha((OUT / "resumed-build.log").read_bytes()) == resume["new_log_sha256"]

payload = {}
provenance = {}
for row in prepared["sources"]:
    data = (PROJECT / row["path"]).read_bytes()
    assert sha(data) == row["sha256"], row["path"]
    assert len(data) == row["bytes"]
    payload[row["path"]] = data
    provenance[row["path"]] = row

additional = [
    "lean-toolchain", "lake-manifest.json", "lakefile.lean", "README.md", "UPSTREAM.json",
    "rebuild.py", "verify_package.py", "Audit/C3Signed.lean", "Audit/C3Nonzero.lean",
    "Audit/NativeC3.lean", "Audit/PNT.lean", "audit/standalone-rebuild/build.log",
    "audit/standalone-rebuild/build-exit.txt", "audit/standalone-rebuild/receipt.json",
]
for name in additional:
    payload[name] = (PROJECT / name).read_bytes()

historical = {
    "standalone-build-attempt1.log": "audit/standalone-rebuild/initial-parallel-attempt.log",
    "standalone-build-attempt1-exit.txt": "audit/standalone-rebuild/initial-parallel-attempt-exit.txt",
    "sequential-build.log": "audit/standalone-rebuild/earlier-sequential.log",
    "resumed-build.log": "audit/standalone-rebuild/resumed.log",
    "resumed-build-exit.txt": "audit/standalone-rebuild/resumed-exit.txt",
    "resumed-build-receipt.json": "audit/standalone-rebuild/resume-receipt.json",
}
for source, target in historical.items():
    data = (OUT / source).read_bytes()
    (PROJECT / target).parent.mkdir(parents=True, exist_ok=True)
    (PROJECT / target).write_bytes(data)
    payload[target] = data

spec = importlib.util.spec_from_file_location("advanced_rebuild", PROJECT / "rebuild.py")
helper = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helper)
all_modules = helper.sequential_modules()
assert len(all_modules) == 39
lean_paths = sorted(p for p in payload if p.endswith(".lean"))
module_paths = {p[:-5].replace("/", "."): p for p in lean_paths if p != "lakefile.lean"}
assert set(all_modules) == set(module_paths)

def lean_code(text):
    """Remove nested block comments, line comments and strings for token checks."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1; out.extend("  "); i += 2
            elif text.startswith("-/", i):
                depth -= 1; out.extend("  "); i += 2
            else:
                out.append("\n" if text[i] == "\n" else " "); i += 1
        elif text.startswith("/-", i):
            depth = 1; out.extend("  "); i += 2
        elif text.startswith("--", i):
            while i < len(text) and text[i] != "\n":
                out.append(" "); i += 1
        elif text[i] == '"':
            out.append(" "); i += 1
            while i < len(text):
                if text[i] == "\\":
                    out.extend("  "); i += 2
                elif text[i] == '"':
                    out.append(" "); i += 1; break
                else:
                    out.append("\n" if text[i] == "\n" else " "); i += 1
        else:
            out.append(text[i]); i += 1
    assert depth == 0, "Unclosed Lean comment"
    return "".join(out)

stub_paths = {
    "Theorems/Thm_ZetaNine_ShortZeroCoefficient_A_even_signed_lower.lean",
    "Theorems/Thm_ZetaNine_ShortZeroCoefficient_A_ne_zero_of_even.lean",
}
code = {p: lean_code(payload[p].decode("utf-8-sig")) for p in lean_paths}
sorry_paths = {p for p,s in code.items() if re.search(r"(?<![\w.`])\b(?:sorry|sorryAx|admit)\b", s)}
# Architect preserves quoted ``sorryAx names for hole detection and a g.admit
# method in its tactic implementation. Those metaprogram tokens are not proof
# holes. The compiled theorem axiom reports are the decisive no-sorry check.
metaprogram_token_paths = {p for p,s in code.items() if re.search(r"\b(?:sorryAx|admit)\b", s)} - sorry_paths
assert metaprogram_token_paths == {"Architect/CollectUsed.lean", "Architect/Output.lean", "Architect/Tactic.lean"}
axiom_paths = {p for p,s in code.items() if re.search(r"\baxiom\b", s)}
assert sorry_paths == stub_paths, sorted(sorry_paths)
assert not axiom_paths, sorted(axiom_paths)
imports = {m: re.findall(r"(?m)^\s*import\s+([^\r\n]+)", code[p]) for m,p in module_paths.items()}
imports = {m: [word for line in lines for word in line.split()] for m,lines in imports.items()}
external_imports = sorted({i for items in imports.values() for i in items if i not in module_paths})
local_closures = {}
for start in ["Audit.Kernel", "Audit.C3Signed", "Audit.C3Nonzero", "Audit.NativeC3", "Audit.PNT"]:
    seen = set()
    def visit(module):
        if module in seen:
            return
        seen.add(module)
        for imported in imports[module]:
            if imported in module_paths:
                visit(imported)
            else:
                assert imported.startswith(("Mathlib", "Lean", "Init", "Batteries")), (module, imported)
    visit(start)
    paths = sorted(module_paths[m] for m in seen)
    assert not (set(paths) & stub_paths), start
    local_closures[start] = paths

lock = load(PROJECT / "lake-manifest.json")
assert next(x for x in lock["packages"] if x["name"] == "mathlib")["rev"] == PIN
assert any(x["name"] == "batteries" for x in lock["packages"])
assert payload["lean-toolchain"] == b"leanprover/lean4:v4.33.1\n"
upstream = load(PROJECT / "audit/upstream-pnt/kernel-source-manifest.json")
assert len(upstream["sources"]) == 23
for row in upstream["sources"]:
    assert sha(payload[row["path"]]) == row["sha256"]
licenses = ["licenses/PrimeNumberTheoremAnd-APACHE-2.0.txt", "licenses/LeanArchitect-APACHE-2.0.txt"]
assert all(sha(payload[p]) == "c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4" for p in licenses)

immutable = []
for relative, expected, expected_size in [
    ("publication/2026-10-02/zeta9-research-2026-10-02.zip", "68a821653ae08e4f0b2917c770215dfbe60af2670ea3cb6a87521f75b665f2a0", 7756223),
    ("publication/2026-10-02/formal-proofs/zeta9-formal-proofs-2026-10-02.zip", "50e1058a1c44f65271837a1943bc0a0a7c80385c941413d284e7dcb70ad82405", 81079),
]:
    p = TASK / relative
    data = p.read_bytes()
    assert sha(data) == expected and len(data) == expected_size, relative
    immutable.append({"path": relative, "sha256": expected, "bytes": expected_size, "unchanged": True})

for name, data in payload.items():
    parts = PurePosixPath(name).parts
    assert not any(x in {".lake", ".git", ".aws", ".codex", ".agents", ".."} for x in parts), name
    assert PurePosixPath(name).suffix.lower() not in {".olean", ".ilean", ".dll", ".exe", ".so", ".o", ".a", ".bin", ".zip", ".pyc"}, name
    assert not any(x in name.lower() for x in ["api-docs", "auth", "credential", "platform-before", "platform-after"]), name
    assert not re.search(rb"(?i)(?:Authorization\s*:\s*Bearer\s+|sk-[A-Za-z0-9_-]{20,}|github_pat_[A-Za-z0-9_]{20,})", data), "Secret-like content: " + name

files = []
for name in sorted(payload):
    row = {"path": name, "bytes": len(payload[name]), "sha256": sha(payload[name])}
    if name in provenance:
        row["source_provenance"] = provenance[name]
    else:
        row["role"] = "generated offline configuration, audit, rebuild helper, or documentation"
    files.append(row)
manifest = {
    "schema_version": 1, "package_date": "2026-10-02", "package_kind": "advanced complete Lean proof source supplement",
    "lean_version": "4.33.1", "mathlib_revision": PIN, "files": files,
    "payload_file_count": len(files), "lean_source_files_including_lakefile": len(lean_paths),
    "formal_modules": len(module_paths), "upstream_modules": 23,
    "manifest_self_hash_omitted": True, "source_bytes_preserved": True,
    "complete_proof_audit_import_closures": local_closures,
    "reference_statement_stubs": sorted(stub_paths),
    "unchanged_upstream_sorry_detection_or_tactic_infrastructure": sorted(metaprogram_token_paths),
    "all_actual_endpoints_standard_three_axioms": True,
    "required_axiom_declarations": build["required_declarations"],
    "root_irrationality_open": True, "platform_acceptance_claimed": False,
    "earlier_archives_unchanged": immutable,
    "unbundled_dependency": "Pinned Mathlib and its exact transitive package tree from lake-manifest.json",
    "actual_external_imports": external_imports,
    "excluded": ["dependency caches", "PNT/task compiled binaries", "credentials", "API/auth receipts", "git data", "unrelated missions"],
}
manifest_data = (json.dumps(manifest, ensure_ascii=False, indent=2) + "\n").encode("utf-8")
(PROJECT / "source-manifest.json").write_bytes(manifest_data)
(OUT / "source-manifest.json").write_bytes(manifest_data)
with zipfile.ZipFile(ARCHIVE, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as z:
    for name,data in sorted({**payload, "source-manifest.json": manifest_data}.items()):
        info = zipfile.ZipInfo(name, (2026, 10, 2, 0, 0, 0))
        info.compress_type = zipfile.ZIP_DEFLATED
        info.external_attr = 0o100644 << 16
        z.writestr(info, data, compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)

with zipfile.ZipFile(ARCHIVE) as z:
    names = z.namelist()
    assert len(names) == len(set(names))
    assert set(names) == set(payload) | {"source-manifest.json"}
    assert z.testzip() is None
    for row in files:
        data = z.read(row["path"])
        assert len(data) == row["bytes"] and sha(data) == row["sha256"], row["path"]
    assert z.read("source-manifest.json") == manifest_data

archive_data = ARCHIVE.read_bytes()
validation = {
    "status": "PASS", "archive": ARCHIVE.name, "archive_sha256": sha(archive_data),
    "archive_bytes": len(archive_data), "archive_members": len(payload) + 1,
    "source_manifest_sha256": sha(manifest_data), "all_member_sizes_and_sha256_match": True,
    "archive_crc_check": "PASS", "exact_allow_list_member_set": True,
    "all_reviewed_original_and_23_upstream_bytes_preserved": True,
    "apache_licenses_match_original_bytes": True,
    "formal_modules": 39, "lean_source_files_including_lakefile": len(lean_paths),
    "source_axiom_declarations": sorted(axiom_paths),
    "proof_hole_tokens_found_only_in_two_unimported_reference_statement_stubs": sorted(sorry_paths),
    "unchanged_Architect_metaprogram_sorry_detection_tokens": sorted(metaprogram_token_paths),
    "all_five_endpoint_audit_closures_exclude_reference_stubs": True,
    "actual_axiom_audit_declarations": build["required_declarations"],
    "actual_axioms": ["propext", "Classical.choice", "Quot.sound"],
    "build_exit_code": build["exit_code"], "final_build_command": build["command"],
    "build_reuse": "23 upstream modules were compiled in this independent project during the successful earlier sequential steps; no external PNT binary cache borrowed; only unfinished steps were resumed",
    "completed_earlier_sequential_steps": 31, "resumed_build_steps_including_final": 9,
    "first_parallel_attempt_exit_code": 1,
    "earlier_archives_unchanged": immutable,
    "network_API_gh_credential_operations": False,
    "platform_acceptance_claimed": False, "root_irrationality_open": True,
    "excluded_cache_binary_and_secret_member_check": "PASS",
}
validation_data = (json.dumps(validation, ensure_ascii=False, indent=2) + "\n").encode("utf-8")
(OUT / "package-validation.json").write_bytes(validation_data)
(OUT / "README.md").write_bytes(payload["README.md"])
sums = [(ARCHIVE.name, sha(archive_data)), ("source-manifest.json", sha(manifest_data)),
        ("package-validation.json", sha(validation_data)), ("README.md", sha(payload["README.md"]))]
(OUT / "SHA256SUMS.txt").write_text("".join(digest + "  " + name + "\n" for name,digest in sums), encoding="utf-8")
print(json.dumps({k: validation[k] for k in ["status", "archive", "archive_sha256", "archive_bytes", "archive_members", "build_exit_code", "actual_axiom_audit_declarations"]}))
