"""Refresh current formalization navigation while pruning build caches.

Only the current mission's new formalization/public-proof trees are walked.
No files are moved or removed, and no credentials are read.
"""
from __future__ import annotations

import json
import os
from pathlib import Path

TASK = Path(__file__).resolve().parents[1]
WORKSPACE = TASK.parents[1]
# Current short Lean projects use b as buildDir; its IR JSON is compiled output.
PRUNE = {".lake", "b", ".rt", ".git", "__pycache__", ".agents", ".codex"}
EXTENSIONS = {".lean", ".json", ".jsonl", ".md", ".log", ".txt", ".py", ".ps1", ".toml", ".zip", ".yaml", ".yml"}


def source_patterns(folder):
    result = []
    if not folder.exists():
        return result
    for directory, children, names in os.walk(folder, followlinks=False):
        children[:] = [name for name in children if name not in PRUNE and
                       not (Path(directory) / name).is_junction() and
                       not (Path(directory) / name).is_symlink()]
        relative = Path(directory).relative_to(WORKSPACE).as_posix()
        suffixes = {Path(name).suffix for name in names} & EXTENSIONS
        result.extend(f"{relative}/*{suffix}" for suffix in sorted(suffixes))
        result.extend(f"{relative}/{name}" for name in names if name in {"lean-toolchain", "LICENSE", "SHA256SUMS"})
    return result


def main():
    path = TASK / "scope.json"
    scope = json.loads(path.read_text(encoding="utf-8"))
    unsafe = {"missions/zeta9/formalization/**/*",
              "missions/zeta9/verification/formalization-*/**/*",
              "missions/zeta9/publication/2026-10-02/**/*"}
    old = scope["sources"]
    # Retain earlier publication receipts and frozen finite reproductions.
    publication = "missions/zeta9/publication/2026-10-02"
    additions = [f"{publication}/*", f"{publication}/api-docs/*",
                 f"{publication}/platform-before/*", f"{publication}/platform-after/*",
                 f"{publication}/reproduction-*/**/*",
                 "missions/zeta9/scripts/refresh_formal_scope_2026_10_02.py"]
    for name in ("register_formal_batch_2026_10_02.py", "publish_coefficient_2026_10_02.py",
                 "publish_pnt_2026_10_02.py", "refresh_formal_mission_2026_10_02.py",
                 "inspect_platform_progress_2026_10_03.py", "upload_advanced_proofs_2026_10_03.py",
                 "publish_matrix_proofs_new_mission_2026_10_07.py",
                 "audit_current_public_proposal_2026_10_07.py",
                 "audit_new_public_progress_2026_10_07.py",
                 "publish_numerator_pf_new_mission_2026_10_07.py",
                 "verify_analytic_uniform_author_2026_10_07.py",
                 "prepare_analytic_phase_publication_2026_10_07.py",
                 "publish_analytic_phase_new_mission_2026_10_07.py",
                 "fetch_api_docs_2026_10_04.py",
                 "register_coefficient_map_2026_10_03.py", "install_coefficient_map_batch_2026_10_03.py",
                 "publish_coefficient_map_2026_10_03.py", "publish_coefficient_map_jet_2026_10_03.py",
                 "publish_coefficient_map_injectivity_2026_10_04.py", "publish_coefficient_map_partial_fractions_2026_10_04.py",
                 "publish_coefficient_map_reflection_2026_10_04.py",
                 "publish_coefficient_map_finite_sum_2026_10_04.py",
                 "publish_coefficient_map_summation_2026_10_04.py",
                 "publish_coefficient_map_shift_degree_2026_10_04.py",
                 "publish_coefficient_map_aggregate_2026_10_04.py",
                 "publish_coefficient_map_telescoper_2026_10_04.py",
                 "publish_coefficient_map_kernel_bridge_2026_10_04.py",
                 "publish_coefficient_map_connection_2026_10_04.py",
                 "publish_coefficient_map_matrix_2026_10_04.py",
                 "audit_new_mission_2026_10_07.py", "preflight_new_public_mission_2026_10_07.py",
                 "propose_public_mission_2026_10_07.py",
                 "freeze_coefficient_map_finite_sum_2026_10_03.py", "freeze_coefficient_map_shift_degree_2026_10_04.py"):
        script = TASK / "scripts" / name
        if script.is_file():
            additions.append(script.relative_to(WORKSPACE).as_posix())
    additions += source_patterns(TASK / "formalization")
    additions += source_patterns(TASK / "publication/2026-10-02/formal-proofs")
    additions += source_patterns(TASK / "publication/2026-10-02/advanced-proofs")
    additions += source_patterns(TASK / "publication/2026-10-07/new-public-mission")
    for folder in sorted((TASK / "verification").glob("formalization-*")):
        additions += source_patterns(folder)
    additions += source_patterns(TASK / "verification/coefficient-map-connection-offline-precheck-2026-10-04")
    additions += source_patterns(TASK / "verification/coefficient-map-parameter-shift-offline-precheck-2026-10-04")
    for name in ("coefficient-map-formal-transport-numerators-offline-2026-10-04",
                 "coefficient-map-local-transport-offline-2026-10-04"):
        additions += source_patterns(TASK / "verification" / name)
    for name in ("coefficient-map-numerator-pf-native-2026-10-04.md",
                 "analytic-moment-explicit-bound-2026-10-07.md",
                 "analytic-weighted-uniform-source-delta-2026-10-07.md",
                 "coefficient-map-transport-numerators-offline-preparation-2026-10-04.md",
                 "coefficient-map-local-transport-design-2026-10-04.md",
                 "local-transport-static-review-2026-10-04.md"):
        record = TASK / "research" / name
        if record.is_file():
            additions.append(record.relative_to(WORKSPACE).as_posix())
    for name in ("connection-helper-scope-check-2026-10-04.log",
                 "connection-helper-scope-check-2026-10-04-exit.txt"):
        record = TASK / "verification" / name
        if record.is_file():
            additions.append(record.relative_to(WORKSPACE).as_posix())
    # Replace our generated directory patterns on each run, keeping stable
    # shared-module registrations and all other task research unchanged.
    prefixes = ("missions/zeta9/formalization/", "missions/zeta9/verification/formalization-",
                "missions/zeta9/publication/2026-10-02/formal-proofs/")
    prefixes += ("missions/zeta9/publication/2026-10-02/advanced-proofs/",)
    prefixes += ("missions/zeta9/publication/2026-10-07/new-public-mission/",)
    prefixes += ("missions/zeta9/verification/coefficient-map-connection-offline-precheck-2026-10-04/",)
    prefixes += ("missions/zeta9/verification/coefficient-map-parameter-shift-offline-precheck-2026-10-04/",)
    keep = [p for p in old if p not in unsafe and not p.startswith(prefixes)]
    scope["sources"] = list(dict.fromkeys(keep + additions))
    path.write_text(json.dumps(scope, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print("Formalization navigation refreshed; .lake, b, .rt, junctions and compiled artifacts excluded. No files moved.")


if __name__ == "__main__":
    main()
