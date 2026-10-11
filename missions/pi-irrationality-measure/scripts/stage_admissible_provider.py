"""Pure Python staging adapter for the complete AdmissibleParameters provider.

Frozen plans, source files, exporters, and existing provider outputs are read
only. The original accepted byte-edit engine is reused in an isolated root.
No Lean process or platform request is made by this adapter.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path

import generate_namespace_context_providers as readonly
import generate_platform_provider_bundles as producer
import generate_shared_source_snapshot as base
import generate_structural_kernel_source_snapshot as source_gen
import prepare_structural_provider_snapshot as snapshot
import validate_structural_provider_bundle as structural
import validate_provider_bundle as ordinary

TASK = Path(__file__).resolve().parents[1]
DEST = TASK / "verification/ap2"
BATCH = "s"
ADMISSIBLE = "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters"
WEIGHT = "OAI.NumberTheory.PiExponent.Approximation.WeightSeparation"
MODULES = (WEIGHT, ADMISSIBLE)


def configure():
    """Only process-local staging roots change; frozen implementations stay pinned."""
    producer.OUTPUT = DEST
    snapshot.DEFAULT_PROVIDER_ROOT = DEST
    snapshot.BATCH = BATCH
    structural.PROVIDER_ROOT = DEST
    structural.BATCH = BATCH
    old_resolve = ordinary.resolve_provider_root
    ordinary.resolve_provider_root = lambda value=None: (
        DEST.resolve() if Path(value).resolve() == DEST.resolve() else old_resolve(value))
    # A new root still has the exact same frozen, freshly checked 875-plan basis.
    old_basis = ordinary.check_complete_provider_basis
    ordinary.check_complete_provider_basis = lambda root: old_basis(ordinary.COMPLETE_PREVIEW.resolve())


def generate():
    configure()
    if (DEST / "generation-report.json").is_file():
        raise ValueError("Stage already exists; use --check-only instead of overwriting")
    g = readonly.readonly_generator()
    g.input_hashes[base.task_relative(Path(__file__))] = base.sha_file(Path(__file__))
    base.write_json(DEST / "live-import-inventory.json", g.imports)
    reports = []
    for module in MODULES:
        risks = g.module_name_risk(module)
        if risks:
            raise ValueError("Unsupported provider source boundary: " + json.dumps(risks))
        reports.append(g.stage_bundle(module, BATCH))
    result = structural.structural_check(ADMISSIBLE)
    provider = structural.provider_stage(result, write=True)
    staged = snapshot.stage(DEST, ADMISSIBLE, require_provider=False)
    report = dict(schema_version=1, source_commit=ordinary.COMMIT,
        provider_root=base.task_relative(DEST), batch=BATCH,
        frozen_all_shared_plan_unchanged=True, reports=reports,
        structure_row_count=49, provider_ci_count=len(g.snapshot_requests(ADMISSIBLE, False)),
        weight_ci_count=len(g.snapshot_requests(WEIGHT, False)),
        provider_command=("python scripts/preflight_staged_module.py " + provider["source"]
            + " --root " + provider["root"] + " --imports-manifest "
            + provider["manifest"].relative_to(TASK / "verification").as_posix()
            + " --emit-olean --timeout-seconds 300"),
        generated_stage=staged, lean_started=False, api_used=False, validated=False)
    base.write_json(DEST / "generation-report.json", report)
    return report


def check():
    configure()
    result = structural.structural_check(ADMISSIBLE)
    snapshot.check(DEST, ADMISSIBLE, require_provider=False)
    report = json.loads((DEST / "generation-report.json").read_bytes())
    paths = [str(p.resolve()) for p in DEST.rglob("*") if p.is_file()]
    if any(len(p) >= 240 for p in paths):
        raise ValueError("Staged path exceeds strict 239 character budget")
    return dict(checked=True, rows=result["family"]["expected_rows"],
        provider_ci_count=report["provider_ci_count"], max_path_length=max(map(len, paths)),
        source_certificate_sha256=base.sha_file(structural.SOURCE_CERTIFICATE),
        lean_started=False, api_used=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--stage", action="store_true")
    mode.add_argument("--check-only", action="store_true")
    mode.add_argument("--bind-provider", action="store_true")
    args = parser.parse_args()
    configure()
    if args.stage:
        result = generate()
    elif args.bind_provider:
        result = snapshot.stage(DEST, ADMISSIBLE, require_provider=True)
    else:
        result = check()
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
