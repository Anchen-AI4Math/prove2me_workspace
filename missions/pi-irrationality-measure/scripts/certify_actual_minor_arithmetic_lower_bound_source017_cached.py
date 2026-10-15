"""Run the unchanged AP17 strict consumer with one full child-certificate replay.

The AP17 stage and consumer both call the same expensive, pure AP17 private-mirror
validator. This runner memoizes its complete first result within this process;
the original AP17 validator and certificate serialization remain unchanged.
"""
from __future__ import annotations

import argparse
import copy
import json
from pathlib import Path

import certify_actual_minor_arithmetic_lower_bound_source017_node as node
import certify_selected_minor_lower_child_mirror_probe_v5 as child


def validate_once() -> tuple[dict, int, int]:
    actual_validate = child.validate
    saved: dict | None = None
    full_replays = 0
    cache_hits = 0

    def child_once() -> dict:
        nonlocal saved, full_replays, cache_hits
        if saved is None:
            result = actual_validate()
            path = node.stage.MIRROR_STAGE / node.stage.mirror.CERTIFICATE
            node.need(node.stage.encode(result) == path.read_bytes(),
                      'First complete private-mirror replay differs from its certificate')
            saved = copy.deepcopy(result)
            full_replays += 1
        else:
            cache_hits += 1
        return copy.deepcopy(saved)

    child.validate = child_once
    try:
        report = node.validate()
    finally:
        child.validate = actual_validate
    node.need(full_replays == 1 and cache_hits >= 1,
              'AP17 memoization did not reuse exactly one complete child replay')
    return report, full_replays, cache_hits


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument('--certify-existing', action='store_true')
    modes.add_argument('--check-only', action='store_true')
    args = parser.parse_args()

    report, full_replays, cache_hits = validate_once()
    path: Path = node.STAGE / node.stage.CERTIFICATE
    raw = node.stage.encode(report)
    if path.exists():
        node.need(path.read_bytes() == raw, 'Existing immutable AP17 certificate differs')
    elif args.certify_existing:
        path.write_bytes(raw)
    else:
        node.need(False, 'Check-only requires an existing actual AP17 certificate')
    print(json.dumps({'certificate': node.rel(path),
                      'certificate_sha256': node.sha(path),
                      'validated': report['validated'],
                      'Std3_only': report['Std3_only'],
                      'child_full_replays': full_replays,
                      'child_cache_hits': cache_hits,
                      'Lean_started': False, 'API_used': False}, indent=2))


if __name__ == '__main__':
    main()
