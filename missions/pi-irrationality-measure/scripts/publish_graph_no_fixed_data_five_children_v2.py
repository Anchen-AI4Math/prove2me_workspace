"""Publication-v3 entrypoint for the source-helper NoFixedData graph sketch.

Only --advance may contact the platform, reserved for the root agent. It
reuses the already reviewed five-child durable HTTP/graph driver with this
successor's new strict certificate, solution, payloads, and isolated DEST.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
from unittest.mock import patch

import prepare_graph_no_fixed_data_five_children_v2_publication as offline
import publish_graph_no_fixed_data_five_children as prior


SELF = Path(__file__).resolve()
DEST = offline.DEST


def preparation():
    prep, problem, descriptor, payloads, pins, cert = offline.check()
    offline.need(offline.sha(SELF) == pins["online_wrapper_sha256"] and
                 offline.sha(offline.API) == pins["api_client_sha256"] and
                 offline.sha(Path(prior.__file__)) == pins["reused_durable_graph_driver_sha256"],
                 "Successor online/API driver differs from frozen v3 preparation")
    # The reused driver intentionally reads the original unchanged five
    # theorem comparators, NoFixedData comparator, and root graph names.
    offline.need(prior.STAGE == offline.stage.old.STAGE and
                 prior.stage.ARITH == offline.stage.old.ARITH and
                 prior.stage.NFD_FILE == offline.stage.old.NFD_FILE and
                 (prior.STAGE / prior.stage.NFD_FILE).read_bytes() == offline.NFD_WIRE.read_bytes(),
                 "Durable graph driver no longer points to exact original child wires")
    return prep, problem, descriptor, payloads, pins, cert


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--prepare-only", action="store_true")
    mode.add_argument("--check-only", action="store_true")
    mode.add_argument("--advance", action="store_true")
    args = parser.parse_args()
    prep, problem, descriptor, payloads, pins, cert = preparation()
    online = DEST / "online-preparation-driver.json"
    if args.prepare_only:
        offline.exact(online, offline.encode(pins))
        result = {"prepared": True, "network_used": False,
                  "NoFixedData_theorem_id": pins["NoFixedData_theorem_id"],
                  "Open_sketch": True, "closed_proof": False}
    elif args.check_only:
        offline.need(online.is_file() and online.read_bytes() == offline.encode(pins),
                     "Frozen successor online preparation differs")
        result = {"checked": True, "network_used": False,
                  "Open_sketch": True, "closed_proof": False}
    else:
        offline.need(online.is_file() and online.read_bytes() == offline.encode(pins),
                     "Reviewed successor online preparation differs")
        with patch.multiple(prior, offline=offline, DEST=DEST, SELF=SELF):
            result = prior.advance()
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
