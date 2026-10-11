"""Use the frozen n1 online driver for the separately certified n2z payload."""
from pathlib import Path
from unittest.mock import patch
import prepare_successive_approximations_n2z_publication as offline
import publish_successive_approximations_n1 as bridge

SELF = Path(__file__).resolve()
BRIDGE_SHA = "0d888c8840d6683dfab21af01f4fd687a64c99b1044270c3f583c1f4aaec29ff"

def preparation():
    # The frozen n2z producer returns metadata directly, without n1's extra
    # encoded-metadata tuple element. Keep its own five-field contract intact.
    offline.check()
    manifest, _, metadata, payloads, pins = offline.artifacts()
    bridge.saved_gate(manifest)
    pins = dict(pins)
    pins["api_client_sha256"] = offline.sha(offline.ROOT / "scripts/p2m_api.py")
    pins["online_wrapper_sha256"] = offline.sha(SELF)
    pins["offline_preparation_sha256"] = offline.sha(offline.DEST / "preparation.json")
    pins["online_bridge_sha256"] = BRIDGE_SHA
    return manifest, metadata, payloads, pins

if __name__ == "__main__":
    if offline.sha(Path(bridge.__file__)) != BRIDGE_SHA:
        raise ValueError("Frozen first-search and at-most-once publisher bridge changed")
    with patch.object(bridge, "offline", offline), patch.object(bridge, "SELF", SELF), \
         patch.object(bridge, "TASK", offline.TASK), patch.object(bridge, "ROOT", offline.ROOT), \
         patch.object(bridge, "PUB", offline.DEST), patch.object(bridge, "preparation", preparation):
        bridge.main()
