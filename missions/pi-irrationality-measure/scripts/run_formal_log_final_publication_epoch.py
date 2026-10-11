"""Bounded explicit f4 API driver: one complete review, then frozen advances."""
import json
import time
from pathlib import Path
import publish_formal_log_final_node as publisher


def main():
    result = publisher.prepare(
        publisher.DEFAULT_STAGE,
        publisher.TASK / "platform/formal-log-node-metadata/formalLog_packets_surjective_iff_truncated.json",
        write=False,
    )
    state_path = result[1] / "publication.json"
    for cycle in range(1, 9):
        try:
            publisher.advance(*result)
        except OSError as error:
            state = json.loads(state_path.read_text(encoding="utf-8")) if state_path.exists() else {}
            uncertain = (state.get("publication_intent") and not state.get("job_id")) or (
                state.get("verification_intent") and not state.get("submission_id")
            )
            print(json.dumps({"cycle": cycle, "network_error": str(error), "uncertain_post": bool(uncertain)}), flush=True)
            if uncertain:
                raise
        state = json.loads(state_path.read_text(encoding="utf-8"))
        print(json.dumps({"cycle": cycle, **{key: state.get(key) for key in (
            "job_id", "theorem_id", "submission_id", "accepted", "confirmed_proved"
        )}}, ensure_ascii=True), flush=True)
        if state.get("accepted") is True and state.get("confirmed_proved") is True:
            return
        if cycle < 8:
            time.sleep(20)
    raise SystemExit("Bounded publication epoch ended; continue only from saved known IDs")


if __name__ == "__main__":
    main()
