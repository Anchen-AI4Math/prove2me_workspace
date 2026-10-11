"""One baseline-first f2 readonly benchmark; no Lean, API or frozen writes."""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
from time import perf_counter
from unittest.mock import patch
import formal_log_source_cache_epoch as memo
import validate_formal_log_successor_node as checker

TASK = checker.TASK
CERT = TASK / "verification/flp3/f2/successor-node-validation.json"
CERT_SHA = "0ea655a3c17277cffa04478a11f4f9a914dfd5d8278d3fdfac2b9e56f3eef6c9"
CHECKER_SHA = "20f761f0d169c7af296faea379bb7547909abd56f79d0bdba03a207d7617bfb4"
OUTPUT = TASK / "verification/formal-log-source-cache-epoch-benchmark.json"


def exact_certificate(view, raw):
    encoded = (json.dumps(view["certificate"]["data"], indent=2, ensure_ascii=False) + "\n").encode("utf-8")
    if encoded != raw or view["certificate"]["sha256"] != CERT_SHA or CERT.read_bytes() != raw:
        raise ValueError("Full readonly result differs byte-for-byte from frozen f2 certificate")
    return hashlib.sha256(encoded).hexdigest()


def main():
    raw = CERT.read_bytes()
    if hashlib.sha256(raw).hexdigest() != CERT_SHA or memo.security.sha(Path(checker.__file__)) != CHECKER_SHA:
        raise ValueError("Frozen f2 checker/certificate differs")
    baseline = {"calls": 0, "full_calls": 0, "hits": 0, "full_seconds": 0.0}
    def counted(g, results):
        baseline["calls"] += 1; baseline["full_calls"] += 1
        start = perf_counter()
        try: return memo.ORIGINAL_SOURCE_CACHE(g, results)
        finally: baseline["full_seconds"] += perf_counter() - start
    print(json.dumps({"phase": "baseline", "Lean_started": False, "network_used": False}), flush=True)
    start = perf_counter()
    with patch.object(memo.context, "source_cache", counted):
        original = checker.validate_formal_successor_node("f2")
    baseline["elapsed_seconds"] = perf_counter() - start
    baseline["certificate_sha256"] = exact_certificate(original, raw)
    print(json.dumps({"phase": "baseline-complete", **baseline}), flush=True)
    print(json.dumps({"phase": "memoized", "same_g_only": True}), flush=True)
    start = perf_counter()
    with memo.SourceCacheEpoch() as epoch:
        cached = checker.validate_formal_successor_node("f2")
    candidate = dict(epoch.stats)
    candidate["elapsed_seconds"] = perf_counter() - start
    candidate["certificate_sha256"] = exact_certificate(cached, raw)
    if cached != original:
        raise ValueError("Memoized entire readonly view differs from baseline")
    if baseline["calls"] != 6 or candidate["calls"] != 6 or candidate["full_calls"] != 3 or candidate["hits"] != 3:
        raise ValueError("Audited same-object call-count prediction differs")
    record = {"schema_version": 1, "artifact_kind": "formal-log-source34-cache-readonly-f2-benchmark",
        "network_used": False, "Lean_started": False, "publisher_switched": False,
        "helper_sha256": memo.security.sha(Path(memo.__file__)),
        "benchmark_sha256": memo.security.sha(Path(__file__)),
        "baseline": baseline, "memoized": candidate, "exact_entire_view_equal": True,
        "certificate_bytes_equal_to_frozen_f2": True, "input_stability": candidate["input_stability"],
        "saved_seconds": baseline["elapsed_seconds"] - candidate["elapsed_seconds"],
        "observed_speedup_ratio": baseline["elapsed_seconds"] / candidate["elapsed_seconds"],
        "trial_caveat": "Single sequential baseline-first trial; cached leg has warmer OS/Python caches and shared-machine load may differ. Call counts and certificate byte equality are independently asserted."}
    data = (json.dumps(record, indent=2, ensure_ascii=False, sort_keys=True) + "\n").encode("utf-8")
    if OUTPUT.exists() and OUTPUT.read_bytes() != data:
        raise ValueError("Benchmark output exists; preserve it rather than overwrite")
    OUTPUT.write_bytes(data)
    print(json.dumps(record, sort_keys=True), flush=True)


if __name__ == "__main__": main()
