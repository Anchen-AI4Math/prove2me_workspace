"""Optional same-invocation memo for the frozen source34 readonly consumer.

Use ``with SourceCacheEpoch() as epoch:`` around readonly work, then consume its
result only after successful exit. Nothing installs this in a publisher. Each
distinct (g, results) pair runs the original full verifier once. Hits require
the same bounded argument projection and fixed evidence-file fingerprints;
returned copies cannot poison later hits. Exit hashes the complete typed input
closure. No persistence, Lean, API, certificate writes or cross-g reuse.
"""
from __future__ import annotations
from copy import deepcopy
import hashlib
import json
from pathlib import Path
from time import perf_counter
from unittest.mock import patch

import validate_namespace_context_providers as context
import formal_log_node_security_pins as security

SELF = Path(__file__).resolve()
CONTEXT_SHA = "fc398f10e2a4403aa1461569e0b9b3d1b6c6efbfad474c0f150d91fcbe8a7dd8"
GENERATOR_SHA = "5887e585b899b4a3c07499f55e4766a2694ad6c279ae70b2138e885b6e6dbead"
SECURITY_SHA = "8adf3e87f2dc8f7b219cfd55364e3cca391307ffacd46fc6e8d3b12773da7a4f"
ORIGINAL_SOURCE_CACHE = context.source_cache
MODULES = (
    "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame",
    "OAI.NumberTheory.PiExponent.Jets.JetGeometry",
    "OAI.NumberTheory.PiExponent.Jets.FormalJetDerivatives",
    "OAI.NumberTheory.PiExponent.Jets.FormalLogJet",
)


def bounded_projection(g, results):
    """Only the argument fields source_certificate/catalog_binding actually read.

    Requests/owner coordinates are small metadata. Expressions, plans, catalogs
    and snapshot JSONL are hashed as files, never recursively keyed as JSON.
    """
    if tuple(context.gen.MODULES) != MODULES or set(results) != set(MODULES):
        raise ValueError("Exact fixed source34 module domain differs")
    requests = [r for module in MODULES for r in results[module]["original"]]
    if len(requests) != 34:
        raise ValueError("Exact source34 request count differs")
    owners = []
    for request in requests:
        if not isinstance(request, dict) or any(not isinstance(k, str) or type(v) not in (str, int, bool, type(None))
                                                for k, v in request.items()):
            raise ValueError("Source34 request key contains non-metadata data")
        unit = g.units[request["command_unit"]]
        module = request["expected_module"]
        owners.append({"command_unit": request["command_unit"], "graph_names": unit["graph_names"],
            "start": unit["start"]["offset"], "end": unit["end"]["offset"],
            "source_sha256": g.modules[module]["source_sha256"],
            "facts_sha256": g.state["stage2"][module.replace(".", "/") + ".lean"]["facts_sha256"]})
    raw = json.dumps({"graph_sha": g.graph_sha, "requests": requests, "owners": owners},
                     sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")
    return hashlib.sha256(raw).hexdigest()


class SourceCacheEpoch:
    def __init__(self):
        self.original = ORIGINAL_SOURCE_CACHE
        self.dependencies = {name: getattr(context, name) for name in
                             ("source_certificate", "record", "rows", "read", "sha")}
        self.catalog_binding = context.gen.request_catalog_binding
        self.pairs = {}
        self.stats = {"calls": 0, "full_calls": 0, "hits": 0, "full_seconds": 0.0,
                      "copy_seconds": 0.0, "input_stability": False}
        self.entered = self.closed = False

    def _fixed_functions(self):
        for path, expected in [(Path(context.__file__), CONTEXT_SHA),
                               (Path(context.gen.__file__), GENERATOR_SHA),
                               (Path(security.__file__), SECURITY_SHA)]:
            if security.sha(path) != expected:
                raise ValueError("Frozen source34 implementation changed")
        if any(getattr(context, name) is not fn for name, fn in self.dependencies.items()) \
                or context.gen.request_catalog_binding is not self.catalog_binding:
            raise ValueError("Frozen source34 dependency function replaced in memory")

    def _inventory(self):
        cp = context.SOURCE_CERT.resolve(); c = security.read(cp)
        if (c.get("artifact_kind") != "context-source34-kernel-certificate"
                or c.get("row_count") != 34 or c.get("source_module_count") != 4
                or c.get("partial") is not True or c.get("platform_ready") is not False):
            raise ValueError("Only the fixed partial source34 evidence domain is supported")
        i = security.Inventory()
        i.pin(cp, security.sha(cp), "certificate")
        i.pin(SELF, security.sha(SELF))
        i.pin(Path(context.__file__), CONTEXT_SHA)
        i.pin(Path(context.gen.__file__), GENERATOR_SHA)
        i.pin(Path(security.__file__), SECURITY_SHA)
        i.pin(security.RUNTIME, c["preflight"]["data"]["runtime_sha256"])
        i.pin(Path(i.runtime["executable"]), i.runtime["executable_sha256"])
        for name, h in i.runtime["project_hashes"].items(): i.pin(security.ROOT / name, h)
        pins = i.finish()
        # Fingerprint direct evidence metadata/source/actual JSONL at every hit.
        # The entire OLean/source/facts/implementation closure is hashed at entry
        # and exit; all expected SHA values are part of this immutable domain.
        direct = [cp, context.gen.CATALOG, context.gen.SOURCE_SUBSET,
                  security.V / "platform-unit-plan-preview.json",
                  context.DEST / "source-snapshot/ContextSourceSnapshot.lean",
                  context.DEST / "source-snapshot/source-imports.json",
                  context.DEST / "source-snapshot/source.jsonl",
                  i.path(c["preflight"]["record"]),
                  i.path(c["preflight"]["data"]["log"]), security.RUNTIME]
        direct += [i.path(c["preflight"]["data"]["manifest"])]
        self.direct = {str(Path(p).resolve()): security.sha(p) for p in direct}
        self.logical_paths = {str(Path(p).absolute()): str(Path(p).resolve()) for p in direct}
        snapshot = (context.DEST / "source-snapshot/source.jsonl").resolve()
        stat = snapshot.stat()
        # rows() authenticates the actual exporter write window using mtime.
        # Byte hashes alone cannot detect touch-without-content-change.
        self.snapshot_metadata = {str(snapshot): (stat.st_size, stat.st_mtime_ns)}
        pinmap = {r["path"]: r["sha256"] for r in pins}
        if any(pinmap.get(path) != h for path, h in self.direct.items()):
            raise ValueError("Direct source34 inputs escape the complete typed closure")
        self.domain = hashlib.sha256(json.dumps(pins, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
        return pins

    def _direct_guard(self):
        for lexical, resolved in self.logical_paths.items():
            if str(Path(lexical).resolve()) != resolved:
                raise ValueError("Source34 evidence path resolution changed inside epoch")
        for path, expected in self.snapshot_metadata.items():
            stat = Path(path).stat()
            if (stat.st_size, stat.st_mtime_ns) != expected:
                raise ValueError("Source34 actual JSONL write-window metadata changed")
        for path, h in self.direct.items():
            if security.sha(path) != h:
                raise ValueError("Source34 fixed evidence changed inside epoch")

    def _fingerprint(self, g, results):
        self._fixed_functions()
        self._direct_guard()
        return self.domain, bounded_projection(g, results)

    def _copy(self, value):
        start = perf_counter(); copied = deepcopy(value)
        self.stats["copy_seconds"] += perf_counter() - start
        return copied

    def _run_original(self, g, results):
        return self.original(g, results)

    def _cached(self, g, results):
        if not self.entered or self.closed:
            raise ValueError("Source34 memo is only usable inside its explicit epoch")
        self.stats["calls"] += 1
        fingerprint = self._fingerprint(g, results)
        key = id(g), id(results)
        if key in self.pairs:
            row = self.pairs[key]
            if row["g"] is not g or row["results"] is not results or row["fingerprint"] != fingerprint:
                raise ValueError("Source34 arguments mutated inside epoch")
            self.stats["hits"] += 1
            return self._copy(row["value"])
        start = perf_counter(); value = self._run_original(g, results)
        self.stats["full_seconds"] += perf_counter() - start
        self.stats["full_calls"] += 1
        if self._fingerprint(g, results) != fingerprint:
            raise ValueError("Source34 input changed during the full original verifier")
        # Strong references prohibit object-id reuse. Store a private copy, and
        # let the first caller receive its original verifier result unchanged.
        self.pairs[key] = {"g": g, "results": results, "fingerprint": fingerprint, "value": self._copy(value)}
        return value

    def __enter__(self):
        if self.entered or context.source_cache is not self.original:
            raise ValueError("Nested/reused/replaced source34 epochs are unsupported")
        self.started = perf_counter(); self._fixed_functions(); self.pins = self._inventory()
        self.patch = patch.object(context, "source_cache", self._cached)
        self.patch.__enter__(); self.entered = True
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        try:
            self._fixed_functions()
            self._direct_guard()
            for row in self.pairs.values():
                if bounded_projection(row["g"], row["results"]) != row["fingerprint"][1]:
                    raise ValueError("Source34 mutable owner/request inputs changed before epoch exit")
            security.assert_security_pins(self.pins)
            self.stats["input_stability"] = True
            self.stats["typed_input_count"] = len(self.pins)
        finally:
            self.closed = True
            self.patch.__exit__(exc_type, exc_value, traceback)
            self.stats["epoch_seconds"] = perf_counter() - self.started
            self.pairs.clear()
        return False
