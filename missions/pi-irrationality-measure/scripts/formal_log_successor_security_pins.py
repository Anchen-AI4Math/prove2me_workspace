"""Typed successor evidence inventory; kernel/AST JSON remains opaque bytes.

Call only after one complete readonly successor review. Per-request guards hash
this closed inventory without replaying kernel checkers or starting Lean/API.
"""
from pathlib import Path
import formal_log_node_security_pins as frozen

TASK, ROOT, V, TOOLCHAIN = frozen.TASK, frozen.ROOT, frozen.V, frozen.TOOLCHAIN
SELF = Path(__file__).resolve()
EXTERNAL_API = {"Meta/Eqns.lean", "Util/FoldConsts.lean", "Environment.lean", "Util/CollectAxioms.lean"}
sha, read, fail = frozen.sha, frozen.read, frozen.fail


def external_path(path):
    p = Path(path).resolve()
    allowed = {(TOOLCHAIN / "src/lean/Lean" / s).resolve() for s in EXTERNAL_API}
    fail(p not in allowed or not p.is_file(), "Outside four fixed Lean API source files")
    return p


class Inventory(frozen.Inventory):
    def external(self, rows):
        fail(not isinstance(rows, list) or len(rows) != 4, "Exact four Lean API pins required")
        fail({r.get("lean_source_suffix") for r in rows} != EXTERNAL_API, "API source suffix domain differs")
        for r in rows:
            fail(set(r) != {"path", "sha256", "toolchain_root", "lean_source_suffix"}, "Typed external API schema differs")
            p = external_path(r["path"])
            fail(Path(r["toolchain_root"]).resolve() != TOOLCHAIN
                 or p != (TOOLCHAIN / "src/lean/Lean" / r["lean_source_suffix"]).resolve(), "Typed API path/toolchain binding differs")
            h = frozen.digest(r["sha256"])
            fail(sha(p) != h or str(p) in self.pins and self.pins[str(p)] != h, "Lean API source SHA changed")
            self.pins[str(p)] = h

    def certificate(self, d):
        super().certificate(d)
        for k in ["parent_node_certificate", "source_manifest", "snapshot_manifest"]:
            self.ref(d, k, role="certificate" if k == "parent_node_certificate" else "manifest")
        for k in ["source_preparation", "snapshot", "child_type_output", "child_proof_references"]:
            self.ref(d, k, role="child-preparation" if k == "source_preparation" else None)
        for child in d.get("child_certificates", []):
            self.ref(child, "certificate", role="certificate"); self.ref(child, "output_olean")
        if "auxiliary_ci_certificate" in d:
            self.ref(d["auxiliary_ci_certificate"], "path", "sha256", role="certificate")
        if "baseline_checker" in d: self.ref(d["baseline_checker"], "path", "sha256")
        if "external_lean_api_sources" in d: self.external(d["external_lean_api_sources"])
        if "retained_original_preparation" in d: self.pinmap(d["retained_original_preparation"])
        if "preparation" in d: self.ref(d, "preparation", role="aux-preparation")
        # Each explicit output map is relative to its certificate's exact stage.
        # No recursive traversal of expressions, catalogs or source facts occurs.

    def certificate_at(self, path, d):
        self.certificate(d)
        stage = path.parent
        for name, h in d.get("output_json_sha256", {}).items():
            self.pin(self.path(name) if "/" in name else stage / name, h)
        kind = d.get("artifact_kind")
        if kind in {"formal-log-proof-node-kernel-certificate", "formal-log-successor-proof-node-kernel-certificate", "formal-log-f3-complete-proof-node-kernel-certificate"}:
            m = read(stage / "manifest.json")
            for name, h in m["outputs_sha256"].items(): self.pin(stage / name, h)
            names = ["c1.json", "c2.json", "c3.json", "c4.json", "certified-inputs.json"]
            if stage.name == "f1": names += ["c4b.json"]
            for name in names: self.pin(stage / name, sha(stage / name), "manifest")
            self.pin(stage / "preparation.json", sha(stage / "preparation.json"), "preparation")
            if stage.name == "f1": self.pin(stage / "refs-repair-preparation.json", sha(stage / "refs-repair-preparation.json"), "repair")
        elif kind == "formal-log-proved-child-kernel-certificate":
            self.ref(d, "source_preparation", role="child-preparation")
            p = stage / "child-snapshot-preparation.json"
            self.pin(p, sha(p), "child-preparation")

    def child_preparation(self, d):
        for k in ["parent_node_certificate", "manifest"]:
            self.ref(d, k, role="certificate" if k == "parent_node_certificate" else "manifest")
        for k in ["certified_solution", "source", "output", "child_olean"]: self.ref(d, k)

    def aux_preparation(self, d):
        self.maps(d); self.external(d["external_lean_api_sources"])
        self.pinmap(d["retained_original_preparation"])
        for r in d["files"].values():
            self.ref(r, "source"); self.ref(r, "manifest", role="manifest")

    def finish(self):
        handlers = {"preflight": self.preflight, "manifest": self.manifest, "preparation": self.preparation,
                    "repair": self.repair, "fast": self.fast, "child-preparation": self.child_preparation,
                    "aux-preparation": self.aux_preparation}
        while self.queue:
            p, role = self.queue.pop(); identity = (str(p), role)
            if identity in self.seen: continue
            self.seen.add(identity)
            if role == "certificate": self.certificate_at(p, read(p))
            else:
                fail(role not in handlers, "Unknown typed successor evidence role")
                handlers[role](read(p))
        return [{"path": p, "sha256": h} for p, h in sorted(self.pins.items())]


def reviewed_security_pins(evidence):
    stage = Path(evidence["stage"]).resolve()
    fail(evidence.get("validated") is not True or stage not in [(V / "flp3" / n).resolve() for n in ["f2", "f3"]], "Only reviewed f2/f3 accepted")
    i = Inventory(); c = evidence["certificate"]; cp = i.path(c["path"])
    fail(read(cp) != c["data"], "Readonly certificate view changed")
    i.pin(cp, c["sha256"], "certificate"); i.pin(SELF, sha(SELF)); i.pin(Path(frozen.__file__), sha(Path(frozen.__file__)))
    i.pin(frozen.RUNTIME, evidence["manifest_data"]["runtime_sha256"])
    i.pin(Path(i.runtime["executable"]), i.runtime["executable_sha256"])
    for p, h in i.runtime["project_hashes"].items(): i.pin(ROOT / p, h)
    return i.finish()


def assert_security_pins(pins):
    _, roots = frozen.runtime_roots(); fail(not isinstance(pins, list) or not pins, "Empty successor security inventory")
    previous = None
    for r in pins:
        fail(not isinstance(r, dict) or set(r) != {"path", "sha256"}, "Typed pin schema differs")
        p = Path(r["path"]).resolve()
        if p in {(TOOLCHAIN / "src/lean/Lean" / s).resolve() for s in EXTERNAL_API}: p = external_path(p)
        else: p = frozen.confined(p, roots)
        fail(str(p) != r["path"] or previous is not None and previous >= r["path"], "Pins must be unique sorted resolved paths")
        previous = r["path"]
        fail(sha(p) != frozen.digest(r["sha256"]), "Reviewed successor input changed: " + str(p))
