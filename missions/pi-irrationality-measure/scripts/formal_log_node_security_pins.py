"""Typed file inventory after one full readonly f1 kernel review; no Lean/API.

Only explicitly assigned evidence roles enter the JSON workqueue. Hash maps,
AST/plans/catalogs/kernel JSON and source/JSONL inputs are always opaque bytes.
"""
import hashlib
import json
from pathlib import Path
import preflight_staged_module as runner

TASK = Path(__file__).resolve().parents[1]
ROOT, V, SELF = TASK.parents[1], TASK / "verification", Path(__file__).resolve()
F1, RUNTIME = V / "flp3/f1", V / "lean-runtime.json"
TOOLCHAIN = Path(r"C:\Users\anche\.elan\toolchains\leanprover--lean4---v4.33.1").resolve()
PROJECT_FILES = {"lakefile.lean", "lake-manifest.json", "lean-toolchain"}
TASK_REAL, ROOT_REAL = TASK.resolve(), ROOT.resolve()


def fail(condition, message):
    if condition: raise ValueError(message)


def digest(h):
    fail(not isinstance(h,str) or len(h)!=64 or any(c not in "0123456789abcdef" for c in h),"Invalid typed SHA256")
    return h


def sha(p):
    h=hashlib.sha256()
    with Path(p).open("rb") as f:
        for b in iter(lambda:f.read(1048576),b""):h.update(b)
    return h.hexdigest()


def read(p):return json.loads(Path(p).read_text(encoding="utf-8"))


def runtime_roots():
    r=read(RUNTIME)
    fail(Path(r["executable"]).resolve()!=TOOLCHAIN/"bin/lean.exe" or set(r["project_hashes"])!=PROJECT_FILES,"Fixed runtime changed")
    roots=[p.resolve() for p in runner.effective_search_path(r["environment"]["LEAN_PATH"])]
    for p in roots:
        fail(not p.is_relative_to(TASK_REAL) and not p.is_relative_to(ROOT_REAL/".lake") and p!=TOOLCHAIN/"lib/lean","OLean root outside fixed scope")
    return r,roots


def confined(path,roots):
    p=Path(path).resolve()
    fail(not p.is_file(),"Missing reviewed file: "+str(p))
    if p.is_relative_to(TASK_REAL):
        fail(any(x in {".aws",".git",".codex",".agents"} for x in p.relative_to(TASK_REAL).parts),"Internal/authentication path outside scope")
        return p
    if p.parent==ROOT_REAL and p.name in PROJECT_FILES:return p
    if p==TOOLCHAIN/"bin/lean.exe":return p
    if p.suffix==".olean" and any(p.is_relative_to(r) for r in roots):return p
    raise ValueError("File outside reviewed fixed scope: "+str(p))


class Inventory:
    def __init__(self):
        self.runtime,self.roots=runtime_roots()
        self.pins,self.queue,self.seen,self.deps_seen={},[],set(),set()
    def path(self,s,verification=False,scripts=False):
        fail(not isinstance(s,str) or not s,"Missing typed path")
        p=Path(s)
        if not p.is_absolute():p=(V if verification else TASK/"scripts" if scripts else ROOT if p.parts[0]=="missions" else TASK)/p
        return confined(p,self.roots)
    def pin(self,p,h,role=None):
        p,h=confined(p,self.roots),digest(h);key=str(p)
        if key in self.pins:fail(self.pins[key]!=h,"Conflicting pin: "+key)
        else:
            fail(sha(p)!=h,"Reviewed file changed: "+key);self.pins[key]=h
        if role is not None:self.queue.append((p,role))
    def ref(self,d,k,h=None,role=None,verification=False):
        h=h or k+"_sha256"
        if isinstance(d.get(k),str) and d.get(h) is not None:self.pin(self.path(d[k],verification),d[h],role)
    def pinmap(self,d,scripts=False):
        fail(not isinstance(d,dict),"Pin map schema differs")
        for p,h in d.items():self.pin(self.path(p,scripts=scripts and Path(p).name==p),h)
    def maps(self,d):
        for k in ["input_hashes","manifest_inputs","implementation_hashes","implementation_sha256"]:
            if k in d:self.pinmap(d[k],k=="implementation_sha256")
    def deps(self,rows):
        for d in rows:
            h=d.get("sha256_before",d.get("sha256"))
            if d.get("sha256_after") is not None:fail(d["sha256_after"]!=h or d["stable_during_compile"] is not True,"OLean instability")
            identity=(d["module"],d["path"],d["resolved_search_root"],h)
            if identity in self.deps_seen:continue
            self.deps_seen.add(identity);p=self.path(d["path"]);root=Path(d["resolved_search_root"]).resolve();leaf=Path(*d["module"].split("."))
            fail(root not in self.roots or p!=(root/leaf).with_suffix(".olean").resolve(),"OLean module/path/root mismatch")
            first=next(((r/leaf).with_suffix(".olean").resolve() for r in self.roots if (r/leaf).with_suffix(".olean").is_file()),None)
            fail(first!=p,"OLean no longer first in runtime");self.pin(p,h)
    def sources(self,d):
        for k in ["source","original_source","facts","port_source","immutable_source","output","snapshot_core"]:self.ref(d,k)
    def wrapper(self,d):
        if "record" in d:self.ref(d,"record",role="preflight")
        elif "path" in d:self.ref(d,"path","sha256",role="preflight")
        else:raise ValueError("Unknown preflight wrapper")
        self.ref(d,"log");self.ref(d,"output_olean")
        if isinstance(d.get("dependency_oleans"),list):self.deps(d["dependency_oleans"])
    def preflight(self,d):
        for k in ["source","manifest"]:
            fail(d[k+"_sha256_before"]!=d[k+"_sha256_after"],"Actual input instability")
            self.pin(self.path(d[k]),d[k+"_sha256_before"],"manifest" if k=="manifest" else None)
        self.ref(d,"runtime_path","runtime_sha256");self.ref(d,"lean_executable");self.ref(d,"log");self.ref(d,"output_olean")
        for k in ["manifest_input_hashes_before","manifest_input_hashes_after"]:
            for p,r in d[k].items():
                fail(r["matches"] is not True or r["expected_sha256"]!=r["actual_sha256"],"Actual input hash mismatch")
                self.pin(self.path(p),r["expected_sha256"])
        for k in ["runtime_project_pins","runtime_project_pins_after"]:
            fail(set(d[k])!=PROJECT_FILES,"Project pin domain mismatch")
            for p,r in d[k].items():
                fail(r["matches"] is not True or r["expected_sha256"]!=r["actual_sha256"],"Project input hash mismatch")
                self.pin(ROOT/p,r["expected_sha256"])
        self.deps(d["dependency_oleans"])
    def manifest(self,d):
        self.maps(d);self.sources(d)
        for k in ["source_catalog_bindings","source_request_bindings","namespace_context_overlay","full_owner_catalog","subset_catalog"]:self.ref(d,k)
        for r in d.get("import_provenance",[]):
            if isinstance(r,dict):self.sources(r)
        if d.get("actual_import_oleans") is not None:self.deps(d["actual_import_oleans"])
    def certificate(self,d):
        self.maps(d);self.ref(d,"manifest",role="manifest")
        for k in ["provider_source","owner_catalog","source_jsonl","generated_jsonl"]:self.ref(d,k)
        for k in ["source34_certificate","source18_certificate"]:self.ref(d,k,role="certificate")
        for k in ["preflight","bundle_preflight","generated_group_preflight","generated_snapshot_preflight"]:
            if isinstance(d.get(k),dict):self.wrapper(d[k])
        pfs=d.get("preflights",[])
        for pf in (pfs.values() if isinstance(pfs,dict) else pfs):self.wrapper(pf)
        for r in d.get("source_components",[]):self.sources(r)
        for r in d.get("definition_certificates",[]):
            self.ref(r,"certificate",role="certificate");self.ref(r,"output_olean","output_lean_sha256")
        if "external_provider" in d:self.ref(d["external_provider"],"certificate",role="certificate");self.ref(d["external_provider"],"output_olean")
        if "generated_group_jsonl_sha256" in d:self.pin(self.path(d["generated_group_preflight"]["data"]["source"]).parent/"generated.jsonl",d["generated_group_jsonl_sha256"])
        if "source_subset_certificate" in d:self.ref(d["source_subset_certificate"],"certificate",role="certificate")
        if "fast_generated_snapshot" in d:
            f=d["fast_generated_snapshot"];self.ref(f,"helper");self.ref(f,"source",verification=True);self.ref(f,"generated_jsonl");self.ref(f,"provenance",role="fast")
        if d.get("source_only_original_kernel_certificate") is True:
            self.ref(d,"generator");self.ref(d,"validator");c=d["catalog"];self.ref(c,"path","sha256");self.ref(c,"full_owner_catalog")
            for r in c["bundle_coverage"]:self.ref(r,"provider_manifest",role="manifest");self.ref(r,"snapshot_requests")
            for s in d["shards"]:
                self.pinmap(s["manifest_inputs"]);self.ref(s,"manifest",role="manifest")
                for k in ["lean_source","request_manifest","owner_manifest","jsonl"]:self.ref(s,k)
                for r in s["raw_sources"]:self.sources(r)
                self.wrapper(s["preflight"]);self.deps(s["olean_resolution"]["dependency_oleans"])
    def preparation(self,d):
        self.ref(d,"base_snapshot");self.ref(d,"generated_with_refs")
        for r in d["compile_manifests"].values():self.ref(r,"manifest",role="manifest")
    def repair(self,d):
        for k in ["source","output","prior_failed_log","prior_failed_generated_type_archive"]:self.ref(d,k)
        self.ref(d,"manifest",role="manifest");self.ref(d,"prior_failed_preflight",role="preflight")
    def fast(self,d):
        self.maps(d);self.ref(d,"helper");self.ref(d,"fast_snapshot");a=d["actual_provider_evidence"];self.wrapper(a["bundle_preflight"]);self.deps(a["actual_import_oleans"])
    def finish(self):
        handlers={"certificate":self.certificate,"preflight":self.preflight,"manifest":self.manifest,"preparation":self.preparation,"repair":self.repair,"fast":self.fast}
        while self.queue:
            p,role=self.queue.pop();identity=(str(p),role)
            if identity in self.seen:continue
            self.seen.add(identity);fail(role not in handlers,"Unknown evidence role");handlers[role](read(p))
        return [{"path":p,"sha256":h} for p,h in sorted(self.pins.items())]


def reviewed_security_pins(evidence):
    """Materialize/verify typed file pins AFTER one complete readonly f1 review."""
    fail(evidence.get("validated") is not True or Path(evidence["stage"]).resolve()!=F1.resolve(),"Expected reviewed f1 view")
    i=Inventory();c,m=evidence["certificate"],evidence["manifest_data"];cp=i.path(c["path"])
    fail(read(cp)!=c["data"],"Trusted certificate view differs from current bytes")
    i.pin(cp,c["sha256"],"certificate");i.pin(SELF,sha(SELF));i.pin(RUNTIME,c["data"]["preflights"]["SnapshotGeneratedWithRefs2.lean"]["data"]["runtime_sha256"])
    i.pin(Path(i.runtime["executable"]),i.runtime["executable_sha256"])
    for p,h in i.runtime["project_hashes"].items():i.pin(ROOT/p,h)
    for p,h in m["outputs_sha256"].items():i.pin(F1/p,h)
    for p,h in c["data"]["output_json_sha256"].items():i.pin(F1/p,h)
    for name in ["c1.json","c2.json","c3.json","c4.json","c4b.json","certified-inputs.json"]:
        p=F1/name;i.pin(p,sha(p),"manifest")
    for name,role in [("preparation.json","preparation"),("refs-repair-preparation.json","repair")]:
        p=F1/name;i.pin(p,sha(p),role)
    return i.finish()


def assert_security_pins(pins):
    """Per-request fixed-file hashes only; no certificate/Graph/kernel replay."""
    _,roots=runtime_roots();fail(not isinstance(pins,list) or not pins,"Empty security inventory");previous=None
    for r in pins:
        fail(not isinstance(r,dict) or set(r)!={"path","sha256"},"Security pin schema differs");p=confined(r["path"],roots)
        fail(str(p)!=r["path"] or previous is not None and previous>=r["path"],"Paths must be unique sorted resolved absolute files");previous=r["path"]
        fail(sha(p)!=digest(r["sha256"]),"Exact reviewed publication input changed: "+str(p))
