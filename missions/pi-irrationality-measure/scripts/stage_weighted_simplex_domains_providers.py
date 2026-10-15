"""Stage two exact foundational Def providers; no Lean/API/credentials."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import preflight_staged_module as runner

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
V = TASK / "verification"
SELF = Path(__file__).resolve()
CORE = V / "StructuralKernelSnapshotCore.inc"
AST = V / "ast-unit-inventory.json"
SCOPES = V / "ast-scope-inventory.json"
GRAPH = V / "decl_graph.jsonl"
OWNERS = V / "shared-source-snapshot/complete-source/CompleteSource875.owners.json"
COVERAGE = V / "ap9/published-definition-coverage.json"
RUNTIME = V / "lean-runtime.json"
PREFLIGHT = Path(runner.__file__)
CONTEXT = TASK / "scripts/validate_namespace_context_providers.py"
COMMIT = "adc7f1241b42e322a6451854ab7e4b4c146bf78a"
SOURCE_SNAPSHOT = "SourceSnapshot.lean"
GENERATED_SNAPSHOT = "GeneratedSnapshot.lean"
SOURCE_JSON = "source-full-ci.jsonl"
GENERATED_JSON = "generated-full-ci.jsonl"
SIMPLEX_MODULE = "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexCounting_WeightedDomains"
DOMAIN_MODULE = "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_InterpolationMatrix_Domains"
CONFIGS = {
    "simplex": {
        "source_module": "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting",
        "platform_module": SIMPLEX_MODULE,
        "source_sha256": "69cf799999bdc7da4c293a578fb23eb225b6850e94e775cc5726f0d2da7dea2d",
        "namespace": "OAI.PiExponent", "namespace_stack": ["OAI", "PiExponent"],
        "contexts": [(146, 170, "open scoped BigOperators"), (4976, 4996, "open Filter Topology")],
        "specs": [("OAI.PiExponent.realWeightedSimplex", 6443, 6698, 154, 158),
                  ("OAI.PiExponent.strictWeightedSimplex", 6702, 6912, 160, 163)],
        "imports": ["Mathlib"],
        "title": "Finite real-weighted simplices",
        "statement": "For real weights w indexed by a finite set of d coordinates and a real height H, define the finite weak simplex of natural exponent vectors using coordinate ranges up to the natural floor of H/w_i and the inequality sum_i w_i a_i <= H. Define the strict simplex by filtering this finite weak simplex with sum_i w_i a_i < H. These exact finite sets supply the row and column domains of the interpolation matrix; no positivity or asymptotic theorem is asserted here.",
    },
    "domains": {
        "source_module": "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
        "platform_module": DOMAIN_MODULE,
        "source_sha256": "ab84501a2a29cb569118260ffd1adb30ca827936727fa868db0e829cb1bfde38",
        "namespace": "OAI.PiExponent.InterpolationMatrix", "namespace_stack": ["OAI", "PiExponent", "InterpolationMatrix"],
        "contexts": [(126, 150, "open scoped BigOperators")],
        "specs": [("OAI.PiExponent.InterpolationMatrix.columnWeights", 2274, 2375, 58, 59),
                  ("OAI.PiExponent.InterpolationMatrix.rowWeights", 2379, 2512, 61, 62),
                  ("OAI.PiExponent.InterpolationMatrix.Column", 2516, 2645, 64, 65),
                  ("OAI.PiExponent.InterpolationMatrix.Row", 2649, 2799, 67, 68)],
        "imports": ["Mathlib", SIMPLEX_MODULE],
        "title": "Weighted row and column domains for interpolation",
        "statement": "Given real weights w_0, v_0, theta and w indexed by m coordinates, form column weights (w_0,w) and row weights (v_0,w/theta). The column domain is the finite real-weighted simplex at height H with column weights. The row domain is the product of Fin K and the strict weighted simplex at height H with row weights. These are the exact finite indexing domains used by the source interpolation matrix.",
    },
}


def sha_bytes(raw): return hashlib.sha256(raw).hexdigest()
def sha(path): return sha_bytes(Path(path).read_bytes())
def read(path): return json.loads(Path(path).read_text(encoding="utf-8"))
def encode(value): return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode("utf-8")
def rel(path): return Path(path).resolve().relative_to(TASK.resolve()).as_posix()
def workspace_rel(path): return Path(path).resolve().relative_to(ROOT.resolve()).as_posix()
def need(ok, message):
    if not ok: raise ValueError(message)


def config(key):
    c = dict(CONFIGS[key])
    c["stage"] = V / "ap9" / key
    c["source"] = TASK / "port/lean" / Path(*c["source_module"].split(".")).with_suffix(".lean")
    c["original"] = TASK / "source/lean" / Path(*c["source_module"].split(".")).with_suffix(".lean")
    c["provider_file"] = c["platform_module"].replace(".", "/") + ".lean"
    c["names"] = [x[0] for x in c["specs"]]
    return c


def authority(c):
    raw = c["source"].read_bytes()
    need(sha_bytes(raw) == c["source_sha256"], "Pinned provider source changed")
    module = next(x for x in read(AST)["modules"] if x["module"] == c["source_module"])
    scope_module = next(x for x in read(SCOPES)["modules"]
                        if x["source"] == c["source_module"].replace(".", "/") + ".lean")
    need(module["source_sha256"] == c["source_sha256"]
         and scope_module["source_sha256"] == c["source_sha256"], "Source AST hash binding differs")
    owners = {x["source_name"]: x for x in read(OWNERS)["owners"] if x["source_name"] in c["names"]}
    graph = {x["name"]: x for x in map(json.loads, GRAPH.read_text(encoding="utf-8").splitlines()) if x["name"] in c["names"]}
    units = []
    original = c["original"].read_bytes().replace(b"\r\n", b"\n")
    for name, start, end, first, last in c["specs"]:
        ast = next(x for x in module["units"] if name in x["graph_names"])
        scope = next(x for x in scope_module["declarations"] if x["verified_name"] == name)
        owner = owners[name]
        need(ast["start"]["offset"] == start and ast["end"]["offset"] == end
             and ast["start"]["line"] == first and ast["end"]["line"] == last
             and ast["graph_names"] == [name] and ast["graph_kinds"] == ["def"]
             and ast["privateTok"] is None and not ast["is_instance_command"] and not ast["is_local_instance"], "Actual public Def AST differs: " + name)
        need(scope["namespace"] == c["namespace"]
             and [x["name"] for x in scope["scope_stack"]] == c["namespace_stack"]
             and all(x["kind"] == "namespace" for x in scope["scope_stack"])
             and len(scope["context_commands"]) == len(c["contexts"]), "Actual namespace or section context differs")
        for context, (a, b, text) in zip(scope["context_commands"], c["contexts"], strict=True):
            need(context["syntaxKind"] == "Lean.Parser.Command.open"
                 and context["range"]["start"]["offset"] == a and context["range"]["end"]["offset"] == b
                 and raw[a:b] == text.encode(), "Exact open context changed")
        need(owner["source_module"] == c["source_module"] and owner["source_sha256"] == c["source_sha256"]
             and owner["command_unit"] == c["source_module"] + ":" + str(start)
             and owner["unit_start_offset"] == start and owner["unit_end_offset"] == end
             and owner["graph_kind"] == "def" and not owner["source_private"], "Complete source owner differs")
        unit = raw[start:end]
        need(original.count(unit.replace(b"\r\n", b"\n")) == 1, "Original/port Def unit differs")
        need(graph[name]["typeDeps"] == [] and set(graph[name]["valueDeps"]) <=
             set(c["names"] + [x[0] for x in CONFIGS["simplex"]["specs"]]),
             "Tiny foundational Def gained outside dependencies")
        units.append({"name": name, "start": start, "end": end, "source_lines": [first,last],
                      "sha256": sha_bytes(unit), "bytes": unit, "ast": ast, "scope": scope,
                      "owner": owner, "graph": graph[name]})
    return units


def request_text(owner, expected_module):
    fields = {"sourceName": owner["source_name"], "expectedPublicName": owner["source_name"],
              "expectedModule": expected_module, "graphKind": "def", "declGraphSha256": owner["decl_graph_sha256"],
              "declGraphRowSha256": owner["decl_graph_row_sha256"], "ownerKind": owner["owner_kind"],
              "ownerId": owner["owner_id"], "commandUnit": owner["command_unit"], "familyRoot": owner["source_name"]}
    return "    { " + ", ".join(k + " := " + json.dumps(v) for k,v in fields.items()) + " }"


def snapshot(c, units, generated):
    module = c["platform_module"] if generated else c["source_module"]
    output = c["stage"] / (GENERATED_JSON if generated else SOURCE_JSON)
    requests = ",\n".join(request_text(x["owner"], module) for x in units)
    return ("import Lean\nimport " + module + "\n\n" + CORE.read_text(encoding="utf-8").rstrip()
            + "\n\nopen PiExponentStructuralKernelSnapshot\n\ndef weightedDomainRequests : Array StructuralRequest := #[\n"
            + requests + "\n  ]\n\nrun_meta do\n  exportStructuralSnapshotJsonl weightedDomainRequests "
            + json.dumps(workspace_rel(output)) + "\n\n" + "\n".join("#print axioms " + n for n in c["names"]) + "\n").encode()


def stage_files(key):
    c = config(key)
    units = authority(c)
    raw = ("".join("import " + x + "\n" for x in c["imports"]) + "\nnamespace OAI\n\n"
           + "open scoped BigOperators\n\nnamespace " + c["namespace"][4:] + "\n\n"
           + ("open Filter Topology\n\n" if key == "simplex" else "")).encode()
    raw += b"\n\n".join(x["bytes"] for x in units)
    raw += ("\n\nend " + c["namespace"][4:] + "\n\nend OAI\n").encode()
    need(b"sorry" not in raw and b"theorem " not in raw, "Provider contains a proof lemma or sorry")
    outputs = {c["provider_file"]: raw, SOURCE_SNAPSHOT: snapshot(c,units,False), GENERATED_SNAPSHOT: snapshot(c,units,True)}
    coverage = read(COVERAGE)
    need(coverage["audited_definition_count"] == 22 and coverage["none_provided"] and coverage["none_mentioned"], "Frozen literal published coverage changed")
    inputs = {rel(p): sha(p) for p in [SELF,c["source"],c["original"],AST,SCOPES,GRAPH,OWNERS,CORE,RUNTIME,PREFLIGHT,CONTEXT,COVERAGE]}
    inputs.update({x["publication_record"]: x["publication_record_sha256"] for x in coverage["records"]})
    plans = [(c["provider_file"], c["imports"], "emit-olean", c["platform_module"]),
             (SOURCE_SNAPSHOT,["Lean",c["source_module"]],"modecheck","SourceSnapshot"),
             (GENERATED_SNAPSHOT,["Lean",c["platform_module"]],"modecheck","GeneratedSnapshot")]
    commands = []
    for i,(filename,imports,mode,module) in enumerate(plans,1):
        manifest = {"schema_version":1,"artifact_kind":"ap9-foundational-provider-bounded-compiler-manifest",
                    "output":workspace_rel(c["stage"]/filename),"output_sha256":sha_bytes(outputs[filename]),
                    "imports":imports,"input_hashes":inputs,"runtime_sha256":sha(RUNTIME),
                    "mode":mode,"emit_olean":mode=="emit-olean","timeout_seconds":300,
                    "expected_actual_module_identity":module,"validated":False,"submission_ready":False}
        outputs[f"c{i}.json"] = encode(manifest)
        commands.append("python scripts/preflight_staged_module.py ap9/"+key+"/"+filename+
            " --root ap9/"+key+" --imports-manifest ap9/"+key+f"/c{i}.json --timeout-seconds 300"+
            (" --emit-olean" if mode=="emit-olean" else ""))
    source_url = f"https://github.com/openai/math/blob/{COMMIT}/lean/"+c["source_module"].replace(".","/")+f".lean#L{c['specs'][0][3]}-L{c['specs'][-1][4]}"
    metadata = {"definition_title":c["title"],"natural_language_statement":c["statement"],
                "source":"OpenAI math, commit "+COMMIT+": "+source_url,
                "source_commit":COMMIT,"source_url":source_url,
                "tags":["linear-algebra","number-theory","openai-pi-exponent-017"]}
    outputs["academic-metadata.json"] = encode(metadata)
    outputs["preparation.json"] = encode({"schema_version":1,"artifact_kind":"ap9-foundational-provider-preparation",
        "source_commit":COMMIT,"source_module":c["source_module"],"platform_module":c["platform_module"],
        "source_path":rel(c["source"]),"source_sha256":sha(c["source"]),"original_source_path":rel(c["original"]),
        "original_source_sha256":sha(c["original"]),"provided_names":c["names"],"provider_file":c["provider_file"],
        "exact_source_units":[{k:v for k,v in x.items() if k!="bytes"} for x in units],
        "source_context_commands":[x[2] for x in c["contexts"]],"input_hashes":inputs,
        "order":[x[0] for x in plans],"commands":commands,"snapshot_outputs":{SOURCE_SNAPSHOT:rel(c["stage"]/SOURCE_JSON),GENERATED_SNAPSHOT:rel(c["stage"]/GENERATED_JSON)},
        "expected_provider_olean":"verification/staged-build/lib/lean/"+c["platform_module"].replace(".","/")+".olean",
        "published_coverage":rel(COVERAGE),"published_coverage_sha256":sha(COVERAGE),
        "Lean_started":False,"API_used":False,"validated":False,"submission_ready":False,"proposal_status":"Draft"})
    return outputs


def check_only(key):
    c=config(key); generated=stage_files(key)
    for name,raw in generated.items():need((c["stage"]/name).is_file() and (c["stage"]/name).read_bytes()==raw,"Stage changed: "+name)
    for i,filename in enumerate([c["provider_file"],SOURCE_SNAPSHOT,GENERATED_SNAPSHOT],1):
        m=read(c["stage"]/f"c{i}.json");runner.verify_manifest_inputs(m);runner.verify_source_certificate(c["stage"]/filename,m)
    return {"stage":rel(c["stage"]),"checked_files":len(generated),"all_hashes_match":True,"Lean_started":False,"API_used":False,"validated":False}


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument("--provider",choices=list(CONFIGS),required=True)
    modes=parser.add_mutually_exclusive_group(required=True);modes.add_argument("--prepare",action="store_true");modes.add_argument("--check-only",action="store_true");args=parser.parse_args()
    if args.prepare:
        c=config(args.provider)
        for name,raw in stage_files(args.provider).items():
            p=c["stage"]/name
            if p.exists():need(p.read_bytes()==raw,"Refusing to overwrite frozen stage: "+name)
            else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(raw)
    print(json.dumps(check_only(args.provider),indent=2))


if __name__=="__main__":main()
