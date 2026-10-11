"""Certify exact source-command CI provenance from existing bounded evidence.

Never runs Lean or a network request. Command ownership is the actual Name-set
delta. Copied-prefix maps have a separate authority and must also pass original
CI type/full-def-value comparison. No suffix/printed private number is guessed.
"""
import argparse
import hashlib
import json
from pathlib import Path

from generate_independent_node import runtime_pin

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
STAGE = TASK/"verification/command-emission-probe"
STD3 = {"propext","Classical.choice","Quot.sound"}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text(encoding="utf-8"))


def mission_file(value):
    p=Path(value)
    if not p.is_absolute():
        p=TASK/p
    p=p.resolve()
    if not p.is_relative_to(TASK.resolve()) or not p.is_file():
        raise ValueError("Missing/outside mission evidence file: "+str(value))
    return p


def checked_plan():
    plan=read(STAGE/"probe-plan.json")
    if runtime_pin()!=plan["runtime_sha256"] or plan.get("validated") or plan.get("lean_started") or plan.get("api_used"):
        raise ValueError("Stale runtime or unsafe command-probe plan")
    for p,h in plan["input_hashes"].items():
        if sha(mission_file(p))!=h:
            raise ValueError("Command-probe selected input pin changed: "+p)
    for p,h in plan["pinned_lean_api_source_hashes"].items():
        if sha(Path(p))!=h:
            raise ValueError("Pinned command elaboration API source changed: "+p)
    expected={"CommandEmission.lean","SourceOriginalSnapshot.lean","SourcePrefixSnapshot.lean"}
    if set(plan["outputs_sha256"])!=expected:
        raise ValueError("Probe requires command/source/prefix three-file witness")
    for f,h in plan["outputs_sha256"].items():
        if sha(STAGE/f)!=h:
            raise ValueError("Exact command probe source bytes changed: "+f)
    for row in plan["direct_import_olean_witnesses"]:
        p=row["resolved_first_ordered_runtime_olean"]
        if row["missing"] or not p or sha(Path(p))!=row["olean_sha256"]:
            raise ValueError("Command/source dependency OLean unavailable or changed: "+row["module"])
    return plan


def checked_record(plan, filename, path=None):
    p=mission_file(path) if path else STAGE/(filename+".preflight.json")
    r=read(p)
    source=(ROOT/r["source"]).resolve()
    if (source!=(STAGE/filename).resolve() or r["exit_code"]!=0 or r["original_exit_code"]!=0
            or r["timed_out"] or not r["source_unchanged"] or r["mode"]!="verification"
            or r["source_sha256"]!=plan["outputs_sha256"][filename]
            or r["runtime_sha256"]!=plan["runtime_sha256"] or r["runtime_kind"]!="captured-lake-env"
            or not 0<r["seconds"]<=300 or r["timeout_seconds"]!=300):
        raise ValueError("Not an exact current successful strict 300-second probe preflight: "+filename)
    log=(ROOT/r["log"]).resolve()
    if not log.is_relative_to(TASK/"verification") or not log.is_file():
        raise ValueError("Probe log is missing/outside verification")
    actual_log=sha(log)
    if r.get("log_sha256") is not None and r["log_sha256"]!=actual_log:
        raise ValueError("Probe log bytes differ from preserved record")
    return {"record":p.relative_to(TASK).as_posix(),"record_sha256":sha(p),"record_data":r,
            "log":log.relative_to(TASK).as_posix(),"log_sha256":actual_log}


def checked_expr(tree, params, depth=0):
    if not isinstance(tree,list) or not tree or not isinstance(tree[0],str):
        raise ValueError("Malformed structural kernel Expr JSON")
    tag=tree[0]
    def level(t):
        if not isinstance(t,list) or not t or not isinstance(t[0],str):
            raise ValueError("Malformed kernel universe JSON")
        if t[0]=="zero" and len(t)==1:
            return
        if t[0]=="param" and len(t)==2 and isinstance(t[1],str) and t[1] in params:
            return
        if t[0]=="succ" and len(t)==2:
            level(t[1]);return
        if t[0] in {"max","imax"} and len(t)==3:
            level(t[1]);level(t[2]);return
        raise ValueError("Free/unknown kernel universe parameter or metavariable")
    if tag=="bvar" and len(tree)==2 and isinstance(tree[1],int) and not isinstance(tree[1],bool) and 0<=tree[1]<depth:
        return
    if tag=="sort" and len(tree)==2:
        level(tree[1]);return
    if tag=="const" and len(tree)==3 and isinstance(tree[1],str) and isinstance(tree[2],list):
        for t in tree[2]:level(t)
        return
    if tag=="app" and len(tree)==3:
        checked_expr(tree[1],params,depth);checked_expr(tree[2],params,depth);return
    if tag in {"lambda","forall"} and len(tree)==4 and tree[1] in {"explicit","implicit","strictImplicit","instance"}:
        checked_expr(tree[2],params,depth);checked_expr(tree[3],params,depth+1);return
    if tag=="let" and len(tree)==5 and isinstance(tree[4],bool):
        checked_expr(tree[1],params,depth);checked_expr(tree[2],params,depth);checked_expr(tree[3],params,depth+1);return
    if tag=="projection" and len(tree)==4 and isinstance(tree[1],str) and isinstance(tree[2],int) and not isinstance(tree[2],bool) and tree[2]>=0:
        checked_expr(tree[3],params,depth);return
    if tag=="natLiteral" and len(tree)==2 and isinstance(tree[1],int) and not isinstance(tree[1],bool) and tree[1]>=0:
        return
    if tag=="stringLiteral" and len(tree)==2 and isinstance(tree[1],str):
        return
    raise ValueError("Free/loose/unknown kernel Expr JSON tag: "+tag)


def checked_ci(row, owner_kind, owner_module):
    if (row["kind"] not in {"def","theorem"} or row["owner"]["kind"]!=owner_kind
            or row["owner"]["module"]!=owner_module or not isinstance(row["actualName"],str)
            or not isinstance(row["privateUserName"],str) or not row["privateUserName"]
            or not isinstance(row["axioms"],list) or not set(row["axioms"])<=STD3):
        raise ValueError("Actual CI kind/owner/private user-name/Std3 mismatch")
    levels=row["levelParams"]
    if not isinstance(levels,list) or any(not isinstance(p,str) for p in levels) or len(set(levels))!=len(levels):
        raise ValueError("CI universe parameter binders are not unique strings")
    checked_expr(row["type"],set(levels))
    if row["kind"]=="def":
        if row["value"] is None or not isinstance(row["safety"],str):
            raise ValueError("Actual definition has no complete value/safety metadata")
        checked_expr(row["value"],set(levels))
    elif row["value"] is not None or row["safety"] is not None:
        raise ValueError("Theorem proof values must stay null")


def normalized(tree, params, names):
    if not isinstance(tree,list):return tree
    if tree and isinstance(tree[0],str) and tree[0]=="param":
        return ["param",params[tree[1]]]
    if tree and isinstance(tree[0],str) and tree[0] in {"const","projection"}:
        return [tree[0],names.get(tree[1],tree[1])]+[normalized(v,params,names) for v in tree[2:]]
    return [normalized(v,params,names) for v in tree]


def compare_ci(source, generated, names):
    if (source["kind"]!=generated["kind"] or source["safety"]!=generated["safety"]
            or set(source["axioms"])!=set(generated["axioms"])
            or len(source["levelParams"])!=len(generated["levelParams"])):
        raise ValueError("Source/reelaborated CI kind, safety, universe arity or axioms differ")
    left={p:i for i,p in enumerate(source["levelParams"])}
    right={p:i for i,p in enumerate(generated["levelParams"])}
    for field in ["type"]+(["value"] if source["kind"]=="def" else []):
        if normalized(source[field],left,names)!=normalized(generated[field],right,{}):
            raise ValueError("Source/reelaborated structural kernel "+field+" differs: "+source["actualName"])


def certify(plan, paths):
    records={f:checked_record(plan,f,paths.get(f)) for f in plan["outputs_sha256"]}
    emitted_path=STAGE/"command-emitted.json"
    source_path=STAGE/"original-command-closure.json"
    prefix_path=STAGE/"original-prefix-closure.json"
    emitted,originals,prefix=read(emitted_path),read(source_path),read(prefix_path)
    if (emitted["association"]!="exact-parser-command-env-Name-set-delta"
            or emitted["sourceModule"]!=plan["source_module"]
            or emitted["sourceCommandSHA256"]!=plan["exact_command_sha256"]
            or emitted["primaryExpectedUserName"]!=plan["source_primary_graph_row"]["userName"]
            or emitted["theoremProofValuesExported"] is not False):
        raise ValueError("Emission output differs from the exact authoritative source command")
    own_module=emitted["probeMainModule"]
    names=emitted["actualEmittedNames"]
    rows=emitted["rows"]
    if (not isinstance(own_module,str) or not own_module or len(names)!=len(set(names))
            or len(rows)!=len(names) or {r["actualName"] for r in rows}!=set(names)
            or emitted["afterNameCount"]-emitted["beforeNameCount"]!=len(names)):
        raise ValueError("Actual before-after CI delta is incomplete or duplicated")
    for row in rows:checked_ci(row,"OwnModule",own_module)
    primary=[r for r in rows if r["actualName"]==emitted["primaryActualName"]]
    if len(primary)!=1 or primary[0]["privateUserName"]!=emitted["primaryExpectedUserName"] or primary[0]["kind"]!="def":
        raise ValueError("Actual emitted primary does not match source binding uniquely")
    by_original={r["actualName"]:r for r in originals+prefix}
    expected={r["name"]:r for r in plan["source_original_private_closure_requests"]+plan["copied_prefix_private_closure_requests"]}
    if set(by_original)!=set(expected):
        raise ValueError("Source/prefix original CI domains differ from authenticated requests")
    for original_rows,request_rows in ((originals,plan["source_original_private_closure_requests"]),(prefix,plan["copied_prefix_private_closure_requests"])):
        if (len(original_rows)!=len(request_rows) or len({r["actualName"] for r in original_rows})!=len(original_rows)
                or {r["actualName"] for r in original_rows}!={r["name"] for r in request_rows}):
            raise ValueError("One original CI exporter domain differs from its exact request list")
    original_map={r["actualName"]:r for r in originals}
    for row in prefix:
        if row["actualName"] in original_map and row!=original_map[row["actualName"]]:
            raise ValueError("Overlapping original/prefix source CI exports differ")
    for row in originals+prefix:
        checked_ci(row,"ImportedModule",plan["source_module"])
        req=expected[row["actualName"]]
        if row["kind"]!=req["kind"] or row["privateUserName"]!=req["userName"]:
            raise ValueError("Original actual CI differs from source Graph identity")
    prefix_maps=emitted["copiedPrefixMappings"]
    expected_prefix={r["name"]:r for r in plan["copied_prefix_private_closure_requests"]}
    if len(prefix_maps)!=len(expected_prefix) or {r["sourceGraphName"] for r in prefix_maps}!=set(expected_prefix):
        raise ValueError("Actual prefix maps do not exactly cover copied source-private prefix CI closure")
    candidates={r["privateUserName"]:r for r in rows}
    if len(candidates)!=len(rows):
        raise ValueError("Actual emitted private user-names are not unique")
    prefix_actuals=set()
    for entry in prefix_maps:
        row=entry["CI"];checked_ci(row,"OwnModule",own_module)
        req=expected_prefix[entry["sourceGraphName"]]
        if (entry["association"]!="copied-prefix-actual-OwnModule-CI"
                or entry["sourceUserName"]!=req["userName"] or row["privateUserName"]!=req["userName"]
                or row["actualName"] in set(names)|prefix_actuals or row["privateUserName"] in candidates):
            raise ValueError("Prefix CI map is ambiguous or falsely associated with target command delta")
        prefix_actuals.add(row["actualName"]);candidates[row["privateUserName"]]=row
    name_map={}
    for source_name,row in by_original.items():
        match=candidates.get(row["privateUserName"])
        if not match:
            raise ValueError("Original closure private CI has no actual emitted/prefix user-name correspondence: "+source_name)
        name_map[source_name]=match["actualName"]
    comparisons=[]
    for source_name,row in by_original.items():
        target=candidates[row["privateUserName"]]
        compare_ci(row,target,name_map)
        comparisons.append({"source_graph_name":source_name,"actual_reelaborated_name":target["actualName"],
                            "kind":row["kind"],"kernel_type_equal":True,"complete_def_value_equal":row["kind"]=="def"})
    result={"validated":True,"association":"exact-parser-command-env-Name-set-delta",
        "source_unit":plan["source_module"]+":"+str(plan["source_unit"]["start"]["offset"]),
        "source_command_range":plan["exact_command_range"],"source_command_sha256":plan["exact_command_sha256"],
        "actual_emitted_names":names,"copied_prefix_actual_names":sorted(prefix_actuals),
        "source_to_actual_kernel_names":name_map,"comparisons":comparisons,
        "all_closed_types":True,"all_def_values_complete_and_equal":True,"theorem_values_null":True,
        "all_axioms_std3":True,"preflights":records,"runtime_sha256":plan["runtime_sha256"],
        "input_hashes":plan["input_hashes"],"probe_plan_sha256":sha(STAGE/"probe-plan.json"),
        "parser_sha256":sha(Path(__file__)),"json_sha256":{p.name:sha(p) for p in [emitted_path,source_path,prefix_path]},
        "generated_alias_provider_availability":False,"submission_ready":False,
        "pending":["repeat actual command delta and type/full-value correspondence for generated provider/node alias command",
                   "reviewed source/context closure placement; global planner remains untouched"]}
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    mode=parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check-only",action="store_true")
    mode.add_argument("--certify-existing",action="store_true")
    parser.add_argument("--emission-record",help="Mission-relative exact existing successful preflight record")
    parser.add_argument("--original-record")
    parser.add_argument("--prefix-record")
    args=parser.parse_args()
    try:
        plan=checked_plan()
        if args.check_only:
            result={"validated":False,"status":"exact-probe-plan-checked","probe_plan_sha256":sha(STAGE/"probe-plan.json"),
                    "original_ci_requests":len(plan["source_original_private_closure_requests"]),
                    "prefix_ci_requests":len(plan["copied_prefix_private_closure_requests"]),"submission_ready":False}
        else:
            paths={"CommandEmission.lean":args.emission_record,"SourceOriginalSnapshot.lean":args.original_record,
                   "SourcePrefixSnapshot.lean":args.prefix_record}
            result=certify(plan,paths)
            (STAGE/"command-provenance-validation.json").write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
        print(json.dumps(result,indent=2))
    except (ValueError,KeyError,FileNotFoundError,TypeError) as error:
        print(json.dumps({"validated":False,"status":"rejected","error":str(error),"submission_ready":False}))
        raise SystemExit(2)


if __name__=="__main__":main()
