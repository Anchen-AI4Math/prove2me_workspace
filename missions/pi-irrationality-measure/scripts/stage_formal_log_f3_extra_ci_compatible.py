"""Retain the first companion preparation and split typed external API pins.

The frozen preflight accepts mission-relative input_hashes. External Lean API
sources remain explicitly checked evidence, outside that runner input map.
"""
from __future__ import annotations
import json
from pathlib import Path
import stage_formal_log_f3_extra_ci as original
import validate_namespace_context_providers as context

TASK,STAGE=original.TASK,original.STAGE
SELF=Path(__file__).resolve()
ORIGINAL_SHA='2ea870cb464716e6457027d44524bbdc616e28589a7ab2bc811df4032e7be805'

def plan():
    if context.sha(Path(original.__file__))!=ORIGINAL_SHA:raise ValueError('Frozen first producer changed')
    old=original.plan()
    if context.read(STAGE/'preparation.json')!=old:raise ValueError('Retained first preparation differs')
    old_manifests=original.manifests(old)
    pins={};external=[]
    runtime=context.read(TASK/'verification/lean-runtime.json')
    toolchain=Path(runtime['executable']).resolve().parent.parent
    allowed=['Meta/Eqns.lean','Util/FoldConsts.lean','Environment.lean','Util/CollectAxioms.lean']
    for path,h in old['input_hashes'].items():
        p=Path(path)
        if p.is_absolute():
            suffix=p.resolve().relative_to(toolchain/'src/lean/Lean').as_posix()
            if suffix not in allowed:raise ValueError('External input outside exact fixed Lean API files')
            external.append({'path':str(p.resolve()),'sha256':h,'toolchain_root':str(toolchain),'lean_source_suffix':suffix})
        else:pins[path]=h
    if sorted(e['lean_source_suffix'] for e in external)!=sorted(allowed):raise ValueError('Exact external API domain differs')
    retained={context.rel(STAGE/'preparation.json'):context.sha(STAGE/'preparation.json')}
    for name,f in old['files'].items():
        p=TASK/f['manifest']
        if context.read(p)!=old_manifests[name]:raise ValueError('Retained invalid manifest differs')
        retained[context.rel(p)]=context.sha(p)
    pins.update(retained);pins[context.rel(SELF)]=context.sha(SELF)
    p=dict(old);p['input_hashes']=pins
    p['external_lean_api_sources']=sorted(external,key=lambda e:e['path'])
    p['retained_original_preparation']=retained
    p['artifact_kind']='formal-log-f3-extra-ci-compatible-preparation'
    p['compatibility_move_only']='external fixed Lean API source pins split out of mission-only input_hashes'
    p['files']={name:dict(f,manifest=context.rel(STAGE/(f['side']+'2.json'))) for name,f in old['files'].items()}
    return p

def manifests(p):
    result=original.manifests(p)
    for m in result.values():m['external_lean_api_sources']=p['external_lean_api_sources']
    return result

def main():
    p=plan();ms=manifests(p)
    for name,f in p['files'].items():context.write_exact(TASK/f['manifest'],ms[name])
    context.write_exact(STAGE/'preparation2.json',p)
    print(json.dumps({'files':p['files'],'producer_sha256':context.sha(SELF),'Lean_started':False},indent=2))

if __name__=='__main__':main()
