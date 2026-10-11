"""Prepare two exact f3 companion CI probes; no Lean or network operations."""
from __future__ import annotations
import json
from pathlib import Path
import generate_equation_provenance_probe as eq
import validate_formal_log_successor_node as nodes
import validate_namespace_context_providers as context
import formal_log_node_refs as refs
from generate_independent_node import runtime_pin

TASK,ROOT,V=nodes.TASK,nodes.ROOT,nodes.V
STAGE=V/'flp3/e3'
SELF=Path(__file__).resolve()
BASE_SHA='20f761f0d169c7af296faea379bb7547909abd56f79d0bdba03a207d7617bfb4'
PRIMARY=['OAI.PiExponent.FormalLogJet.formalLog','OAI.PiExponent.FormalLogTruncation.logTail']
REQUIRED=['OAI.PiExponent.FormalLogJet.formalLog.eq_1','OAI.PiExponent.FormalLogTruncation.logTail.eq_1']
AUX_PRIMARY='OAI.PiExponent.FormalLogTruncation.shiftVars'
AUX='OAI.PiExponent.FormalLogTruncation.shiftVars._proof_1'
SOURCE_MODULES=['OAI.NumberTheory.PiExponent.Jets.FormalLogJet','OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation']
GEN_MODULES=['Definitions.Def_OAI_NumberTheory_PiExponent_Jets_FormalLogJet','Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_FormalLogTruncation']
ROW_PATHS={
 'original':['verification/providers-context-preview/source-snapshot/source.jsonl','verification/providers-formal-log-preview/source-snapshot/source.jsonl'],
 'generated':['verification/providers-context-preview/generated-snapshot/generated.jsonl','verification/providers-formal-log-preview/generated-snapshot/generated.jsonl']}

AUX_PROBE=r'''
open Lean Meta in
run_meta do
  let primary := `OAI.PiExponent.FormalLogTruncation.shiftVars
  let required := `OAI.PiExponent.FormalLogTruncation.shiftVars._proof_1
  let ci ← getConstInfo primary
  let .defnInfo d := ci | throwError "Auxiliary parent must be actual Definition"
  let names := d.value.getUsedConstants.toList.map Name.toString |>.mergeSort
  unless names.contains required.toString do
    throwError "Required helper is not a literal constant in primary full value"
  let aux ← getConstInfo required
  match aux with
  | .thmInfo _ => pure ()
  | _ => throwError "Referenced auxiliary must be a proved theorem"
  let env ← getEnv
  let some idx := env.getModuleIdxFor? required
    | throwError "Auxiliary helper must belong to imported certified Definition"
  unless env.header.moduleNames[idx.toNat]?.map Name.toString == some MODULE do
    throwError "Referenced proof helper owner differs from certified Definition"
  IO.FS.writeFile OUTPUT <| (Json.mkObj [
    ("schemaVersion",toJson (1 : Nat)),("side",toJson SIDE),
    ("probeMainModule",toJson env.mainModule.toString),
    ("getter",toJson "Lean.Expr.getUsedConstants"),
    ("primaryValueRefs",toJson names),
    ("primaryBinding",← PiExponentEquationProvenanceProbe.checkedCI primary),
    ("helper",← PiExponentEquationProvenanceProbe.checkedCI required),
    ("theoremProofValuesExported",toJson false)]).compress
'''

def rows(side):
    by={}
    for p in ROW_PATHS[side]:
        for line in (TASK/p).read_bytes().splitlines():
            row=json.loads(line)
            if row['resolvedName'] in PRIMARY+[AUX_PRIMARY]:
                if row['resolvedName'] in by:raise ValueError('Duplicate primary safe CI')
                by[row['resolvedName']]=row
    if set(by)!=set(PRIMARY+[AUX_PRIMARY]):raise ValueError('Exact safe primary snapshot domain missing')
    return by

def render(side):
    modules=SOURCE_MODULES if side=='original' else GEN_MODULES
    imports=['Lean','Lean.Meta.Eqns','Lean.Util.FoldConsts',*modules]
    core=(V/'TypeOnlyTheoremSnapshotCore.inc').read_text(encoding='utf-8')
    text=''.join('import '+m+'\n' for m in imports)+'\n'+core+eq.PROBE
    for i,(primary,module) in enumerate(zip(PRIMARY,modules,strict=True)):
        output=(STAGE/f'{side}-eq{i}.json').relative_to(ROOT).as_posix()
        text+='\nrun_meta do\n  PiExponentEquationProvenanceProbe.exportEquationSnapshot `'+primary+' '+json.dumps(module)+' '+json.dumps(output)+' '+json.dumps(side)+'\n'
    text+=AUX_PROBE.replace('MODULE',json.dumps(modules[1])).replace('OUTPUT',json.dumps((STAGE/f'{side}-aux.json').relative_to(ROOT).as_posix())).replace('SIDE',json.dumps(side))
    return text.encode(),imports

def plan():
    if context.sha(Path(nodes.__file__))!=BASE_SHA:raise ValueError('Frozen successor checker changed')
    definitions=context.read(V/'flp3/f3/certified-inputs.json')['definition_certificates']
    selected=[next(d for d in definitions if d['source_module']==m) for m in SOURCE_MODULES]
    for side in ['original','generated']:
        safe=rows(side)
        if AUX not in refs.kernel_refs(safe[AUX_PRIMARY]['value']):raise ValueError('Auxiliary absent from certified primary fullvalue')
    current_refs=context.read(V/'flp3/f3/proof-references.json')['rows'][0]['valueRefs']
    if not set(REQUIRED+[AUX])<=set(current_refs):raise ValueError('Extra names are not actual f3 proof references')
    inputs={context.rel(p):context.sha(p) for p in [SELF,Path(nodes.__file__),Path(eq.__file__),Path(refs.__file__),
        V/'flp3/f3/certified-inputs.json',V/'flp3/f3/manifest.json',V/'flp3/f3/proof-references.json',V/'TypeOnlyTheoremSnapshotCore.inc',
        V/'TypeOnlyTheoremSnapshotCore.lineage.json',V/'lean-runtime.json',*[TASK/p for paths in ROW_PATHS.values() for p in paths]]}
    for d in selected:
        inputs[d['certificate']]=d['certificate_sha256'];inputs[d['output_olean']]=d['output_lean_sha256']
        c=context.read(TASK/d['certificate'])
        for k in ['source18_certificate','source34_certificate']:
            if k in c:inputs[c[k]]=c[k+'_sha256']
    runtime=context.read(V/'lean-runtime.json');lean=Path(runtime['executable']).parent.parent/'src/lean/Lean'
    for suffix in ['Meta/Eqns.lean','Util/FoldConsts.lean','Environment.lean','Util/CollectAxioms.lean']:
        p=lean/suffix;inputs[str(p)]=context.sha(p)
    files={}
    for side,name in [('original','ProbeSource'),('generated','ProbeGenerated')]:
        raw,imports=render(side);path=STAGE/(name+'.lean')
        files[name]={'side':side,'source':context.rel(path),'source_sha256':__import__('hashlib').sha256(raw).hexdigest(),
            'manifest':context.rel(STAGE/(side+'.json')),'imports':imports}
    return {'schema_version':1,'artifact_kind':'formal-log-f3-extra-ci-companion-preparation',
        'input_hashes':inputs,'definition_certificates':selected,'primary_names':PRIMARY,'required_equations':REQUIRED,
        'auxiliary_primary':AUX_PRIMARY,'required_auxiliary':AUX,'files':files,'runtime_sha256':runtime_pin(),
        'validated':False,'submission_ready':False,'Lean_started':False,'server_parent_pending':True}

def manifests(p):
    return {name:{'schema_version':1,'artifact_kind':'formal-log-f3-extra-ci-file-import-certificate',
        'output':(TASK/f['source']).relative_to(ROOT).as_posix(),'output_sha256':f['source_sha256'],
        'imports':f['imports'],'input_hashes':p['input_hashes'],'runtime_sha256':p['runtime_sha256'],
        'timeout_seconds':300,'node_validated':False,'submission_ready':False,'Lean_started':False}
        for name,f in p['files'].items()}

def main():
    STAGE.mkdir(parents=True,exist_ok=True);p=plan();ms=manifests(p)
    for name,f in p['files'].items():
        raw,_=render(f['side']);path=TASK/f['source']
        if path.exists() and path.read_bytes()!=raw:raise ValueError('Immutable companion source differs')
        if not path.exists():path.write_bytes(raw)
        context.write_exact(TASK/f['manifest'],ms[name])
    context.write_exact(STAGE/'preparation.json',p)
    print(json.dumps({'stage':context.rel(STAGE),'files':p['files'],'producer_sha256':context.sha(SELF),'Lean_started':False},indent=2))

if __name__=='__main__':main()
