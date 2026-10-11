"""Stage actual proved c2/c3 modules from certified f2/f3 literal solutions.

No Lean or API runs. The frozen c1 producer supplies only its imported kernel
exporter; these new preparations preserve all c1 and parent node files.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import stage_formal_log_proved_child as original
import validate_formal_log_successor_node as f2check
import validate_formal_log_f3_complete_node_repaired as f3check
import stage_formal_log_successor_children as retained
import validate_namespace_context_providers as context

TASK,ROOT,V=f2check.TASK,f2check.ROOT,f2check.V
SELF=Path(__file__).resolve()
RETAINED_SHA='36e3e5b1600eee918f51062ea3390674bb9a23a7d309ad94683bc539a94b8114'
OLD_PRODUCER_SHA='50dcb20b111191434d901101e651bf1a3b6c374510797a56556f47d333f158d7'
PARENT_CHECKER_SHA={'c2':'20f761f0d169c7af296faea379bb7547909abd56f79d0bdba03a207d7617bfb4',
                    'c3':'e59db91b0c19026106294683e737c4f1060439d9aaccb9addd5502aa9e158a7a'}
NODES={'c2':'OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:12753',
       'c3':'OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:14165'}
THEOREMS={'c2':'OAI.PiExponent.FormalLogTruncation.logTail_mem_rationalWeightedIdeal',
          'c3':'OAI.PiExponent.FormalLogTruncation.shiftMap_truncatedFormalJet'}
sha,read,rel,fail=context.sha,context.read,context.rel,context.fail

def paths(which):
    fail(which not in NODES,'Only c2/c3 proved successors supported')
    stage=V/'flp3'/which;module='Theorems.Thm_'+THEOREMS[which].replace('.','_')
    return {'stage':stage,'module':module,'theorem':THEOREMS[which],
        'source':stage/Path(*module.split('.')).with_suffix('.lean'),
        'source_manifest':stage/'child-module.json','source_preparation':stage/'child-source-preparation.json',
        'snapshot':stage/'ChildSnapshot.lean','snapshot_manifest':stage/'child-snapshot.json',
        'snapshot_preparation':stage/'child-snapshot-preparation.json',
        'types':stage/'child-type.json','refs':stage/'child-proof-references.json'}

def parent(which):
    fail(sha(Path(retained.__file__))!=RETAINED_SHA,'Retained first child producer changed')
    checker=f2check if which=='c2' else f3check
    fail(sha(Path(original.__file__))!=OLD_PRODUCER_SHA or sha(Path(checker.__file__))!=PARENT_CHECKER_SHA[which],
         'Frozen exporter/parent checker changed')
    result=f2check.validate_formal_successor_node('f2') if which=='c2' else f3check.validate_formal_f3_node()
    c=result['certificate']['data']
    fail(c['node']!=NODES[which] or c['theorem_name']!=THEOREMS[which] or any(c[k] is not True for k in
        ['validated','Std3_only','target_stub_unused','actual_project_reference_coverage_complete']),
        'Expected exact actual proof/type/reference parent certificate')
    return result,checker

def rebinding(source,theorem):
    fail(b'sorry' in source,'Certified solution must be sorry-free')
    edits=[(b'theorem solution ',('theorem '+theorem+' ').encode()),
           (b'#print axioms solution',('#print axioms '+theorem).encode())]
    out=source;ledger=[]
    for old,new in edits:
        fail(out.count(old)!=1 or out.count(new),'Literal child rebinding anchor not unique/fresh')
        offset=out.index(old);ledger.append({'start':offset,'end':offset+len(old),'source':old.decode(),'replacement':new.decode()})
        out=out.replace(old,new,1)
    return out,ledger

def source_documents(which,evidence,checker):
    p=paths(which);raw,ledger=rebinding(evidence['solution_bytes'],p['theorem']);m=evidence['manifest_data']
    cert=TASK/evidence['certificate']['path'];solution=ROOT/m['solution']
    pins={rel(x):sha(x) for x in [SELF,Path(retained.__file__),Path(original.__file__),Path(checker.__file__),cert,evidence['manifest'],solution]}
    output_sha=__import__('hashlib').sha256(raw).hexdigest()
    manifest={'schema_version':1,'artifact_kind':'proved-formal-log-successor-child-module-import-certificate',
        'output':p['source'].relative_to(ROOT).as_posix(),'output_sha256':output_sha,'imports':m['imports'],
        'input_hashes':pins,'runtime_sha256':m['runtime_sha256'],'parent_node_certificate':rel(cert),
        'parent_node_certificate_sha256':sha(cert),'theorem_name':p['theorem'],'module':p['module'],
        'emit_olean_required':True,'timeout_seconds':300,'server_parent_pending':True,'validated':False,'submission_ready':False}
    prep={'schema_version':1,'artifact_kind':'proved-formal-log-successor-child-source-preparation',
        'parent_node':NODES[which],'parent_node_certificate':rel(cert),'parent_node_certificate_sha256':sha(cert),
        'certified_solution':rel(solution),'certified_solution_sha256':sha(solution),'output':rel(p['source']),
        'output_sha256':output_sha,'module':p['module'],'theorem_name':p['theorem'],'edit_ledger':ledger,
        'only_literal_binding_and_axiom_marker_renamed':True,'statement_stub_imported':False,'Lean_started':False,
        'server_parent_pending':True,'validated':False,'submission_ready':False}
    return raw,manifest,prep

def source_replay(which,evidence,checker):
    p=paths(which);raw,manifest,prep=source_documents(which,evidence,checker)
    fail(p['source'].read_bytes()!=raw or read(p['source_manifest'])!=manifest or read(p['source_preparation'])!=prep,
         'Exact successor child source/preparation/manifest differs')
    f2check.formal.runner.verify_manifest_inputs(manifest)
    f2check.formal.runner.verify_source_certificate(p['source'],manifest)
    f2check.formal.runner.certified_imports(p['source'],manifest)
    fail(max(len(str(x.resolve())) for x in [p['source'],Path(str(p['source'])+'.preflight.json'),p['source_manifest']])>=240,
         'Successor child path exceeds Windows budget')
    return prep

def snapshot_documents(which,evidence,source_pf):
    p=paths(which);olean=V/'staged-build/lib/lean'/Path(*p['module'].split('.')).with_suffix('.olean')
    fail(source_pf['data']['output_olean_sha256']!=sha(olean),'Current proved child OLean differs from retained actual emission')
    core=(V/'TypeOnlyTheoremSnapshotCore.inc').read_text(encoding='utf-8')
    text=('import Lean\nimport '+p['module']+'\n\n'+core+original.IMPORTED_REFS+
        '\nset_option pp.universes true\nset_option pp.fullNames true\nset_option pp.explicit true\n'+
        'run_meta do\n  PiExponentInterfaceSnapshot.exportSnapshot #[`'+p['theorem']+'] '+json.dumps(p['types'].relative_to(ROOT).as_posix())+'\n'+
        'run_meta do\n  FormalLogImportedChildSnapshot.exportChild `'+p['theorem']+' '+json.dumps(p['module'])+' '+json.dumps(p['refs'].relative_to(ROOT).as_posix())+'\n'+
        '#print axioms '+p['theorem']+'\n')
    cert=TASK/evidence['certificate']['path'];record=TASK/source_pf['record']
    pins={rel(x):sha(x) for x in [SELF,Path(retained.__file__),Path(original.__file__),cert,p['source'],p['source_manifest'],p['source_preparation'],record,olean,V/'TypeOnlyTheoremSnapshotCore.inc']}
    raw=text.encode();output_sha=__import__('hashlib').sha256(raw).hexdigest()
    manifest={'schema_version':1,'artifact_kind':'proved-formal-log-successor-child-snapshot-import-certificate',
        'output':p['snapshot'].relative_to(ROOT).as_posix(),'output_sha256':output_sha,'imports':['Lean',p['module']],
        'input_hashes':pins,'runtime_sha256':evidence['manifest_data']['runtime_sha256'],'theorem_name':p['theorem'],
        'child_module':p['module'],'child_olean':rel(olean),'child_olean_sha256':sha(olean),'timeout_seconds':300,
        'server_parent_pending':True,'validated':False,'submission_ready':False}
    prep={'schema_version':1,'artifact_kind':'proved-formal-log-successor-child-snapshot-preparation',
        'source':rel(p['snapshot']),'source_sha256':output_sha,'child_module':p['module'],'child_olean':rel(olean),
        'child_olean_sha256':sha(olean),'type_output':rel(p['types']),'proof_reference_output':rel(p['refs']),
        'actual_imported_owner_required':True,'Std3_required':True,'Lean_started':False,'server_parent_pending':True,
        'validated':False,'submission_ready':False}
    return raw,manifest,prep

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('child',choices=sorted(NODES));g=parser.add_mutually_exclusive_group(required=True)
    g.add_argument('--prepare-source',action='store_true');g.add_argument('--check-source',action='store_true');g.add_argument('--prepare-snapshot',action='store_true');a=parser.parse_args()
    evidence,checker=parent(a.child);p=paths(a.child)
    if a.prepare_source:
        raw,manifest,prep=source_documents(a.child,evidence,checker)
        original.exact_io.write_exact(p['source'],raw);context.write_exact(p['source_manifest'],manifest);context.write_exact(p['source_preparation'],prep)
        source_replay(a.child,evidence,checker)
    elif a.check_source:prep=source_replay(a.child,evidence,checker)
    else:
        source_replay(a.child,evidence,checker)
        pf=context.record(p['source'],p['source_manifest'],'emit-olean',p['module'],p['stage'])
        raw,manifest,prep=snapshot_documents(a.child,evidence,pf)
        original.exact_io.write_exact(p['snapshot'],raw);context.write_exact(p['snapshot_manifest'],manifest);context.write_exact(p['snapshot_preparation'],prep)
    print(json.dumps(prep,indent=2))

if __name__=='__main__':main()
