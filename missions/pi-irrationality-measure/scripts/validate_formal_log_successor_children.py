"""Readonly kernel certificates for the actually proved c2/c3 child modules."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch
import stage_formal_log_successor_children as emitter
import validate_formal_log_proved_child as original
import validate_formal_log_node as base
import validate_formal_log_truncation_provider as formalci
import validate_namespace_context_providers as context
import validate_standalone_platform_node as standalone

TASK,ROOT,V=emitter.TASK,emitter.ROOT,emitter.V
SELF=Path(__file__).resolve()
PRODUCER_SHA='36e3e5b1600eee918f51062ea3390674bb9a23a7d309ad94683bc539a94b8114'
OLD_CHECKER_SHA='828afd8a0b732b1e222a67a60e52f60d09d15ac14d784cfd5c9c6075fa462ac0'
CERT_NAME='proved-child-validation.json'
sha,read,rel,fail=context.sha,context.read,context.rel,context.fail

def certify(which):
    fail(sha(Path(emitter.__file__))!=PRODUCER_SHA or sha(Path(original.__file__))!=OLD_CHECKER_SHA,
         'Frozen successor child producer/imported proof consumer changed')
    evidence,checker=emitter.parent(which);c=evidence['certificate']['data'];p=emitter.paths(which)
    prep=emitter.source_replay(which,evidence,checker)
    source_pf=context.record(p['source'],p['source_manifest'],'emit-olean',p['module'],p['stage'])
    raw,manifest,snapshot_prep=emitter.snapshot_documents(which,evidence,source_pf)
    fail(p['snapshot'].read_bytes()!=raw or read(p['snapshot_manifest'])!=manifest or read(p['snapshot_preparation'])!=snapshot_prep,
         'Exact imported successor child snapshot source/preparation/manifest differs')
    snapshot_pf=context.record(p['snapshot'],p['snapshot_manifest'],'modecheck','ChildSnapshot',p['stage'])
    olean=V/'staged-build/lib/lean'/Path(*p['module'].split('.')).with_suffix('.olean')
    dep=next(d for d in snapshot_pf['data']['dependency_oleans'] if d['module']==p['module'])
    fail(dep['sha256_before']!=sha(olean) or source_pf['data']['output_olean_sha256']!=sha(olean),
         'Imported child snapshot does not use the exact emitted proved OLean')
    parent_stage=evidence['stage'];parent_pf=c['preflights']['SnapshotGeneratedWithRefs.lean']
    parent_types=base.kernel_rows(parent_stage/'generated-type.json',[p['theorem'],'solution'],parent_pf)
    child_types=base.kernel_rows(p['types'],[p['theorem']],snapshot_pf)
    base.same_type(parent_types[0],parent_types[1]);base.same_type(parent_types[0],child_types[0])
    fail(c['output_json_sha256']['proof-references.json']!=sha(parent_stage/'proof-references.json'),
         'Parent actual proof output differs from certified current file')
    parent_solution=next(r for r in read(parent_stage/'proof-references.json')['rows'] if r['name']=='solution')
    # Reuse only the immutable c1 reader's strict imported CI document schema,
    # with two exact identity constants replaced in memory after parent replay.
    with patch.object(original,'emitter',SimpleNamespace(THEOREM=p['theorem'],MODULE=p['module'])):
        proof=original.proof_row(p['refs'],snapshot_pf)
    for field in ['levelParams','typeRefs','valueRefs']:
        fail(proof[field]!=parent_solution[field],'Imported successor proof refs/universes differ from exact parent solution: '+field)
    fail(set(proof['axioms'])!=set(parent_solution['axioms']) or len(proof['axioms'])!=len(parent_solution['axioms']),
         'Imported successor proof axioms differ from exact parent solution')
    fail(proof['levelParams']!=child_types[0]['levelParams'],'Imported proof binders differ from same-run structural type snapshot')
    from formal_log_node_refs import kernel_refs
    fail(set(proof['typeRefs'])!=kernel_refs(child_types[0]['type']),'Actual imported child type refs differ from structural type')
    audits={'source':standalone.audit_axioms(context.file(source_pf['data']['log']),p['theorem']),
            'snapshot':standalone.audit_axioms(context.file(snapshot_pf['data']['log']),p['theorem'])}
    fail(any(set(a)!=context.STD3 for a in audits.values()) or set(proof['axioms'])!=context.STD3,
         'Source and imported successor proofs are not exact Std3')
    names=set(proof['typeRefs']+proof['valueRefs']);provided=set(c['actual_definition_provided_names'])
    project=sorted(n for n in names if n in provided or n.startswith(('OAI.','Definitions.','Theorems.','Solutions.','_private.OAI.')))
    fail(not set(project)<=set(c['allowed_project_names']) or p['theorem'] in names or 'solution' in names,
         'Imported successor proof uses uncertified project CIs or target/solution stubs')
    return {'schema_version':1,'artifact_kind':'formal-log-proved-successor-child-kernel-certificate','validated':True,
        'parent_node':emitter.NODES[which],'parent_node_certificate':evidence['certificate']['path'],
        'parent_node_certificate_sha256':evidence['certificate']['sha256'],'theorem_name':p['theorem'],'module':p['module'],
        'source':rel(p['source']),'source_sha256':sha(p['source']),'source_manifest':rel(p['source_manifest']),
        'source_manifest_sha256':sha(p['source_manifest']),'source_preparation':rel(p['source_preparation']),
        'source_preparation_sha256':sha(p['source_preparation']),'output_olean':rel(olean),'output_olean_sha256':sha(olean),
        'snapshot':rel(p['snapshot']),'snapshot_sha256':sha(p['snapshot']),'snapshot_manifest':rel(p['snapshot_manifest']),
        'snapshot_manifest_sha256':sha(p['snapshot_manifest']),'snapshot_preparation':rel(p['snapshot_preparation']),
        'snapshot_preparation_sha256':sha(p['snapshot_preparation']),'child_type_output':rel(p['types']),
        'child_type_output_sha256':sha(p['types']),'child_proof_references':rel(p['refs']),'child_proof_references_sha256':sha(p['refs']),
        'literal_edit_count':len(prep['edit_ledger']),'exact_certified_solution_rebinding':True,'statement_stub_imported':False,
        'actual_imported_owner':True,'actual_imported_owner_evidence':proof['owner'],
        'kernel_type_equal_to_parent_source_target_solution':True,'proof_type_refs_equal_to_parent_solution':True,
        'proof_value_refs_equal_to_parent_solution':True,'proof_self_reference_absent':True,'actual_project_refs':project,
        'allowed_project_names':c['allowed_project_names'],'Std3_only':True,'axioms':audits,'source_preflight':source_pf,
        'snapshot_preflight':snapshot_pf,'max_file_seconds':max(source_pf['data']['seconds'],snapshot_pf['data']['seconds']),
        'implementation_hashes':{rel(x):sha(x) for x in [SELF,Path(emitter.__file__),Path(original.__file__),Path(checker.__file__),Path(base.__file__),Path(formalci.__file__),Path(context.__file__),Path(standalone.__file__)]},
        'server_parent_pending':True,'submission_ready':False,'source_scope_partial':True}

def validate_successor_child(which):
    c=certify(which);p=emitter.paths(which)['stage']/CERT_NAME
    fail(not p.is_file() or read(p)!=c,'Successor proved child certificate missing/stale after readonly replay')
    return {'certificate':{'path':rel(p),'sha256':sha(p),'data':c},'validated':True,'submission_ready':False}

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('child',choices=sorted(emitter.NODES));g=p.add_mutually_exclusive_group(required=True)
    g.add_argument('--certify-existing',action='store_true');g.add_argument('--validate-only',action='store_true');a=p.parse_args()
    try:
        if a.certify_existing:
            c=certify(a.child);path=emitter.paths(a.child)['stage']/CERT_NAME;context.write_exact(path,c);r={'path':rel(path),'sha256':sha(path),'data':c}
        else:r=validate_successor_child(a.child)['certificate']
        print(json.dumps({'validated':True,'certificate':r['path'],'sha256':r['sha256'],'max_file_seconds':r['data']['max_file_seconds'],'submission_ready':False},indent=2))
    except (ValueError,KeyError,StopIteration,FileNotFoundError,TypeError) as e:
        print(json.dumps({'validated':False,'error':str(e)}));raise SystemExit(2)

if __name__=='__main__':main()
