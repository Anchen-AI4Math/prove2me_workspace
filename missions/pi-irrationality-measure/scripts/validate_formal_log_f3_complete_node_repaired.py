"""Certify f3 with the frozen baseline and three individually certified CIs.

The baseline checker, its f2 certificate, and all f3 compiler inputs remain
immutable. This adapter extends only the reference-domain consumer after full
same-current-input validation of the source/generated companion certificate.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
from unittest.mock import patch
import validate_formal_log_f3_complete_node as retained
import validate_formal_log_successor_node as baseline
import validate_formal_log_f3_extra_ci as extra
import validate_namespace_context_providers as context

TASK,V=baseline.TASK,baseline.V
SELF=Path(__file__).resolve()
STAGE=V/'flp3/f3'
CERT_NAME='complete-node-validation.json'
BASELINE_SHA='20f761f0d169c7af296faea379bb7547909abd56f79d0bdba03a207d7617bfb4'
RETAINED_SHA='3f8d5c18bab76b26888d1e9d87a8bce56bf243b448fb3c1ecc1487f947d944b5'
EXTRA_CHECKER_SHA='c7681f2a0bac9521d0ef52fc2633e071bcce3ffac0c91cfd82d73cd07717f76d'
read,sha,rel,fail=context.read,context.sha,context.rel,context.fail

def certify():
    fail(sha(Path(retained.__file__))!=RETAINED_SHA,'Retained first adapter changed')
    fail(sha(Path(baseline.__file__))!=BASELINE_SHA or sha(Path(extra.__file__))!=EXTRA_CHECKER_SHA,
         'Frozen baseline/extra-CI consumer changed')
    m=read(STAGE/'manifest.json')
    definitions,provided=baseline.base.definition_interfaces(m)
    child=baseline.child_interface()
    auxiliary=extra.validate_extra_ci(definitions)
    names=auxiliary['data']['provided_names']
    fail(names!=extra.gen.REQUIRED+[extra.gen.AUX] or len(set(names))!=3 or set(names)&set(provided),
         'Only the three separate actual-certified auxiliary CIs may extend the reference domain')
    # The frozen checker still performs all source/statement/solution/inline,
    # ownership, actual preflight, universes, Std3 and proof-reference checks.
    # Only the source of the allowed CI Name set is adapted, and every added
    # Name is backed by the complete paired CI certificate validated above.
    def reviewed_interfaces(actual):
        fail(actual!=m,'Unexpected node manifest passed to auxiliary adapter')
        return definitions,dict(provided, **{r['name']: r['source_owner']['module'] for r in auxiliary['data']['comparisons']})
    with patch.object(baseline.base,'definition_interfaces',reviewed_interfaces), \
         patch.object(baseline,'child_interface',lambda:child):
        c=baseline.certify(STAGE)
    # Keep provided ordinary Definition names distinct from certified
    # compiler-generated theorem companions in the saved certificate.
    c['artifact_kind']='formal-log-f3-complete-proof-node-kernel-certificate'
    c['actual_definition_provided_names']=provided
    c['actual_auxiliary_provided_names']=names
    c['auxiliary_ci_certificate']={'path':auxiliary['path'],'sha256':auxiliary['sha256']}
    c['auxiliary_ci_comparisons']=auxiliary['data']['comparisons']
    c['baseline_checker']={'path':rel(Path(baseline.__file__)),'sha256':BASELINE_SHA,
        'reference_domain_only_adapter':True,'all_original_checks_replayed':True}
    c['implementation_hashes'].update({rel(SELF):sha(SELF),rel(Path(extra.__file__)):sha(Path(extra.__file__)),
        rel(Path(extra.gen.__file__)):sha(Path(extra.gen.__file__)),
        rel(Path(extra.compatible.__file__)):sha(Path(extra.compatible.__file__))})
    c['input_hashes']=dict(c['input_hashes'])
    c['input_hashes'][auxiliary['path']]=auxiliary['sha256']
    c['implementation_hashes'][rel(Path(retained.__file__))]=RETAINED_SHA
    c['retained_first_adapter']={'path':rel(Path(retained.__file__)),'sha256':RETAINED_SHA,'failure_before_certificate':'dict plus list in allowed-reference mapping adapter'}
    return c

def validate_formal_f3_node(stage=STAGE):
    fail(baseline.stage_path(stage)!=STAGE.resolve(),'Only exact f3 stage supported')
    c=certify();p=STAGE/CERT_NAME
    fail(not p.is_file() or read(p)!=c,'Complete f3 certificate missing/stale after full readonly replay')
    m=read(STAGE/'manifest.json')
    return {'stage':STAGE,'manifest':STAGE/'manifest.json','manifest_data':m,
        'certificate':{'path':rel(p),'sha256':sha(p),'data':c},
        'statement_bytes':(baseline.ROOT/m['statement']).read_bytes(),
        'solution_bytes':(baseline.ROOT/m['solution']).read_bytes(),
        'source_command_witness':c['source_command_witness'],'validated':True,
        'server_parent_pending':True,'submission_ready':False}

def main():
    p=argparse.ArgumentParser(description=__doc__);g=p.add_mutually_exclusive_group(required=True)
    g.add_argument('--certify-existing',action='store_true');g.add_argument('--validate-only',action='store_true');a=p.parse_args()
    try:
        if a.certify_existing:
            c=certify();path=STAGE/CERT_NAME;context.write_exact(path,c);r={'path':rel(path),'sha256':sha(path),'data':c}
        else:r=validate_formal_f3_node()['certificate']
        print(json.dumps({'validated':True,'certificate':r['path'],'sha256':r['sha256'],
            'actual_auxiliary_provided_names':r['data']['actual_auxiliary_provided_names'],
            'max_file_seconds':r['data']['max_file_seconds'],'submission_ready':False},indent=2))
    except (ValueError,KeyError,StopIteration,FileNotFoundError,TypeError) as e:
        print(json.dumps({'validated':False,'error':str(e)}));raise SystemExit(2)

if __name__=='__main__':main()
