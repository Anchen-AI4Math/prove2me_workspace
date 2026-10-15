"""Bind the official dual-kernel pass to this exact submitted source and model."""
from datetime import datetime,timezone
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
VER=HERE/'verification'
FINAL=VER/'bigospeedrun-official-final'
read=lambda p:json.loads(p.read_text(encoding='utf-8'))
r=read(FINAL/'receipt.json')
request=read(FINAL/'selected-request.json')
download=read(FINAL/'download-receipt.json')
source=read(FINAL/'source-sha256.json')
package=read(VER/'bigospeedrun-package-receipt.json')
expected={p:h for p,h in package['package_hashes'].items() if p.endswith('.lean')}
assert source==expected, 'Official verifier did not check the exact staged Lean source set'
assert r['status']=='passed' and r['verification_stage']=='final' and r['test_only'] is False
assert r['request']['repo_url']=='https://github.com/Anchen0823/three-sum-1960614'
assert r['request']['commit']=='8c25c0325de5be4286413f39ca0c9278aad33f52'
assert r['request']['direct_submission']['bound']=='980307/500000'
assert r['request']['direct_submission']['problem']=='3sum'
assert r['profile']['challenge_sha256']=='4291e3f05781cea42f9d672ff73ceac1f6d1a0c3021038e94372fa8f7e1ad987'
assert r['profile']['lean_toolchain']=='leanprover/lean4:v4.33.1'
assert r['verifier_commit']=='51489ee2ac82596a41375e92ea8108814f931242'
assert r['theorem_names']==['Race.bound']
for kernel in ['lean','nanoda']:
    assert r['kernels'][kernel]['status']=='passed'
    assert r['kernels'][kernel]['reason']=='comparator_acceptance'
    assert r['kernels'][kernel]['exit_code']==0
assert r['axiom_audit']['status']=='passed' and r['axiom_audit']['exit_code']==0
assert set(r['axiom_audit']['reported_axioms']['Race.bound'])=={'propext','Classical.choice','Quot.sound'}
assert request['issue_number']==8 and request['test_only'] is False
assert request['inputs']==r['request']
assert request['submission']['commit']==r['request']['commit']
assert download['run_id']==38567645711 and download['artifact_id']==11904143134
for record in download['files']:
    assert hashlib.sha256((FINAL/record['path']).read_bytes()).hexdigest()==record['sha256']
result={'audited_at_utc':datetime.now(timezone.utc).isoformat(),
        'official_checked_at_utc':r['checked_at'],'source_commit':r['request']['commit'],
        'source_files_matched':len(source),'bound':'980307/500000','problem':'3sum',
        'theorem':'Race.bound','lean_kernel_passed':True,'nanoda_kernel_passed':True,
        'axiom_audit_passed':True,'comparator_passed':True,
        'axioms':['propext','Classical.choice','Quot.sound'],
        'run_url':r['run_url'],'receipt_artifact_id':11904143134,
        'receipt_sha256':hashlib.sha256((FINAL/'receipt.json').read_bytes()).hexdigest(),
        'artifact_archive_sha256':download['archive_sha256'],
        'site_data_checked':False}
(VER/'bigospeedrun-official-audit.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
state_path=VER/'bigospeedrun-submission.json'
state=read(state_path)
state.update(official_lean_verified=True,official_nanoda_passed=True,
             official_comparator_passed=True,official_axiom_audit_passed=True,
             verification_run_id=38567645711,verification_run_url=r['run_url'],
             final_receipt_artifact_id=11904143134,
             official_checked_at_utc=r['checked_at'])
state_path.write_text(json.dumps(state,indent=2)+'\n',encoding='utf-8')
package.update(comparator_passed=True,official_fresh_build_and_verification_passed=True,
               official_lean_kernel_passed=True,official_nanoda_kernel_passed=True,
               official_receipt='verification/bigospeedrun-official-final/receipt.json')
(VER/'bigospeedrun-package-receipt.json').write_text(json.dumps(package,indent=2)+'\n',encoding='utf-8')
download['official_receipt_fields_not_yet_audited']=False
(FINAL/'download-receipt.json').write_text(json.dumps(download,indent=2)+'\n',encoding='utf-8')
print('Official pass audited:',len(source),'exact Lean files, Lean + nanoda + standard-three-axiom audit.')
