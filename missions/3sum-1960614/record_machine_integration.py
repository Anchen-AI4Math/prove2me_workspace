"""Record only successful exact machine-component builds and their axioms."""
from datetime import datetime,timezone
import hashlib
import json
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
VER=HERE/'verification'
standard='[propext, Classical.choice, Quot.sound]'
checks={
 'machine_scale_rates':'machine-scale-rates-build.txt',
 'machine_band_rates':'machine-band-rates-build-final.txt',
 'machine_local_schedule':'machine-band-rates-build-final.txt',
 'machine_size_initializer':'machine-size-initializer-build.txt',
 'integrated_switch_bounds':'integrated-switch-build-next.txt',
 'integrated_switch_program':'integrated-switch-build-next.txt',
 'machine_global_initializer':'machine-global-initializer-build-next.txt',
 'machine_global_encoding':'machine-global-encoding-build.txt',
 'parameter_initializer':'parameter-initializer-build.txt'}
optional='local-cover-initializer-build-next.txt'
if (VER/optional).exists() and 'Build completed successfully' in (VER/optional).read_text(encoding='utf-8'):
    checks['local_cover_initializer']=optional
for name,filename in {'hierarchy_rates':'stage-rates-build-next.txt',
                      'stage_rates':'stage-rates-build-next.txt',
                      'arithmetic_rates':'arithmetic-resources-build-next.txt',
                      'switch_resources':'arithmetic-resources-build-next.txt'}.items():
    if (VER/filename).exists() and 'Build completed successfully' in (VER/filename).read_text(encoding='utf-8'):
        checks[name]=filename
partial='full-machine-build.txt'
if (VER/partial).exists():
    log=(VER/partial).read_text(encoding='utf-8')
    for name in ('hierarchy_rates','stage_rates','arithmetic_rates','switch_resources','raw_cost_exponent'):
        module='Solutions.Sol_ThreeSum1960614_'+name
        if any(('Built '+module in line or 'Replayed '+module in line) for line in log.splitlines()) and any(
            module.removeprefix('Solutions.')+'.lean:' in line and
            "'solution' depends on axioms: "+standard in line for line in log.splitlines()):
            checks[name]=partial
complete='full-machine-build-fifth.txt'
complete_passed=False
if (VER/complete).exists():
    full_log=(VER/complete).read_text(encoding='utf-8')
    complete_passed='Build completed successfully (9447 jobs).' in full_log
    if complete_passed:
        for proof in (ROOT/'Solutions').glob('Sol_ThreeSum1960614_*.lean'):
            if any(proof.name in line and "'solution' depends on axioms: "+standard in line
                   for line in full_log.splitlines()):
                checks[proof.stem.removeprefix('Sol_ThreeSum1960614_')]=complete
records={}
for name,filename in checks.items():
    log=(VER/filename).read_text(encoding='utf-8')
    module='Solutions.Sol_ThreeSum1960614_'+name
    module_passed=any(('Built '+module in line or 'Replayed '+module in line) for line in log.splitlines())
    assert 'Build completed successfully' in log or (filename==partial and module_passed),filename
    proof=ROOT/'Solutions'/('Sol_ThreeSum1960614_'+name+'.lean')
    assert any(proof.name in line and "'solution' depends on axioms: "+standard in line for line in log.splitlines()),name
    code=proof.read_text(encoding='utf-8')
    assert 'sorry' not in code
    records[name]={'build_log':filename,'proof_path':proof.relative_to(ROOT).as_posix(),
       'proof_sha256':hashlib.sha256(proof.read_bytes()).hexdigest(),
       'complete_scoped_build_passed':'Build completed successfully' in log,
       'component_module_passed':module_passed,
       'axioms':['propext','Classical.choice','Quot.sound']}
hashes={p.relative_to(ROOT).as_posix():hashlib.sha256(p.read_bytes()).hexdigest()
    for p in (HERE/'machine/lean').rglob('*.lean')}
full_targets={'complete_machine_goal','machine_cost_bridge','model_bound'}
full_proved=complete_passed and full_targets <= records.keys()
submission_file=VER/'bigospeedrun-submission.json'
submission=(json.loads(submission_file.read_text(encoding='utf-8'))
            if submission_file.exists() else {})
model_graph_file=VER/'model-graph-check.json'
model_graph=(json.loads(model_graph_file.read_text(encoding='utf-8'))
             if model_graph_file.exists() else {})
result={'recorded_at_utc':datetime.now(timezone.utc).isoformat(),'verified_components':records,
 'source_hashes':hashes,'complete_word_ram_goal_proved':full_proved,
 'complete_scoped_build_passed':complete_passed,
 'universal_machine_cost_bridge_proved':full_proved,
 'independent_fixed_model_lower_bound_proved':full_proved,
 'bigospeedrun_submitted':submission.get('submitted',False),
 'bigospeedrun_submission_issue':submission.get('issue_url'),
 'bigospeedrun_official_lean_verified':submission.get('official_lean_verified',False),
 'bigospeedrun_official_nanoda_passed':submission.get('official_nanoda_passed',False),
 'platform_machine_upload_complete':False,
 'platform_independent_model_branch_complete':model_graph.get('model_branch_complete',False),
 'remaining':('Prove2Me exact-text transplantation and remote graph verification'
              if submission.get('official_lean_verified') else
              'Prove2Me exact-text transplantation and remote graph verification; official independent Big O Speedrun validation')}
(VER/'machine-integration-progress.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print('Recorded',len(records),'standard-axiom solution contracts. Local exact word-RAM goal proved:',full_proved)
