"""Record checked local proof and remote graph states separately."""
from datetime import datetime,timezone
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
VER=HERE/'verification'
graph=json.loads((VER/'graph-check.json').read_text(encoding='utf-8'))
assert graph['proved_theorem_count']==14 and graph['main_goal_status']=='Open'
assert len(graph['verified_paths'])==15
build=(VER/'closed-machine-build-final.txt').read_text(encoding='utf-8')
assert 'Build completed successfully' in build
cover=(VER/'concrete-cover-build.txt').read_text(encoding='utf-8')
assert 'Build completed successfully' in cover
standard='[propext, Classical.choice, Quot.sound]'
assert "Sol_ThreeSum1960614_concrete_local_cover.lean:18:0: 'solution' depends on axioms: "+standard in cover
names=['ThreeSum1960614.quartic_parameter_certificate','ThreeSum1960614.integer_schedule',
       'ThreeSum1960614.executable_scale_limits','ThreeSum1960614.local_cover_bounds']
for name in names:
    assert "'"+name+"' depends on axioms: "+standard in build
for file in ['Sol_ThreeSum1960614_closed_analysis.lean',
             'Sol_ThreeSum1960614_quartic_program_contract.lean',
             'Sol_ThreeSum1960614_actual_quartic_program.lean']:
    assert any(file in line and "'solution' depends on axioms: "+standard in line
        for line in build.splitlines()), file
analysis=(ROOT/'Definitions/Def_ThreeSum1960614_Analysis.lean').read_text(encoding='utf-8')
narrow=(HERE/'machine/lean/Submission/ThreeSum/AnalysisDefinitions.lean').read_text(encoding='utf-8')
assert analysis[analysis.index('set_option'):]==narrow[narrow.index('set_option'):]
def read(name): return json.loads((VER/name).read_text(encoding='utf-8'))
actual_edges=[]
for path in graph['verified_paths']:
    actual_edges.append(path)
planned=[['integer_schedule','actual_quartic_program'],
 ['executable_scale_limits','costs_solve_3sum'],
 ['actual_quartic_program','costs_solve_3sum'],
 ['local_cover_bounds','costs_solve_3sum']]
plan={'status':'15 actual verified paths; machine connections below remain planned',
 'actual_verified_paths':actual_edges,'planned_machine_edges':planned,
 'independent_roots':['fixed_model_lower_bound'],'remote_graph_complete':False,
 'note':'Actual graph edges come from accepted submissions, not from this plan. Local machine modules have not been uploaded as a complete project.'}
(VER/'graph-plan.json').write_text(json.dumps(plan,indent=2)+'\n',encoding='utf-8')
files={}
for p in (HERE/'machine/lean').rglob('*.lean'):
    assert 'sorry' not in p.read_text(encoding='utf-8'),p
    files[p.relative_to(ROOT).as_posix()]=hashlib.sha256(p.read_bytes()).hexdigest()
result={'recorded_at_utc':datetime.now(timezone.utc).isoformat(),
 'accepted_supporting_nodes':14,'verified_remote_paths':15,'main_goal_proved':False,
 'closed_analytic_kernel_axioms':['propext','Classical.choice','Quot.sound'],
 'quartic_light_program_kernel_axioms':['propext','Classical.choice','Quot.sound'],
 'actual_depth_program_kernel_axioms':['propext','Classical.choice','Quot.sound'],
 'concrete_local_cover_kernel_axioms':['propext','Classical.choice','Quot.sound'],
 'local_main_goal_proved':read('machine-integration-progress.json')['complete_word_ram_goal_proved'],
 'complete_word_ram_bridge_proved':read('machine-integration-progress.json')['universal_machine_cost_bridge_proved'],
 'big_o_speedrun_submitted':read('machine-integration-progress.json')['bigospeedrun_submitted'],
 'big_o_speedrun_official_lean_verified':read('machine-integration-progress.json')['bigospeedrun_official_lean_verified'],
 'big_o_speedrun_official_nanoda_passed':read('machine-integration-progress.json')['bigospeedrun_official_nanoda_passed'],
 'source_hashes':files,'closed_proofs':read('closed-analysis-manifest.json'),
 'remaining':read('machine-integration-progress.json')['remaining']}
model_graph=VER/'model-graph-check.json'
if model_graph.exists():
    model=read('model-graph-check.json')
    assert model['model_branch_complete']
    result['independent_model_branch']=model
    result['accepted_supporting_nodes']+=len(model['proved_theorems'])
    result['verified_remote_paths']+=len(model['verified_paths'])
    plan['independent_model_branch']=model
    plan['actual_verified_paths'].extend(model['verified_paths'])
    plan['status']=str(len(plan['actual_verified_paths']))+' actual verified paths; full machine connections remain planned'
    (VER/'graph-plan.json').write_text(json.dumps(plan,indent=2)+'\n',encoding='utf-8')
(VER/'verified-progress.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print('Recorded local complete proof and',result['accepted_supporting_nodes'],
      'remote accepted nodes,',result['verified_remote_paths'],'actual graph paths. Remote main goal remains Open.')
