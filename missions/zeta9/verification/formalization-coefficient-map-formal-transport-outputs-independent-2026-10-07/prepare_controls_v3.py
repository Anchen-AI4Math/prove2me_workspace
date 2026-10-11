import re,sys
import inspect_prepare as p
from prepare_controls import save
sys.stdout.reconfigure(encoding='utf-8')
old=p.load(p.OUT/'control-preparation-v2.json')
a=p.load(p.AUTHOR/'author-audit.json')
original=(p.TASK/'formalization/CoefficientMapFormalTransportOutputs.lean').read_text(encoding='utf-8-sig')
actual=(p.AUTHOR/'OutputsVerifiedSource.lean').read_text(encoding='utf-8-sig')
assert len(re.findall(r'^theorem\s+\w+',original,re.M))==16
for row in old['original_exact_headers']:
 assert original.count(row['header']+' :=')==1
 assert actual.count(row['header']+' :=')==1
assertion=(p.PROJECT/old['assertions']['project_relative']).read_text(encoding='utf-8')
assert assertion.count('open ZetaNine.CoefficientMapFormalTransportOutputs\n')==1
assertion=assertion.replace('open ZetaNine.CoefficientMapFormalTransportOutputs\n','open ZetaNine.CoefficientMapFormalTransportOutputs\nopen ZetaNine.HarmonicStability\n')
for row in old['original_exact_headers']:
 assert assertion.count(row['header'].replace('theorem '+row['name'],'theorem expected_'+row['name'],1)+' :=')==1
r=save('OutputsIndependentAssertionsV2',assertion)
semantic=(p.PROJECT/old['semantic']['project_relative']).read_text(encoding='utf-8')
assert semantic.count('import OutputsIndependentAssertionsV1\n')==1
semantic=semantic.replace('import OutputsIndependentAssertionsV1\n','import OutputsIndependentAssertionsV2\n').replace('`OutputsIndependentAssertionsV1]','`OutputsIndependentAssertionsV2]')
s=save('OutputsIndependentSemanticV3',semantic)
plan=dict(old);plan['assertions']=r;plan['semantic']=s
plan['helper_modules']=[x if x!='OutputsIndependentAssertionsV1' else 'OutputsIndependentAssertionsV2' for x in plan['helper_modules']]
plan['repair']='First actual assertions compiler call failed only because original unqualified harmonicPower namespace was not opened in independently generated assertion context; private V2 adds open ZetaNine.HarmonicStability. All 16 original theorem headers unchanged and personally compared literally with original shared source and verified source. Semantic private V3 updates imported assertions module and actual helper inventory module accordingly; original source/control files/failure logs untouched.'
plan['whole_failed_assertions_run_preserved']='actual-runs/c025-a01; whole failed run excluded; no assertion object produced'
plan['assertions_header_original_and_verified_literal_comparison']=True
p.dump(p.OUT/'control-preparation-v3.json',plan)
print('Private V2 assertion context and V3 semantic created;16 exact original headers remain literally unchanged.')
