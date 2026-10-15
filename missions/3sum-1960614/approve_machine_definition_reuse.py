"""Seal faithful public definition reuse after interface and kernel checks."""
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
VER=HERE/'verification'
ROOT=HERE.parents[1]
MODULES={
 'Submission.EndStatement':('Definitions.Def_TrulySubcubicAPSP_SourceSpecification',None),
 'Submission.ThreeSumApsp.Lang.Syntax':('Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax','c7e5fc80-c454-4ef5-a6b8-50ad42ba2c3a'),
 'Submission.ThreeSumApsp.Lang.Logic':('Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic','0f0fb5b6-9dcf-4a34-8f0f-c60b941eec9d'),
 'Submission.ThreeSum.AnalysisDefinitions':('Definitions.Def_ThreeSum1960614_Analysis','4f989e3e-71e0-4d7d-ad99-06cb29a25354')}

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def load(side):return {r['name']:r for r in map(json.loads,(VER/f'reuse-interfaces-{side}.jsonl').read_text(encoding='utf-8').splitlines())}
a,b=load('native'),load('platform')
report=json.loads((VER/'reuse-primary-definition-comparison.json').read_text(encoding='utf-8'))
log=(VER/'reuse-generated-equalities-check.txt').read_text(encoding='utf-8')
assert ': error:' not in log and 'error(' not in log
for i,name in enumerate(('Light.Op.noConfusion','Light.instDecidableEqOp')):
    assert 'Kernel checked definition-body equality: '+name in log
    assert f"'ThreeSum1960614.ReuseAudit.interface_{i}' does not depend on any axioms" in log
special={'Light.Op.noConfusion','Light.instDecidableEqOp'}
names=report['source_backed_definition_names']
assert len(names)==229 and set(report['unmatched_source_backed_definitions'])==special
approved={}
for name in names:
    assert name in a and name in b
    if name not in special:
        assert a[name]['alphaType']==b[name]['alphaType'],name
        assert a[name]['matcherValue']==b[name]['matcherValue'],name
    native=a[name]['module']
    assert native in MODULES
    module,tid=MODULES[native]
    assert b[name]['module']==module
    approved[name]={'native_module':native,'definition_module':module,'theorem_id':tid,
                    'check':'kernel-definitional-equality' if name in special else 'exact-alpha-type-and-matcher-normal-value'}

manifest={'approved':True,'source_definition_count':len(approved),'definitions':approved,
          'modules':{m:{'definition_module':v[0],'theorem_id':v[1],
                       'native_sha256':sha(HERE/'machine/lean'/Path(*m.split('.')).with_suffix('.lean')),
                       'public_sha256':sha(ROOT/Path(*v[0].split('.')).with_suffix('.lean'))}
                     for m,v in MODULES.items()},
          'evidence':{p:sha(VER/p) for p in ['reuse-interfaces-native.jsonl','reuse-interfaces-platform.jsonl',
                     'reuse-generated-equalities-check.txt','check_reuse_generated_equalities.lean']},
          'normalization':'Erase binder labels and metadata; expand only Lean-recognized matchers with beta reduction. Two generated-body equalities are separately kernel checked without axioms. No user constant is substituted.'}
(VER/'machine-definition-reuse.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
print('Approved faithful reuse of',len(approved),'source-backed definition interfaces in four public bundles.')
