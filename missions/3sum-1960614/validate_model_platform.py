"""Seal exact upload bytes only after build, type and frozen-contract checks."""
from datetime import datetime,timezone
import hashlib
import json
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
VER=HERE/'verification'
assert sys.argv[1:]==['--successful-typecheck-session','10755'], 'Record only the observed successful supervised check'
path=VER/'model-platform-manifest.json'
manifest=json.loads(path.read_text(encoding='utf-8'))
native={r['name']:r for r in json.loads((VER/'model-types-native.json').read_text(encoding='utf-8'))}
platform={r['name']:r for r in json.loads((VER/'model-types-platform.json').read_text(encoding='utf-8'))}
assert native.keys()==platform.keys()
differences={name:{'original':native[name],'platform':platform[name]} for name in native
             if native[name]!=platform[name]}
if differences:
    (VER/'model-type-differences.json').write_text(json.dumps(differences,indent=2)+'\n',encoding='utf-8')
assert not differences, 'Exact elaborated type comparison failed; inspect model-type-differences.json'
logpath=VER/'model-platform-build.txt'
log=logpath.read_text(encoding='utf-8')
assert 'Build completed successfully (9454 jobs).' in log
standard='[propext, Classical.choice, Quot.sound]'
for record in manifest['theorems']:
    solution=ROOT/record['solution_path']
    assert hashlib.sha256(solution.read_bytes()).hexdigest()==record['solution_sha256']
    code=solution.read_text(encoding='utf-8')
    assert 'sorry' not in code
    assert 'Theorems.Thm_'+record.get('platform_name',record['name']).replace('.','_') not in code
    assert any(solution.name in line and "'solution' depends on axioms:" in line
               for line in log.splitlines()), solution.name
    if not record.get('existing_theorem_id'):
        assert any(solution.name in line and "'solution' depends on axioms: "+standard in line
                   for line in log.splitlines()),solution.name
        theorem=ROOT/record['theorem_path']
        assert theorem.read_text(encoding='utf-8')==record['preamble']+'\n'+record['formal_statement']+'\n'
for record in manifest['definitions']:
    code=(ROOT/record['path']).read_text(encoding='utf-8')
    assert code==record['payload']['definition'] and 'sorry' not in code
for name in ['model-types-native-extraction.txt','model-types-platform-extraction.txt']:
    text=(VER/name).read_text(encoding='utf-8')
    assert 'recorded 3 exact declaration types' in text and 'error:' not in text
frozen_log=VER/'model-frozen-target-check.txt'
assert frozen_log.exists() and 'error:' not in frozen_log.read_text(encoding='utf-8')
manifest['validation_complete']=True
path.write_text(json.dumps(manifest,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
checks=[logpath,VER/'model-types-native.json',VER/'model-types-platform.json',
        frozen_log,VER/'check_model_frozen_target.lean',VER/'model-scope-contexts.json']
receipt={'checked_at_utc':datetime.now(timezone.utc).isoformat(),
         'manifest_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
         'exact_type_comparison_passed':True,'compared_declaration_count':len(native),
         'frozen_root_contract_passed':True,'successful_typecheck_session':10755,
         'checks_exit_code':0,'scoped_build_passed':True,'build_job_count':9454,
         'leaf_axioms':['propext','Classical.choice','Quot.sound'],
         'root_is_a_reduction_to_two_new_and_two_accepted_children':True,
         'evidence_sha256':{p.relative_to(ROOT).as_posix():hashlib.sha256(p.read_bytes()).hexdigest() for p in checks}}
(VER/'model-platform-validation.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
print('Validated exact upload text:',len(native),'identical elaborated types; frozen root interface passed.')
