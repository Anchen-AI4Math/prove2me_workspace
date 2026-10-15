"""Supervised exact-type gate; failed or interrupted runs never seal a payload."""
import argparse
from datetime import datetime,timezone
import json
import os
from pathlib import Path
import subprocess
import sys
from machine_skeleton import HERE,VER,ROOT,sha

parser=argparse.ArgumentParser()
parser.add_argument('--model-regression',action='store_true')
parser.add_argument('--scope-regression',action='store_true')
parser.add_argument('--compiled-solutions',action='store_true')
args=parser.parse_args()
assert not (args.model_regression and args.scope_regression)
stem=('machine-scope-regression' if args.scope_regression else
      'machine-regression' if args.model_regression else 'machine-platform')
manifest_path=VER/(stem+'-manifest.json')
manifest=json.loads(manifest_path.read_text(encoding='utf-8'))
for record in manifest['definitions']:
    assert sha((ROOT/record['path']).read_bytes())==record['sha256']
for record in manifest['theorems']:
    for key in ['solution','theorem']:
        assert sha((ROOT/record[key+'_path']).read_bytes())==record[key+'_sha256']
checks=json.loads((VER/(stem+'-type-checks.json')).read_text(encoding='utf-8'))
compiled_inputs=[]
if args.compiled_solutions:
    benchmark_dir=VER/'batch-ci-benchmark-v1'
    benchmark=json.loads((benchmark_dir/'validation.json').read_text(encoding='utf-8'))
    assert benchmark['all_compiled_CI_records_identical_to_individual_imports'] and benchmark['compared_solutions']==12
    assert sha((HERE/'prepare_batch_solution_types.py').read_bytes())==benchmark['generator_sha256']
    for name,digest in benchmark['archived_evidence_sha256'].items():
        assert sha((benchmark_dir/name).read_bytes())==digest
    compiled_inputs=json.loads((VER/(stem+'-compiled-solution-inputs.json')).read_text(encoding='utf-8'))
    assert {r['module'] for r in compiled_inputs}=={r['solution_module'] for r in manifest['theorems']}
    for entry in compiled_inputs:
        assert sha(Path(entry['path']).read_bytes())==entry['artifact_sha256']
    checks=[c for c in checks if c['label'] in ['native','stubs']]
    checks.append({'label':'compiled-solutions','path':stem+'-types-compiled-solutions.lean',
                   'output':stem+'-types-compiled-solutions.json','declaration_count':len(manifest['theorems'])})
lake=Path.home()/'.elan/toolchains/leanprover--lean4---v4.33.1/bin/lake.exe'
env=os.environ.copy();env['LEAN_NUM_THREADS']='1'
evidence={};types={}
if not (args.model_regression or args.scope_regression):
    companion_path=VER/'machine-auto-validation.json'
    companion=json.loads(companion_path.read_text(encoding='utf-8'))
    assert not companion['probe_only'] and companion['all_companion_types_and_bodies_equal']
    assert companion['manifest_sha256']==sha(manifest_path.read_bytes())
    assert companion['theorem_count']==len(manifest['theorems'])
    for name,digest in companion['evidence_sha256'].items():
        assert sha((VER/name).read_bytes())==digest
        evidence[name]=digest
    evidence[companion_path.name]=sha(companion_path.read_bytes())
for check in checks:
    path=VER/check['path'];output=VER/check['output']
    if output.exists():output.unlink()
    log=path.with_suffix('.txt')
    with log.open('w',encoding='utf-8') as handle:
        result=subprocess.run([str(lake),'env','lean',str(path)],cwd=ROOT,env=env,
                              stdout=handle,stderr=subprocess.STDOUT)
    assert result.returncode==0,('CI extraction failed',str(log))
    records=json.loads(output.read_text(encoding='utf-8'))
    assert len(records)==check['declaration_count']
    types[check['label']]={r['name']:r for r in records}
    evidence[check['path']]=sha(path.read_bytes())
    evidence[log.name]=sha(log.read_bytes())
    evidence[output.name]=sha(output.read_bytes())
    print('Checked',check['label'],len(records),'exact CI types',flush=True)
native=types['native'];stubs=types['stubs'];differences=[]
assert native.keys()==stubs.keys()
for index,theorem in enumerate(manifest['theorems']):
    name=theorem['original_decl']
    solution_side='compiled-solutions' if args.compiled_solutions else 'solution-'+str(index)
    for side in ['stubs',solution_side]:
        got=types[side][name]
        if any(native[name][key]!=got[key] for key in ['universeCount','normalizedType']):
            differences.append({'name':name,'side':side,'original':native[name],'staged':got})
(VER/(stem+'-type-differences.json')).write_text(json.dumps(differences,indent=2)+'\n',encoding='utf-8')
assert not differences,'Exact type gate failed; inspect saved differences.'
for entry in compiled_inputs:
    assert sha(Path(entry['path']).read_bytes())==entry['artifact_sha256']
receipt={'checked_at_utc':datetime.now(timezone.utc).isoformat(),'all_exit_codes_zero':True,
         'compared_node_count':len(native),'compared_types_per_node':['native','stub','solution'],
         'exact_types_equal_after_explicit_relocation':True,'manifest_sha256':sha(manifest_path.read_bytes()),
         'normalization':'Invert recorded constant relocation; erase binder labels and metadata; align universe parameter labels by binder position. No unfolding or type simplification.',
         'evidence_sha256':evidence,'publication_authorized_by_this_receipt':False}
receipt['solution_type_readback']='compiled ConstantInfo via ModuleData' if args.compiled_solutions else 'individual solution imports'
if not (args.model_regression or args.scope_regression):
    receipt['validated_compiler_companion_relocations']=len(companion['mapping'])
if compiled_inputs:
    receipt['compiled_artifacts']=compiled_inputs
(VER/(stem+'-type-validation.json')).write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
print('All',len(native),'native, stub and solution types agree after explicit relocation.',flush=True)
