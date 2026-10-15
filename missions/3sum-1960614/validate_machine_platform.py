"""Seal main upload payloads after complete compiler/type/contract/metadata gates."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
VER=HERE/'verification'
sha=lambda path:hashlib.sha256(path.read_bytes()).hexdigest()
read=lambda name:json.loads((VER/name).read_text(encoding='utf-8'))
manifest_path=VER/'machine-platform-manifest.json'
manifest=read(manifest_path.name)
assert not manifest['regression_only'] and not manifest['validation_complete']
before=sha(manifest_path)
types=read('machine-platform-type-validation.json')
build=read('machine-scoped-build-validation.json')
contract=read('machine-frozen-bridge-validation.json')
for receipt in (types,build,contract):assert receipt['manifest_sha256']==before
assert types['all_exit_codes_zero'] and types['exact_types_equal_after_explicit_relocation']
assert types['compared_node_count']==len(manifest['theorems'])
assert build['exit_code']==0 and build['all_scoped_batches_passed']
assert build['log_sha256']==sha(VER/'machine-platform-build.txt')
assert contract['frozen_root_contract_passed']
assert read('machine-platform-type-differences.json')==[]

batch_dir=HERE/'metadata/machine-batches'
index=json.loads((batch_dir/'index.json').read_text(encoding='utf-8'))
metadata={}
for batch in index:
    input_path=ROOT/batch['input']
    assert sha(input_path)==batch['sha256']
    output=batch_dir/('output-'+str(batch['batch']).zfill(3)+'.json')
    entries=json.loads(output.read_text(encoding='utf-8'))
    assert isinstance(entries,list) and {r['name'] for r in entries}==set(batch['names'])
    for entry in entries:
        assert entry['name'] not in metadata
        assert isinstance(entry['natural_language_statement'],str) and len(entry['natural_language_statement'])>=100
        assert isinstance(entry['tags'],list) and all(isinstance(tag,str) for tag in entry['tags'])
        metadata[entry['name']]=entry

environment=manifest['environment']
tag=manifest['project_tag']
for definition in manifest['definitions']:
    path=ROOT/definition['path']
    assert sha(path)==definition['sha256']
    assert not any(module.startswith('Theorems.') for module in definition['dependencies'])
    name=definition['module'].removeprefix('Definitions.Def_')
    entry=metadata.pop(name)
    assert 0<len(entry['definition_title'])<=200
    sources=[]
    for module in definition.get('original_modules',[definition['original_module']]):
        source_path=('Submission/Closed3Sum/'+module.removeprefix('Closed3Sum.').replace('.','/')
                     if module.startswith('Closed3Sum.') else module.replace('.','/'))+'.lean'
        sources.append(manifest['source_repository']+'/blob/'+manifest['source_commit']+'/'+source_path)
    definition['payload']={
        'definition_name':name,'definition_title':entry['definition_title'],
        'definition':path.read_text(encoding='utf-8'),
        'natural_language_statement':entry['natural_language_statement'],
        'source':'\n'.join(sources),'tags':list(dict.fromkeys([tag,*entry['tags']])),
        'env':environment}
for theorem in manifest['theorems']:
    for kind in ('theorem','solution'):
        assert sha(ROOT/theorem[kind+'_path'])==theorem[kind+'_sha256']
    assert (ROOT/theorem['theorem_path']).read_text(encoding='utf-8')==theorem['preamble']+'\n'+theorem['formal_statement']+'\n'
    entry=metadata.pop(theorem['name'])
    assert 0<len(entry['theorem_title'])<=200 and len(entry['explanation'])>=100
    theorem['platform_name']=theorem['name']
    theorem['explanation']=entry['explanation']
    theorem['payload']={
        'theorem_name':theorem['name'],'theorem_title':entry['theorem_title'],
        'formal_statement':theorem['formal_statement'],'preamble':theorem['preamble'],
        'natural_language_statement':entry['natural_language_statement'],
        'source':theorem['source'],'tags':list(dict.fromkeys([tag,*entry['tags']])),
        'env':environment}
assert not metadata
roots=[t for t in manifest['theorems'] if t.get('existing_theorem_id')]
assert len(roots)==1 and roots[0]['existing_theorem_id']=='7c23d3cb-c4a0-4bc1-975a-ca2e5849adc6'
assert roots[0]['name']=='ThreeSum1960614.costs_solve_3sum'
manifest['validation_complete']=True
manifest_path.write_text(json.dumps(manifest,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
receipt={'checked_at_utc':datetime.now(timezone.utc).isoformat(),
         'manifest_sha256':sha(manifest_path),'pre_metadata_manifest_sha256':before,
         'exact_type_comparison_passed':True,'frozen_root_contract_passed':True,
         'scoped_build_passed':True,'metadata_complete':True,
         'compared_node_count':types['compared_node_count'],
         'evidence_sha256':{name:sha(VER/name) for name in
                           ('machine-platform-type-validation.json','machine-scoped-build-validation.json',
                            'machine-frozen-bridge-validation.json','machine-platform-build.txt')}}
(VER/'machine-platform-validation.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
print('Sealed',len(manifest['definitions']),'Def payloads and',len(manifest['theorems']),'exact theorem/solution payloads; publication not yet run.')
