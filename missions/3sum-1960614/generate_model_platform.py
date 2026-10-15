"""Skeleton subtraction for the independent fixed-model proof branch.

Only official Stage 2 spans cut declarations/proofs or rename identifiers.
Lean-parsed non-declaration scope commands control hoisting to top level.
The frozen public root is reused, with a separate definally-equal target check.
"""
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
VER=HERE/'verification'
plan=json.loads((VER/'model-node-classification.json').read_text(encoding='utf-8'))
contexts={c['module']:c for c in json.loads((VER/'model-scope-contexts.json').read_text(encoding='utf-8'))}
units=plan['units']
PREFIX='ThreeSum1960614.FixedModel.'
BASE='Definitions.Def_ThreeSum1960614_Analysis'
DEF_MODULES={
 'Submission.ThreeSum.FixedModelAlgebra':'Definitions.Def_ThreeSum1960614_FixedModelAlgebra',
 'Submission.ThreeSum.ModelWitnessLogs':'Definitions.Def_ThreeSum1960614_ModelWitnessPoints'}
ROOT_NAME=PREFIX+'complete_lower_bound'
EXISTING_ROOT='9319378a-d6f7-45f7-b66b-35f91d017f2e'
NEW_NODES=[PREFIX+'bound_of_witnesses',PREFIX+'witness_logs']
SHARED_IMPORTS=[BASE,*DEF_MODULES.values()]
TAG='3sum-1960614'


def sha(data):return hashlib.sha256(data).hexdigest()


def source_link(module,first,last):
    path=('Submission/Closed3Sum/'+module.removeprefix('Closed3Sum.').replace('.','/')
          if module.startswith('Closed3Sum.') else module.replace('.','/'))+'.lean'
    return plan['public_source_repository']+'/blob/'+plan['public_source_commit']+'/'+path+f'#L{first}-L{last}'


def edit(data,changes):
    ordered=sorted(changes,key=lambda e:(e[0],e[1]))
    previous=-1
    for start,end,_ in ordered:
        assert 0<=start<=end<=len(data)
        assert start>=previous,('overlapping oracle edits',ordered)
        previous=end
    for start,end,replacement in reversed(ordered):
        data=data[:start]+replacement+data[end:]
    return data


sources={}
facts={}
for module,receipt in plan['module_receipts'].items():
    path=HERE/'machine/lean'/Path(*module.split('.')).with_suffix('.lean')
    assert sha(path.read_bytes())==receipt['source_sha256']
    sources[module]=path.read_text(encoding='utf-8').encode('utf-8')
    assert sha(sources[module])==receipt['oracle_input_sha256']
    fp=ROOT/receipt['facts_path']
    assert sha(fp.read_bytes())==receipt['facts_sha256']
    facts[module]=[json.loads(line) for line in fp.read_text(encoding='utf-8').splitlines() if line.strip()]


def skeleton(module,selected,imports,flatten_scopes=False):
    data=sources[module]
    kept={(units[uid]['fact']['declStart']['offset'],units[uid]['fact']['declEnd']['offset']) for uid in selected}
    changes=[(0,contexts[module]['headerEndOffset'],
              ('\n'.join('import '+m for m in sorted(set(imports)))+'\n\n').encode())]
    for fact in facts[module]:
        if fact['kind']=='decl':
            a,b=fact['declStart']['offset'],fact['declEnd']['offset']
            if (a,b) not in kept:changes.append((a,b,b''))
    if flatten_scopes:
        for command in contexts[module]['commands']:
            if command['syntaxKind'] in {'Lean.Parser.Command.namespace','Lean.Parser.Command.section','Lean.Parser.Command.end'}:
                changes.append((command['startOffset'],command['endOffset'],b''))
    return edit(data,changes).decode('utf-8').rstrip()+'\n'


def target_text(unit,new_name,stub=False):
    module=unit['module']; fact=unit['fact']; start=fact['declStart']['offset']
    end=fact['valStart']['offset'] if stub else fact['declEnd']['offset']
    matches=[f for f in facts[module] if f['kind']=='ref' and f['const']==unit['primary']
             and start<=f['start']['offset']<fact['valStart']['offset']]
    assert len(matches)==1,(unit['primary'],matches)
    binding=matches[0]
    changes=[(binding['start']['offset']-start,binding['end']['offset']-start,new_name.encode())]
    if stub and fact['docstring']:
        doc=fact['docstring']
        changes.append((doc['start']['offset']-start,doc['end']['offset']-start,b''))
    if fact['privateTok']:
        token=fact['privateTok']
        changes.append((token['start']['offset']-start,token['end']['offset']-start,b''))
    text=edit(sources[module][start:end],changes).decode('utf-8')
    return text+(':= by sorry' if stub else '')


def close_scopes(module):
    stack=[]
    for command in contexts[module]['commands']:
        kind=command['syntaxKind']; ids=command['identifiers']
        if kind=='Lean.Parser.Command.namespace':
            assert len(ids)==1,command
            stack.append(ids[0])
        elif kind=='Lean.Parser.Command.section':
            assert len(ids)<=1,command
            stack.append(ids[0] if ids else '')
        elif kind=='Lean.Parser.Command.end':
            assert stack,command
            name=stack.pop()
            if ids:assert len(ids)==1 and ids[0]==name,(command,name)
    return ''.join('\nend'+(' '+name if name else '')+'\n' for name in reversed(stack))


manifest={'source_repository':plan['public_source_repository'],
          'source_commit':plan['public_source_commit'],'project_tag':TAG,
          'environment':'0df444a360eaa60ab8c11dca51a86af692955474',
          'classification_sha256':sha((VER/'model-node-classification.json').read_bytes()),
          'validation_complete':False,'definitions':[],'theorems':[]}


def write(module,code):
    path=ROOT/Path(*module.split('.')).with_suffix('.lean')
    path.parent.mkdir(exist_ok=True)
    path.write_text(code,encoding='utf-8',newline='\n')
    return path.relative_to(ROOT).as_posix(),sha(path.read_bytes())


for module,output in DEF_MODULES.items():
    selected=[uid for uid,u in units.items() if u['module']==module and u['classification'].startswith('def-')]
    dependencies=[BASE] if module.endswith('FixedModelAlgebra') else [DEF_MODULES['Submission.ThreeSum.FixedModelAlgebra']]
    body=skeleton(module,selected,dependencies)
    assert 'sorry' not in body
    first=min(units[uid]['fact']['declStart']['line'] for uid in selected)
    last=max(units[uid]['fact']['declEnd']['line'] for uid in selected)
    path,digest=write(output,body)
    is_algebra=module.endswith('FixedModelAlgebra')
    name=output.removeprefix('Definitions.Def_')
    description=(r'Exact rational witnesses for the expansion-232 analytic model. The constants include lower bounds $E_0$ and $\kappa_0$, a ratio floor $\rho_0$, a split point $s$, upper and lower point bounds $G$ and $H$, and a saving cap $U$. The auxiliary coefficients are $$a=1-2\rho_0,\quad A=\tfrac12-\kappa_0-\rho_0,\quad C=aE_0-A.$$ The target is $1.96061349120$. These are numerical definitions; the model bound is proved separately.'
                 if is_algebra else
                 r'The exact rational evaluation point $$u=\frac{859960785302793}{5000000000000000}$$ used to force a lower bound on the ratio parameter in the expansion-232 analytic model. This definition states no logarithmic or entropy inequality; those are separate proof obligations.')
    manifest['definitions'].append({'module':output,'path':path,'sha256':digest,
      'dependencies':dependencies,'payload':{'definition_name':name,
      'definition_title':'Exact witness constants for the expansion-232 model' if is_algebra else 'Rational ratio evaluation point for the model lower bound',
      'definition':body,'natural_language_statement':description,'source':source_link(module,first,last),
      'tags':[TAG,'3sum','exact-certificates'],'env':manifest['environment']}})

for uid in plan['node_topological_order']:
    unit=units[uid]
    if unit['classification']=='reuse-node':continue
    name=unit['primary']; module=unit['module']
    assert name in NEW_NODES+[ROOT_NAME]
    helpers=unit['inline_units']
    assert all(units[h]['module']==module for h in helpers),('cross-module helper requires its own skeleton',name)
    children=[units[c]['primary'] for c in unit['child_nodes']]
    imports=SHARED_IMPORTS+['Theorems.Thm_'+child.replace('.','_') for child in children]
    solution=skeleton(module,helpers,imports)+close_scopes(module)
    solution+='\nopen ThreeSum1960614 ThreeSum1960614.FixedModel in\n'
    solution+=target_text(unit,'solution')+'\n\n#print axioms solution\n'
    assert 'sorry' not in solution
    basename='model_platform_bound' if name==ROOT_NAME else 'FixedModel_'+name.rsplit('.',1)[1]
    sol_module='Solutions.Sol_ThreeSum1960614_'+basename
    sol_path,sol_sha=write(sol_module,solution)
    preamble=skeleton(module,[],SHARED_IMPORTS,flatten_scopes=True)
    preamble+='\nopen ThreeSum1960614 ThreeSum1960614.FixedModel\n'
    formal=target_text(unit,name,stub=True)
    record={'name':name,'original_module':module,'original_decl':unit['primary'],
            'solution_module':sol_module,'solution_path':sol_path,'solution_sha256':sol_sha,
            'children':children,'source':source_link(module,unit['fact']['declStart']['line'],unit['fact']['declEnd']['line'])}
    if name==ROOT_NAME:
        record.update(existing_theorem_id=EXISTING_ROOT,platform_name='ThreeSum1960614.fixed_model_lower_bound',
                      original_solution_type_uses='ThreeSum1960614.FixedModel.lowerTarget',
                      frozen_target_check_required=True)
    else:
        thm_module='Theorems.Thm_'+name.replace('.','_')
        path,digest=write(thm_module,preamble+'\n'+formal+'\n')
        record.update(theorem_module=thm_module,theorem_path=path,theorem_sha256=digest,
                      preamble=preamble,formal_statement=formal)
    manifest['theorems'].append(record)

path=VER/'model-platform-manifest.json'
path.write_text(json.dumps(manifest,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print('Generated',len(manifest['definitions']),'Def bundles and',len(manifest['theorems']),
      'proofs; the existing fixed-model root is reused. Validation/upload still pending.')
