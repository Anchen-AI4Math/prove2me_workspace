"""Generate reviewable upload files; never publish or mark them validated.

--model-regression exercises the same renderer on the already closed six-file
branch, with a separate local namespace and separate unsealed manifest.
"""
import argparse
from collections import defaultdict
import json
from pathlib import Path
from machine_skeleton import Renderer,HERE,ROOT,VER,COMMAND,sha

parser=argparse.ArgumentParser()
parser.add_argument('--model-regression',action='store_true')
parser.add_argument('--scope-regression',action='store_true')
args=parser.parse_args()
assert not (args.model_regression and args.scope_regression)
classification=('scope-regression-classification.json' if args.scope_regression else
                'model-node-classification.json' if args.model_regression else 'machine-node-classification.json')
plan=json.loads((VER/classification).read_text(encoding='utf-8'))
prefix=('ThreeSum1960614.MachineScopeRegression' if args.scope_regression else
        'ThreeSum1960614.MachineRegression' if args.model_regression else 'ThreeSum1960614.Machine')
renderer=Renderer(plan,prefix)
units=plan['units']
base=prefix.replace('.','_')
provided=lambda unit:unit['primary'] in renderer.reuse['definitions'] or unit['classification']=='reuse-definition'
bundles=defaultdict(list)
for uid,unit in units.items():
    if unit['classification'].startswith('def-') and not provided(unit):bundles[unit['module']].append(uid)
for module in renderer.sources:
    reuse_record=renderer.reuse['modules'].get(module)
    if reuse_record and reuse_record.get('skip_macro_bundle',renderer.reuse.get('schema_version',1)==1):continue
    if any(c['syntaxKind'] in {COMMAND+'macro',COMMAND+'mixfix'} for c in renderer.contexts[module]['commands']):
        bundles.setdefault(module,[])
definition_modules={m:'Definitions.Def_'+base+'_'+m.replace('.','_') for m in bundles}
# Coalesce topologically adjacent source skeletons. Each original module's
# scopes still open/close independently; no declaration is hand-split.
# The advisory size budget counts nonempty lines and preserves every byte.
definition_groups=[]
if not (args.model_regression or args.scope_regression):
    group=[];line_budget=0;byte_budget=0
    for module in renderer.module_order(bundles):
        content=renderer.skeleton(module,bundles[module])
        lines=sum(bool(line.strip()) for line in content.splitlines())
        size=len(content.encode())
        if group and (line_budget+lines>500 or byte_budget+size>250000):
            definition_groups.append(group);group=[];line_budget=0;byte_budget=0
        group.append(module);line_budget+=lines;byte_budget+=size
    if group:definition_groups.append(group)
    for index,group in enumerate(definition_groups,1):
        for module in group:definition_modules[module]='Definitions.Def_'+base+'_Bundle'+str(index).zfill(3)
else:
    definition_groups=[[m] for m in renderer.module_order(bundles)]

def providers(modules):
    seen=set();pending=list(modules);found=set()
    while pending:
        module=pending.pop()
        if module in seen:continue
        seen.add(module)
        if module in definition_modules:found.add(definition_modules[module])
        found.update(renderer.definition_providers(module))
        for child in renderer.imports(module):
            if child in renderer.sources:pending.append(child)
    return found

def write(module,code):
    path=ROOT/Path(*module.split('.')).with_suffix('.lean')
    path.parent.mkdir(exist_ok=True)
    path.write_text(code,encoding='utf-8',newline='\n')
    return path.relative_to(ROOT).as_posix(),sha(path.read_bytes())

def header(imports,source_modules):
    imports=set(imports)|{'Lean'}
    notices=[]
    for module in sorted(source_modules):
        comment=renderer.header_comments(module)
        if comment and comment not in notices:notices.append(comment)
    text='\n\n'.join(notices)
    return (text+'\n\n' if text else '')+'\n'.join('import '+m for m in sorted(set(imports)))+'\n\n'

def opens_prelude(modules):
    # Opening a namespace before its first retained declaration is legal in
    # the native source only because preceding declarations populated it.
    # Empty namespace commands restore that scope without adding constants.
    names=set()
    for module in modules:
        for c in renderer.contexts[module]['commands']:
            if c['syntaxKind']==COMMAND+'namespace':
                for frame in renderer.scope_stack(module,c['endOffset']):
                    if frame['namespace']:names.add(prefix+'.'+frame['namespace'])
                    if frame['namespace']:names.add(frame['namespace'])
            elif c['syntaxKind']==COMMAND+'open':
                namespace=renderer.scope_stack(module,c['startOffset'])[-1]['namespace']
                for opened in c['opens']:
                    if opened['variant']=='simple':
                        for ident in opened['namespaces']:
                            names.update(renderer.namespace_choices(module,namespace,ident['name']))
    return ''.join('namespace '+n+'\nend '+n+'\n' for n in sorted(names))+'\n'

manifest={'source_repository':plan['public_source_repository'],'source_commit':plan['public_source_commit'],
          'classification_sha256':sha((VER/classification).read_bytes()),'validation_complete':False,
          'regression_only':args.model_regression or args.scope_regression,'namespace_prefix':prefix,
          'definitions':[],'theorems':[],'rename_map':renderer.name_map}
manifest['environment']='0df444a360eaa60ab8c11dca51a86af692955474'
manifest['project_tag']='3sum-1960614'
manifest['reused_theorems']=[{'name':renderer.name_map[u['primary']],'original_decl':u['primary'],
                            'theorem_id':renderer.accepted[u['primary']]['theorem_id']}
                           for u in units.values() if u['classification']=='reuse-node']
for group in definition_groups:
    destination=definition_modules[group[0]]
    imports=providers(group)-{destination}
    imports.update(renderer.external_imports(group))
    body=header(imports,group)+opens_prelude(group)
    body+='\n'.join(renderer.skeleton(module,bundles[module]) for module in group)
    path,digest=write(destination,body)
    manifest['definitions'].append({'original_module':group[0],'original_modules':group,'module':destination,
                                  'path':path,'sha256':digest,'dependencies':sorted(imports)})

native_index=json.loads((VER/'extended-reuse-compact-index.json').read_text(encoding='utf-8'))['native'] if not manifest['regression_only'] else {}
universe_counts={name:r['universeCount'] for name,r in native_index.items()}

for uid in plan['node_topological_order']:
    unit=units[uid]
    if unit['classification']=='reuse-node':continue
    module=unit['module'];name=renderer.name_map[unit['primary']]
    helpers=defaultdict(list)
    for helper in unit['inline_units']:helpers[units[helper]['module']].append(helper)
    children=[renderer.name_map[units[c]['primary']] for c in unit['child_nodes']]
    all_modules=set(helpers)|{module}
    imports=providers(all_modules)
    imports.update(renderer.external_imports(all_modules))
    imports.update('Theorems.Thm_'+child.replace('.','_') for child in children)
    assert 'Theorems.Thm_'+name.replace('.','_') not in imports
    body=header(imports,all_modules)+opens_prelude(all_modules)
    for helper_module in renderer.module_order(helpers):
        body+=renderer.skeleton(helper_module,helpers[helper_module],
            skip_imported_syntax=not manifest['regression_only'])+'\n'
    context=renderer.active_context(module,unit['fact']['declStart']['offset'])
    # Opening the enclosing namespace is file-local here; solution itself is
    # always a root theorem. Native section variable/include commands remain.
    if manifest['regression_only']:
        solution=body+context+'\n'+renderer.declaration(unit,target='solution')+'\n\n#print axioms solution\n'
        implementation=None
    else:
        implementation=name+'__implementation_'+sha(uid.encode())[:10]
        universes=['u_implementation_'+str(i) for i in range(universe_counts[unit['primary']])]
        suffix='.{'+','.join(universes)+'}' if universes else ''
        solution=body+'section\n'+context+'\n'+renderer.declaration(unit,target=implementation)+'\nend\n\n'
        term='(@'+implementation+suffix+')'
        solution+='theorem solution'+suffix+' : type_of% '+term+' := '+term+'\n\n#print axioms solution\n'
    sol_module='Solutions.Sol_'+name.replace('.','_')
    sp,ss=write(sol_module,solution)
    statement_imports=providers([module])|set(renderer.external_imports([module]))
    statement_imports.update('Theorems.Thm_'+child.replace('.','_') for child in children)
    preamble=header(statement_imports,[module])+opens_prelude([module])+context
    preamble+=renderer.hoisted_context(unit)
    statement=renderer.declaration(unit,target=name,stub=True)
    thm_module='Theorems.Thm_'+name.replace('.','_')
    tp,ts=write(thm_module,preamble+'\n'+statement+'\n')
    record={'name':name,'original_decl':unit['primary'],'original_module':module,
        'solution_implementation':implementation,
        'solution_module':sol_module,'solution_path':sp,'solution_sha256':ss,
        'theorem_module':thm_module,'theorem_path':tp,'theorem_sha256':ts,
        'preamble':preamble,'formal_statement':statement,'children':children,'source':renderer.source_link(unit)}
    if name=='ThreeSum1960614.costs_solve_3sum' and not manifest['regression_only']:
        frozen=json.loads((VER/'machine-frozen-bridge-contract.json').read_text(encoding='utf-8'))
        assert frozen['theorem_name']==name
        record.update(existing_theorem_id=frozen.get('theorem_id',frozen.get('id')),
                      frozen_target_check_required=True)
        assert record['existing_theorem_id']=='7c23d3cb-c4a0-4bc1-975a-ca2e5849adc6'
    manifest['theorems'].append(record)
output=('machine-scope-regression-manifest.json' if args.scope_regression else
        'machine-regression-manifest.json' if args.model_regression else 'machine-platform-manifest.json')
(VER/output).write_text(json.dumps(manifest,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print('Generated',len(manifest['definitions']),'definition bundles and',len(manifest['theorems']),
      'theorem/solution pairs; all compile/type gates remain pending.')
