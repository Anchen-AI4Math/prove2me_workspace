"""Reachability planning from Lean declaration facts; never splits source text."""
from collections import Counter
import json
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent
VER=HERE/'verification'
rows=[json.loads(x) for x in (VER/'machine-decl-graph.jsonl').read_text(encoding='utf-8').splitlines() if x]
byname={x['name']:x for x in rows}
targets=['ThreeSum1960614.costs_solve_3sum',
 'ThreeSum.solvedInTime_980307_500000',
 'ThreeSum1960614.FixedModel.complete_lower_bound']
model_only='--model' in sys.argv
main_reduction_file=VER/'main-reduction-bridge-plan.json'
main_reduction=(json.loads(main_reduction_file.read_text(encoding='utf-8'))
                if main_reduction_file.exists() else None)
if not model_only and main_reduction and main_reduction['actual_paths_verified']:
    # The original decimal main theorem already has an accepted reduction.
    # Publish its missing universal bridge; do not replace the original goal
    # or create a duplicate direct proof node for the same result.
    targets=[main_reduction['remaining_source_upload_target']]
    context_path=VER/'machine-scope-contexts.json'
    contexts={c['module']:c for c in json.loads(context_path.read_text(encoding='utf-8'))}
    assert all(c['parsePassed'] for c in contexts.values())
    modules=set()
    pending=[byname[targets[0]]['module']]
    while pending:
        module=pending.pop()
        if module in modules:continue
        modules.add(module)
        for item in contexts[module]['imports']:
            for ident in item['identifiers']:
                if ident['name'] in contexts:pending.append(ident['name'])
    rows=[r for r in rows if r['module'] in modules]
    byname={r['name']:r for r in rows}
if model_only:
    targets=['ThreeSum1960614.FixedModel.complete_lower_bound']
    # Import headers select the independent branch. Declaration reachability
    # still comes exclusively from the official Lean Stage 1 graph below.
    modules=set()
    pending=['Submission.ThreeSum.ModelWitnessBounds']
    while pending:
        module=pending.pop()
        if module in modules:continue
        modules.add(module)
        source=HERE/'machine/lean'/Path(*module.split('.')).with_suffix('.lean')
        for line in source.read_text(encoding='utf-8').splitlines():
            fields=line.split()
            if fields and fields[0]=='import':
                pending.extend(m for m in fields[1:]
                               if m.startswith(('Submission.','Closed3Sum.')))
    rows=[r for r in rows if r['module'] in modules]
    byname={r['name']:r for r in rows}
assert all(x in byname for x in targets)
accepted=json.loads((VER/'proof-status.json').read_text(encoding='utf-8'))
reuse={('ThreeSum1960614.'+k):v for k,v in accepted.items() if v['status']=='ACCEPTED'}
model_graph_file=VER/'model-graph-check.json'
model_graph=(json.loads(model_graph_file.read_text(encoding='utf-8'))
             if model_graph_file.exists() else None)
if not model_only and model_graph and model_graph['model_branch_complete']:
    for theorem in model_graph['proved_theorems']:
        reuse[theorem['source_name']]={
            'theorem_id':theorem['theorem_id'],'submission_id':theorem['submission_id'],
            'status':'ACCEPTED','platform_name':theorem['platform_name']}
todo=targets+[x['name'] for x in rows if x['isInstance']]
seen=set()
while todo:
    name=todo.pop()
    if name in seen or name not in byname:
        continue
    seen.add(name)
    row=byname[name]
    todo.extend(row['typeDeps'])
    if name not in reuse:
        todo.extend(row['valueDeps'])
    if row['kind']=='inductive':
        todo.extend(x['name'] for x in rows if x['kind']=='ctor' and name in x['typeDeps'])
live=[byname[x] for x in sorted(seen) if byname[x]['startLine']>0]
participating=sorted({x['module'] for x in rows})
counts=dict(Counter(x['module'] for x in live))
result={'stage':'Lean declaration reachability complete; Stage 2 spans and type comparisons still required',
 'public_source_repository':'https://github.com/Anchen0823/three-sum-1960614',
 'public_source_commit':'8c25c0325de5be4286413f39ca0c9278aad33f52',
 'source_path_mapping':{'Submission.':'Submission/','Closed3Sum.':'Submission/Closed3Sum/'},
 'roots':targets,'instance_roots':[x['name'] for x in rows if x['isInstance']],
 'oracle_row_count':len(rows),'reachable_with_span_count':len(live),
 'reachable_generated_count':sum(byname[x]['startLine']==0 for x in seen),
 'live_rows':live,'participating_modules':participating,'live_count_by_module':counts,
 'reusable_accepted_nodes':{x:reuse[x] for x in sorted(seen) if x in reuse},
 'accepted_library_nodes':{x:v for x,v in reuse.items() if x in byname},
 'reuse_candidates':['APSPSource_ThreeSumApsp_Lang_Syntax','APSPSource_ThreeSumApsp_Lang_Logic'],
 'published_independent_model_branch':model_graph if not model_only else None,
 'original_main_goal_reduction':main_reduction if not model_only else None,
 'source_generated':False,'platform_uploaded':False,
 'note':'Syntax/Logic definition reuse still requires Lean type comparison. Node/helper classification requires Stage 2 proof spans. No namespace or source edits inferred by regex.'}
(VER/('model-upload-plan.json' if model_only else 'machine-upload-plan.json')).write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(len(rows),'oracle rows;',len(live),'reachable source declarations;',len(participating),'participating modules.')
print('Accepted reusable nodes:',', '.join(result['reusable_accepted_nodes']))
