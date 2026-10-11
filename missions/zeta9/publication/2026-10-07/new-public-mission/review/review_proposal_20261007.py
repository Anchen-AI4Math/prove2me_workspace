"""Pure source/snapshot review. Never imports API helpers or runs network/Lean."""
from pathlib import Path
from datetime import datetime, timezone
import ast, collections, hashlib, json, re

TASK=Path(__file__).resolve().parents[4]
OUT=TASK/'publication/2026-10-07/new-public-mission'
REVIEW=OUT/'review'
ROOT_ID='523f37b8-ae98-406c-a3f7-43aa8e002dd7'
OLD_MISSION='8195d8fe-059f-4515-92b4-57b585e2bac6'
OLD_PROPOSAL='06faf23f-00c2-4edf-92ab-1212cdb7d7d6'
MATRIX_IDS={'3e15df20-1023-4b72-95ab-1ad07c34b3e5','134e564c-4327-43b0-9ecd-e7d08fa133ec','bb7477e4-5539-4015-b8cf-9bad57e1c8a0'}
R_IDS={'60c1cf49-6b01-448c-b38a-88dc2fcb8ba0','691b1665-f122-47f7-a3e4-2c28a06055f2'}
POSITIVE_DOMAIN_IDS={'e202eaff-c82b-4d8b-b7a2-8b2896798987','2de22270-2e72-4a2a-8279-109158a6bc9d'}

def load(path):return json.loads(path.read_text(encoding='utf-8-sig'))
def binding(path):return dict(task_relative=path.relative_to(TASK).as_posix(),bytes=path.stat().st_size,sha256=hashlib.sha256(path.read_bytes()).hexdigest())
def save(name,value):
    (REVIEW/name).write_text(json.dumps(value,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')

def main():
    plan=load(OUT/'proposal-plan.json');pre=OUT/'focused-preflight'
    index=load(pre/'canonical-index.json')
    values={r['id']:load(pre/'canonical'/(r['id']+'.json')) for r in index}
    checks=[]
    def check(name,condition):
        assert condition,name
        checks.append(dict(name=name,passed=True))
    check('88 actual canonical snapshots, no duplicate ids',len(index)==len(values)==88)
    check('all canonical snapshots public and active',all(v['visibility']=='public' and not v.get('deprecated_at') for v in values.values()))
    counts=dict(collections.Counter(v['status'] for v in values.values()))
    check('actual canonical 18 Definition, 64 Proved, 6 Open',counts=={'Definition':18,'Proved':64,'Open':6})
    check('actual goal canonical Open public',values[ROOT_ID]['status']=='Open' and values[ROOT_ID]['visibility']=='public')
    check('all three Matrix targets published Open',all(values[k]['status']=='Open' for k in MATRIX_IDS))
    check('new public OpenProblem metadata',plan['visibility']=='public' and plan['mission_type']=='OpenProblem' and plan['root_theorem_id']==ROOT_ID)
    check('source introduction exact, 1258 words',plan['description']==(OUT/'content/mission-introduction.md').read_text(encoding='utf-8') and len(plan['description'].split())==1258)
    check('91 plan source bindings current',len(plan['bindings'])==91)
    for row in plan['bindings']:
        p=TASK/row['path'];actual=binding(p)
        check('bound '+row['path'],actual['bytes']==row['bytes'] and actual['sha256']==row['sha256'])
    order=plan['reference_order'];position={k:i for i,k in enumerate(order)}
    check('88 exact canonical references once each',len(order)==len(set(order))==88 and set(order)==set(values))
    defs={k:v for k,v in values.items() if v['status']=='Definition'}
    check('18 definitions first; actual root next',set(order[:18])==set(defs) and order[18]==ROOT_ID)
    modules={'Definitions.Def_'+v['theorem_name'].replace('.','_'):k for k,v in defs.items()}
    dependencies=[]
    for k,v in defs.items():
        for line in v['definition'].splitlines():
            if not line.startswith('import '):continue
            for imported in line.removeprefix('import ').split():
                if imported.startswith('Definitions.Def_'):
                    check('definition import present '+imported,imported in modules)
                    dependency=modules[imported]
                    check('definition dependency first '+imported,position[dependency]<position[k])
                    dependencies.append(dict(definition=k,imported_module=imported,dependency=dependency))
    ms=plan['milestones'];byid={r['theorem_id']:r for r in ms}
    check('69 exact milestone ids, distinct from definitions and root',len(ms)==len(byid)==69 and set(byid)==set(order[19:]))
    old=load(pre/'milestones.json')['milestones'];linked=[r for r in old if r.get('theorem')]
    check('old 66 theorem links and 3 Matrix added',len(linked)==66 and {r['theorem']['id'] for r in linked}|MATRIX_IDS==set(byid))
    corrected=[]
    for row in linked:
        k=row['theorem']['id'];new=byid[k]
        original=row['milestone_description'].replace('existing open theorem','existing published theorem')
        if new['milestone_description']!=original:corrected.append(k)
        check('source milestone title retained '+k,new['milestone_title']==row['title'])
    check('only R1 R2 and positive-argument descriptions deliberately corrected',set(corrected)==R_IDS|POSITIVE_DOMAIN_IDS)
    check('R1 R2 no false stronger assertion',all('not claimed to be strictly stronger' in byid[k]['milestone_description'] for k in R_IDS))
    check('positive domain clarified without assuming W has positive values',all('positive natural arguments' in byid[k]['milestone_description'] for k in POSITIVE_DOMAIN_IDS))
    check('all milestone titles within documented 200 chars',all(len(r['milestone_title'])<=200 for r in ms))
    check('rational selected Matrix preimage distinguished from integrality','preimage is rational' in byid['134e564c-4327-43b0-9ecd-e7d08fa133ec']['milestone_description'])
    check('all Matrix original even n>=2 and integer targets retained',all('n≥2' in byid[k]['milestone_description'] for k in MATRIX_IDS) and all('integer' in byid[k]['milestone_description'] for k in MATRIX_IDS-{'3e15df20-1023-4b72-95ab-1ad07c34b3e5'}))
    sourcepath=TASK/'scripts/propose_public_mission_2026_10_07.py'
    source=sourcepath.read_text(encoding='utf-8');tree=ast.parse(source)
    check('source API mutations guarded against both old identifiers','assert OLD_MISSION not in path and OLD_PROPOSAL not in path' in source)
    check('new identifier explicitly excludes old proposal','assert identifier!=OLD_PROPOSAL' in source)
    check('no old mission methods or launch helpers called',not any(isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute) and n.func.attr in ['sync','release','mission'] for n in ast.walk(tree)))
    check('published references only, no new draft declarations','{"kind":"reference","theorem_id":k}' in source and '"kind":"theorem"' not in source and '"kind":"definition"' not in source)
    check('unknown create recovered through paginated own proposals','own_proposals(client)' in source and 'Ambiguous proposal recovery' in source)
    check('resumed items reread before posting','detail=client.call("GET",endpoint)' in source and 'if k in item_ids: continue' in source)
    check('resumed milestones reread and compare before documented overwrite','current=client.call("GET",endpoint+"/milestones")' in source and 'if old and all(old.get(k)==v for k,v in body.items()): continue' in source)
    check('both milestone readbacks normalize title vs milestone_title',source.count('r.get("milestone_title",r.get("title"))')==2)
    check('mutation intent is saved before client call',source.index('save(state_path,state)')<source.index('result=client.call(method,path,body)'))
    check('final detail and milestone readbacks saved','save(OUT/"proposal-readback.json",final)' in source and 'save(OUT/"milestones-readback.json",final_milestones)' in source)
    check('receipt honestly leaves human launch and moderator approval','Human confirms reference items and clicks Submit Proposal in the web app; public missions then require moderator approval' in source and '"public_catalog_live":False' in source)
    api_source=(TASK/'scripts/publish_mission_2026_10_02.py').read_text(encoding='utf-8')
    check('API helper never automatically retries mutations','range(4 if method == "GET" else 1)' in api_source)
    state=load(OUT/'publication-state.json')
    check('actual new proposal id excludes old resources',state['proposal_id'] not in [OLD_MISSION,OLD_PROPOSAL])
    check('actual journal has no old resource writes',all(OLD_MISSION not in r['path'] and OLD_PROPOSAL not in r['path'] for r in state['journal']))
    check('actual journal mutation routes are new proposal only',all(r['path']=='/mission-proposals' or r['path'].startswith('/mission-proposals/'+state['proposal_id']) for r in state['journal']))
    readback=None
    if (OUT/'proposal-receipt.json').exists():
        final=load(OUT/'proposal-readback.json');raw=load(OUT/'milestones-readback.json')
        entries=raw['milestones'] if isinstance(raw,dict) else raw
        check('actual final new public Draft metadata',final['id']==state['proposal_id'] and final['visibility']=='public' and final['status']=='Draft' and final['description']==plan['description'])
        ids={r['theorem_id']:r['id'] for r in final['items']}
        check('actual final reference map matches all 88 canonical ids exactly',len(final['items'])==len(ids)==88 and set(ids)==set(order) and all(r['kind']=='reference' for r in final['items']))
        check('actual final canonical root main and order exact',final['main_item_id']==ids[ROOT_ID] and final['item_order']==[ids[k] for k in order])
        actual={r['item_id']:r for r in entries}
        check('actual final 69 milestone item ids exact',len(entries)==len(actual)==69 and set(actual)=={ids[k] for k in byid})
        for k,expected in byid.items():
            got=actual[ids[k]]
            check('actual faithful milestone text '+k,got.get('milestone_title',got.get('title'))==expected['milestone_title'] and got['milestone_description']==expected['milestone_description'])
        readback=dict(proposal_id=state['proposal_id'],references=88,milestones=69,metadata_exact=True,all_canonical_item_mapping_and_order_exact=True,all_milestone_texts_exact=True)
    sources=[sourcepath,OUT/'proposal-plan.json',pre/'summary.json',pre/'canonical-index.json',pre/'milestones.json',OUT/'content/mission-introduction.md',OUT/'publication-state.json',TASK/'scripts/publish_mission_2026_10_02.py']
    sources+=[pre/'canonical'/(k+'.json') for k in order]
    sources+=[TASK/'formalization/platform/readback-2026-10-07/api-docs-v0.12.1/references/mission_captain.md']
    if readback:sources+=[OUT/'proposal-receipt.json',OUT/'proposal-readback.json',OUT/'milestones-readback.json']
    report=dict(verdict='PASS' if readback else 'SOURCE_PLAN_PASS_FINAL_READBACK_PENDING',role='independent pure proposal source/snapshot reviewer',
        checked_at=datetime.now(timezone.utc).isoformat(),API_executed=False,Lean_executed=False,Root_script_modified=False,old_resource_writes=0,
        authorization='Parent confirms the latest human explicitly requested a new directly public mission proposal',
        checks=checks,actual_canonical_counts=counts,introduction_words=1258,definition_dependencies=dependencies,
        corrected_R1_R2_ids=sorted(R_IDS),clarified_positive_argument_ids=sorted(POSITIVE_DOMAIN_IDS),final_readback=readback,
        review_boundaries=['No new theorem/declaration draft exists; official reference items take no blind readback.',
          'Human-only per-item confirmation and Submit Proposal in the web app, followed by moderator review, remain required.',
          'Canonical R1/R2 old natural-language wording is left immutable; new milestone text correctly distinguishes unrestricted existence from the actual construction.',
          'Milestones 49 and 51 explicitly say positive natural arguments; no positive-value hypothesis is inferred for arbitrary multipliers.'],
        nonblocking_hardening=['Uploader final asserts could also compare full theorem_id->item_id mapping; this pure review directly verifies that mapping from actual final readback.',
          'Name-only create recovery is adequate for the observed unique fresh name and journal, but a generalized uploader should validate recovery metadata/creation timing.'],
        stable_inputs=[binding(path) for path in sources])
    save('proposal-source-plan-review-2026-10-07.json',report)
    print(json.dumps(dict(verdict=report['verdict'],checks=len(checks),source_bindings=len(sources),canonical_counts=counts,final_readback=readback),ensure_ascii=False))

if __name__=='__main__':main()
