"""Pure AP18 original-source route/candidate; closed Accepted child remains pending."""
from __future__ import annotations
import argparse,json
from pathlib import Path
import stage_collision_multiplicity_provider as data
TASK,ROOT,V=data.TASK,data.ROOT,data.V
SELF=Path(__file__).resolve();STAGE=V/'ap18/translated-summand-bound'
TARGET='OAI.PiExponent.DeterminantAnalyticBound.translated_summand_bound'
PARENT='OAI.PiExponent.Collision.sum_weight_ge_of_low_count_le'
PARENT_STAGE=V/'nodes-preview'/PARENT.replace('.','_')
CHILD_MODULE='Theorems.Thm_OAI_PiExponent_Collision_sum_weight_ge_of_low_count_le_closed_ap18'
IMPORTS=['Mathlib.Algebra.BigOperators.Group.Finset.Basic','Mathlib.Algebra.Order.BigOperators.Ring.Finset','Mathlib.Analysis.SpecialFunctions.Exp','Mathlib.Tactic']
SPECS=[('OAI.PiExponent.Collision.sum_multiplicity_eq_card_filter',5106,5424),
 ('OAI.PiExponent.Collision.sum_sq_le_card_mul_sum_sq',157,374),
 ('OAI.PiExponent.Collision.sum_sq_le_card_mul_total_sq',378,731),
 ('OAI.PiExponent.Collision.sum_sq_le_card_mul_univ_sq',1816,2029),
 ('OAI.PiExponent.DeterminantAnalyticBound.two_alternative_exponent',215,4393),
 (TARGET,4397,5770)]
read,sha,sha_bytes,encode,need,rel=data.read,data.sha,data.sha_bytes,data.encode,data.need,data.rel

def source_units():
    data.check_only()
    ast,scopes=read(data.ap9.AST),read(data.ap9.SCOPES)
    graph={r['name']:r for r in map(json.loads,data.ap9.GRAPH.read_text(encoding='utf-8').splitlines())}
    owners={r['source_name']:r for r in read(data.ap9.OWNERS)['owners']}
    pub=read(PARENT_STAGE/'publication.json');cert=read(PARENT_STAGE/'validation.json')
    body=pub['target_readback']['body'];wire=(body['preamble']+body['formal_statement']).encode()
    need(pub['confirmed_proved'] is True and body['status']=='Proved' and body['theorem_name']==PARENT
         and pub['theorem_id']=='84999320-3725-4c17-b1cb-428d9f92f6cc'
         and pub['submission_id']=='78ad72fd-0fdd-44e6-93c7-f0e607baa6fa'
         and pub['last_verify_verdict']['body']['status']=='ACCEPTED'
         and cert['validated'] is True and cert['kernel_types_equal'] is True
         and cert['standard_axioms_only'] is True,'Actual Accepted Collision parent differs')
    sol=next(PARENT_STAGE.glob('Sol_*.lean'));thm=next(PARENT_STAGE.glob('Thm_*.lean'))
    need(wire==thm.read_bytes() and sha(sol)==pub['verify_intent']['solution_sha256']
         and b'multiplicity' not in wire and b'multiplicity' not in sol.read_bytes(),
         'Accepted parent exact public wire/proof or multiplicity boundary differs')
    pins={rel(p):sha(p) for p in [SELF,data.SELF,data.ap9.AST,data.ap9.SCOPES,data.ap9.GRAPH,
         data.ap9.OWNERS,PARENT_STAGE/'publication.json',PARENT_STAGE/'validation.json',
         PARENT_STAGE/'original-type.json',PARENT_STAGE/'generated-type.json',sol,thm,
         data.STAGE/'preparation.json',data.STAGE/data.PROVIDER_FILE,data.COVERAGE]}
    rows=[]
    for name,a,b in SPECS:
        m=next(m for m in ast['modules'] if any(name in u['graph_names'] for u in m['units']))
        u=next(u for u in m['units'] if name in u['graph_names']);module=m['module']
        source=TASK/('port/lean/'+module.replace('.','/')+'.lean')
        original=TASK/('source/lean/'+module.replace('.','/')+'.lean')
        raw=source.read_bytes();command=raw[a:b]
        sm=next(m for m in scopes['modules'] if m['source']==module.replace('.','/')+'.lean')
        scope=next(s for s in sm['declarations'] if s['verified_name']==name)
        contexts=[raw[c['range']['start']['offset']:c['range']['end']['offset']].decode() for c in scope['context_commands']]
        owner=owners[name]
        need(m['source_sha256']==sm['source_sha256']==sha(source)
             and [u['start']['offset'],u['end']['offset']]==[a,b]
             and u['graph_names']==[name] and u['graph_kinds']==['theorem']
             and u['privateTok'] is None and not u['is_instance_command'] and not u['is_local_instance']
             and owner['command_unit']==module+':'+str(a) and owner['source_sha256']==sha(source)
             and original.read_bytes().replace(b'\r\n',b'\n').count(command.replace(b'\r\n',b'\n'))==1,
             'Exact original source theorem AST/owner differs: '+name)
        expected=['open scoped BigOperators']
        if 'CollisionOccupancy' in module:expected+=['variable {G : Type*}']
        if name.endswith('sum_sq_le_card_mul_univ_sq'):expected+=['variable [Fintype G]']
        need(contexts==expected and all(s['kind']=='namespace' for s in scope['scope_stack'])
             and scope['namespace']==name.rsplit('.',1)[0],'Actual source namespace/universes/instances differ')
        rows.append({'name':name,'module':module,'source':rel(source),'source_sha256':sha(source),
             'original':rel(original),'original_sha256':sha(original),'start':a,'end':b,
             'command_sha256':sha_bytes(command),'proof_suffix_sha256':sha_bytes(command[u['valueStart']['offset']-a:]),
             'ast':u,'scope':scope,'owner':owner,'contexts':contexts,'graph':graph[name],'bytes':command})
        pins[rel(source)]=sha(source);pins[rel(original)]=sha(original)
    closure=set();pending=[TARGET];boundary={PARENT,data.NAMES[0]}
    while pending:
        n=pending.pop()
        if n in closure:continue
        need(n in graph,'Unknown actual source project dependency: '+n);closure.add(n)
        if n not in boundary:pending+=graph[n]['typeDeps']+graph[n]['valueDeps']
    need(closure-boundary=={r['name'] for r in rows} and len(closure)==8,'Six-proof source closure differs')
    return rows,closure,pins,pub,wire

def stage_files():
    rows,closure,pins,pub,wire=source_units();target=rows[-1];cmd=target['bytes']
    ns=target['ast']['nameRange']['start']['offset']-target['start'];ne=target['ast']['nameRange']['end']['offset']-target['start'];vs=target['ast']['valueStart']['offset']-target['start']
    need(cmd[vs:vs+5]==b':= by','Original proof delimiter differs')
    preamble=(''.join('import '+m+'\n' for m in IMPORTS+[data.PLATFORM_MODULE])+'\nopen scoped BigOperators\n\n').encode()
    formal=cmd[:ns]+TARGET.encode()+cmd[ne:vs]+b':= by\n  sorry\n'
    parts=[(''.join('import '+m+'\n' for m in IMPORTS+[data.PLATFORM_MODULE,CHILD_MODULE])+'\n').encode()]
    for row in rows[:-1]:
        namespace=row['scope']['namespace'];parts.append(('\nnamespace '+namespace+'\nsection\n'+ '\n'.join(row['contexts'])+'\n\n').encode()+row['bytes']+('\n\nend\nend '+namespace+'\n').encode())
    parts.append(b'\nopen scoped BigOperators\nopen OAI.PiExponent OAI.PiExponent.DeterminantAnalyticBound\n\n'+cmd[:ns]+b'solution'+cmd[ne:]+b'\n')
    solution=b''.join(parts)
    need(solution.count(b'theorem solution')==1 and b'sorry' not in solution
         and solution[solution.rindex(b':= by'):].rstrip()==cmd[vs:].rstrip(),'Literal global solution proof differs')
    outputs={'candidate-target.lean.txt':preamble+formal,'candidate-solution.lean.txt':solution,
             'original-target-command.lean.txt':cmd,'accepted-parent-public-wire.lean.txt':wire}
    for r in rows:outputs['source-units/'+r['name'].replace('.','_')+'.port.lean.txt']=r['bytes']
    lines=sum(r['ast']['end']['line']-r['ast']['start']['line']+1 for r in rows)
    result={'schema_version':1,'artifact_kind':'ap18-translated-summand-source-route-candidate',
      'source_commit':data.COMMIT,'source_name':TARGET,'source_module':target['module'],
      'source_graph_closure_names':sorted(closure),'inline_proof_AST_count':len(rows),'inline_source_lines':lines,
      'inline_original_units':[{k:v for k,v in r.items() if k!='bytes'} for r in rows],
      'target_preamble':preamble.decode(),'target_formal_statement':formal.decode(),
      'mathlib_imports_candidate':IMPORTS,'no_blanket_Mathlib_import':True,
      'all_original_proof_suffixes_unchanged':True,'original_port_equal_modulo_line_endings':True,
      'provider_boundary_names':[data.NAMES[0],PARENT],'multiplicity_provider':data.PLATFORM_MODULE,
      'multiplicity_actual_kernel_certificate_pending':True,'multiplicity_Published_readback_pending':True,
      'accepted_parent_theorem_id':pub['theorem_id'],'accepted_parent_proof_id':pub['submission_id'],
      'accepted_parent_exact_wire_sha256':sha_bytes(wire),'accepted_parent_wire_mentions_multiplicity':False,
      'accepted_parent_closed_mirror_module_pending':CHILD_MODULE,
      'missing_closed_child_interface':[{'name':PARENT,'original_AST_range':[6196,7240],
         'private_inline_helper':'OAI.PiExponent.Collision.cutoff_mul_high_count_le_sum',
         'requirement':'Original two proof commands, actual compiled closed original-name theorem, full type/refs/owner/Std3 and immutable Accepted snapshot. Old global solution/comparator is insufficient.'}],
      'files':{f:sha_bytes(raw) for f,raw in outputs.items()},'input_hashes':pins,
      'compiler_manifests_created':False,'compiled':False,'validated':False,'submission_ready':False,
      'proposal_status':'Draft','Lean_started':False,'API_used':False}
    outputs['route-preparation.json']=encode(result);return outputs

def check_only():
    outputs=stage_files()
    for name,raw in outputs.items():need((STAGE/name).read_bytes()==raw,'Immutable route/candidate differs: '+name)
    return {'checked_files':len(outputs),'source_AST_units':6,'source_lines':110,
       'Accepted_child_closed_mirror_pending':True,'compiler_manifests_created':False,
       'validated':False,'Lean_started':False,'API_used':False}

def main():
    p=argparse.ArgumentParser(description=__doc__);g=p.add_mutually_exclusive_group(required=True)
    g.add_argument('--prepare',action='store_true');g.add_argument('--check-only',action='store_true');a=p.parse_args()
    if a.prepare:
        for name,raw in stage_files().items():
            path=STAGE/name
            if path.exists():need(path.read_bytes()==raw,'Refusing overwrite: '+name)
            else:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(raw)
    print(json.dumps(check_only(),ensure_ascii=False,indent=2))
if __name__=='__main__':main()
