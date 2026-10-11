from pathlib import Path
import hashlib,json,re,sys
OUT=Path(__file__).resolve().parent;TASK=OUT.parents[2];ROOT=TASK.parent.parent;PROJECT=TASK/'.rt/apfa1'
AUTHOR=TASK/'verification/formalization-analytic-phase-upper-bound-2026-10-07';INDEP=TASK/'verification/formalization-analytic-phase-upper-bound-independent-2026-10-07'
AUTHOR_SHA='a8f8cf52008b69f7b8e7e868a3c754ebc72c89f4f6f1aa89f9ca2bfdf1ff2647'
INDEP_SHA='f487b27f1668432926ad505e4f30a67e41c1abf75ad9690cc2c84369487067cc'
ROOT_GATE=TASK/'verification/formalization-project-handoff-2026-10-07/root-phase-independent-complete-binding-rehash.json'
SOURCE_SHAS=['2b53b56f103bc69322c35d18e120c248cc34402fe831b7be86651f584d3bf4bd','388c2be7c6401e0b0944e5ee9601ddd4f9359f85d05319ce191e6c6a4d0f1635']
TARGETS=[('phase_strictAntiOn_right',''),('phase_global_lt_certified','x hx'),('phase_global_upper_bound','')]
def load(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def bind(p):
 p=p.resolve();r=dict(bytes=p.stat().st_size,sha256=sha(p))
 try:r['task_relative']=p.relative_to(TASK.resolve()).as_posix()
 except ValueError:
  try:r['root_relative']=p.relative_to(ROOT.resolve()).as_posix()
  except ValueError:r['absolute_path']=str(p)
 return r
def resolve(r):return TASK/r['task_relative'] if 'task_relative'in r else ROOT/r['root_relative'] if 'root_relative'in r else Path(r['absolute_path'])
def check(rows):
 for r in rows:
  p=resolve(r);assert p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],str(p)
def dump(p,x):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
def write(p,text):p.parent.mkdir(parents=True,exist_ok=True);assert not p.exists();p.write_text(text,encoding='utf-8')
def decls(text):
 rows=[];ms=list(re.finditer(r'^(def|theorem)\s+(\w+)',text,re.M))
 for i,m in enumerate(ms):
  end=ms[i+1].start() if i+1<len(ms) else text.rfind('end ZetaNine.AnalyticPhase')
  chunk=text[m.start():end].rstrip()+'\n';header=chunk.split(':=',1)[0].rstrip()
  rows.append(dict(kind=m.group(1),name=m.group(2),header=header,source=chunk))
 return rows

def main():
 sys.stdout.reconfigure(encoding='utf-8');assert not PROJECT.exists(),'apfa1 must be absent; never reset contexts'
 assert sha(AUTHOR/'author-audit.json')==AUTHOR_SHA and sha(INDEP/'independent-audit.json')==INDEP_SHA
 root=load(ROOT_GATE);assert root['independent_report_sha256']==INDEP_SHA and root['Root_personally_stream_rehashed_all'] and root['stable_bindings']==26076 and root['mismatches']==0
 native=load(AUTHOR/'author-audit.json');texts=[];sources=[];allrows=[]
 for r,s in zip(native['sources'],SOURCE_SHAS):
  origin=resolve(r['exported_source']);assert sha(origin)==s;original=resolve(r['shared'])
  a=origin.read_text(encoding='utf-8-sig');b=original.read_text(encoding='utf-8-sig');actual=decls(a);initial=decls(b)
  assert [(x['kind'],x['name'],x['header']) for x in actual]==[(x['kind'],x['name'],x['header']) for x in initial]
  for x,y in zip(actual,initial):
   if x['kind']=='def':assert x['source']==y['source']
  texts.append(a);allrows+=actual;sources.append(dict(export=bind(origin),original=bind(original)))
 definitions=[x for x in allrows if x['kind']=='def'];theorems=[x for x in allrows if x['kind']=='theorem'];assert len(definitions)==7 and len(theorems)==34
 canonical='Definitions/Def_ZetaNine_AnalyticPhase.lean'
 preamble='import Mathlib.Analysis.SpecialFunctions.Log.Deriv\nimport Mathlib.Analysis.Calculus.Deriv.MeanValue\nimport Mathlib.Tactic\n\nset_option autoImplicit false\nnoncomputable section\nopen Set\nopen scoped BigOperators\n'
 definition=preamble+'\nnamespace ZetaNine.AnalyticPhase\n\n'+ '\n'.join(x['source'] for x in definitions)+'\nend ZetaNine.AnalyticPhase\n'
 # All verified proof declarations retained, original headers and bodies unchanged.
 proof='import Definitions.Def_ZetaNine_AnalyticPhase\nimport Mathlib.Tactic\n\nset_option autoImplicit false\nset_option maxHeartbeats 8000000\nnoncomputable section\nopen Set\nopen scoped BigOperators\nnamespace ZetaNine.AnalyticPhase\n\n'+'\n'.join(x['source'] for x in theorems)+'\nend ZetaNine.AnalyticPhase\n\nopen ZetaNine.AnalyticPhase\n'
 byname={x['name']:x for x in theorems}
 staged=OUT/'staged';write(staged/canonical,definition);payloads=[dict(kind='definition',path=canonical,binding=bind(staged/canonical))];targetplan=[]
 for name,args in TARGETS:
  row=byname[name];localref='Theorems/Thm_ZetaNine_AnalyticPhase_'+name+'.lean';localsol='Solutions/Sol_ZetaNine_AnalyticPhase_'+name+'.lean'
  ref='import Definitions.Def_ZetaNine_AnalyticPhase\nset_option autoImplicit false\nopen Set\nopen ZetaNine.AnalyticPhase\n\n'+row['header'].replace('theorem '+name,'theorem ZetaNine.AnalyticPhase.'+name,1)+' := by sorry\n'
  solution=proof+row['header'].replace('theorem '+name,'theorem solution',1)+' := by\n  exact ZetaNine.AnalyticPhase.'+name+(' '+args if args else '')+'\n\n#print axioms solution\n'
  write(staged/localref,ref);write(staged/localsol,solution)
  payloads += [dict(kind='statement_type_catalog_only',path=localref,binding=bind(staged/localref)),dict(kind='complete_solution',path=localsol,binding=bind(staged/localsol))]
  targetplan.append(dict(theorem_name='ZetaNine.AnalyticPhase.'+name,local_reference=localref,local_solution=localsol,wrapper_arguments=args,exact_original_header=row['header']))
 oracle=[]
 for source,name in zip(texts,['AnalyticPhase','AnalyticPhaseUpperBound']):
  source=source.replace('namespace ZetaNine.AnalyticPhase','namespace PhasePlatformNativeOracle').replace('end ZetaNine.AnalyticPhase','end PhasePlatformNativeOracle')
  source=source.replace('import missions.zeta9.formalization.AnalyticPhase\n','import Native.AnalyticPhase\n')
  oracle.append(dict(module='Native.'+name,path='Native/'+name+'.lean',source=source))
 # Generic strict lossless DAG SOURCE only, no mathematical object/cache borrowing.
 core=TASK/'.rt/api1/APIPhaseExprDagV1.lean';fixture=TASK/'.rt/api1/APIPhaseExprDagValidationV1.lean'
 coretext=core.read_text(encoding='utf-8');assert coretext.startswith('import Lean\n') and 'CoefficientMap' not in coretext
 fixturetext=fixture.read_text(encoding='utf-8').replace('import APIPhaseExprDagV1\n','import PhasePlatformExprDagV1\n').replace('import missions.zeta9.formalization.AnalyticPhaseUpperBound\n','import Definitions.Def_ZetaNine_AnalyticPhase\n')
 assert 'missions.' not in fixturetext
 configs=[(x,TASK/'.rt/aph1'/x) for x in ['lean-toolchain','lake-manifest.json']]
 generic_wrapper=(TASK/'.rt/psi1/lean_call.py').read_text(encoding='utf-8').replace('PARAMETER_SUMMATION_INDEPENDENT_PATH_RECEIPT','PHASE_PLATFORM_PATH_RECEIPT')
 contexts=[];PROJECT.mkdir()
 schedules=[]
 for tag in ['native','definition','reference','right','certified','global']:
  ctx=PROJECT/tag;ctx.mkdir();rows=[]
  write(ctx/'lakefile.toml','name = "phasePlatformAuthor_'+tag+'"\nbuildDir = "b"\n[[require]]\nname = "mathlib"\ngit = "https://github.com/leanprover-community/mathlib4.git"\nrev = "0df444a360eaa60ab8c11dca51a86af692955474"\n[[lean_lib]]\nname = "Phase"\nroots = ["Definitions.Def_ZetaNine_AnalyticPhase"]\n')
  for name,origin in configs:(ctx/name).write_bytes(origin.read_bytes())
  write(ctx/'lean_call.py',generic_wrapper)
  if tag=='native':
   for text,name in zip(texts,['AnalyticPhase','AnalyticPhaseUpperBound']):
    rel='missions/zeta9/formalization/'+name+'.lean';write(ctx/rel,text);rows.append(dict(module='missions.zeta9.formalization.'+name,path=rel,binding=bind(ctx/rel),label='native-'+name))
  else:
   write(ctx/canonical,definition);rows.append(dict(module='Definitions.Def_ZetaNine_AnalyticPhase',path=canonical,binding=bind(ctx/canonical),label='actual-definition'))
   if tag=='reference':
    for target in targetplan:
     rel=target['local_reference'];write(ctx/rel,(staged/rel).read_text(encoding='utf-8'));rows.append(dict(module=rel[:-5].replace('/','.'),path=rel,binding=bind(ctx/rel),label='reference-type-only-'+target['theorem_name'].rsplit('.',1)[-1]))
   else:
    for row in oracle:write(ctx/row['path'],row['source']);rows.append(dict(module=row['module'],path=row['path'],binding=bind(ctx/row['path']),label='own-oracle-'+row['module'].rsplit('.',1)[-1]))
    if tag!='definition':
     index=['right','certified','global'].index(tag);rel=targetplan[index]['local_solution'];write(ctx/rel,(staged/rel).read_text(encoding='utf-8'));rows.append(dict(module=rel[:-5].replace('/','.'),path=rel,binding=bind(ctx/rel),label='complete-solution'))
    for module,text in [('PhasePlatformExprDagV1',coretext),('PhasePlatformExprDagValidationV1',fixturetext)]:
     write(ctx/(module+'.lean'),text);rows.append(dict(module=module,path=module+'.lean',binding=bind(ctx/(module+'.lean')),label='own-'+module))
  contexts.append(dict(tag=tag,task_relative=ctx.relative_to(TASK).as_posix(),initially_absent=True,math_sources=rows))
 dump(OUT/'target-plan.json',dict(definition='ZetaNine_AnalyticPhase',local_definition=canonical,targets=targetplan,existing_definitions=[],canonical_dependencies=[],payloads=payloads,Mathlib_ENV='0df444a360eaa60ab8c11dca51a86af692955474',raw_references_are_type_only_never_proof=True))
 stable=[bind(p) for p in staged.rglob('*.lean')]+[bind(p) for p in PROJECT.rglob('*') if p.is_file()]+[bind(OUT/'inspect_prepare.py'),bind(ROOT_GATE),bind(AUTHOR/'author-audit.json'),bind(INDEP/'independent-audit.json')]
 dump(OUT/'source-preparation.json',dict(role='Phase platform AUTHOR; not native author or native/platform independent reviewer',native_author_SHA=AUTHOR_SHA,native_independent_SHA=INDEP_SHA,Root_native_independent_full_binding_gate=bind(ROOT_GATE),critical_sources=sources,native_definitions=definitions,native_theorems=theorems,exact_original_34_forall_headers_preserved=True,exact_original_7_definition_source_preserved=True,contexts=contexts,payloads=payloads,stable_files=stable,original_native_definition_and_proof_SOURCE_reuse_disclosed=True,oracle_namespace_altered_ONLY_for_independent_whole_value_and_kernel_type_comparison=True,full_raw_Expr_differences_must_be_recorded_honestly=True,generic_DAG_source_reuse=dict(core=bind(core),fixtures=bind(fixture)),foreign_mathematical_objects_borrowed=False,API_calls=0,Root_scope_writes=0,platform_independent_gate_still_required=True,complete_Z9_A=False,author_PASS_claimed=False))
 print(json.dumps(dict(status='PURE_PHASE_PLATFORM_7_PAYLOAD_SOURCE_STAGING',payloads=7,contexts=6,original_defs=7,original_theorems=34,sourceprep_SHA=sha(OUT/'source-preparation.json')),indent=2))
if __name__=='__main__':main()
