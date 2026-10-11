from pathlib import Path
import ast, hashlib, json, re, sys
sys.stdout.reconfigure(encoding='utf-8')
OUT=Path(__file__).resolve().parent; TASK=OUT.parents[1]; ROOT=TASK.parents[1]
AUTHOR=TASK/'verification/formalization-coefficient-map-connection-2026-10-04'
PROJECT=OUT/'p'; BUILD=TASK/'.rt/ci1/b'; MODULE='missions.zeta9.formalization.CoefficientMapConnection'
SOURCE=TASK/'formalization/CoefficientMapConnection.lean'
CONTROL_HASHES={
 'compile-receipt.json':'d6dec3cc709eba34d307ed85d521906e13129a0453a22cb32ebf6d77b011c9f0',
 'type-audit-receipt.json':'6a134c567b23f3319eeb5f3bdf28e3fa099ea715cf5894d99accd8e12329be8a',
 'author-audit.json':'306fb4fc9b838c50c2928317994107f20605e4f8c9acd610d22d962492b75972',
 'source-manifest.json':'dec02f5213b8e92cd2575225b55ade114aff7af6561bbd2b296bf2ebfe3a9190',
 'SHA256SUMS.txt':'6fc61bb0625ad243a09df436c919955be60686d2ea9dc2ba4288f15448ba7a99'}
SOURCE_HASH='098d82f606b5b6fda1e1d08524ef23db3ed3943a90ae109439f5046c031337e8'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,d): p.parent.mkdir(parents=True,exist_ok=True); p.write_bytes((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode())
def bind(p):
 p=p.resolve();row={'root_relative':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':sha(p)}
 if p.is_relative_to(TASK):row['task_relative']=p.relative_to(TASK).as_posix()
 return row
def verify():
 assert sha(SOURCE)==SOURCE_HASH
 for n,h in CONTROL_HASHES.items(): assert sha(AUTHOR/n)==h,n
 manifest=json.loads((AUTHOR/'source-manifest.json').read_text(encoding='utf-8'))
 assert len(manifest['files'])==53
 for row in manifest['files']:
  p=TASK/row['task_relative']; assert p.resolve().is_relative_to(TASK)
  assert p.stat().st_size==row['bytes'] and sha(p)==row['sha256'],row
 entries=(AUTHOR/'SHA256SUMS.txt').read_text(encoding='utf-8').splitlines()
 assert len(entries)==54
 for line in entries:
  h,n=line.split('  ',1);p=(AUTHOR/n).resolve();assert p.is_relative_to(TASK) and sha(p)==h,n
 audit=json.loads((AUTHOR/'author-audit.json').read_text(encoding='utf-8'))
 assert audit['verdict']=='PASS' and len(audit['checks'])==23 and all(x['pass'] for x in audit['checks'])
 receipt=json.loads((AUTHOR/'compile-receipt.json').read_text(encoding='utf-8'))
 row=receipt['rows'][-1];assert row['exit_code']==0 and row['attempt']==7 and row['source_sha256']==SOURCE_HASH
 assert (AUTHOR/row['exit_file']).read_text().strip()=='0'
 assert 'Build completed successfully (3006 jobs)' in (AUTHOR/row['log']).read_text(encoding='utf-8')
 assert sha(AUTHOR/row['retained_object'])==row['retained_object_sha256']
 return manifest
if __name__=='__main__':
 verify();assert not BUILD.exists(),'Never overwrite a used independent cache'
 PROJECT.mkdir(parents=True,exist_ok=True)
 copies=[(SOURCE,PROJECT/(MODULE.replace('.','/')+'.lean')),
  (AUTHOR/'type-audit.lean',PROJECT/'a.lean'),(AUTHOR/'boundary-audit.lean',PROJECT/'ab.lean'),
  (ROOT/'lean-toolchain',PROJECT/'lean-toolchain'),(ROOT/'lake-manifest.json',PROJECT/'lake-manifest.json')]
 for source,target in copies: target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(source.read_bytes())
 (PROJECT/'lakefile.lean').write_bytes(('import Lake\nopen Lake DSL\npackage connectionIndependent where\n  buildDir := "'+BUILD.as_posix()+'"\nlean_lib Native where\n  roots := #[`'+MODULE+']\n').encode())
 original_names=re.findall(r'^(def|theorem)\s+(\w+)',SOURCE.read_text(encoding='utf-8'),re.M)
 own_names=re.findall(r'^theorem\s+(\w+)',(OUT/'b.lean').read_text(encoding='utf-8'),re.M)
 allp=[target for _,target in copies]+[PROJECT/'lakefile.lean',OUT/'b.lean',OUT/'t.lean']
 paths=[]
 for p in allp+[BUILD/(MODULE.replace('.','/')+suf) for suf in ['.olean','.olean.private','.olean.server','.ilean','.ir','.c','.c.o','.trace']]+[OUT/(f's{i:02}'+suf) for i in range(1,7) for suf in ['.ps1','.log','-exit.txt']]:
  assert len(str(p))+64<=259,(str(p),len(str(p))+64)
  paths.append({'path_task_relative':p.relative_to(TASK).as_posix(),'absolute_length':len(str(p)),'length_with_64_suffix':len(str(p))+64})
 for n in ['prepare.py','driver.py','finalize.py']:
  p=OUT/n
  if p.exists():ast.parse(p.read_text(encoding='utf-8'))
 dump(OUT/'output-path-preflight.json',{'all_paths_with_64_char_suffix_below_260':True,'maximum':max(r['length_with_64_suffix'] for r in paths),'paths':paths})
 old=TASK/'verification/coefficient-map-connection-offline-precheck-2026-10-04'
 dump(OUT/'enrollment.json',{'status':'PINNED_FROZEN_AUTHOR_PARENT_LANE_GRANTED_NOT_YET_INDEPENDENT_PASS','source_sha256':SOURCE_HASH,
  'parent_lane_authorization':'Root 2026-10-04 explicitly allocated one serial lane after author freeze',
  'new_cache_task_relative':BUILD.relative_to(TASK).as_posix(),'borrowed_native_objects':False,'only_Mathlib_package_cache_shared':True,
  'controls':CONTROL_HASHES,'author_members':54,'expected_textual_source_declarations':original_names,
  'expected_own_boundary_names':own_names,'actual_parser_or_module_counts_not_assumed':True,
  'stable_files':[bind(p) for p in allp],
  'historical_offline_39_checks':{'role':'symbolic precheck on earlier core snapshot, not the final native proof','bindings':[bind(old/n) for n in ['offline-alignment-report.json','precheck-freeze.json','observed-Connection-source.lean','observed-connection-paper.md']]}})
 print('Pinned author 54 members; copied actual source/types/boundaries; prepared',len(own_names),'own boundary theorems; cache absent; path maximum',max(r['length_with_64_suffix'] for r in paths),flush=True)
