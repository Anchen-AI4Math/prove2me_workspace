from run_step import *
verify();enroll=load(OUT/'preparation-enrollment.json')
assert load(OUT/'fresh-source-compile-receipt.json')['complete']
graph=(BATCH/'extract_decl_graph.lean').read_text(encoding='utf-8-sig')
for name in ['decl_graph.jsonl','lean-path-selected.json']:
 assert graph.count('"../'+name+'"')==1;graph=graph.replace('"../'+name+'"','"'+(OUT/name).as_posix()+'"')
source=OUT/'g.lean';write(source,graph);run('actual independent Stage1 graph',source,N)
template=(BATCH/'extract_CoefficientMapTelescoper_sketch.lean').read_text(encoding='utf-8-sig')
old='../CoefficientMapTelescoper-oracle-input.lean';assert template.count(old)==1
for i,name in enumerate(list(enroll['original_source_hashes'])+['HarmonicStability']):
 snapshot=OUT/(name+'-s.lean');src=OUT/(f'p{i}.lean');write(src,template.replace(old,snapshot.as_posix()))
 actual=PROJECT/'Definitions/Def_ZetaNine_HarmonicStability.lean' if name=='HarmonicStability' else PROJECT/'missions/zeta9/formalization'/(name+'.lean')
 run('actual independent Stage2 '+name,src,N,args=[actual.as_posix(),'ZetaNine'],copy=OUT/(name+'-f.jsonl'))
src=OUT/'h.lean';write(src,(BATCH/'extract_header.lean').read_bytes());run('actual independent header',src,N,args=[(PROJECT/'missions/zeta9/formalization/CoefficientMapTelescoper.lean').as_posix()],copy=OUT/'header.jsonl')
for i,r in enumerate(enroll['fixed_native_controls']):
 src=OUT/(f'cp{i}.lean');write(src,template.replace(old,(OUT/(f'control{i}-s.lean')).as_posix()))
 run('actual independent control parser '+r['module'],src,N,args=[(PROJECT/(r['module']+'.lean')).as_posix()],copy=OUT/(f'control{i}-f.jsonl'))
dump(OUT/'extraction-summary.json',{'complete':True,'actual_graph_records':len(rows(OUT/'decl_graph.jsonl')),'source_Stage2_count':10,'control_Stage2_count':2,'header_count':1,'no_author_objects':True})
