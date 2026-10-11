"""Continue only the unfinished official parser/header/staged-parent phase, serial lane2."""
import sys
import prepare as p
import run_actual as actual

def main():
    sys.stdout.reconfigure(encoding='utf-8')
    state=actual.gate()
    row=next(x for x in state['native_sources'] if x['parser_name']=='CoefficientMapMatrix')
    actual.run('stage2-CoefficientMapMatrix',['--run','extract_CoefficientMapMatrix_sketch_v2.lean',row['project_relative'],'ZetaNine'],'CoefficientMapMatrix-sketch_info.jsonl')
    actual.run('stage2-header',['--run','extract_header.lean','missions/zeta9/formalization/CoefficientMapMatrix.lean'],'header_info.jsonl')
    parents=[x for x in state['parent_definitions'] if x['module']!='Definitions.Def_ZetaNine_HarmonicStability']
    for row in actual.topological_sources(parents,'root_relative'):
        obj='b/lib/lean/'+row['module'].replace('.','/')+'.olean'
        (p.PROJECT/obj).parent.mkdir(parents=True,exist_ok=True)
        actual.run('build-parent-'+row['module'].rsplit('.',1)[1],['-o',obj,row['root_relative']])
    latest={x['label']:x for x in p.load(p.OUT/'compile-receipt.json')['rows']}
    assert len(latest)==44 and all(x['exit_code']==0 for x in latest.values())
    print('All44 distinct source/control/oracle labels actual0; first Matrix parser failure retained and excluded.')

if __name__=='__main__':main()
