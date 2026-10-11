"""Versioned repair of an unused boundary; mathematical endpoint bytes unchanged."""
import sys
sys.dont_write_bytecode=True
import prepare as p

def main():
    plan=p.load(p.OUT/'author-controls-plan-2026-10-07.json')
    for row in plan['staged_controls']:
        old=row['label'];new=old.removesuffix('_V1')+'_V2'
        source=(p.OUT/(old+'.lean')).read_text(encoding='utf-8-sig')
        start=source.index('theorem checked_actual_weighted_jets_agree')
        end=source.index('open Lean Meta',start)
        source=source[:start]+source[end:]
        source=source.replace('  emitAuthorProof `checked_actual_weighted_jets_agree "closed_boundary_proof"\n','')
        p.write(p.OUT/(new+'.lean'),source);p.write(p.PROJECT/(new+'.lean'),source)
        row['label']=new;row['boundary_count']=9
    plan['excluded_other_unreached_boundary']=['checked_actual_weighted_jets_agree']
    plan['unreached_weighted_boundary_reason']='Requires excluded extra numerator_local_coefficient_weighted_agreement bridge; not reachable from the three generic endpoints. Original full native boundary proof remains frozen.'
    p.dump(p.OUT/'author-controls-plan-v2-2026-10-07.json',plan)
    source=(p.OUT/'execute_author_v3_20261007.py').read_text(encoding='utf-8-sig')
    source=source.replace("    compile_module('author-native-reachable-v1',plan['native_control'])", "    latest={r['label']:r for r in p.load(p.OUT/'compile-receipt.json')['rows']}\n    assert latest['author-native-reachable-v1']['exit_code']==0\n    print('prior actual native control exit0 retained; no Lean rerun.',flush=True)")
    source=source.replace("'author-controls-plan-2026-10-07.json'", "'author-controls-plan-v2-2026-10-07.json'")
    source=source.replace("+'-v1',row['label']", "+'-v2',row['label']")
    source=source.replace("    import argparse", "    import argparse\n    sys.stdout.reconfigure(encoding='utf-8')")
    p.write(p.OUT/'execute_author_v4_20261007.py',source)
    print('Prepared V2 controls; no Lean executed and all older versions unchanged.')

if __name__=='__main__':main()
