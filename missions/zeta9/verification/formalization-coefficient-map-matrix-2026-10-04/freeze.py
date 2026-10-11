"""Freeze exact successful Matrix author evidence; preserve failed attempts."""
import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path
import run_author

OUT = Path(__file__).resolve().parent
TASK = OUT.parents[1]
ROOT = TASK.parents[1]
SOURCE = TASK / 'formalization/CoefficientMapMatrix.lean'
EXPECTED = 'a4bf1766c8bbcc1f2f83af27594ba10b3dfcd4e55058f10ccc4d4b25cb9c6d99'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    run_author.gate()
    assert sha(SOURCE) == EXPECTED
    receipts = []
    paths = {SOURCE, Path(__file__).resolve()}
    records = []
    for name, count in [('source-audit-01',22),('endpoint-audit-01',12)]:
        receipt = json.loads((OUT/name/'receipt.json').read_text(encoding='utf-8'))
        assert receipt['actual_exit'] == 0 and receipt['source_sha256'] == EXPECTED
        log = (OUT/receipt['log']).read_text(encoding='utf-8')
        found = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log)
        assert len(found) == count
        for declaration, body in found:
            printed = [x.strip() for x in body.split(',') if x.strip()]
            normalized = [re.sub(r'\.\{[^}]*\}','',x) for x in printed]
            assert set(normalized) <= STANDARD, (declaration,normalized)
            records.append({'name':declaration,'axioms':normalized,'printed_axioms':printed})
    for path in sorted(OUT.glob('*/receipt.json')):
        row = json.loads(path.read_text(encoding='utf-8'))
        for key, digest_key in [('log','log_sha256'),('exit_file','exit_sha256')]:
            assert sha(OUT/row[key]) == row[digest_key]
        assert int((OUT/row['exit_file']).read_text()) == row['actual_exit']
        receipts.append(row)
    final = json.loads((OUT/'compile-03/receipt.json').read_text(encoding='utf-8'))
    assert final['actual_exit'] == 0 and final['source_sha256'] == EXPECTED
    assert sha(OUT/'compile-03/compiled.olean') == final['retained_object_sha256']
    assert (OUT/'compile-03/CoefficientMapMatrix.lean').read_bytes() == SOURCE.read_bytes()
    assert [r['actual_exit'] for r in receipts].count(0) == 3
    assert [r['actual_exit'] for r in receipts].count(1) == 2
    parent = json.loads(run_author.AUTHOR.read_text(encoding='utf-8'))
    for row in parent['stable_files']:
        if row['root_relative'].endswith('.lean') and '/formalization/' in row['root_relative']:
            paths.add(ROOT/row['root_relative'])
    paths.add(ROOT/'Definitions/Def_ZetaNine_HarmonicStability.lean')
    for path in OUT.rglob('*'):
        if path.is_file() and path.suffix in {'.lean','.py','.json','.log','.txt','.olean','.md'}:
            if path.name not in {'author-audit.json','source-manifest.json','SHA256SUMS.txt'}:
                paths.add(path)
    files = []
    for path in sorted(paths,key=lambda p:p.as_posix()):
        assert path.resolve().is_relative_to(ROOT.resolve())
        files.append({'root_relative':path.relative_to(ROOT).as_posix(),
                      'bytes':path.stat().st_size,'sha256':sha(path)})
    checks = [{'name':name,'pass':True} for name in [
        'source_exact_bytes','final_native_build_actual_zero','source22_exact_type_and_axioms',
        'six_explicit_endpoint_types','five_complete_definition_value_rfl',
        'actual_pure_nine_inverse_nonzero','all34_axiom_reports_standard_only',
        'frozen_parent59_bindings_and14_source_copies','two_failed_source_attempts_retained']]
    report = {'verdict':'PASS','checked_at':datetime.now(timezone.utc).isoformat(),
              'source_sha256':EXPECTED,'checks':checks,'source_records':22,
              'definitions':5,'theorems':17,'author_endpoint_records':12,
              'axiom_reports':records,'stable_files':files,'actual_successes':3,
              'retained_failed_attempts':[r for r in receipts if r['actual_exit']],
              'author_parent_cache_reused':True,'fresh_parent_build_claimed':False,
              'independent_objects_borrowed':False,'frozen_parent_author_sha256':run_author.FROZEN,
              'source_precompilation_comment_is_historical':True,
              'scope':'actual monomial-row F and S inverse formula; original even n>=2; rational multiplier',
              'integral_multiplier_preimage_proved':False,'independent_review':'PENDING',
              'platform_acceptance_claimed':False,'irrationality_proved':False}
    target = OUT/'author-audit.json'
    assert not target.exists()
    target.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print('Matrix author9 checks /34 Std3 records /',len(files),'bindings; SHA256',sha(target))

if __name__ == '__main__':
    main()
