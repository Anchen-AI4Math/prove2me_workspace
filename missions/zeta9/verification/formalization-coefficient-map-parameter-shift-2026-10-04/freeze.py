"""Freeze actual author evidence; preserve the initial failed compilation."""
import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path

OUT = Path(__file__).resolve().parent
TASK = OUT.parents[1]
ROOT = TASK.parents[1]
SOURCE = TASK / 'formalization/CoefficientMapParameterShift.lean'
EXPECTED = '5e472326fd47f4ad470cf89493fa75e57e22806cd1b1ac12697c878b06f69065'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def load(path):
    return json.loads(path.read_text(encoding='utf-8'))

def main():
    assert sha(SOURCE) == EXPECTED
    state = load(OUT / 'preparation-state.json')
    first = load(OUT / 'first-build-receipt.json')
    compile_receipt = load(OUT / 'attempt-01/receipt.json')
    audit = load(OUT / 'type-audit-receipt.json')
    assert len(first['rows']) == 14
    assert all(r['actual_exit'] == 0 for r in first['rows'][:13])
    assert first['rows'][13]['actual_exit'] == 1
    assert compile_receipt['actual_exit'] == audit['actual_exit'] == 0
    assert compile_receipt['source_sha256'] == audit['source_sha256'] == EXPECTED
    assert compile_receipt['inherited_Lean_search_paths_removed']
    assert audit['inherited_Lean_search_paths_removed']
    paths = [SOURCE]
    project = Path(state['project'])
    for row in state['sources']:
        original = ROOT / row['root_relative']
        copied = project / row['project_relative']
        expected = EXPECTED if original == SOURCE else row['sha256']
        assert sha(original) == sha(copied) == expected
        paths.append(original)
    rows = first['rows'] + [compile_receipt, audit]
    for row in rows:
        for name in ('log', 'exit_file'):
            path = OUT / row[name]
            assert sha(path) == row['log_sha256' if name == 'log' else 'exit_sha256']
            paths.append(path)
        assert int((OUT / row['exit_file']).read_text()) == row['actual_exit']
    assert sha(OUT / 'attempt-01/compiled.olean') == compile_receipt['retained_object_sha256']
    assert (OUT / 'attempt-01/CoefficientMapParameterShift.lean').read_bytes() == SOURCE.read_bytes()
    assert sha(OUT / 'type-audit.lean') == audit['audit_source_sha256']
    log = (OUT / audit['log']).read_text(encoding='utf-8')
    reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log)
    assert len(reports) == 20
    axiom_records = []
    for name, body in reports:
        printed_axioms = [x.strip() for x in body.split(',') if x.strip()]
        axioms = [re.sub(r'\.\{[^}]*\}', '', x) for x in printed_axioms]
        assert set(axioms) <= STANDARD, (name, axioms)
        axiom_records.append({'name': name, 'axioms': axioms, 'printed_axioms': printed_axioms})
    for path in OUT.rglob('*'):
        if path.is_file() and path.suffix in {'.lean', '.py', '.json', '.txt', '.log', '.olean'}:
            if path.name not in {'author-audit.json', 'source-manifest.json', 'SHA256SUMS.txt'}:
                paths.append(path)
    files = []
    for path in sorted(set(paths), key=lambda p: p.as_posix()):
        assert path.resolve().is_relative_to(ROOT.resolve())
        files.append({'root_relative': path.relative_to(ROOT).as_posix(),
                      'sha256': sha(path), 'bytes': path.stat().st_size})
    result = {'verdict': 'PASS', 'checked_at': datetime.now(timezone.utc).isoformat(),
              'source_sha256': EXPECTED, 'stage': 'native author only',
              'source_records': 17, 'explicit_endpoint_types': 3,
              'axiom_reports': axiom_records, 'stable_files': files,
              'actual_successful_parent_compiles': 13,
              'actual_successful_final_source_compiles': 1,
              'actual_successful_final_type_audits': 1,
              'historical_failures_retained_and_excluded': [first['rows'][13]],
              'freeze_preflight_diagnostic': 'First Python freeze rejected universe-suffixed standard axiom names; normalization repaired before this freeze; no Lean execution in the failed freeze.',
              'fresh_initial_cache': first['fresh_cache_before_first'],
              'native_objects_borrowed': first['native_objects_borrowed'],
              'actual_own_cache_resolution_independently_verified': False,
              'independent_review': 'PENDING', 'platform_acceptance_claimed': False,
              'five_formal_output_transport_proved': False,
              'infinite_sum_parameter_transport_proved': False}
    target = OUT / 'author-audit.json'
    assert not target.exists(), 'Author freeze already exists; do not overwrite'
    target.write_text(json.dumps(result, ensure_ascii=False, indent=2)+'\n', encoding='utf-8')
    print('Author PASS:', len(files), 'bindings; 20 Std3 reports; SHA256', sha(target))

if __name__ == '__main__':
    main()
