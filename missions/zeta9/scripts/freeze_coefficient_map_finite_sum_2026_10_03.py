"""Freeze observed native finite-sum compilation, without reading credentials."""
from __future__ import annotations
import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
OUT = TASK / 'verification/formalization-coefficient-map-finite-sum-2026-10-03'
SOURCE = TASK / 'formalization/CoefficientMapFiniteSum.lean'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(name, value):
    (OUT / name).write_text(json.dumps(value, ensure_ascii=False, indent=2)+'\n', encoding='utf-8')


def main():
    assert not (OUT / 'compile-receipt.json').exists(), 'Already frozen; do not overwrite.'
    final_log = TASK / 'formalization/CoefficientMapFiniteSum.attempt-04.log'
    final_exit = TASK / 'formalization/CoefficientMapFiniteSum.attempt-04-exit.txt'
    audit_log = OUT / 'type-audit-attempt-01.log'
    audit_exit = OUT / 'type-audit-attempt-01-exit.txt'
    assert final_exit.read_text(encoding='utf-8-sig').strip() == '0'
    assert audit_exit.read_text(encoding='utf-8-sig').strip() == '0'
    assert 'sorryAx' not in final_log.read_text(encoding='utf-8')
    records = [json.loads(line) for line in audit_log.read_text(encoding='utf-8').splitlines() if line.startswith('{')]
    declarations = re.findall(r'(?m)^(?:def|theorem) (\w+)\b', SOURCE.read_text(encoding='utf-8'))
    assert len(declarations) == 11 and len(records) == 17
    observed = {r['declaration'] for r in records}
    assert {f'ZetaNine.CoefficientMapFiniteSum.{name}' for name in declarations} <= observed
    assert all(set(r['axioms']) <= STANDARD for r in records)
    assert all(set(r['axioms']) == STANDARD for r in records if r['definitionValue'] is None)
    assert sum(r['definitionValue'] is not None for r in records) == 4
    save('type-report.json', records)
    dependencies = [ROOT/'Definitions/Def_ZetaNine_HarmonicStability.lean']
    dependencies += [TASK/'formalization'/f'{name}.lean' for name in
                     ('CoefficientMap', 'CoefficientMapJet', 'CoefficientMapInjectivity', 'CoefficientMapPartialFractions')]
    receipt = {
        'verdict': 'PASS_ACTUAL_FINITE_SUM_IDENTITY_ONLY',
        'date_utc': datetime.now(timezone.utc).isoformat(),
        'source': str(SOURCE), 'source_sha256': sha(SOURCE),
        'environment': {'lean_toolchain': 'leanprover/lean4:v4.33.1',
                        'mathlib_manifest_revision': '0df444a360eaa60ab8c11dca51a86af692955474'},
        'source_compile': {'status': 'observed', 'exit_code': 0, 'observed_exec_session_id': 60126,
            'observed_completion_chunk_id': '0d1bb3', 'log': str(final_log), 'log_sha256': sha(final_log),
            'observed_exit_file': str(final_exit), 'object': str(SOURCE.with_suffix('.olean')),
            'object_sha256': sha(SOURCE.with_suffix('.olean')), 'printed_targets': 6,
            'command': ['lake','env','lean','-o','missions/zeta9/formalization/CoefficientMapFiniteSum.olean',
                        'missions/zeta9/formalization/CoefficientMapFiniteSum.lean'],
            'working_directory': str(ROOT), 'lean_path_prefix': ROOT.as_posix(),
            'only_standard_three_axioms': True},
        'imported_statement_audit': {'status': 'observed', 'exit_code': 0,
            'observed_exec_session_id': 43503, 'observed_completion_chunk_id': 'a3488d',
            'source': str(OUT/'type-audit.lean'), 'source_sha256': sha(OUT/'type-audit.lean'),
            'log': str(audit_log), 'log_sha256': sha(audit_log), 'observed_exit_file': str(audit_exit),
            'source_definitions': 4, 'source_theorems': 7, 'additional_exact_statements': 6,
            'records': 17, 'all_source_declarations_covered': True, 'actual_definition_values': 4,
            'only_standard_three_axioms': True, 'report': 'type-report.json',
            'report_sha256': sha(OUT/'type-report.json'),
            'command': ['lake','env','lean', (OUT/'type-audit.lean').relative_to(ROOT).as_posix()],
            'working_directory': str(ROOT), 'lean_path_prefix': ROOT.as_posix()},
        'unchanged_dependencies': [{'source': str(p), 'source_sha256': sha(p)} for p in dependencies],
        'retained_attempts': [{'attempt': i, 'exit_code': int((TASK/f'formalization/CoefficientMapFiniteSum.attempt-{i:02d}-exit.txt').read_text(encoding='utf-8-sig').strip()),
                              'log_sha256': sha(TASK/f'formalization/CoefficientMapFiniteSum.attempt-{i:02d}.log')}
                             for i in range(1,5)],
        'limitations': ['Finite rational identity only; no analytic convergence or infinite sum.',
                        'The odd-only identity explicitly assumes the five actual coefficient cancellations.',
                        'Properness alone does not cancel rho_1: n=0,W=X^4 gives finiteL=H_T and rho_1=1.',
                        'No assertion of original aggregate F invertibility, J or irrationality.']}
    save('compile-receipt.json', receipt)
    files = [SOURCE, SOURCE.with_suffix('.olean'), OUT/'type-audit.lean', audit_log, audit_exit,
             OUT/'type-report.json', OUT/'compile-receipt.json']
    files += sorted((TASK/'formalization').glob('CoefficientMapFiniteSum.attempt-*.log'))
    files += sorted((TASK/'formalization').glob('CoefficientMapFiniteSum.attempt-*-exit.txt'))
    lines = [f'{sha(p)}  {p.relative_to(TASK).as_posix()}' for p in files]
    (OUT/'SHA256SUMS.txt').write_text('\n'.join(lines)+'\n',encoding='utf-8')
    assert all(sha(TASK/line.split('  ',1)[1]) == line.split('  ',1)[0] for line in lines)
    print(f'Finite-sum freeze PASS: 17 type records, {len(files)} frozen files; SHA256 {sha(SOURCE)}.')


if __name__ == '__main__':
    main()
