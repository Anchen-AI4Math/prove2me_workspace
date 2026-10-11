"""Freeze the observed successful shift-operator proof and its actual type audit."""
from __future__ import annotations
import hashlib
import json
import re
import sys
from datetime import datetime, timezone
from pathlib import Path

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
OUT = TASK / 'verification/formalization-coefficient-map-shift-degree-2026-10-04'
SOURCE = TASK / 'formalization/CoefficientMapShiftDegree.lean'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(name, value):
    (OUT/name).write_text(json.dumps(value, ensure_ascii=False, indent=2)+'\n', encoding='utf-8')


def main():
    sys.stdout.reconfigure(encoding='utf-8')
    assert not (OUT/'compile-receipt.json').exists(), 'Keep the existing freeze unchanged.'
    toolchain = (ROOT/'lean-toolchain').read_text(encoding='utf-8').strip()
    manifest = json.loads((ROOT/'lake-manifest.json').read_text(encoding='utf-8'))
    mathlib = next(p for p in manifest['packages'] if p['name'] == 'mathlib')
    assert toolchain == 'leanprover/lean4:v4.33.1'
    assert mathlib['rev'] == '0df444a360eaa60ab8c11dca51a86af692955474'
    source_log = TASK/'formalization/CoefficientMapShiftDegree.compile-attempt3.log'
    source_exit = TASK/'formalization/CoefficientMapShiftDegree.compile-attempt3-exit.txt'
    audit_log = OUT/'type-audit-attempt1.log'
    audit_exit = OUT/'type-audit-attempt1-exit.txt'
    assert source_exit.read_text().strip() == audit_exit.read_text().strip() == '0'
    text = source_log.read_text(encoding='utf-8')
    assert not re.search(r'\b(?:error|sorryAx)\b', text)
    printed = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', text)
    assert len(printed) == 5 and all({x.strip() for x in s.split(',')} == STANDARD for s in printed)
    rows = [json.loads(line) for line in audit_log.read_text(encoding='utf-8').splitlines() if line.startswith('{')]
    assert len(rows) == 22 and len({r['declaration'] for r in rows}) == 22
    assert all(set(r['axioms']) == STANDARD for r in rows)
    native = [r for r in rows if r['declaration'].startswith('ZetaNine.CoefficientMapShiftDegree.')]
    assert len(native) == 15 and sum(r['definitionValue'] is not None for r in native) == 3
    code = re.sub(r'/\-[\s\S]*?\-/', '', SOURCE.read_text(encoding='utf-8'))
    assert not re.search(r'\b(?:sorry|admit|axiom|unsafe)\b', code)
    save('type-report.json', {'records': 22, 'source_definitions': 3, 'source_theorems': 12,
        'additional_closed_statements': 7, 'only_standard_three_axioms': True, 'records_actual': rows})
    save('compile-receipt.json', {
        'verdict': 'PASS_ACTUAL_POLYNOMIAL_SHIFT_COEFFICIENT_AND_LOW_DEGREE_OBSTRUCTION_ONLY',
        'checked_at': datetime.now(timezone.utc).isoformat(),
        'source': SOURCE.relative_to(ROOT).as_posix(), 'source_sha256': digest(SOURCE),
        'environment': {'lean_toolchain': toolchain, 'mathlib_rev': mathlib['rev']},
        'source_compile': {'exit_code': 0, 'observed_session_id': 40780, 'observed_completion_chunk_id': '2742f1',
            'command': ['lake','env','lean','-o','missions/zeta9/formalization/CoefficientMapShiftDegree.olean',
                        'missions/zeta9/formalization/CoefficientMapShiftDegree.lean'],
            'working_directory': str(ROOT), 'outer_LEAN_PATH_prefix': str(ROOT),
            'log_sha256': digest(source_log), 'exit_sha256': digest(source_exit),
            'object_sha256': digest(SOURCE.with_suffix('.olean')), 'printed_targets': 5,
            'only_standard_three_axioms': True},
        'imported_statement_audit': {'exit_code': 0, 'observed_session_id': 14010,
            'observed_completion_chunk_id': '0f8dfd',
            'command': ['lake','env','lean','missions/zeta9/verification/formalization-coefficient-map-shift-degree-2026-10-04/type-audit.lean'],
            'working_directory': str(ROOT), 'outer_LEAN_PATH_prefix': str(ROOT),
            'source_sha256': digest(OUT/'type-audit.lean'), 'log_sha256': digest(audit_log),
            'exit_sha256': digest(audit_exit), 'records': 22, 'source_definitions': 3,
            'source_theorems': 12, 'additional_closed_statements': 7, 'only_standard_three_axioms': True,
            'report_sha256': digest(OUT/'type-report.json')},
        'retained_failed_attempts': [
            {'attempt': 1, 'exit': 1, 'reason': 'two degree simp goals remained; temporary elaborator sorryAx excluded'},
            {'attempt': 2, 'exit': 1, 'reason': 'redundant norm_num after solved goals; excluded despite standard printed axioms'}],
        'scope': 'Actual A/B operator coefficient and degree obstruction. No rational telescoper relationship is assumed or proved in this source; original aggregate inverse and irrationality are separate.'})
    members = [SOURCE, SOURCE.with_suffix('.olean'), Path(__file__).resolve(),
        ROOT/'lean-toolchain', ROOT/'lake-manifest.json', TASK/'research/coefficient-map-shift-degree-2026-10-04.md']
    members += [TASK/('formalization/CoefficientMapShiftDegree.'+suffix) for suffix in [
        'source-attempt1.lean','source-attempt2.lean','compile-attempt1.log','compile-attempt1-exit.txt',
        'compile-attempt2.log','compile-attempt2-exit.txt','compile-attempt3.log','compile-attempt3-exit.txt']]
    members += [OUT/name for name in ['type-audit.lean','type-audit-attempt1.log','type-audit-attempt1-exit.txt',
        'type-report.json','compile-receipt.json']]
    for relative in ['Taylor.lean','Reverse.lean','HasseDeriv.lean','Monic.lean','Coeff.lean',
                     'Eval/Degree.lean','Degree/Operations.lean','Degree/Defs.lean']:
        members.append(ROOT/'.lake/packages/mathlib/Mathlib/Algebra/Polynomial'/relative)
    bindings = []
    for path in sorted(set(members)):
        bindings.append({'task_relative': path.relative_to(TASK).as_posix() if path.is_relative_to(TASK) else None,
            'root_relative': path.relative_to(ROOT).as_posix(), 'bytes': path.stat().st_size, 'sha256': digest(path)})
    save('source-manifest.json', {'source_sha256': digest(SOURCE), 'files': bindings})
    lines = [row['sha256']+'  '+row['root_relative'] for row in bindings]
    lines.append(digest(OUT/'source-manifest.json')+'  '+(OUT/'source-manifest.json').relative_to(ROOT).as_posix())
    (OUT/'SHA256SUMS.txt').write_text('\n'.join(lines)+'\n', encoding='utf-8')
    for row in bindings:
        path = ROOT/row['root_relative']
        assert path.stat().st_size == row['bytes'] and digest(path) == row['sha256']
    print(json.dumps({'source_sha256': digest(SOURCE), 'receipt_sha256': digest(OUT/'compile-receipt.json'),
        'manifest_sha256': digest(OUT/'source-manifest.json'), 'SHA256SUMS_sha256': digest(OUT/'SHA256SUMS.txt'),
        'frozen_members': len(bindings), 'type_records': 22, 'verdict': 'PASS'}, ensure_ascii=False))


if __name__ == '__main__':
    main()
