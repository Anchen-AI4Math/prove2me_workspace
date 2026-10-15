"""Apply exact, reviewed proof-only disambiguations reported by the server."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
VER = HERE / 'verification'
digest = lambda data: hashlib.sha256(data).hexdigest()
manifest_path = VER / 'machine-platform-manifest.json'
manifest = json.loads(manifest_path.read_text(encoding='utf-8'))
conversion_path = VER / 'server-macro-apply-state.json'
conversion = json.loads(conversion_path.read_text(encoding='utf-8'))
safe_lines = '\n'.join([
    '      (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))',
    '      (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))',
    '      simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul] <;> omega',
])
safe_pair = '    refine ⟨(by\n' + safe_lines + '\n    ), (by\n' + safe_lines + '\n    ), ?_⟩'
old_safe_first = '''    refine ⟨by (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
                  (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
                  simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)),'''
patches = {
    'ThreeSum1960614.Machine.ThreeSum.TrimScales.fullOutputs_log_rate': [
        ('(by omega : mu n ≠ 0)',
         '(by omega : _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n ≠ 0)')
    ],
    'ThreeSum1960614.Machine.ThreeSum.HierarchyScales.initial_query_eventually_le': [
        ('(by omega : 0 < mu n)',
         '(by omega : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n)')
    ],
    'ThreeSum1960614.Machine.ThreeSum.StageBounds.terminalChoices_log_rate': [
        ('(by omega : 0 < mu n)',
         '(by omega : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n)')
    ],
    'ThreeSum1960614.Machine.ThreeSum.UniformStageBounds.budget_active_powerBound': [
        ('(by omega : 0 < mu n)',
         '(by omega : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n)')
    ],
    'ThreeSum1960614.Machine.Light.Ends.of_blockSafe': [
        ('Ends.of_blockSafe ',
         'of_blockSafe__implementation_89a79a0685 '),
        ('_root_.ThreeSum1960614.Machine.Light.Ends.of_blockSafe__implementation_89a79a0685 ',
         'of_blockSafe__implementation_89a79a0685 ')
    ],
    'ThreeSum1960614.Machine.ThreeSum.LightWeightedEnumeration.meets': [
        ('· simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightWeightedEnumeration.output_zero,_root_.Light.seg_cons]',
         '· change _root_.Light.Seg _ _ _\n        simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightWeightedEnumeration.output_zero,_root_.Light.seg_cons,_root_.Light.Seg]'),
        ('simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightWeightedEnumeration.output_zero,_root_.Light.seg_cons]',
         'simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightWeightedEnumeration.output_zero,_root_.Light.seg_cons,_root_.Light.Seg]'),
        ('· rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightWeightedEnumeration.output_succ hfull,_root_.Light.seg_append,_root_.ThreeSum1960614.Machine.ThreeSum.LightWeightedEnumeration.output_length]',
         '· change _root_.Light.Seg _ _ _\n          rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightWeightedEnumeration.output_succ hfull,_root_.Light.seg_append,_root_.ThreeSum1960614.Machine.ThreeSum.LightWeightedEnumeration.output_length]')
    ],
    'ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration.meets': [
        ('· simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration.output_zero,_root_.Light.seg_cons]',
         '· change _root_.Light.Seg _ _ _\n        simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration.output_zero,_root_.Light.seg_cons,_root_.Light.Seg]'),
        ('· rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration.output_succ hfull,_root_.Light.seg_append,_root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration.output_length]',
         '· change _root_.Light.Seg _ _ _\n          rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration.output_succ hfull,_root_.Light.seg_append,_root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration.output_length]')
    ],
    'ThreeSum1960614.Machine.Light.Emod.reduce_ends': [
        (old_safe_first + ''' by (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
                                 (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
                                 simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)), ?_⟩''', safe_pair)
    ],
    'ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeDivide.reduce_ends': [
        (old_safe_first + '''by (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
                                (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
                                simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)),?_⟩''', safe_pair)
    ],
}
changes = []
prepared = []
for name, replacements in patches.items():
    record = next(r for r in manifest['theorems'] if r['name'] == name)
    path = ROOT / record['solution_path']
    original = path.read_bytes()
    assert digest(original) == record['solution_sha256'], name
    source = original.decode('utf-8')
    for before, after in replacements:
        if before not in source:
            assert after in source or any(other in source for other, _ in replacements), name
            continue
        assert source.count(before) in (1, 2, 4), name
        source = source.replace(before, after)
    revised = source.encode('utf-8')
    if original == revised:
        continue
    entry = conversion['items'][record['solution_path']]
    assert entry['result_sha256'] == digest(original)
    backup = VER / 'server-proof-originals' / (path.stem + '-' + digest(original)[:12] + '.lean.txt')
    if backup.exists():
        assert backup.read_bytes() == original
    else:
        backup.write_bytes(original)
    prepared.append((name, record, path, original, revised, entry, backup))
for name, record, path, original, revised, entry, backup in prepared:
    path.write_bytes(revised)
    change = {'name': name, 'path': record['solution_path'],
              'previous_sha256': digest(original), 'current_sha256': digest(revised),
              'reason': 'restore source reference and definition scope after the platform transplant',
              'changed_statement': False, 'backup': str(backup.relative_to(ROOT))}
    record['solution_sha256'] = digest(revised)
    entry.setdefault('post_conversion_changes', []).append(change)
    entry['result_sha256'] = digest(revised)
    changes.append(change)
if changes:
    manifest_path.write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    conversion_path.write_text(json.dumps(conversion, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    receipt_path = VER / 'server-proof-scope-corrections.json'
    previous = json.loads(receipt_path.read_text(encoding='utf-8')) if receipt_path.exists() else {}
    receipt = {'recorded_at_utc': datetime.now(timezone.utc).isoformat(),
               'changes': previous.get('changes', []) + changes,
               'manifest_sha256': digest(manifest_path.read_bytes())}
    receipt_path.write_text(
        json.dumps(receipt, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
print('Applied', len(changes), 'reviewed proof scope corrections.')
