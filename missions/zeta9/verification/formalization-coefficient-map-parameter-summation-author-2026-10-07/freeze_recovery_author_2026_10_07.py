"""Pure final AUTHOR freeze derived from the preserved V3 freeze SOURCE."""
from pathlib import Path
import execute_native_author as e


def main():
    original = e.OUT / 'freeze_author_v3.py'
    assert e.sha(original) == '60d2795674a9a7072c13658443675d057299e0d635fd2cd044d4db5ceed6082e'
    source = original.read_text(encoding='utf-8')
    marker = "  author_expected_and_serializer_SOURCE_reuse_disclosed=True,foreign_cache_objects_borrowed=False,"
    assert source.count(marker) == 1
    replacement = marker + "\n  continuation_recovery=e.load(e.OUT/'recovery-provenance-2026-10-07.json'),\n  continuation_reuse_of_same_author_SOURCE_objects_disclosed=True,\n  source_rebuilds_by_this_recovery=0,additional_resolver_actual_calls_by_this_recovery=1,"
    derived = source.replace(marker, replacement)
    old = " additional_whole_function_rfl_and_resolver_calls=2,fresh_native_sources=22,complete_expected_theorems=17,"
    new = " additional_whole_function_rfl_and_resolver_final_success_calls=2,additional_resolver_failed_attempts_retained=1,fresh_native_sources=22,complete_expected_theorems=17,"
    assert derived.count(old) == 1
    derived = derived.replace(old, new)
    target = e.OUT / 'derived_freeze_recovery_2026_10_07.py'
    if target.exists():
        assert target.read_text(encoding='utf-8') == derived
    else:
        e.write(target, derived)
    assert not (e.OUT / 'author-audit.json').exists(), 'Existing freeze is immutable; inspect it instead of rerunning.'
    receipt = e.load(e.OUT / 'compile-receipt.json')
    assert len(receipt['rows']) == 34
    assert sum(r['exit_code'] == 0 for r in receipt['rows']) == 31
    assert sum(r['exit_code'] != 0 for r in receipt['rows']) == 3
    namespace = {'__name__': 'parameter_recovery_freeze', '__file__': str(target)}
    exec(compile(derived, str(target), 'exec'), namespace)
    namespace['main']()


if __name__ == '__main__':
    main()
