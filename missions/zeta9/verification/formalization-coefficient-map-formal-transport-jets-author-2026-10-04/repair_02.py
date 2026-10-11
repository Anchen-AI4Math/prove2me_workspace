"""Repair only own expected-control namespace visibility after a real failure."""
import difflib
import prepare as p


def main():
    p.native_gate()
    failed=next(r for r in reversed(p.load(p.OUT/'compile-receipt.json')['rows']) if
        r['label']=='control-JetsFullTypeAudit' and r['exit_code']==1)
    source=p.PROJECT/'JetsFullTypeAudit.lean'
    old=source.read_text(encoding='utf-8-sig')
    marker='open Finset Polynomial\n'
    assert old.count(marker)==1 and '\nopen ZetaNine\n' not in old
    new=old.replace(marker,marker+'open ZetaNine\n')
    assert p.statement_headers(old.encode())==p.statement_headers(new.encode())
    assert old.split('\nopen Lean Meta\n')[-1]==new.split('\nopen Lean Meta\n')[-1]
    p.write(p.OUT/'retained-private-fulltype-before-repair-02.lean',source.read_bytes())
    p.write(source,new)
    p.write(p.OUT/'private-repair-02.diff',''.join(difflib.unified_diff(old.splitlines(keepends=True),
        new.splitlines(keepends=True),fromfile='initial-fulltype-control',tofile='private-fulltype-repair-02')))
    ledger=p.load(p.OUT/'private-proof-repairs.json')
    ledger['allowed_current_source_bindings'].append(p.binding(source))
    ledger['repairs'].append(dict(number=2,after_actual_failed_label=failed['label'],
        after_actual_failed_attempt=failed['attempt'],actual_Lean_exit=1,
        description='Open the actual ZetaNine parent namespace for unqualified original CoefficientMapFiniteSum headers; no type or metadata change.',
        retained_before=p.binding(p.OUT/'retained-private-fulltype-before-repair-02.lean'),
        diff=p.binding(p.OUT/'private-repair-02.diff'),after=p.binding(source)))
    p.dump(p.OUT/'private-proof-repairs.json',ledger)
    p.native_gate()
    print('PRIVATE_CONTROL_NAMESPACE_REPAIR_02',p.sha(source))


if __name__=='__main__':main()
