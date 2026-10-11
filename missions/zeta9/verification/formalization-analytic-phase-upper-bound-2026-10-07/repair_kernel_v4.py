"""Private control V4 handles compiler helper reuse across source-derived aliases."""
import sys
sys.dont_write_bytecode=True
import prepare_native as p

def main():
    original=(p.OUT/'controls-v3/APKernel.lean').read_text(encoding='utf-8')
    old='''      if n.getPrefix == actual && n.getString!.startsWith "_proof_" then
        let paired := Name.str expected n.getString!
        let a ← getConstInfo n
        let b ← getConstInfo paired
'''
    new='''      if n.getPrefix.getPrefix == actual.getPrefix && n.getString!.startsWith "_proof_" then
        let a ← getConstInfo n
        let some va0 := a.value? true | throwError "Missing actual helper proof {n}"
        let mut matched : Option Name := none
        for m in bb.getUsedConstants do
          if m.getPrefix.getPrefix == expected.getPrefix && m.getString!.startsWith "_proof_" then
            let c ← getConstInfo m
            if let some vc := c.value? true then
              if Expr.equal a.type c.type && Expr.equal va0 vc then matched := some m
        let some paired := matched | throwError "No full-expression identical expected helper for {n}"
        let b ← getConstInfo paired
'''
    assert original.count(old)==1
    source=original.replace(old,new)
    p.write(p.OUT/'controls-v4/APKernel.lean',source);p.write(p.PROJECT/'APKernel.lean',source)
    prior=(p.OUT/'run_native_v2.py').read_text(encoding='utf-8')
    oldprint="if result.returncode:print((result.stdout+result.stderr).decode('utf-8',errors='replace'),flush=True)"
    newprint="if result.returncode:print('\\n'.join(line for line in (result.stdout+result.stderr).decode('utf-8',errors='replace').splitlines() if not line.startswith('AP_RECORD|')),flush=True)"
    assert prior.count(oldprint)==1
    p.write(p.OUT/'run_native_v3.py',prior.replace(oldprint,newprint))
    p.dump(p.OUT/'controls-kernel-v4-repair.json',dict(reason='Compiler reuses identical numeral proof helpers across definitions in the single alias module',
      matching='Pair by full raw type AND full raw proof Expr.equal, then actual isDefEq and value type checks; no assumed name correspondence',
      raw_values_and_false_Expr_equal_retained=True,no_binder_or_metadata_erasure=True,
      failed_attempt_retained='actual-runs/control-kernel-v3-01',control=p.binding(p.PROJECT/'APKernel.lean'),
      runner=p.binding(p.OUT/'run_native_v3.py'),runner_change='Only suppress AP_RECORD lines from failed call console echo; every byte stays in original stdout/stderr/log'))
    print('Kernel V4 matches shared compiler helpers by actual full expressions.',flush=True)
if __name__=='__main__':main()
