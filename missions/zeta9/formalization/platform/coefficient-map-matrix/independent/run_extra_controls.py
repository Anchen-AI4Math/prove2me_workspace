"""Additional serial native whole-type and own-object controls. No import-time execution."""
import sys
import prepare as p
import author_stage as stage
import run_actual as actual

def main():
    sys.stdout.reconfigure(encoding='utf-8')
    p.execution_gate()
    _, frozen, _=p.native_gate()
    source=p.INDEPENDENT/'kernel-types.lean'
    b=next(x for x in frozen['stable_files'] if (p.ROOT/x['root_relative'] if 'root_relative'in x else p.TASK/x['task_relative']).resolve()==source.resolve())
    assert source.stat().st_size==b['bytes'] and p.sha(source)==b['sha256']
    stage.save_leaf('native-expected-kernel',source.read_bytes())
    actual.run('native-expected-kernel',['native-expected-kernel.lean'])
    actual.run('own-object-resolution',['own-object-resolution.lean'])
    print('Native22 expected proofs/17 real type Meta and actual37 own-object resolver completed.')

if __name__=='__main__': main()
