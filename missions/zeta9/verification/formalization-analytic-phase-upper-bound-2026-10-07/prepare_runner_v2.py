"""Versioned runner adds exact own source/object dependency snapshots for controls."""
import sys
sys.dont_write_bytecode=True
import prepare_native as p

def main():
    original=(p.OUT/'run_native.py').read_text(encoding='utf-8')
    marker='    inputs.append(p.binding(Path(__file__)))\n'
    added='''    if label.startswith('control-'):
        for module in p.EXPECTED:
            relative='missions/zeta9/formalization/'+module
            inputs.append(p.binding(p.PROJECT/(relative+'.lean')))
            obj=p.PROJECT/('b/lib/lean/'+relative+'.olean')
            assert obj.exists(), 'Controls require previously SOURCE-built own objects'
            for path in sorted(obj.parent.glob(obj.name+'*')):
                inputs.append(p.binding(path))
'''
    assert original.count(marker)==1
    p.write(p.OUT/'run_native_v2.py',original.replace(marker,marker+added))
    p.dump(p.OUT/'runner-v2-preparation.json',dict(original_runner=p.binding(p.OUT/'run_native.py'),
      new_runner=p.binding(p.OUT/'run_native_v2.py'),change='Record own original-source-derived private sources and object dependencies before every control call',
      prior_actual_receipt_unchanged=True,no_foreign_proof_objects=True))
    print('Versioned control runner prepared.',flush=True)
if __name__=='__main__':main()
