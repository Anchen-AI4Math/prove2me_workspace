"""Bind historical compiler inputs/outputs before an authorized source repair."""
from pathlib import Path
import hashlib,json,sys
import prepare as p


def retain(row,folder):
    ident=hashlib.sha256((row['label']+':'+str(row['attempt'])).encode()).hexdigest()[:16]
    short=p.PROJECT/'h'/ident
    for key,field in [('input_bindings','retained_input_bindings'),('output_bindings','retained_output_bindings')]:
        if field in row:continue
        kept=[]
        for index,binding in enumerate(row[key]):
            source=p.TASK/binding['task_relative']
            assert source.stat().st_size==binding['bytes'] and p.sha(source)==binding['sha256']
            snapshot=short/(('i' if key=='input_bindings' else 'o')+str(index).zfill(3))
            assert len(str(snapshot))<=259
            p.write(snapshot,source.read_bytes())
            kept.append(dict(original_task_relative=binding['task_relative'],snapshot_binding=p.binding(snapshot)))
        row[field]=kept
    row['actual_original_input_output_metadata_preserved']=True


def main():
    receipt=p.load(p.OUT/'compile-receipt.json')
    for row in receipt['rows']:
        folder=p.TASK/row['log']['task_relative'];retain(row,folder.parent)
    p.dump(p.OUT/'compile-receipt.json',receipt)
    print(json.dumps(dict(actual_rows_retained=len(receipt['rows']),failed_Lean_runs_retained=sum(r['exit_code']!=0 for r in receipt['rows']))))


if __name__=='__main__':main()
