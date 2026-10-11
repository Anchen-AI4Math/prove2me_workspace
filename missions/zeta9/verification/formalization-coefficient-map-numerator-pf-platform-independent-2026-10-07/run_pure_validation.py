"""Retain exact pure graph/span validation input, stdout, stderr and terminal exit."""
import argparse, json, os, subprocess, sys
import inspect_author as p
sys.stdout.reconfigure(encoding='utf-8')
parser=argparse.ArgumentParser();parser.add_argument('script');args=parser.parse_args()
assert args.script.startswith('analyze_oracles') and args.script.endswith('.py') and '/' not in args.script and '\\' not in args.script
source=p.OUT/args.script;assert source.is_file()
root=p.OUT/'pure-validation-runs';root.mkdir(exist_ok=True)
number=len(list(root.iterdir()))+1;folder=root/('analysis-a'+str(number).zfill(2));folder.mkdir()
snapshot=folder/'source.py';snapshot.write_bytes(source.read_bytes())
command=[r'C:\Users\anche\AppData\Local\Programs\Python\Python312\python.exe',str(source)]
result=subprocess.run(command,cwd=p.TASK,capture_output=True)
(folder/'stdout.log').write_bytes(result.stdout);(folder/'stderr.log').write_bytes(result.stderr)
(folder/'exit.txt').write_text(str(result.returncode)+'\n',encoding='ascii')
report=dict(actual_command=command,execution_CWD=str(p.TASK),exit_code=result.returncode,
    source=p.bind(source),snapshot=p.bind(snapshot),Lean_invocations=0,
    evidence=[p.bind(folder/name) for name in ['stdout.log','stderr.log','exit.txt']],
    failed_validation_excluded=result.returncode!=0)
(folder/'receipt.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(result.stdout.decode('utf-8',errors='replace'));print(result.stderr.decode('utf-8',errors='replace'))
assert result.returncode==0,'Pure validation failed; complete input/log/exit retained. Version any repaired validation source.'
