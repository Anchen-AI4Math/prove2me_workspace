from pathlib import Path
import json, hashlib, subprocess, sys

TASK = Path(__file__).resolve().parents[2]
ROOT = TASK.parent.parent
OUT = Path(__file__).resolve().parent
PROJECT = TASK / '.rt/np1'
CACHE = PROJECT / 'b/lib/lean'
PARENT = TASK / '.rt/ps1'
PS = TASK / 'verification/formalization-coefficient-map-parameter-shift-2026-10-04'

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p): return json.loads(p.read_text(encoding='utf8'))
def write(p, text):
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_bytes(text if isinstance(text, bytes) else text.encode())
def dump(p, value): write(p, json.dumps(value, indent=2)+'\n')

def verify():
    prep = load(OUT/'preparation.json')
    assert sha(PS/'author-audit.json') == prep['PS_author_audit_sha256']
    for row in prep['author_stable_files']:
        p=ROOT/row['root_relative']
        assert sha(p)==row['sha256'] and p.stat().st_size==row['bytes']
    for row in prep['reused_parent_objects']:
        for key in ['origin_task_relative','own_copy_task_relative']:
            p=TASK/row[key]
            assert sha(p)==row['sha256'] and p.stat().st_size==row['bytes']
    for row in prep['parent_source_copies']:
        assert sha(ROOT/row['root_relative'])==sha(PROJECT/row['project_relative'])==row['sha256']
    assert sha(TASK/'formalization/CoefficientMapFormalTransportData.lean') == 'ae9f4eab8efecd88aaae5d4b13da7ba4bed7db89bbf257d3b0645e1b8584fb27'
    return prep

def run(logical, source, module=None):
    verify()
    receipt = load(OUT/'compile-receipt.json') if (OUT/'compile-receipt.json').exists() else {'rows':[]}
    label='r'+str(len(receipt['rows'])+1).zfill(2)
    source_snapshot=OUT/(label+'s.lean')
    write(source_snapshot,source.read_bytes())
    wrapper=OUT/(label+'.ps1')
    script='$env:LEAN_NUM_THREADS="1"\n'
    script+='$allowedPackageRoot="'+(ROOT/'.lake/packages').as_posix().lower()+'/"\n'
    script+='$selected=@($env:LEAN_PATH -split ";" | Where-Object { $_ -and ([System.IO.Path]::GetFullPath($_).Replace("\\","/").ToLowerInvariant().StartsWith($allowedPackageRoot)) })\n'
    script+='$env:LEAN_PATH="'+CACHE.as_posix()+';"+($selected -join ";")\n'
    script+='Set-Location -LiteralPath "'+PROJECT.as_posix()+'"\n& lean '
    output=CACHE/(module.replace('.','/')+'.olean') if module else None
    if output:
        output.parent.mkdir(parents=True,exist_ok=True)
        script+='-o "'+output.as_posix()+'" '
    script+='"'+source.as_posix()+'"\nexit $LASTEXITCODE\n'
    write(wrapper,script)
    assert all(len(str(p))+64<=259 for p in [wrapper,OUT/(label+'.log'),OUT/(label+'e.txt')]+([output] if output else []))
    command=['lake','env','pwsh','-NoProfile','-ExecutionPolicy','Bypass','-File',str(wrapper)]
    result=subprocess.run(command,cwd=ROOT,capture_output=True)
    log=OUT/(label+'.log'); ex=OUT/(label+'e.txt')
    write(log,result.stdout+result.stderr);write(ex,str(result.returncode)+'\n')
    row={'label':label,'logical':logical,'command':command,'actual_exit':result.returncode,
         'source_task_relative':source.relative_to(TASK).as_posix(),'source_sha256':sha(source),
         'snapshot':source_snapshot.name,'snapshot_sha256':sha(source_snapshot),
         'log':log.name,'log_sha256':sha(log),'exit_file':ex.name,'exit_sha256':sha(ex),
         'wrapper':wrapper.name,'wrapper_sha256':sha(wrapper),
         'output_task_relative':output.relative_to(TASK).as_posix() if output else None,
         'output_sha256':sha(output) if output and output.exists() else None,
         'parent_14_objects_reused_not_fresh':True,'Root_or_independent_proof_objects_reused':False}
    receipt['rows'].append(row);dump(OUT/'compile-receipt.json',receipt)
    verify()
    print(logical,'actual exit',result.returncode,flush=True)
    if result.returncode: print(log.read_text(encoding='utf8'),flush=True)
    return result.returncode

if __name__=='__main__':
    module=sys.argv[1]
    if module in ['CoefficientMapFormalTransportData','CoefficientMapNumeratorPartialFractions']:
        src=PROJECT/'missions/zeta9/formalization'/(module+'.lean')
        write(src,(TASK/'formalization'/(module+'.lean')).read_bytes())
        code=run('actual own '+module,src,'missions.zeta9.formalization.'+module)
    else: code=run('actual own '+module,OUT/(module+'.lean'))
    sys.exit(code)
