from run_step import *
verify()
assert load(OUT/'replay-summary.json')['complete']
cmd=['lake','env','lean','--version'];p=subprocess.run(cmd,cwd=ROOT,capture_output=True)
write(OUT/'runtime-version.log',p.stdout+p.stderr);write(OUT/'runtime-version-exit.txt',str(p.returncode)+'\n')
dump(OUT/'runtime-version-receipt.json',{'command':cmd,'working_directory':str(ROOT),'exit_code':p.returncode,
 'log_sha256':sha(OUT/'runtime-version.log'),'exit_sha256':sha(OUT/'runtime-version-exit.txt'),'proof_objects_written':False})
assert p.returncode==0 and 'version 4.33.1' in p.stdout.decode('utf-8')
print(p.stdout.decode('utf-8').strip(),flush=True)
