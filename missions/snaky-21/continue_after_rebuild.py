"""Continue the finite publication job after both required rebuild phases pass."""
import json
import subprocess
import sys
import time
from pathlib import Path
import pipeline
import publish
import local_completion

HERE=Path(__file__).resolve().parent

def main():
    sys.stdout.reconfigure(encoding='utf-8')
    while True:
        build_out=(HERE/'verification'/'rebuild-stdout.log').read_text(encoding='utf-8')
        pub_out=(HERE/'verification'/'cache-publish6-stdout.log').read_text(encoding='utf-8')
        for name in ('rebuild-stderr.log','cache-publish6-stderr.log'):
            error=(HERE/'verification'/name).read_text(encoding='utf-8')
            if 'Traceback (most recent call last)' in error:
                raise RuntimeError('A prerequisite phase failed: '+name)
        if 'Actual relocated-cache proof audited' in build_out and 'Split cache wrapper and catalog definitions published.' in pub_out:
            if not local_completion.unchanged():
                raise RuntimeError('Rebuilt proof sources changed after audit')
            break
        time.sleep(10)
    print('Prerequisite audit and definition publication passed; resume proof queue.',flush=True)
    result=subprocess.run([sys.executable,'-B',str(HERE/'queue_finish.py')],cwd=pipeline.ROOT,env=pipeline.environment())
    if result.returncode:
        raise RuntimeError('Proof publication queue needs repair')

if __name__=='__main__':
    main()
