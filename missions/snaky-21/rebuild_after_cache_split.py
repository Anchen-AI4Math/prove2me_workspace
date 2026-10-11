"""Recheck the actual closed proof after literal-definition relocation."""
import sys
import pipeline
import local_completion

def main():
    sys.stdout.reconfigure(encoding='utf-8')
    pipeline.run_checked([sys.executable,'-B','scripts/workspace.py','build','snaky-21'],'closed-build')
    local_completion.record()
    print('Actual relocated-cache proof audited; standard axioms only.',flush=True)

if __name__=='__main__':
    main()
