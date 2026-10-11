"""Durable entry point for the actual proof and axiom audit."""
import sys
import pipeline

if __name__=='__main__':
    sys.stdout.reconfigure(encoding='utf-8')
    pipeline.run_checked([sys.executable,'-B','scripts/workspace.py','build','snaky-21'],'closed-build')
