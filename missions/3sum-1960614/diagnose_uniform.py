"""Instrument a separate copy of the uniform proof; never alter platform sources."""
import importlib.util
from pathlib import Path
import subprocess

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
spec=importlib.util.spec_from_file_location('workspace',ROOT/'scripts/workspace.py')
workspace=importlib.util.module_from_spec(spec)
spec.loader.exec_module(workspace)
code=(ROOT/'Solutions/Sol_ThreeSum1960614_uniform_entropy_bound.lean').read_text(encoding='utf-8')
markers=[('  have hu :', 'generic tangent starts'),('  have heq :', 'generic tangent slope complete'),
         ('  rw [heq] at htan', 'generic tangent formula complete'),('  let A :','uniform proof starts'),
         ('  have hleft :','tangent-log conversion complete'),('  have hright :','left rational endpoint complete'),
         ('  have hl\' :=','right rational endpoint complete'),('  have htan :=','affine interpolation complete'),
         ('  have hent :','polynomial bound complete'),('  exact lt_of_le_of_lt hent','entropy tangent complete')]
for marker,label in markers:
    assert marker in code,marker
    code=code.replace(marker,'  run_tac do\n    dbg_trace "'+label+'"\n'+marker,1)
target=HERE/'verification/UniformDiagnostic.lean'
target.write_text(code,encoding='utf-8')
lake,env=workspace.lake_environment()
raise SystemExit(subprocess.run([lake,'env','lean',str(target)],cwd=ROOT,env=env).returncode)
