"""Register the exact import closure of one current-task solution."""
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
path = Path(sys.argv[1]).resolve()
assert path.parent == ROOT / 'Solutions' and path.name.startswith('Sol_ThreeSumSharpTail_')
imports = re.findall(r'^import ((?:Definitions|Theorems)\.\S+)\s*$', path.read_text(encoding='utf-8'), re.M)
raise SystemExit(subprocess.call([sys.executable, '-X', 'utf8', str(HERE / 'install_bridge_dependencies.py'), *imports], cwd=ROOT))
