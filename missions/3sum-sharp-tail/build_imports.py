"""Compile the exact shared imports of one selected proof into the task mirror."""
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
source = Path(sys.argv[1]).resolve()
if not source.is_relative_to(ROOT):
    raise ValueError('Select a proof in this workspace')
imports = re.findall(r'^import ((?:Definitions|Theorems)\.\S+)\s*$',
                     source.read_text(encoding='utf-8'), re.M)
raise SystemExit(subprocess.call([sys.executable, '-X', 'utf8', str(HERE / 'build_foundation.py'),
                                 *imports], cwd=ROOT))
