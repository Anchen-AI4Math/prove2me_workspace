"""Configure an isolated package build using only the pinned trusted dependency paths."""
import json
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
OUT=HERE/'verification/standalone-check'
OUT.mkdir(parents=True,exist_ok=True)
manifest=json.loads((ROOT/'lake-manifest.json').read_text(encoding='utf-8'))
entries=[]
for p in manifest['packages']:
    entry={k:p[k] for k in ('name','scope','inherited','configFile','manifestFile') if k in p}
    directory=ROOT/'.lake/packages'/p['name']
    assert directory.exists(),directory
    entry.update(type='path',dir=directory.as_posix())
    entries.append(entry)
manifest.update(packages=entries)
(OUT/'lake-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
(OUT/'lean-toolchain').write_text((ROOT/'lean-toolchain').read_text(encoding='utf-8'),encoding='utf-8')
source=(HERE/'submission-bigospeedrun').as_posix()
(OUT/'lakefile.lean').write_text('''import Lake
open Lake DSL

package ThreeSum1960614Standalone

require mathlib from "'''+(ROOT/'.lake/packages/mathlib').as_posix()+'''"

@[default_target]
lean_lib Submission where
  srcDir := "'''+source+'''"
  roots := #[`Submission]
  globs := #[.one `Submission,.submodules `Submission]
''',encoding='utf-8')
print('Configured isolated build directory:',OUT)
