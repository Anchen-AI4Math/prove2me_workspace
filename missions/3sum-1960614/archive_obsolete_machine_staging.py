"""Archive obsolete generated main files after the node plan changes."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1].resolve()
VER = HERE / 'verification'
manifest = json.loads((VER / 'machine-platform-manifest.json').read_text(encoding='utf-8'))
assert not manifest['regression_only'] and not manifest['validation_complete']
kept = {r['path'] for r in manifest['definitions']}
for theorem in manifest['theorems']:
    kept.update((theorem['theorem_path'], theorem['solution_path']))
archive = (VER / 'obsolete-platform-staging').resolve()
assert archive.is_relative_to(ROOT / 'missions' / '3sum-1960614')
receipt_path = VER / 'obsolete-platform-staging.json'
receipt = json.loads(receipt_path.read_text(encoding='utf-8')) if receipt_path.exists() else []
for folder, prefix in (('Definitions', 'Def_ThreeSum1960614_Machine_'),
                       ('Theorems', 'Thm_ThreeSum1960614_Machine_'),
                       ('Solutions', 'Sol_ThreeSum1960614_Machine_')):
    for path in sorted((ROOT / folder).glob(prefix + '*.lean')):
        relative = path.relative_to(ROOT).as_posix()
        if relative in kept:
            continue
        target = (archive / folder / path.name).resolve()
        assert path.resolve().parent == ROOT / folder and target.is_relative_to(archive)
        assert not target.exists(), target
        data = path.read_bytes()
        target.parent.mkdir(parents=True, exist_ok=True)
        path.rename(target)
        assert target.read_bytes() == data
        receipt.append({'original': relative, 'archive': target.relative_to(ROOT).as_posix(),
                        'sha256': hashlib.sha256(data).hexdigest()})
receipt_path.write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
print('Archived obsolete generated files:', len(receipt), '; native/model/public sources untouched.')
