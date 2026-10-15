"""Create an exact theorem reference for a new checked bridge solution."""
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]


def main():
    suffix = sys.argv[1]
    if not re.fullmatch(r'[a-z][a-z0-9_]*', suffix):
        raise ValueError('Invalid bridge suffix')
    source = ROOT / f'Solutions/Sol_ThreeSumSharpTail_{suffix}.lean'
    text = source.read_text(encoding='utf-8')
    assert text.count('theorem solution') == 1
    prefix, body = text.split('theorem solution', 1)
    signature, _ = body.split(':= by', 1)
    lines = [line for line in prefix.splitlines()
             if re.match(r'^(import |set_option |open )', line)]
    result = '\n'.join(lines) + '\n\n' + 'theorem ThreeSumSharpTail.' + suffix + signature + ':= by sorry\n'
    target = ROOT / f'Theorems/Thm_ThreeSumSharpTail_{suffix}.lean'
    if target.exists() and target.read_text(encoding='utf-8') != result:
        raise ValueError('Existing reference differs; inspect it rather than overwrite it')
    target.write_text(result, encoding='utf-8')
    print('Prepared ' + target.name)


if __name__ == '__main__':
    main()
