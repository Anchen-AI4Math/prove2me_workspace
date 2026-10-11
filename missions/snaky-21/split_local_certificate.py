"""Keep the final kernel-checking modules within bounded resource use."""
import re
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
FULL=HERE/'platform'/'certificate11-computation.lean'

def main():
    target=ROOT/'Solutions'/'Snaky21'/'Certificate11.lean'
    if not FULL.exists():
        FULL.write_text(target.read_text(encoding='utf-8'),encoding='utf-8')
    source=FULL.read_text(encoding='utf-8')
    starts={704:re.search(r'^theorem calc11_',source,re.M).start()}
    for i in range(704,728):
        at=source.index(f'theorem valid_{i} :')
        starts[i+1]=source.index('\ntheorem ',at)+1
    for part,start in enumerate(range(704,728)):
        pre='import Definitions.Def_Snaky21Calc11\nimport Solutions.Snaky21.Geometry\n'
        previous='Certificate10' if part==0 else f'Certificate11Part{part-1:02}'
        pre+=f'import Solutions.Snaky21.{previous}\n\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\nnamespace OAI.Snaky21.Certificate\nopen OAI.Snaky21 OAI.SnakyPrototype\n\n'
        text=pre+source[starts[start]:starts[start+1]]+'\nend OAI.Snaky21.Certificate\n'
        (target.parent/f'Certificate11Part{part:02}.lean').write_text(text,encoding='utf-8')
    tail=source[starts[728]:]
    target.write_text('import Solutions.Snaky21.Certificate11Part23\n\nnamespace OAI.Snaky21.Certificate\nopen OAI.Snaky21 OAI.SnakyPrototype\n\n'+tail,encoding='utf-8')
    print('Final certificate split into 24 closed local proof modules.')

if __name__=='__main__':
    main()
