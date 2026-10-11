"""Compose checked operation equalities without global rewrite searches."""
import re
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
PART=ROOT/'Solutions'/'Snaky21'/'Certificate11Part23.lean'

def main():
    source=PART.read_text(encoding='utf-8')
    refs=re.findall(r'^theorem (calc11_card_\d+_eq) : (.+) = (calc11_card_\d+) :=',source,re.M)
    assert len(refs)==32
    cs=[r[2] for r in refs]
    original=[r[1] for r in refs]
    def ls(items):
        return '['+', '.join(items)+']'
    header=re.search(r'^theorem eq_card_727 : .* := by\n',source,re.M).group(0)
    lines=[header.rstrip()]
    lines.append('  have hL_32 : ([] : List Card) = [] := rfl')
    for i in reversed(range(32)):
        lines.append(f'  have hL_{i} : {ls(original[i:])} = {ls(cs[i:])} :=')
        lines.append(f'    congrArg₂ List.cons {refs[i][0]} hL_{i+1}')
    for field,stem,offset,union in [('required','hA',2331,'unionRequired'),('envelope','hT',2332,'unionEnvelope')]:
        for i in reversed(range(32)):
            number=offset+2*(31-i)
            lines.append(f'  have {stem}_{i} : {union} {ls(cs[i:])} = calc11_set_{number} :=')
            if i==31:
                lines.append(f'    calc11_set_{number}_eq')
            else:
                lines.append(f'    (congrArg (fun s : Finset Cell => {cs[i]}.{field} ∪ s) {stem}_{i+1}).trans calc11_set_{number}_eq')
    for i in reversed(range(1,32)):
        number=2395+(31-i)
        lines.append(f'  have hI_{i} : commonEnvelope {ls([cs[0]]+cs[i:])} = calc11_set_{number} :=')
        if i==31:
            lines.append(f'    calc11_set_{number}_eq')
        else:
            lines.append(f'    (congrArg (fun s : Finset Cell => {cs[i]}.envelope ∩ s) hI_{i+1}).trans calc11_set_{number}_eq')
    lines += [
        f'  have hC : card_727 = combine (8, 8) {ls(cs)} := by',
        '    apply computed_card_ext',
        '    · exact ((congrArg (fun s : Finset Cell => s.erase (8, 8))',
        '        ((congrArg₂ (fun a b : Finset Cell => a ∪ b) hA_0 hI_1).trans calc11_set_2426_eq)).trans calc11_finishA_2427).symm',
        '    · exact ((congrArg (fun s : Finset Cell => insert (8, 8) s) hT_0).trans calc11_finishT_2427).symm',
        '    · decide +kernel',
        '  exact hC.trans (congrArg (combine (8, 8)) hL_0).symm',
    ]
    proof='\n'.join(lines)+'\n'
    pattern=r'^theorem eq_card_727 : .*?\n(?=theorem valid_727 :)'
    paths=[HERE/'platform'/'certificate11-computation.lean',HERE/'platform'/'block11-part23-proof.lean']
    for path in paths:
        text=path.read_text(encoding='utf-8')
        result,count=re.subn(pattern,lambda _:proof+'\n',text,flags=re.M|re.S)
        assert count==1,path
        path.write_text(result,encoding='utf-8')
    candidate=HERE/'verification'/'final-congruence.lean'
    candidate.write_text(re.sub(pattern,lambda _:proof+'\n',source,flags=re.M|re.S)+'\n#print axioms OAI.Snaky21.Certificate.valid_727\n',encoding='utf-8')
    print('Final 32-child identity now composes the same checked equalities by congruence.')

if __name__=='__main__':
    main()
