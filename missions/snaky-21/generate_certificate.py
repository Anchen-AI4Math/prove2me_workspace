"""Untrusted generator: every reconstructed equation is checked by Lean's kernel."""
import hashlib
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SOURCE = HERE / 'source' / 'verification'
SYMMETRY = [0, 1, 4, 5, 2, 3, 6, 7]
BLOCK = 64

def load_module(name, path):
    import sys
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module

def cell(p):
    return f'({p[0]}, {p[1]})'

def finite(points):
    return '∅' if not points else '{' + ', '.join(map(cell, sorted(points))) + '}'

def card(value):
    return f'⟨{finite(value.required)}, {finite(value.support)}, {value.height}⟩'

def main():
    payload = (SOURCE / 'certificate.txt').read_bytes()
    assert hashlib.sha256(payload).hexdigest() == '3fa12d36a6d4dbb185e3f2808c8dfde13d85ee309afbca030d6ad17ae9fe3d04'
    checker = load_module('snaky_upstream', SOURCE / 'verify_certificate.py')
    checker.verify(payload.decode('ascii'))
    ind = load_module('snaky_independent', SOURCE / 'supporting' / 'independent_evaluator.py')
    cert = ind.Certificate(payload.decode('ascii'))
    assert len(cert.cards) == 728 and cert.cards[-1].height == 21
    # Expose the already inspected checker's local reconstruction arrays only
    # after all of its original assertions, then compare every card.
    code = (SOURCE / 'verify_certificate.py').read_text(encoding='utf-8')
    code = code.replace('\n\ndef main():', '\n    return AA, TT, HH\n\ndef main():')
    namespace = {'__name__': 'snaky_arrays'}
    exec(compile(code, 'upstream_array_check', 'exec'), namespace)
    aa, tt, hh = namespace['verify'](payload.decode('ascii'))
    for i, value in enumerate(cert.cards):
        assert (value.required, value.support, value.height) == (aa[i], tt[i], hh[i])
    assert ind.matrix_checks()['composition_pairs_checked'] == 64
    ind.final_groups(cert)

    defs = [[] for _ in range(12)]
    proofs = [[] for _ in range(12)]
    names = [f'card_{i}' for i in range(728)]
    inline_count = 0

    def encode(tree, block, parent):
        nonlocal inline_count
        if isinstance(tree, ind.Reference):
            return (f'placed {SYMMETRY[tree.symmetry]} {cell(tree.shift)} card_{tree.card}',
                    f'placed_valid {SYMMETRY[tree.symmetry]} {cell(tree.shift)} valid_{tree.card}')
        children = [encode(child, block, None) for child in tree.children]
        name = parent
        if name is None:
            name = f'inline_{inline_count}'
            inline_count += 1
        # This evaluator is independent of the upstream checker.
        value = cert.evaluate(tree)
        defs[block].append(f'def {name} : Card := {card(value)}\n')
        expr = f'combine {cell(tree.pivot)} [' + ', '.join(x for x, _ in children) + ']'
        proofs[block].append(f'theorem eq_{name} : {name} = {expr} := by\n  apply computed_card_ext <;> decide +kernel\n')
        valid = ['  rw [eq_' + name + ']',
                 f'  apply combination_rule {cell(tree.pivot)} _ (by simp)',
                 '  intro c hc', '  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc']
        for index, (_, proof) in enumerate(children):
            if index + 1 < len(children):
                valid += ['  rcases hc with rfl | hc', f'  · exact {proof}']
            else:
                valid += ['  subst c', f'  exact {proof}']
        proofs[block].append('theorem valid_' + name.removeprefix('card_') + f' : Valid {name} := by\n' + '\n'.join(valid) + '\n')
        return name, 'valid_' + name.removeprefix('card_')

    for i in range(6):
        defs[0].append(f'def card_{i} : Card := baseCard {i}\n')
        proofs[0].append(f'theorem valid_{i} : Valid card_{i} := base_valid {i}\n')
    for i in range(6,728):
        encode(cert.expressions[i], i // BLOCK, f'card_{i}')
    for block in range(12):
        previous = '' if block == 0 else f'import Definitions.Def_Snaky21Data{block-1:02}\n'
        text = 'import Definitions.Def_Snaky21Core\n' + previous + '\nnamespace OAI.Snaky21.Certificate\nopen OAI.Snaky21 OAI.SnakyPrototype\n\n' + '\n'.join(defs[block]) + '\nend OAI.Snaky21.Certificate\n'
        (ROOT/'Definitions'/f'Def_Snaky21Data{block:02}.lean').write_text(text, encoding='utf-8')
        imports = f'import Definitions.Def_Snaky21Data{block:02}\nimport Solutions.Snaky21.Geometry\n'
        if block:
            imports += f'import Solutions.Snaky21.Certificate{block-1:02}\n'
        helper = ''
        if block == 0:
            helper = 'theorem computed_card_ext {c d : Card} (hA : c.required = d.required) (hT : c.envelope = d.envelope) (hh : c.height = d.height) : c = d := by\n  cases c\n  cases d\n  cases hA\n  cases hT\n  cases hh\n  rfl\n\n'
        lo, hi = block*BLOCK, min((block+1)*BLOCK,728)
        group_type = ' ∧ '.join(f'Valid card_{i}' for i in range(lo,hi)) + ' ∧ True'
        group_proof = '⟨' + ', '.join(f'valid_{i}' for i in range(lo,hi)) + ', True.intro⟩'
        aggregate = f'\ntheorem block{block:02}_valid : {group_type} :=\n  {group_proof}\n'
        text = imports + '\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\nnamespace OAI.Snaky21.Certificate\nopen OAI.Snaky21 OAI.SnakyPrototype\n\n' + helper + '\n'.join(proofs[block]) + aggregate + '\nend OAI.Snaky21.Certificate\n'
        (ROOT/'Solutions'/'Snaky21'/f'Certificate{block:02}.lean').write_text(text, encoding='utf-8')
    report = {'status':'PASS', 'sha256':hashlib.sha256(payload).hexdigest(), 'cards':len(cert.cards), 'inline_combinations':inline_count, 'all_cards_cross_checked':True, 'final':ind.encode(cert.cards[-1]), 'symmetry_conversion':SYMMETRY}
    (HERE/'verification').mkdir(exist_ok=True)
    (HERE/'verification'/'generation.json').write_text(json.dumps(report,indent=2),encoding='utf-8')
    scope_path = HERE/'scope.json'
    scope=json.loads(scope_path.read_text(encoding='utf-8'))
    scope['sources'].append('Definitions/Def_Snaky21Data*.lean') if 'Definitions/Def_Snaky21Data*.lean' not in scope['sources'] else None
    scope['build'] = ['Solutions/Snaky21/Main.lean'] if (ROOT/'Solutions'/'Snaky21'/'Main.lean').exists() else ['Solutions/Snaky21/Geometry.lean', 'Solutions/Snaky21/Strategy.lean', 'Solutions/Snaky21/Certificate11.lean']
    scope_path.write_text(json.dumps(scope,indent=2)+'\n',encoding='utf-8')
    print(f'PASS: all 728 cards cross-checked; generated {inline_count} nested combinations and 12 kernel-proof blocks.')

if __name__ == '__main__':
    main()
