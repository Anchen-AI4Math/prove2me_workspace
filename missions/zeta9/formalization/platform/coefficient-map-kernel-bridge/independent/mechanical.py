"""Reconstruct the true closed Definition and all staged bytes from own oracles."""
from run_step import *
import re

verify()
assert load(OUT / 'extraction-summary.json')['complete']
enrollment = load(OUT / 'execution-preparation.json')
order = enrollment['native_order']
NS = 'ZetaNine.CoefficientMapKernelBridge'
DEFS = ['positiveProduct', 'negativeProduct', 'aValue', 'bValue', 'actualAggregateEquiv',
        'inverseMultiplier', 'prescribedL']
TARGETS = ['original_quartic_aggregate_kernel_zero', 'original_five_dimensional_map_bijective',
           'inverseMultiplier_actual_HasSum_and_absolute']
ARGS = ['n hn2 hn W hW hzero', 'n hn2 hn', 'n hn2 hn b']
graph = rows(OUT / 'decl_graph.jsonl')
by = {r['name']: r for r in graph}
checks = []

def check(name, value, evidence=None):
    checks.append({'name': name, 'pass': bool(value), 'evidence': evidence})
    dump(OUT / 'mechanical-development-checks.json', {'complete': False, 'checks': checks})
    assert value, name

def normalized(values):
    return {r['name']: dict(r, typeDeps=sorted(r['typeDeps']), valueDeps=sorted(r['valueDeps'])) for r in values}

def edit(data, changes):
    edge = len(data)
    for start, end, replacement in sorted(set(changes), reverse=True):
        assert 0 <= start <= end <= edge, 'Overlapping official source spans'
        data = data[:start] + replacement + data[end:]
        edge = start
    return data

check('fresh actual graph matches frozen author graph including genuine controls',
      len(graph) == 377 and normalized(graph) == normalized(rows(BATCH / 'decl_graph.jsonl')), len(graph))
check('actual graph contains no axiom declarations', not any(r['kind'] == 'axiom' for r in graph))
sources = {}
facts = {}
for name in order:
    source = OUT / (name + '-oracle-input.lean')
    sources[name] = source.read_bytes()
    facts[name] = rows(OUT / (name + '-facts.jsonl'))
    previous_snapshot = 'oracle-input.lean' if name.endswith('PartialFractions') else name + '-oracle-input.lean'
    previous_facts = 'sketch_info.jsonl' if name.endswith('PartialFractions') else name + '-sketch_info.jsonl'
    assert sources[name] == (PROJECT / 'missions/zeta9/formalization' / (name + '.lean')).read_bytes().replace(b'\r\n', b'\n')
    assert sources[name] == (BATCH / previous_snapshot).read_bytes()
    assert facts[name] == rows(BATCH / previous_facts)
check('eleven actual source official parser spans and all resolved refs match', True,
      {name: {kind: sum(r['kind'] == kind for r in values) for kind in ['decl', 'ref', 'command']}
       for name, values in facts.items()})
hs = (OUT / 'HarmonicStability-oracle-input.lean').read_bytes()
check('Harmonic official CRLF normalization and source facts exact',
      hs == (PROJECT / 'Definitions/Def_ZetaNine_HarmonicStability.lean').read_bytes().replace(b'\r\n', b'\n')
      == (BATCH / 'Def_ZetaNine_HarmonicStability-oracle-input.lean').read_bytes()
      and rows(OUT / 'HarmonicStability-facts.jsonl') == rows(BATCH / 'Def_ZetaNine_HarmonicStability-sketch_info.jsonl'))

def declaration(name):
    g = by[name]
    module = g['module'].split('.')[-1]
    selected = [f for f in facts[module] if f['kind'] == 'decl'
                and f['declStart']['line'] <= g['startLine'] <= f['declEnd']['line']]
    assert g['startLine'] > 0 and len(selected) == 1 and selected[0]['valStart'] is not None
    return selected[0]

def closure(seeds):
    visited = set()
    pending = list(seeds)
    while pending:
        name = pending.pop()
        if name in visited:
            continue
        visited.add(name)
        pending.extend(by[name]['typeDeps'] + by[name]['valueDeps'])
    return visited

core = [r for r in graph if r['module'].endswith('.CoefficientMapKernelBridge') and r['startLine'] > 0]
check('actual original source has seven definitions and twenty-three proofs',
      len(core) == 30 and sum(r['kind'] == 'def' for r in core) == 7
      and sum(r['kind'] == 'theorem' for r in core) == 23)
control_roots = [r['name'] for r in graph if r['module'] in enrollment['control_modules'] and r['startLine'] > 0]
reached = closure([r['name'] for r in core] + control_roots + [r['name'] for r in graph if r['isInstance']])
provenance = load(BATCH / 'integration-provenance.json')
check('actual closed native control roots and complete transitive closure exact',
      len(control_roots) == 27 and set(control_roots) == set(provenance['native_closed_control_roots'])
      and sorted(reached) == provenance['cross_module_core_closure'])
bridge = ''
helpers = []
helper_facts = []
bridge_opens = []
for module in order[:-1]:
    selected = sorted([by[name] for name in reached if by[name]['module'].endswith('.' + module)
                       and by[name]['kind'] == 'theorem' and by[name]['startLine'] > 0], key=lambda r: r['startLine'])
    if not selected:
        continue
    bridge += 'open scoped BigOperators\nopen Finset Polynomial\n\nnamespace ZetaNine.' + module + '\n\n'
    first = min(r['startLine'] for r in graph if r['module'].endswith('.' + module) and r['startLine'] > 0)
    opens = [f for f in facts[module] if f['kind'] == 'command' and f['syntaxKind'] == 'Lean.Parser.Command.open'
             and f['span']['end']['line'] < first]
    for f in opens:
        bridge += sources[module][f['span']['start']['offset']:f['span']['end']['offset']].decode() + '\n'
        bridge_opens.append({'module': module, 'fact': f})
    if opens:
        bridge += '\n'
    for g in selected:
        f = declaration(g['name'])
        bridge += sources[module][f['declStart']['offset']:f['declEnd']['offset']].decode() + '\n\n'
        helpers.append(g['name'])
        helper_facts.append({'module': module, 'name': g['name'], 'fact': f})
    bridge += 'end ZetaNine.' + module + '\n\n'
check('actual145 complete parent proof bodies and their open contexts exact',
      len(helpers) == 145 and helpers == provenance['inline_helper_names']
      and helper_facts == provenance['inline_helper_facts'] and bridge_opens == provenance['bridge_open_context_facts']
      and bridge.encode() == (BATCH / 'actual-proof-bridge.lean.inc').read_bytes())
write(OUT / 'actual-proof-bridge.lean.inc', bridge)

# Derive the actual constructor proof closure from the new graph and the new
# resolved source references, never from a list of claimed author helpers.
seed = NS + '.original_five_dimensional_map_bijective'
equiv_closure = closure([seed])
forbidden = {NS + '.' + name for name in ['actualAggregateEquiv', 'inverseMultiplier', 'prescribedL']}
check('actual constructor closure has no Equiv inverse or prescribed-output cycle', not (equiv_closure & forbidden))
proofs = [by[name] for name in equiv_closure if by[name]['kind'] == 'theorem' and by[name]['startLine'] > 0]
proofs.sort(key=lambda r: (order.index(r['module'].split('.')[-1]), r['startLine']))
local_names = {r['name']: 'embedded_' + r['name'].replace('.', '__') for r in proofs}
check('true constructor closes151 actual source proofs without private or assumed helpers',
      len(proofs) == 151 and seed in local_names and not any(r['isPrivate'] for r in proofs))
terms = []
transforms = []
available = set()
for g in proofs:
    module = g['module'].split('.')[-1]
    f = declaration(g['name'])
    data = sources[module]
    a, v, b = f['declStart']['offset'], f['valStart']['offset'], f['declEnd']['offset']
    refs = [r for r in facts[module] if r['kind'] == 'ref'
            and a <= r['start']['offset'] and r['end']['offset'] <= b]
    binding = [r for r in refs if r['const'] == g['name'] and r['end']['offset'] <= v]
    assert len(binding) == 1 and f['valKind'] == 'simple'
    start = binding[0]['end']['offset']
    changes = []
    calls = []
    for r in refs:
        x, y = r['start']['offset'], r['end']['offset']
        if x < start:
            continue
        constant = r['const']
        if constant in local_names:
            assert constant in available, 'Constructor local proofs must respect actual dependency order'
            replacement = local_names[constant]
            calls.append(constant)
        else:
            assert not (constant in by and by[constant]['kind'] == 'theorem' and by[constant]['startLine'] > 0), \
                'Project source proof escaped actual constructor closure: ' + constant
            replacement = constant
        changes.append((x - start, y - start, replacement.encode()))
    terms.append('have ' + local_names[g['name']] + edit(data[start:b], changes).decode())
    available.add(g['name'])
    transforms.append({'original_declaration': g['name'], 'local_binding': local_names[g['name']],
        'module': module, 'parser_declaration_fact': f, 'parser_binding_fact': binding[0],
        'parser_resolved_refs': refs, 'local_proof_dependencies': sorted(set(calls)),
        'source_span_sha256': hashlib.sha256(data[a:b]).hexdigest(),
        'changed_only_decl_prefix_binding_and_resolved_references': True, 'new_hypotheses': []})
author_control = next(r for r in load(OUT / 'review-compile-receipt.json')['rows']
                      if r['logical_step'] == 'native control NativeKernelAuthorControl')
native_types = rows(OUT / author_control['log'])
assert len(native_types) == 37
bijection_type = next(r['type'] for r in native_types if r['declaration'] == seed)
closed_proof = '((by\n' + ''.join('    ' + '\n    '.join(t.splitlines()) + '\n' for t in terms)
closed_proof += '    exact ' + local_names[seed] + '\n  ) : ' + bijection_type + ')'
check('whole151 local proof term reconstructed byte-for-byte from own source spans',
      (closed_proof + '\n').encode() == (BATCH / 'closed-actual-aggregate-equiv-proof.lean.inc').read_bytes())
write(OUT / 'closed-actual-aggregate-equiv-proof.lean.inc', closed_proof + '\n')
ep = load(BATCH / 'embedded-bijection-provenance.json')
check('every constructor local transform dependency and source body matches actual author provenance',
      transforms == ep['proof_closure_declarations'] and bijection_type == ep['exact_original_bijection_type'])

source = sources['CoefficientMapKernelBridge']
field = declaration(NS + '.actualAggregateEquiv')
calls = [r for r in facts['CoefficientMapKernelBridge'] if r['kind'] == 'ref' and r['const'] == seed
         and field['valStart']['offset'] <= r['start']['offset'] and r['end']['offset'] <= field['declEnd']['offset']]
assert len(calls) == 1
call = calls[0]
source_opens = []
for module in order:
    first = min(g['startLine'] for g in graph if g['module'].endswith('.' + module) and g['startLine'] > 0)
    for f in facts[module]:
        if f['kind'] == 'command' and f['syntaxKind'] == 'Lean.Parser.Command.open' and f['span']['end']['line'] < first:
            source_opens.append({'module': module, 'parser_fact': f,
                                 'text': sources[module][f['span']['start']['offset']:f['span']['end']['offset']].decode()})
mathlib_imports = list(dict.fromkeys(line for module in order for line in sources[module].decode().splitlines()
                                   if line.startswith('import Mathlib.')))
prefix = 'import Definitions.Def_ZetaNine_CoefficientMapTelescoper\nimport Definitions.Def_ZetaNine_CoefficientMapShiftDegree\n'
prefix += '\n'.join(mathlib_imports) + '\n\nset_option autoImplicit false\nset_option maxHeartbeats 2000000\nnoncomputable section\nopen scoped BigOperators Topology\nopen Finset Polynomial Filter\nopen ZetaNine '
prefix += ' '.join('ZetaNine.' + module for module in order[:-1]) + '\n'
prefix += '\n'.join(dict.fromkeys(r['text'] for r in source_opens)) + '\n\nnamespace ' + NS + '\n\n'
definition_facts = [declaration(NS + '.' + name) for name in DEFS]
parts = []
for name, f in zip(DEFS, definition_facts):
    a, b = f['declStart']['offset'], f['declEnd']['offset']
    body = source[a:b]
    if name == 'actualAggregateEquiv':
        body = edit(body, [(call['start']['offset'] - a, call['end']['offset'] - a, closed_proof.encode())])
    parts.append(body.decode())
definition = prefix + '\n\n'.join(parts) + '\n\nend ' + NS + '\n'
def_relative = 'Definitions/Def_ZetaNine_CoefficientMapKernelBridge.lean'
check('genuine seven Definition source bytes exactly reconstructed no extra global proof declarations',
      definition.encode() == (BATCH / 'staged' / def_relative).read_bytes()
      and len(definition.encode()) == 124831
      and hashlib.sha256(definition.encode()).hexdigest() == '2ec92b17bcb5e578a48cc453365c6d551497bc97fddc4dccf7e632be278f59d3')
check('constructor only real original call is replaced by true closed proof',
      call == ep['original_bijection_call_ref'] and source_opens == ep['true_source_open_contexts']
      and mathlib_imports == ep['actual_native_Mathlib_imports'])
write(PROJECT / def_relative, definition)
write(OUT / 'reconstructed' / def_relative, definition)

header = rows(OUT / 'header.jsonl')
check('actual independent source header exact', len(header) == 1 and header == rows(BATCH / 'header_info.jsonl'))
he = header[0]['end']['offset']
assert source[:he].decode().strip().splitlines() == ['import missions.zeta9.formalization.CoefficientMapTelescoper',
    'import missions.zeta9.formalization.CoefficientMapShiftDegree', 'import Mathlib.Order.Interval.Set.Infinite']
fs = facts['CoefficientMapKernelBridge']
refs = [r for r in fs if r['kind'] == 'ref']
diagnostics = [r for r in fs if r['kind'] == 'command' and r['syntaxKind'] == 'Lean.Parser.Command.printAxioms']
assert diagnostics == provenance['deleted_diagnostic_facts'] and len(diagnostics) == 17
cuts = [(f['declStart']['offset'], f['declEnd']['offset'], b'') for f in definition_facts]
cuts += [(f['span']['start']['offset'], f['span']['end']['offset'], b'') for f in diagnostics] + [(0, he, b'')]
preamble = 'import Definitions.Def_ZetaNine_CoefficientMapKernelBridge\n\nset_option autoImplicit false\nopen scoped BigOperators Topology\nopen Finset Polynomial Filter\nopen ZetaNine ' + NS + ' ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapAggregate\n'
sol_header = 'import Definitions.Def_ZetaNine_CoefficientMapKernelBridge\nimport Mathlib.Tactic\n\nset_option autoImplicit false\nset_option maxHeartbeats 2000000\nnoncomputable section\n' + bridge
ending_opens = 'open ZetaNine ' + NS + ' ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapFiniteSum ZetaNine.CoefficientMapSummation ZetaNine.CoefficientMapAggregate ZetaNine.HarmonicStability\n'
plan = load(BATCH / 'target-plan.json')
request = load(BATCH / 'problems-request.json')
for i, name in enumerate(TARGETS):
    full = NS + '.' + name
    d = declaration(full)
    a, v = d['declStart']['offset'], d['valStart']['offset']
    rs = [r for r in refs if r['const'] == full]
    bindings = [r for r in rs if a <= r['start']['offset'] < v]
    assert len(bindings) == 1
    x, y = bindings[0]['start']['offset'], bindings[0]['end']['offset']
    assert source[x:y].decode() == name
    signature = source[y:v].decode()
    renames = []
    for r in rs:
        start, end = r['start']['offset'], r['end']['offset']
        if any(ca <= start and end <= cb for ca, cb, _ in cuts):
            continue
        original = source[start:end].decode()
        assert original in [name, full]
        renames.append((start, end, ('checked_' + name if original == name else NS + '.checked_' + name).encode()))
    solution = sol_header + '\n' + edit(source, cuts + renames).decode() + '\n\n' + ending_opens
    solution += '\ntheorem solution' + signature + ':= by\n  exact ' + NS + '.checked_' + name + ' ' + ARGS[i] + '\n\n#print axioms solution\n'
    target = plan['targets'][i]
    assert target['wrapper_arguments'] == ARGS[i]
    assert solution.encode() == (BATCH / 'staged' / target['local_solution']).read_bytes()
    formal_changes = [(x - a, y - a, full.encode())]
    if d['docstring']:
        doc = d['docstring']
        formal_changes.append((doc['start']['offset'] - a, doc['end']['offset'] - a, b''))
    formal = edit(source[a:v], formal_changes).decode().strip() + ':= by sorry'
    reference = preamble + '\n' + formal + '\n'
    assert reference.encode() == (BATCH / 'staged' / target['local_reference']).read_bytes()
    pt = provenance['targets'][full]
    assert request['problems'][i]['formal_statement'] == formal and request['problems'][i]['preamble'] == preamble
    assert pt['binding_fact'] == bindings[0] and pt['declaration_fact'] == d and pt['target_refs'] == rs
    assert pt['rename_spans'] == [[start, end] for start, end, _ in renames] and not pt['extra_hypotheses']
    clean = re.sub(r'--[^\n]*', '', re.sub(r'/\-.*?\-/', '', solution, flags=re.S))
    assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b', clean)
    assert not re.search(r'(?m)^import (Theorems|Solutions|missions)\.', solution)
    for relative, text in [(target['local_solution'], solution), (target['local_reference'], reference)]:
        write(PROJECT / relative, text)
        write(OUT / 'reconstructed' / relative, text)
check('all three complete Solutions references requests and original signature spans reconstructed', True,
      {'source_proofs_each': 23, 'true_parent_helpers_each': 145, 'wrapper_each': 1, 'extra_hypotheses': []})
definitions_request = load(BATCH / 'definitions-request.json')
check('exact full genuine Definition request retains true original data and public environment',
      len(definitions_request) == 1 and definitions_request[0]['definition'] == definition
      and definitions_request[0]['env'] == request['env'] and definitions_request[0]['private'] is False
      and request['private'] is False and not provenance['new_external_theorem_boundaries'])
all_defs = [r['name'] for r in graph if r['kind'] == 'def' and r['startLine'] > 0]
check('actual65 source Definitions reconstructed for seven contexts', len(all_defs) == 65)
dump(OUT / 'mechanical-checks.json', {'complete': True, 'checks': checks, 'actual_cross_helpers': helpers,
    'actual_defs': all_defs, 'core_proof_names': [r['name'] for r in core if r['kind'] == 'theorem'],
    'targets': TARGETS, 'constructor_local_proofs': transforms,
    'constructor_proof_has_no_cyclic_equiv_inverse_or_prescribed_data': True,
    'newDefinition_sha256': sha(PROJECT / def_relative), 'Root_and_frozen_input_gate': verify()})
print('Independent graph, source/span and full genuine constructor reconstruction:', len(checks), 'checks PASS', flush=True)
