"""Future own-oracle-driven complete value checks, including proof fields.

No import-time execution. Native/staged canonical definitions occupy separate
Lean environments. Aliases use the actual native parser spans with only their
binding names changed; complete body expressions and proof fields are retained.
"""
from pathlib import Path
import json
import prepare as p
import author_stage as stage
import run_actual as actual

def main():
    p.execution_gate()
    c = stage.context()
    data = [row for row in c['graph'] if row['module'] in c['sources']
            and row['kind'] == 'def' and row['startLine'] > 0]
    data.sort(key=lambda row: (row['module'], row['startLine']))
    assert len(data) == 70 and not any(row['isPrivate'] for row in data)
    chunks = []
    pairs = []
    facts_bound = []
    for index, row in enumerate(data):
        name, module = row['name'], row['module']
        source = c['sources'][module]
        fact = c['declaration'](name)
        a, b = fact['declStart']['offset'], fact['declEnd']['offset']
        header_end = fact['valStart']['offset']
        refs = [ref for ref in c['facts'][module] if ref['kind'] == 'ref'
                and ref['const'] == name and a <= ref['start']['offset']
                and ref['end']['offset'] <= header_end]
        assert len(refs) == 1
        ref = refs[0]
        x, y = ref['start']['offset'], ref['end']['offset']
        namespace, short = name.rsplit('.', 1)
        assert source[x:y].decode() == short
        alias_short = 'independent_complete_value_' + str(index + 1).zfill(3)
        alias = namespace + '.' + alias_short
        chunk = stage.edit(source[a:b], [(x - a, y - a, alias_short.encode())]).decode()
        opens = [f for f in c['facts'][module] if f['kind'] == 'command'
                 and f['syntaxKind'] == 'Lean.Parser.Command.open'
                 and f['span']['end']['offset'] <= a]
        context = '\n'.join(source[f['span']['start']['offset']:f['span']['end']['offset']].decode()
                            for f in opens)
        chunks.append('namespace ' + namespace + '\n' + context + '\n' + chunk +
                      '\nend ' + namespace + '\n')
        pairs.append((name, alias))
        facts_bound.append(dict(name=name, alias=alias, actual_declaration_fact=fact,
                                actual_binding_ref=ref, actual_open_context_facts=opens,
                                native_actual_input=p.binding(p.OUT / next(
                                  r['parser_name'] + '-oracle-input.lean' for r in c['state']['native_sources']
                                  if r['module'] == module)),
                                complete_proof_fields_retained=True))
    common = '''import Lean
set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology Matrix
open Finset Polynomial Filter
'''
    compare = '\nopen Lean Meta\nset_option pp.fullNames true\nset_option pp.proofs true\n'
    for index, (name, alias) in enumerate(pairs):
        compare += f'theorem independent_full_function_rfl_{index + 1:03d} : {name} = {alias} := rfl\n'
    compare += '\nrun_meta do\n'
    compare += '  for (name,aliasName) in [' + ', '.join(
        '(`' + name + ', `' + alias + ')' for name, alias in pairs) + '] do\n'
    compare += '''    let .defnInfo d ← getConstInfo name | throwError "Original is not actual Definition"
    let .defnInfo a ← getConstInfo aliasName | throwError "Source-body alias is not actual Definition"
    let te ← isDefEq d.type a.type
    let ve ← isDefEq d.value a.value
    unless te && ve do throwError "Complete Definition including proof fields differs: {name}"
    let axs ← Lean.collectAxioms aliasName
    IO.println (Json.mkObj [("kind",Json.str "independent_complete_definition_kernel"),
      ("declaration",Json.str name.toString),("alias",Json.str aliasName.toString),
      ("type_kernel_equal",toJson te),("full_value_kernel_equal",toJson ve),
      ("original_type_expression_repr",Json.str (reprStr d.type)),
      ("alias_type_expression_repr",Json.str (reprStr a.type)),
      ("original_complete_value_expression_repr",Json.str (reprStr d.value)),
      ("alias_complete_value_expression_repr",Json.str (reprStr a.value)),
      ("axioms",toJson (axs.toList.map Name.toString))]).compress
'''
    compare += '  for name in [' + ', '.join(
        '`independent_full_function_rfl_' + str(index + 1).zfill(3) for index in range(70)) + '] do\n'
    compare += '''    let .thmInfo t ← getConstInfo name | throwError "Expected actual rfl theorem"
    let axs ← Lean.collectAxioms name
    IO.println (Json.mkObj [("kind",Json.str "independent_complete_function_rfl"),
      ("declaration",Json.str name.toString),("full_type_expression_repr",Json.str (reprStr t.type)),
      ("axioms",toJson (axs.toList.map Name.toString))]).compress
'''
    target = p.load(p.OUT / 'target-plan.json')['targets'][-1]['local_solution'].removesuffix('.lean').replace('/', '.')
    provenance = {'actual_definitions': 70, 'actual_complete_value_strategy':
                  'Full original native source bodies vs own native and staged Definitions, actual Meta/rfl; no erased proofs or PP equality',
                  'actual_parser_bound_declarations': facts_bound, 'environments': []}
    for label, imported in [('native', p.NATIVE), ('staged', target)]:
        filename = 'full-values-' + label
        text = 'import ' + imported + '\n' + common + '\n\n'.join(chunks) + compare
        stage.save_leaf(filename, text)
        actual.run(filename, [filename + '.lean'])
        provenance['environments'].append(dict(label=label, imported=imported,
                                               actual_program=p.binding(p.OUT / (filename + '.lean'))))
    p.dump(p.OUT / 'full-parent-value-provenance.json', provenance)

if __name__ == '__main__':
    main()
