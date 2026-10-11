"""Certify actual rootNode complete values despite hygienic binder repr names."""
from run_step import *

verify()
assert load(OUT / 'replay-summary.json')['complete']
name = 'ZetaNine.CoefficientMapTelescoper.rootNode'
graph = rows(OUT / 'decl_graph.jsonl')
g = next(r for r in graph if r['name'] == name)
facts = rows(OUT / 'CoefficientMapTelescoper-facts.jsonl')
selected = [r for r in facts if r['kind'] == 'decl'
            and r['declStart']['line'] <= g['startLine'] <= r['declEnd']['line']]
assert len(selected) == 1
fact = selected[0]
original = (OUT / 'CoefficientMapTelescoper-oracle-input.lean').read_bytes()
body = original[fact['declStart']['offset']:fact['declEnd']['offset']].decode()
assert not any(r['kind'] == 'ref' and r['const'].startswith('ZetaNine.') and r['const'] != name
               and fact['declStart']['offset'] <= r['start']['offset']
               and r['end']['offset'] <= fact['declEnd']['offset'] for r in facts)
alias_namespace = 'KernelIndependentRootNodeValueComparison'
native_import = 'import missions.zeta9.formalization.CoefficientMapTelescoper'
staged_import = 'import Definitions.Def_ZetaNine_CoefficientMapTelescoper'
native_alias = native_import + '\n\nset_option autoImplicit false\nnamespace ' + alias_namespace + '\n\n' + body
native_alias += '\n\nend ' + alias_namespace + '\n'
native_alias += '\ntheorem independent_rootNode_whole_value_eq : ' + alias_namespace + '.rootNode = ' + name + ' := rfl\n'
staged_alias = native_alias.replace(native_import, staged_import, 1)
helper = (OUT / 'full-kernel-audit.helper.lean').read_text(encoding='utf-8-sig')
details = 'import NativeRootNodeValueComparison\n' + helper
details += '\nrun_meta do\n  checkIndependentNativeAlias `' + name + ' `' + alias_namespace + '.rootNode\n'
details += '  emitIndependentProof `independent_rootNode_whole_value_eq\n'
staged_details = details.replace('import NativeRootNodeValueComparison', 'import StagedRootNodeValueComparison', 1)
for context, cache, module, alias, program in [
        ('native', N, 'NativeRootNodeValueComparison', native_alias, details),
        ('staged', P, 'StagedRootNodeValueComparison', staged_alias, staged_details)]:
    source = PROJECT / (module + '.lean')
    write(source, alias)
    write(OUT / (module + '.lean'), alias)
    run(context + ' actual rootNode same-source whole-value alias', source, cache, cache / (module + '.olean'))
    source = OUT / ('nv.lean' if context == 'native' else 'sv.lean')
    write(source, program)
    run(context + ' actual rootNode whole-kernel equality and rfl', source, cache)
dump(OUT / 'root-node-value-provenance.json', {'original': name, 'alias': alias_namespace + '.rootNode',
    'actual_original_parser_declaration_fact': fact, 'source_body_unchanged': True,
    'native_staged_alias_difference': 'single original/native-to-pure-Definition import only',
    'native_staged_audit_difference': 'single actual alias module import only',
    'direct_actual_full_kernel_comparisons': 2, 'closed_whole_function_rfl_proofs': 2,
    'Root_or_author_objects_borrowed': False, 'new_hypotheses': []})
print('Both actual rootNode whole-function kernel and rfl certificates complete.', flush=True)
