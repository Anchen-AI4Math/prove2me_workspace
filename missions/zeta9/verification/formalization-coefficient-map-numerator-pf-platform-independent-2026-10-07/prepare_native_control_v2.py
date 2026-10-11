"""Generate the independent native control from our actual, SOURCE-built graph."""
from pathlib import Path
import json, sys
import inspect_author as p
import semantic_spec_v2 as s

def main():
    sys.stdout.reconfigure(encoding='utf-8')
    selected=p.load(p.OUT/'own-native-graph-selection.json')
    prep=p.load(p.OUT/'source-preparation.json')
    assert len(selected['definitions'])==11 and len(selected['proofs'])==34
    assert selected['generated']==['ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialBlock.eq_1']
    source='import missions.zeta9.formalization.CoefficientMapNumeratorPartialFractions\n'+s.OPENS
    source+=s.assertions(s.TARGETS)+s.HELPERS+'\nrun_meta do\n'
    source+=''.join('  emitDefinition `'+n+'\n' for n in selected['definitions'])
    source+=''.join('  emitProof `'+n+' "independent_named_native_proof"\n' for n in selected['proofs'])
    source+=''.join('  emitProof `'+n+' "independent_generated_equation_helper"\n' for n in selected['generated'])
    source+=s.assertion_meta(s.TARGETS)
    source+='  emitInternalHelpers ['+', '.join('`'+x['module'] for x in prep['native_sources'])+']\n'
    target=p.PROJECT/'PFIndependentNativeV2.lean'
    assert not target.exists(); target.write_text(source,encoding='utf-8')
    snapshot=p.OUT/'PFIndependentNativeV2.lean'; snapshot.write_bytes(target.read_bytes())
    plan=dict(status='PURE_CONTROL_FROM_OWN_ACTUAL_NATIVE_GRAPH',Lean_invocations_in_generation=0,
        role='Independent reviewer; graph excludes author control modules',
        own_graph=p.bind(p.PROJECT/'native-decl-graph.jsonl'),selection=p.bind(p.OUT/'own-native-graph-selection.json'),
        independent_mathematical_spec=p.bind(p.OUT/'semantic_spec_v2.py'),
        source=p.bind(target),source_snapshot=p.bind(snapshot),
        complete_native_definition_types_values=11,named_native_proof_types=34,
        generated_equation_helper_types=1,complete_independent_forall_theorems=3,
        whole_function_rfl=5,whole_definition_Expr_equal_and_isDefEq=5,closed_boundaries=9,
        all_native_participating_module_internal_helpers_audited=True,
        no_unreached_weighted_bridge_payload_addition=True,independent_PASS_claimed=False)
    (p.OUT/'native-control-preparation-v2.json').write_text(json.dumps(plan,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print('Prepared own11/34/eq1 capture plus complete3 forall,5 full definition comparisons/rfl and9 boundaries.')

if __name__=='__main__':main()
