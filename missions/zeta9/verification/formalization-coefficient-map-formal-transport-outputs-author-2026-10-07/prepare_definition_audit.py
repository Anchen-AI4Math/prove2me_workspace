"""SOURCE-only full definition expectations; author provenance, not independence."""
from pathlib import Path
import hashlib,json,re
OUT=Path(__file__).resolve().parent;TASK=OUT.parents[1];PROJECT=TASK/'.rt/oa1'
groups={
 'CoefficientMapFormalTransportData':['connectionPair','connectionP','connectionQ','connectionGamma',
    'remainderNumerator','shiftedRemainderNumerator','numeratorClearedSeries','numeratorLocalCoefficient',
    'remainderCoefficient','extendedOldCoefficient','extendedRemainderCoefficient','previousRemainderCoefficient'],
 'CoefficientMapFiniteSum':['rho','constantTerm'],
 'CoefficientMapAggregate':['aggregate','aggregateLinearMap','quarticAggregateLinearMap'],
 'CoefficientMapMatrix':['actualFMatrix']}
opening='''import missions.zeta9.formalization.CoefficientMapFormalTransportOutputs
import IndependentExprDagV3
import Lean
noncomputable section
open scoped BigOperators
open Finset Polynomial
open ZetaNine
open ZetaNine.HarmonicStability ZetaNine.CoefficientMap ZetaNine.CoefficientMapJet
open ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions
open ZetaNine.CoefficientMapFiniteSum ZetaNine.CoefficientMapAggregate
open ZetaNine.CoefficientMapKernelBridge ZetaNine.CoefficientMapConnection
open ZetaNine.CoefficientMapMatrix ZetaNine.CoefficientMapFormalTransportData
namespace OutputsAuthorDefinitionExpected
'''
expected=[];pairs=[];provenance=[]
for module,names in groups.items():
    path=PROJECT/f'missions/zeta9/formalization/{module}.lean'
    text=path.read_text(encoding='utf-8-sig')
    for name in names:
        match=re.search(r'^def '+re.escape(name)+r'\b',text,re.M);assert match
        rest=text[match.start():]
        next_decl=re.search(r'\n(?:def|theorem|end)\s',rest)
        block=rest[:next_decl.start()+1] if next_decl else rest
        renamed=block.replace('def '+name,'def expected_'+name,1)
        expected.append(renamed)
        pairs.append(f'(`ZetaNine.{module}.{name}, `OutputsAuthorDefinitionExpected.expected_{name})')
        provenance.append(dict(actual=f'ZetaNine.{module}.{name}',source=str(path),
            source_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
            exact_definition_source_block=block,expected_source_block=renamed,
            expectation_is_author_source_reuse=True))
tail='''end OutputsAuthorDefinitionExpected
open Lean Meta
set_option maxHeartbeats 0
set_option maxRecDepth 20000
run_meta do
  for (actual,expected) in [PAIRS] do
    let .defnInfo a ← getConstInfo actual | throwError "Actual is not a complete definition"
    let .defnInfo b ← getConstInfo expected | throwError "Expected is not a complete definition"
    let typeSame ← isDefEq a.type b.type
    let valueSame ← isDefEq a.value b.value
    unless typeSame && valueSame do throwError "Whole definition kernel mismatch: {actual}"
    let aa ← collectAxioms actual
    let ba ← collectAxioms expected
    let allowed : List Name := [`propext,`Classical.choice,`Quot.sound]
    unless aa.toList.all allowed.contains && ba.toList.all allowed.contains do
      throwError "Nonstandard definition axioms"
    let sourceDag ← ofExcept (IndependentLosslessExprDagV1.persistedRoundTrip a.type a.value)
    let expectedDag ← ofExcept (IndependentLosslessExprDagV1.persistedRoundTrip b.type b.value)
    IO.println (Json.mkObj [("kind",Json.str "actual_complete_definition_kernel_value"),
      ("declaration",Json.str actual.toString),("expected",Json.str expected.toString),
      ("type_kernel_equal",toJson typeSame),("value_kernel_equal",toJson valueSame),
      ("full_source_type_and_value_expression_dag",sourceDag),
      ("full_expected_type_and_value_expression_dag",expectedDag),
      ("all_fields_Expr_equal_roundtrip",toJson true),
      ("source_axioms",toJson (aa.toList.map Name.toString)),
      ("expected_axioms",toJson (ba.toList.map Name.toString))]).compress
'''.replace('PAIRS',', '.join(pairs))
source=opening+'\n'.join(expected)+'\n'+tail
(OUT/'OutputsDefinitionsAudit.lean').write_text(source,encoding='utf-8')
(OUT/'definition-expectation-provenance.json').write_text(json.dumps(dict(
    role='Author full-definition expectation source reuse',records=provenance,
    complete_definition_count=len(pairs),independent_review_claimed=False),ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(f'{len(pairs)} SOURCE-only complete definition expectations prepared; no Lean invoked.')
