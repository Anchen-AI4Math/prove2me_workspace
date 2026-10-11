from pathlib import Path
import json
p=Path(__file__).resolve().parent
q=json.loads((p/'integration-provenance.json').read_text(encoding='utf-8-sig'))
d=p/'staged/Definitions/Def_ZetaNine_CoefficientMapKernelBridge.lean'
print(json.dumps({'new_definition_bytes':d.stat().st_size,'true_parent_proofs_per_Solution':len(q['inline_helper_names']),'all_closed_proof_records_per_Solution':24+len(q['inline_helper_names']),'selected_endpoints':list(q['targets']),'original_proof_body_spans':q['source_proofs'],'global_Def_proof_hypotheses_added':len(q['new_external_theorem_boundaries'])}))