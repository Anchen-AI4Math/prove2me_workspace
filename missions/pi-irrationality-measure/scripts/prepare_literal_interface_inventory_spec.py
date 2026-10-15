"""Pure finite owner-index-first inventory contract for the next 17-Def provider."""
from __future__ import annotations
import argparse,json
from pathlib import Path
import stage_analytic_translated_graph_route as route

TASK,SELF=route.TASK,Path(__file__).resolve()
STAGE=route.V/'ap20/literal-interface-data-spec'
PROBE=STAGE/'OwnerIndexFirstInventory.inc'
REPORT=route.STAGE/'report.json'


def contract():
    data=route.read(REPORT)
    route.need(data['minimal_new_definition_count']==17
         and data['minimal_new_definition_source_lines']==49
         and data['validated'] is False,'Original17Def source-only route differs')
    text=PROBE.read_text(encoding='utf-8')
    scan=text[text.index('for (name, ci) in env.constants.toList do'):text.index('found := found.qsort')]
    route.need('env.getModuleIdxFor? name == some wantedIndex' in scan
         and 'toString' not in scan and 'startsWith' not in text
         and 'IO.FS.writeFile' in text,'Owner index-first unfiltered enumeration contract differs')
    return {'schema_version':1,'artifact_kind':'ap20-next17Def-owner-index-first-raw-inventory-spec',
        'provider_module':route.DATA_MODULE,
        'anchor_name':'OAI.PiExponent.LiteralAnalytic.choiceMatrix',
        'source_only_route':route.rel(REPORT),'source_only_route_sha256':route.sha(REPORT),
        'definition_names':data['minimal_new_definition_names'],
        'source_command_count':17,'source_line_count':49,
        'probe':route.rel(PROBE),'probe_sha256':route.sha(PROBE),
        'structural_core':route.rel(route.base.CORE),'structural_core_sha256':route.sha(route.base.CORE),
        'producer_sha256':route.sha(SELF),
        'scan':'one complete env.constants.toList traversal; exact imported ModuleIdx comparison before formatting',
        'namespace_prefix_or_suffix_whitelist':False,
        'raw_full_types_values_refs_owner_private_names_Std3_axioms_exported':True,
        'raw_inventory_must_be_written_before_any_semantic_domain_classification':True,
        'anticipated_auto_CI_names':[],
        'unknown_actual_CIs_require_genuine_source_generated_closed_type_value_or_Prop_evidence':True,
        'source_proof_cache_export_must_discover_actual_used_CIs_not_guess_names':True,
        'source_snapshot_must_not_export_unrelated_whole_module_theorem_proof_values':True,
        'bounded_context_seconds':300,
        'actual_preflights_and_strict_certificate_pending':True,
        'compiler_manifests_finalized':False,'validated':False,
        'Lean_started':False,'API_used':False,'submission_ready':False}


def main():
    p=argparse.ArgumentParser(description=__doc__);g=p.add_mutually_exclusive_group(required=True)
    g.add_argument('--prepare',action='store_true');g.add_argument('--check-only',action='store_true');a=p.parse_args()
    raw=route.encode(contract());path=STAGE/'inventory-contract.json'
    if path.exists():route.need(path.read_bytes()==raw,'Immutable future inventory spec differs')
    elif a.prepare:path.write_bytes(raw)
    else:route.need(False,'Future inventory spec missing')
    print(json.dumps({'inventory_spec':route.rel(path),'sha256':route.sha(path),
        'validated':False,'Lean_started':False,'API_used':False},indent=2))


if __name__=='__main__':main()
