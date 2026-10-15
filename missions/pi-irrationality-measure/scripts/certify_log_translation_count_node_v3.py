"""Derived strict translation certificate binding actual imported provider OLeans."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import certify_log_translation_count_node as prior
import stage_log_translation_count_node as stage
import certify_full_row_minor_node as kernel
import validate_namespace_context_providers as context

SELF = Path(__file__).resolve()
CERTIFICATE = 'node-validation-v3.json'
DATA_MODULE = 'Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData'
LOGDIV_MODULE = 'Theorems.Thm_OAI_PiExponent_tendsto_log_div_of_normalized_pow'


def need(cond: bool, reason: str) -> None:
    if not cond:
        raise ValueError(reason)


def imported(record, module: str, certified_path: Path, certified_sha: str):
    row = kernel.imported_dep(record, module)
    need(Path(row['path']).resolve() == certified_path.resolve()
         and row['sha256_before'] == row['sha256_after'] == certified_sha
         and row['stable_during_compile'] is True
         and stage.file_sha(certified_path) == certified_sha,
         'Actual first-search imported module differs from certified provider: ' + module)
    return row


def validate() -> dict:
    report = prior.validate()
    data_cert = prior.read(stage.route.CERT)
    logdiv_cert = prior.read(stage.route.LOGDIV_CERT)
    data_path = stage.TASK / data_cert['original_emitted_provider_olean']
    logdiv_path = stage.TASK / logdiv_cert['provider_olean']
    c1 = context.record(stage.STAGE / stage.TARGET_OUTPUT, stage.STAGE / 'c1.json',
                        'modecheck', stage.MODULE, stage.STAGE)
    c2 = context.record(stage.STAGE / stage.SOLUTION_OUTPUT, stage.STAGE / 'c2.json',
                        'emit-olean', stage.SOLUTION_MODULE, stage.STAGE)
    references = {
        'c1_published_data': imported(c1, DATA_MODULE, data_path,
                                      data_cert['original_emitted_provider_olean_sha256']),
        'c2_published_data': imported(c2, DATA_MODULE, data_path,
                                      data_cert['original_emitted_provider_olean_sha256']),
        'c2_accepted_logdiv': imported(c2, LOGDIV_MODULE, logdiv_path,
                                       logdiv_cert['provider_olean_sha256']),
    }
    need(report['validated'] is True and report['Std3_only'] is True
         and report['references_bitwise_equal_under_actual_mapping'] is True,
         'Original complete four-context mathematical replay differs')
    report.update({
        'artifact_kind': 'ap20-log-translation-count-four-original-AST-validation-v3',
        'actual_imported_certified_provider_oleans': references,
        'published_data_cert_sha256': stage.file_sha(stage.route.CERT),
        'accepted_logdiv_mirror_cert_sha256': stage.file_sha(stage.route.LOGDIV_CERT),
        'frozen_original_consumer_preimage_sha256': stage.file_sha(Path(prior.__file__)),
        'implementation_hashes': {
            **report['implementation_hashes'],
            stage.rel(SELF): stage.file_sha(SELF),
        },
    })
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    x = parser.add_mutually_exclusive_group(required=True)
    x.add_argument('--certify-existing', action='store_true')
    x.add_argument('--check-only', action='store_true')
    args = parser.parse_args()
    result = validate()
    path = stage.STAGE / CERTIFICATE
    if args.certify_existing:
        path.write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    else:
        need(path.is_file() and prior.read(path) == result,
             'Saved derived actual OLean-bound certificate differs')
    print(json.dumps({'validated': True, 'certificate': stage.rel(path),
                      'sha256': stage.file_sha(path)}))


if __name__ == '__main__':
    main()
