"""Reconcile only passive drive-case replay notes in the complete ap2 report.

The frozen consumer performs all 62 CI comparisons and replays the structural
certificate before its last report equality check. Capture that final report
only when this last equality fails. All mathematical/preflight fields remain
byte-exact; the two process-dependent Windows diagnostic notes are checked
against their complete finite schemas and the same authenticated files.
"""
from __future__ import annotations
import copy
import json
import os
from pathlib import Path
import admissible_provider_manifest_bridge as bridge
import complete_admissible_provider as complete
import generate_shared_source_snapshot as base
import structural_provider_certificate_evidence_windows as windows

CERT = bridge.DEST / 'complete-validation.json'
NOTES = ('windows_catalog_reconciliation', 'windows_source_reconciliation')


def require(value, message):
    if not value:
        raise ValueError(message)


def authentic_alias(a, b, digest=None, directory=False):
    require(a == b or windows._drive_case_pair(a, b), 'Only exact Windows drive-case aliases accepted')
    pa, pb = Path(a), Path(b)
    require((pa.is_dir() and pb.is_dir()) if directory else (pa.is_file() and pb.is_file()),
            'Authenticated path absent')
    require(os.path.samefile(pa, pb), 'Drive aliases are not the same file')
    if not directory:
        require(base.sha_file(pa) == base.sha_file(pb) == digest, 'Drive alias bytes changed')


def validate_notes(report):
    catalog = complete.read(complete.source_gen.CATALOG)
    recorded, digest = catalog['lean_declaration_source'], catalog['lean_declaration_source_sha256']
    note = report[NOTES[0]]
    if note.get('normalization_applied') is False:
        require(note == dict(normalization_applied=False, recorded=recorded,
                             replayed_before=recorded, sha256=digest), 'Unexpected unnormalized catalog note')
        authentic_alias(recorded, recorded, digest)
    else:
        replayed = note['replayed_before']
        authentic_alias(recorded, replayed, digest)
        require(windows._drive_case_pair(recorded, replayed), 'Catalog note claims a nonexistent case change')
        require(note == dict(normalization_applied=True, field='lean_declaration_source', recorded=recorded,
                             replayed_before=replayed, replayed_after=recorded,
                             suffix_exact_after_drive=True, drive_letters_equal_case_insensitive=True,
                             samefile=True, recorded_sha256=digest, replayed_sha256=digest),
                'Unexpected normalized catalog note')
    source = complete.read(complete.stage.structural.SOURCE_CERTIFICATE)
    lean = source['actual_evidence']['olean_resolution']['dependency_oleans'][0]
    require(lean['module'] == 'Lean' and lean['sha256'] == windows.LEAN_OLEAN_SHA256,
            'Fixed source Lean dependency differs')
    note = report[NOTES[1]]
    common = dict(normalization_applied=False, fields=[], module='Lean', sha256=windows.LEAN_OLEAN_SHA256)
    if note.get('normalization_applied') is False:
        require(note == common, 'Unexpected unnormalized source note')
        authentic_alias(lean['path'], lean['path'], windows.LEAN_OLEAN_SHA256)
        authentic_alias(lean['resolved_search_root'], lean['resolved_search_root'], directory=True)
    else:
        replayed, root = note['replayed_path_before'], note['replayed_search_root_before']
        authentic_alias(lean['path'], replayed, windows.LEAN_OLEAN_SHA256)
        authentic_alias(lean['resolved_search_root'], root, directory=True)
        require(windows._drive_case_pair(lean['path'], replayed)
                and windows._drive_case_pair(lean['resolved_search_root'], root),
                'Source note claims a nonexistent case change')
        require(os.path.samefile(Path(root) / 'Lean.olean', replayed)
                and os.path.samefile(Path(lean['resolved_search_root']) / 'Lean.olean', lean['path']),
                'Source search roots do not resolve to the fixed Lean OLean')
        common.update(normalization_applied=True, fields=[windows.SOURCE_PATH_FIELD, windows.SOURCE_ROOT_FIELD],
                      recorded_path=lean['path'], replayed_path_before=replayed,
                      recorded_search_root=lean['resolved_search_root'], replayed_search_root_before=root,
                      suffixes_exact_after_drive=True, drive_letters_equal_case_insensitive=True,
                      file_samefile=True, root_samefile=True, root_resolves_authenticated_olean=True)
        require(note == common, 'Unexpected normalized source note')


def validate():
    with bridge.installed():
        try:
            result = complete.certify(replay=True)
            fresh = complete.read(CERT)
        except ValueError as error:
            require(str(error) == 'Fresh complete provider report differs from stored certificate',
                    'A prior full kernel/lineage check failed: ' + str(error))
            tb = error.__traceback__
            while tb and not (tb.tb_frame.f_code.co_name == 'certify'
                             and Path(tb.tb_frame.f_code.co_filename).resolve() == Path(complete.__file__).resolve()):
                tb = tb.tb_next
            require(tb is not None and 'report' in tb.tb_frame.f_locals,
                    'Frozen final-report comparison frame is absent')
            fresh = copy.deepcopy(tb.tb_frame.f_locals['report'])
            stored = complete.read(CERT)
            validate_notes(stored)
            validate_notes(fresh)
            left, right = copy.deepcopy(stored), copy.deepcopy(fresh)
            for key in NOTES:
                left.pop(key)
                right.pop(key)
            require(left == right, 'Full report differs outside the two passive Windows replay notes')
            result = dict(validated=True, certificate=base.task_relative(CERT),
                          certificate_sha256=base.sha_file(CERT), rows=62, read_only_replay=True,
                          lean_started=False, api_used=False)
    validate_notes(fresh)
    return dict(result, windows_replay_adapter=base.task_relative(Path(__file__)),
                windows_replay_adapter_sha256=base.sha_file(Path(__file__)),
                reconciled_fields=list(NOTES), full_kernel_and_preflight_report_equal=True,
                fresh_reconciliation={key:fresh[key] for key in NOTES})


if __name__ == '__main__':
    print(json.dumps(validate(), ensure_ascii=True, indent=2))
