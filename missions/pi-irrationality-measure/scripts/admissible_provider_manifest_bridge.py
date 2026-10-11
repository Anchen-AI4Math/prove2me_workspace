"""Reuse the actual emitter record across two exact metadata-only manifests.

The frozen structural consumer expects a family-scoped manifest; the actual
emitter used the complete-provider manifest. Only the three catalog metadata
fields differ. No compiler record, source, OLean, or frozen consumer is edited.
The original preflight verifier still checks the actual manifest and every
ordered import/OLean hash. The adapter is limited to this one provider.
"""
from __future__ import annotations
import argparse
import copy
import json
from contextlib import contextmanager
from pathlib import Path

import complete_admissible_provider as complete
import stage_admissible_provider as stage
import generate_shared_source_snapshot as base
import validate_provider_bundle as ordinary

TASK, DEST = stage.TASK, stage.DEST
SNAP = DEST / 's/snapshots/Def_OAI_NumberTheory_PiExponent_Approximation_AdmissibleParameters'
EXPECTED = SNAP / 'structural-bundle-imports.json'
ACTUAL = DEST / 'e/admissible-imports.json'
MODULE = 'Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_AdmissibleParameters'
PINS = {
    EXPECTED: '7253d7cf18c6869d316f0b7b2eab6a44035032ebae88e083d6721ece98af1370',
    ACTUAL: '51a18779f8a99833247760f2c5d4cdb51d0d77d8eecaf18f57e9f9f95c1fb517',
    Path(complete.__file__): '92d42b1a4b116e2f77b49d682cfdb7454a4a8d810ad529490a3912f377b6f00c',
    Path(stage.__file__): '4f211086d03121b7c16ff11f6e34ffb78cd4e46401523920a0c560fab4b1f806',
    Path(ordinary.__file__): '93a80f728716b46647177691bf1bc9c482015a7f7876fb720617a4a7345067d4',
}


def require(value, message):
    if not value:
        raise ValueError(message)


def check_metadata(old, new):
    projected = copy.deepcopy(old)
    require(projected.pop('structural_family') == 'OAI.PiExponent.AdmissibleParameters',
            'Unexpected structural family')
    require(projected.pop('selected_units') == [stage.ADMISSIBLE + ':2327'],
            'Unexpected atomic structural unit')
    require(projected['artifact_kind'] == 'structural-provider-bundle-imports',
            'Unexpected structural manifest kind')
    projected['artifact_kind'] = 'complete-provider-bundle-imports'
    require(projected == new, 'A field other than the three catalog fields differs')


def binding():
    for path, digest in PINS.items():
        require(base.sha_file(path) == digest, 'Frozen bridge input changed: ' + str(path))
    old, new = (json.loads(p.read_bytes()) for p in (EXPECTED, ACTUAL))
    check_metadata(old, new)
    actual_stage = complete.provider_imports(stage.ADMISSIBLE)
    source = ordinary.VERIFICATION / actual_stage['source']
    require(base.sha_file(source) == new['output_sha256'], 'Provider source changed')
    return old, new, actual_stage, source.resolve()


@contextmanager
def installed():
    stage.configure()
    old, new, actual_stage, source = binding()
    original = ordinary.verify_preflight_record

    def verify(request):
        if Path(request['manifest']).resolve() != EXPECTED.resolve():
            return original(request)
        require((ordinary.VERIFICATION / request['source']).resolve() == source
                and request['module'] == MODULE
                and request['mode'] == 'emit-olean'
                and request['role'] == 'provider-bundle'
                and request['imports'] == new['imports'], 'Bridge request domain differs')
        # Re-read pinned inputs before every delegated verification.
        binding()
        return original(dict(request, manifest=ACTUAL))

    ordinary.verify_preflight_record = verify
    try:
        yield
    finally:
        ordinary.verify_preflight_record = original


def evidence():
    old, new, actual_stage, source = binding()
    return dict(schema_version=1, artifact_kind='exact-provider-manifest-metadata-bridge',
                expected_manifest=base.task_relative(EXPECTED),
                actual_compile_manifest=base.task_relative(ACTUAL),
                input_hashes={base.task_relative(p): h for p, h in PINS.items()},
                adapter=base.task_relative(Path(__file__)), adapter_sha256=base.sha_file(Path(__file__)),
                differing_fields=['artifact_kind', 'structural_family', 'selected_units'],
                compiler_inputs_equal=True, actual_record_verifier_unchanged=True,
                actual_provider_preflight=ordinary.verify_preflight_record(actual_stage),
                lean_started=False, api_used=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=['bind-structural', 'certify', 'replay', 'check'])
    args = parser.parse_args()
    with installed():
        proof = evidence()
        path = DEST / 'manifest-bridge.json'
        if args.mode == 'bind-structural':
            # The earlier unbound provenance is retained, rather than erased.
            provenance = SNAP / 'structural-generated-provenance.json'
            history = SNAP / 'structural-generated-provenance.before-provider.json'
            if not history.exists():
                base.atomic_write(history, provenance.read_bytes())
            result = stage.snapshot.stage(DEST, stage.ADMISSIBLE, require_provider=True)
            base.write_json(path, proof)
        elif args.mode in ('certify', 'replay'):
            require(json.loads(path.read_bytes()) == proof, 'Bridge evidence changed')
            result = complete.certify(replay=args.mode == 'replay')
        else:
            result = proof
    print(json.dumps(result, ensure_ascii=True, indent=2))


if __name__ == '__main__':
    main()
