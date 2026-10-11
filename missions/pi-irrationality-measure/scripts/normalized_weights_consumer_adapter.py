"""Project two checked request annotations to the frozen kernel schema."""
from contextlib import contextmanager
from pathlib import Path
import validate_normalized_weights_provider as consumer

FROZEN = 'feb5c7409db35d8a20f391146593b6cb99244e3f4e0345861230d84aca37551f'
NAME = 'OAI.PiExponent.normalizedLogWeights'
MODULES = {consumer.stage.MODULE, consumer.PLATFORM}


@contextmanager
def installed():
    if consumer.sha(Path(consumer.__file__)) != FROZEN:
        raise ValueError('Frozen consumer changed')
    kernel = consumer.kernel
    original = kernel.validate_row_basic

    def validate(row, request, owner, graph, graph_sha, *, expected_module):
        if not (set(request) == kernel.REQUEST_KEYS | {'expected_public_name', 'expected_module'}
                and request['source_name'] == request['family_root'] == NAME
                and request['expected_public_name'] == NAME
                and expected_module in MODULES
                and request['expected_module'] == request['source_module'] == expected_module
                and owner['source_name'] == NAME
                and owner['source_module'] == consumer.stage.MODULE
                and owner['command_unit'] == consumer.stage.UNIT
                and owner['graph_kind'] == 'def' and owner['source_private'] is False
                and owner.get('family_root', NAME) == NAME):
            raise ValueError('Single-CI request annotation adapter domain differs')
        projected = {key:request[key] for key in kernel.REQUEST_KEYS}
        # A generic catalog owner has no family annotation; this singleton
        # exporter groups only the actual public definition under its own Name.
        family_owner = dict(owner, family_root=NAME)
        return original(row, projected, family_owner, graph, graph_sha, expected_module=expected_module)

    kernel.validate_row_basic = validate
    try:
        yield
    finally:
        kernel.validate_row_basic = original
