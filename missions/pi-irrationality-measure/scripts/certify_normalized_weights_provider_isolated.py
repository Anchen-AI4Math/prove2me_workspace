"""Run the frozen ap3 consumer with its real generator output in private scratch."""
import json
import tempfile
from pathlib import Path
import validate_normalized_weights_provider as consumer
import normalized_weights_consumer_adapter as adapter

FROZEN = 'feb5c7409db35d8a20f391146593b6cb99244e3f4e0345861230d84aca37551f'
if consumer.sha(Path(consumer.__file__)) != FROZEN:
    raise ValueError('Frozen consumer changed')
scratch_parent = (consumer.TASK / '.pe').resolve()
if not scratch_parent.is_relative_to(consumer.TASK.resolve()):
    raise ValueError('Private scratch escapes task')
scratch_parent.mkdir(parents=True, exist_ok=True)
original = consumer.base_generator.DEST
original_generate = consumer.base_generator.Generator.generate
try:
    with tempfile.TemporaryDirectory(prefix='nw-cert-', dir=scratch_parent) as scratch:
        target = Path(scratch).resolve()
        if not target.is_relative_to(scratch_parent):
            raise ValueError('Resolved private scratch escapes task')
        def generate_in_scratch(generator, module):
            # DEST also supplies the graph to __init__; redirect only the
            # actual generate method's output after all inputs are loaded.
            before = consumer.base_generator.DEST
            consumer.base_generator.DEST = target
            try:
                return original_generate(generator, module)
            finally:
                consumer.base_generator.DEST = before
        consumer.base_generator.Generator.generate = generate_in_scratch
        with adapter.installed():
            report = consumer.validate()
finally:
    consumer.base_generator.DEST = original
    consumer.base_generator.Generator.generate = original_generate
print(json.dumps({'validated':report['validated'], 'certificate':report['report'],
                  'sha256':report['report_sha256'], 'source174_used':False,
                  'max_seconds':max(report[k]['seconds'] for k in
                                    ['provider_preflight','source_probe_preflight','generated_probe_preflight']),
                  'lean_started':False,'api_used':False}, indent=2))
