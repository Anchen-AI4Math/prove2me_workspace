"""Pure publication input gate. No network, client, credentials or compiler."""
from pathlib import Path
import argparse
import json
import prepare_publication_v3 as prepared


def gate(pin_path):
    result = prepared.require_root_pin(pin_path)
    root_pin = prepared.load(pin_path)
    index = prepared.OUT / 'interface-bindings-v3.json'
    assert root_pin['prepared_interface_bindings_sha256'] == prepared.sha(index)
    for row in prepared.load(index)['files']:
        prepared.check_binding(row)
    definitions = prepared.load(prepared.OUT / 'definitions-request-v3.json')
    problems = prepared.load(prepared.OUT / 'problems-request-v3.json')
    explanations = prepared.load(prepared.OUT / 'proof-explanations-v3.json')
    wire = [prepared.load(p) for p in sorted((prepared.OUT/'requests-v3').glob('*.json'))]
    assert definitions == [wire[0]] and problems == {
        'env':prepared.ENV, 'private':False, 'problems':[r['problems'][0] for r in wire[1:]]}
    metadata = prepared.load(prepared.OUT / 'publication-metadata-v3.json')
    assert explanations == {k:v['explanation'] for k,v in metadata['problems'].items()}
    for name, explanation in explanations.items():
        path = prepared.OUT / 'proof-explanations-v3' / (name.split('.')[-1] + '.md')
        assert path.read_bytes() == explanation.encode('utf-8')
    definition_source = prepared.OUT/'payloads/Definitions/Def_ZetaNine_CoefficientMapNumeratorPF.lean'
    assert definitions[0]['definition'].encode('utf-8') == definition_source.read_bytes()
    original = prepared.load(prepared.PF/'problems-request.json')
    for old, new in zip(original['problems'], problems['problems']):
        assert {k for k in old if old[k] != new[k]} <= {'natural_language_statement','source'}
        assert old['formal_statement'] == new['formal_statement'] and old['preamble'] == new['preamble']
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('actual_Root_pin', type=Path)
    print(json.dumps(gate(parser.parse_args().actual_Root_pin)))
