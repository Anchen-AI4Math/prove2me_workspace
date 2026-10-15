"""Read all actual translation CI differences once before strict certification."""
from __future__ import annotations

import json

import stage_log_translation_count_node as stage
import certify_full_row_minor_node as kernel
import certify_selected_minor_clearing_bound_node as pairing


def read(name):
    return json.loads((stage.STAGE / name).read_text(encoding='utf-8'))


def project(names):
    return sorted(x for x in names if x.startswith('OAI.') or x.startswith('_private.') and '.OAI.' in x)


def main():
    owned = read(stage.INVENTORY)
    src = {r['name']: r for r in read(stage.SOURCE_REFS)['rows']}
    gen = {r['name']: r for r in read(stage.GENERATED_REFS)['rows']}
    root_map = dict(zip(stage.HELPERS, owned['actualPrivateHelpers'], strict=True))
    root_map[stage.TARGET] = 'solution'
    extra_error = None
    try:
        mapping = dict(root_map)
        mapping.update(pairing.pair_extra(
            {n: r for n, r in src.items() if n not in mapping},
            {n: r for n, r in gen.items() if n not in mapping.values()}, mapping))
    except Exception as exc:
        mapping = root_map
        extra_error = f'{type(exc).__name__}: {exc}'
    pairs = []
    for a, b in mapping.items():
        if a not in src or b not in gen:
            pairs.append({'source': a, 'generated': b, 'missingActualRow': True})
            continue
        x, y = src[a], gen[b]
        sx, sy = kernel.normalized_type(x), kernel.normalized_type(y)
        row = {'source': a, 'generated': b,
               'fullTypeEqual': sx[0] == sy[0] and kernel.rename_expr(sx[1], mapping) == sy[1],
               'axiomsEqual': x['axioms'] == y['axioms'],
               'sourceOwner': x['owner'], 'generatedOwner': y['owner'],
               'closedSourceValue': x['closedValue'], 'closedGeneratedValue': y['closedValue']}
        for field in ['typeRefs', 'valueRefs', 'allUsedConstants']:
            left = {mapping.get(n, n) for n in x[field]}
            right = set(y[field])
            row[field] = {'equal': left == right,
                          'sourceOnly': sorted(left - right),
                          'generatedOnly': sorted(right - left),
                          'sourceProject': project(left),
                          'generatedProject': project(right)}
        pairs.append(row)
    report = {'schema_version': 1,
              'artifact_kind': 'ap20-log-translation-actual-all-CI-read-only-audit',
              'sourceRootNames': read(stage.SOURCE_REFS)['rootNames'],
              'generatedRootNames': read(stage.GENERATED_REFS)['rootNames'],
              'sourceCINames': sorted(src), 'generatedCINames': sorted(gen),
              'rawOwnedNames': owned['rawOwnedNames'],
              'rawOwnedOutsideProofClosure': sorted(set(owned['rawOwnedNames']) - set(gen)),
              'proofClosureOutsideRawOwned': sorted(set(gen) - set(owned['rawOwnedNames'])),
              'actualPrivateHelperMapping': root_map,
              'actualExtraPairingError': extra_error,
              'pairs': pairs,
              'allFullTypesEqual': all(p.get('fullTypeEqual') is True for p in pairs),
              'allAxiomsEqual': all(p.get('axiomsEqual') is True for p in pairs),
              'allProjectRefsEqual': all(all(p[f]['sourceProject'] == p[f]['generatedProject']
                                             for f in ['typeRefs', 'valueRefs', 'allUsedConstants'])
                                         for p in pairs if not p.get('missingActualRow')),
              'noLeanOrAPI': True}
    path = stage.STAGE / 'actual-ci-audit.json'
    path.write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({'pairs': len(pairs),
                      'allFullTypesEqual': report['allFullTypesEqual'],
                      'allAxiomsEqual': report['allAxiomsEqual'],
                      'allProjectRefsEqual': report['allProjectRefsEqual'],
                      'actualExtraPairingError': extra_error,
                      'report': stage.rel(path)}))


if __name__ == '__main__':
    main()
