"""Find genuine theorem paths ending in the exact accepted parent submission."""


def graph_endpoint(theorem_id, depth=2, direction='children'):
    # These exact fields were read from the deployed public frontend client.
    # Default graphs include high-fanout parent neighborhoods; focus children
    # when auditing a theorem's own accepted decomposition.
    assert direction in ('children', 'parents')
    return f'/theorems/{theorem_id}/graph?depth={depth}&expand_node={theorem_id}&direction={direction}'


def actual_child_path(edges, child, submission, parent):
    sketch = 'sketch-' + submission
    assert (sketch, parent, 'sketch') in edges, ('Missing parent edge', parent, submission)
    if (child, sketch, 'sketch') in edges:
        return {'path_kind': 'direct', 'actual_node_path': [child, sketch, parent]}
    parents = {}
    for source, target, kind in edges:
        if kind == 'sketch':
            parents.setdefault(source, []).append(target)
    pending = [(child, [child])]
    seen = set()
    while pending:
        current, path = pending.pop()
        if current == sketch:
            return {'path_kind': 'transitive', 'actual_node_path': path + [parent]}
        if current in seen:
            continue
        seen.add(current)
        pending.extend((next_node, path + [next_node]) for next_node in parents.get(current, []))
    raise AssertionError(('Missing actual dependency path', child, submission, parent))
