"""Refine unproved server checks without running Lean or changing published data."""
import json
import re
from prepare_remote_milestone import HERE, ROOT, PLATFORM, ACTUAL, NS, OPTIONS, SOURCE, module, projection, spec


def main():
    manifest_path = PLATFORM / 'milestone35-manifest.json'
    manifest = json.loads(manifest_path.read_text(encoding='utf-8'))
    journal = json.loads((PLATFORM / 'journal.json').read_text(encoding='utf-8'))
    changed = []
    for parent, children in list(manifest['subparts'].items()):
        expanded = []
        for slug in children:
            obj = json.loads((PLATFORM / (slug + '.json')).read_text(encoding='utf-8'))
            name = obj['theorem_name']
            record = journal.get('proof:' + name, {})
            typ = obj['formal_statement'].split(' : ', 1)[1].rsplit(' := by sorry', 1)[0]
            indices = [int(i) for i in re.findall(r'\(rowAt (\d+) = data_', typ)]
            timed_out = record.get('status') == 'ERROR' and 'timed out' in record.get('result', {}).get('error_message', '')
            if record.get('status') in ('ACCEPTED', 'PENDING') or len(indices) <= 1 or (len(indices) <= 4 and not timed_out):
                expanded.append(slug)
                continue
            limit = max(1, len(indices) // 2) if timed_out else 4
            source = (ROOT / obj['proof_file']).read_text(encoding='utf-8')
            if not re.search(r'^theorem (?:entry_\d+_checked|row_\d+) :', source, re.M):
                expanded.append(slug)
                continue
            own = []
            for match in re.finditer(r'^theorem (?:entry_(\d+)_checked|row_(\d+))', source, re.M):
                i = int(match[1] or match[2])
                if i in indices and (not own or own[-1][0] != i):
                    own.append((i, match.start()))
            assert [i for i, _ in own] == indices
            end_at = source.index('\nend ' + NS, own[-1][1])
            bodies = {i: source[pos:own[k + 1][1] if k + 1 < len(own) else end_at]
                      for k, (i, pos) in enumerate(own)}
            bodies = {i: re.sub(r'^#check.*\n?', '', code, flags=re.M) for i, code in bodies.items()}
            prefix = source[:own[0][1]]
            ranges = [indices[k:k + limit] for k in range(0, len(indices), limit)]
            names = [name.removesuffix('_correct') + f'_piece{k:02}_correct' for k in range(len(ranges))]
            locations = {i: (k, items.index(i)) for k, items in enumerate(ranges) for i in items}
            match = re.fullmatch(r'milestone35-block(\d+)-group(\d+)((?:-piece\d+)*)', slug)
            assert match
            block, group = map(int, match.groups()[:2])
            stem = f'Certificate35Block{block:02}Group{group:02}' + ''.join(f'Piece{int(i):02}' for i in re.findall(r'-piece(\d+)', match[3]))
            original_actual = ACTUAL / (stem + '.lean')
            old_actual = original_actual.read_text(encoding='utf-8')
            actual_imports = old_actual[:old_actual.index('set_option')]
            leaves = []
            for k, items in enumerate(ranges):
                code = ''.join(bodies[i] for i in items)
                earlier = sorted({int(i) for i in re.findall(r'row_(\d+)', code)
                                  if int(i) in locations and int(i) < items[0]})
                needed = sorted({locations[i][0] for i in earlier})
                added_imports = ''.join('import ' + module(names[j]) + '\n' for j in needed)
                at = prefix.index('set_option')
                aliases = ''.join(f'theorem row_{i} : rowAt {i} = data_{i} := ({projection(names[locations[i][0]], locations[i][1])}).1\n' for i in earlier)
                piece_type = ' ∧ '.join(f'(rowAt {i} = data_{i} ∧ Good (rowAt {i}) ∧ ' +
                                         (f'EntryGood {i}' if i >= 6 else 'True') + ')' for i in items) + ' ∧ True'
                proof = '⟨' + ', '.join(f'⟨row_{i}, good_{i}, ' + (f'entry_good_{i}' if i >= 6 else 'trivial') + '⟩' for i in items) + ', trivial⟩'
                upload = prefix[:at] + added_imports + prefix[at:] + aliases + code
                upload += '\nend ' + NS + '\nopen ' + NS + ' OAI.SnakyCertificate\n'
                upload += f'theorem solution : {piece_type} := by\n  exact {proof}\n'
                leaf = slug + f'-piece{k:02}'
                leaves.append(spec(leaf, names[k], f'35-move certificate: exact rows {items[0]}–{items[-1]}',
                    'theorem ' + names[k] + ' : ' + piece_type + ' := by sorry', obj['preamble'], upload,
                    f'Exact finite certificate data, row invariants and backward references for original rows {items[0]} through {items[-1]}.',
                    'Use the proved table lookups and earlier child rows; check the three RowData fields and predicates with decide +kernel. '
                    f'This server verification contains at most {limit} rows. No local Lean process is started.'))
                actual_base = actual_imports if k == 0 else 'import Solutions.SnakyMilestones.' + stem + f'Piece{k-1:02}\n'
                actual = actual_base + OPTIONS + 'namespace ' + NS + '\nopen OAI.SnakyCertificate\n' + code
                actual += f'\ntheorem {names[k].removeprefix(NS + ".")} : {piece_type} := by\n  exact {proof}\nend ' + NS + '\n'
                (ACTUAL / (stem + f'Piece{k:02}.lean')).write_text(actual, encoding='utf-8')
            assembled = '⟨' + ', '.join(projection(names[locations[i][0]], locations[i][1]) for i in indices) + ', trivial⟩'
            wrapper = ''.join('import ' + module(n) + '\n' for n in names) + OPTIONS + 'open ' + NS + ' OAI.SnakyCertificate\n'
            wrapper += f'theorem solution : {typ} := by\n  exact {assembled}\n'
            (ROOT / obj['proof_file']).write_text(wrapper, encoding='utf-8')
            obj['explanation'] = 'Projection-only assembly from the smaller proved row checks; the published statement and all original certificate data are unchanged.'
            (PLATFORM / (slug + '.json')).write_text(json.dumps(obj, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
            actual = 'import Solutions.SnakyMilestones.' + stem + f'Piece{len(ranges)-1:02}\n' + OPTIONS
            actual += 'namespace ' + NS + '\nopen OAI.SnakyCertificate\n'
            actual += f'theorem {name.removeprefix(NS + ".")} : {typ} := by\n  exact {assembled}\nend ' + NS + '\n'
            original_actual.write_text(actual, encoding='utf-8')
            expanded.extend(leaves + [slug])
            changed.append({'group': slug, 'row_limit': limit, 'pieces': leaves})
        manifest['subparts'][parent] = expanded
    manifest_path.write_text(json.dumps(manifest, indent=2) + '\n', encoding='utf-8')
    record_path = HERE / 'verification' / 'remote-refinement.json'
    history = json.loads(record_path.read_text(encoding='utf-8')) if record_path.exists() else []
    record_path.write_text(json.dumps(history + changed, indent=2) + '\n', encoding='utf-8')
    print('Refined', len(changed), 'unproved groups; no Lean invoked.', flush=True)


if __name__ == '__main__':
    main()
