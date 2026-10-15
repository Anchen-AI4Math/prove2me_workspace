"""Refresh obsolete open-bridge wording only after full server graph acceptance."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
from platform import api

VER = Path(__file__).resolve().parent / 'verification'
MISSION = '01a7fb00-e5c3-4a42-a3c2-2cbf04330ffc'
MAIN = 'a53b364e-57a0-4d2c-adc6-983a74218a4b'
BRIDGE = '7c23d3cb-c4a0-4bc1-975a-ca2e5849adc6'
MILESTONE = '3b1f9d5d-e0de-4a71-90a8-b13928cc37e8'
read = lambda p: json.loads(p.read_text(encoding='utf-8'))
save = lambda name, value: (VER / name).write_text(
    json.dumps(value, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
receipt = read(VER / 'machine-graph-check.json')
state = read(VER / 'machine-platform-publish.json')
assert receipt['full_machine_graph_complete']
assert receipt['every_planned_node_connected_to_original_main']
assert receipt['manifest_sha256'] == state['manifest_sha256']
assert state['all_proofs_accepted'] and state['actual_edge_audit_complete']
assert receipt['new_proved_node_count'] == 481
assert receipt['reused_proved_node_count'] == 110
main = api('GET', '/theorems/' + MAIN)
assert main['status'] == 'Proved'
assert 'EndStatement.ThreeSum.SolvedInTime 1.960614' in main['formal_statement']
milestones_path = '/missions/' + MISSION + '/milestones'
milestones_before = api('GET', milestones_path)
assert milestones_before['pagination']['total'] == len(milestones_before['milestones']) == 7
assert all(r['completed'] and r['theorem']['status'] == 'Proved'
           for r in milestones_before['milestones'])


def read_mission():
    offset = 0
    while True:
        page = api('GET', f'/missions?limit=100&offset={offset}')
        matches = [m for m in page['missions'] if m['id'] == MISSION]
        assert len(matches) <= 1
        if matches:
            return matches[0]
        offset += len(page['missions'])
        if not page['missions'] or offset >= page['total']:
            raise RuntimeError('The existing live mission was not found')


before = read_mission()
assert before['main_theorem']['theorem_id'] == MAIN
description = before['description']
old_bridge = 'The **machine bridge** is therefore an open theorem in this mission.'
new_bridge = ('The **machine bridge** has now been proved in this mission. Its accepted '
              'dependency tree connects the modified program and its runtime analysis '
              'to the unchanged campaign specification.')
old_obligation = ('The campaign goal requires an additional result: the actual modified '
                  'program must obey the certified costs, and its operational correctness '
                  'must reach the foundation specification.')
new_obligation = ('The completed machine extension proves that the actual modified program '
                  'obeys the certified costs and that its operational correctness reaches '
                  'the foundation specification.')
desired = description.replace(old_bridge, new_bridge).replace(old_obligation, new_obligation)
notice = ('## Verified completion - 15 October 2026\n\n'
          'The original exact goal `EndStatement.ThreeSum.SolvedInTime 1.960614` is '
          '**Proved** on Prove2Me. All seven original milestones are complete. The '
          'complete machine extension has 481 accepted theorem proofs and reuses '
          '110 proved theorem nodes; its accepted dependencies connect to the original '
          'main reduction. The independent fixed-model lower bound remains separate '
          'from the algorithm proof. Scientific priority and global optimality are '
          'not asserted by these formal verification results.\n\n')
if not desired.startswith('## Verified completion - 15 October 2026'):
    desired = notice + desired
assert old_bridge not in desired and old_obligation not in desired
milestone = next(r for r in milestones_before['milestones'] if r['id'] == MILESTONE)
assert milestone['theorem']['id'] == BRIDGE
title = milestone['title'].replace('outstanding algorithmic extension — ', '')
intent = {'requested_at_utc': datetime.now(timezone.utc).isoformat(),
          'mission_id': MISSION, 'main_theorem_id': MAIN,
          'description_before_sha256': hashlib.sha256(description.encode()).hexdigest(),
          'mission_payload': {'description': desired},
          'milestone_id': MILESTONE, 'milestone_payload': {'title': title},
          'changes_formal_targets_or_links': False}
save('mission-completion-metadata-before.json', before)
save('mission-completion-metadata-intent.json', intent)
if desired != description:
    save('mission-completion-description-response.json',
         api('PATCH', '/missions/' + MISSION, {'description': desired}))
if title != milestone['title']:
    save('mission-completion-milestone-response.json',
         api('PATCH', '/milestones/' + MILESTONE, {'title': title}))
after = read_mission()
milestones_after = api('GET', milestones_path)
assert after['description'] == desired
for key in ('name', 'mission_type', 'campaign_id', 'campaign'):
    assert before.get(key) == after.get(key), key
assert before['main_theorem']['theorem_id'] == after['main_theorem']['theorem_id'] == MAIN
assert {r['id']: r['theorem']['id'] for r in milestones_before['milestones']} == {
    r['id']: r['theorem']['id'] for r in milestones_after['milestones']}
assert all(r['completed'] and r['theorem']['status'] == 'Proved'
           for r in milestones_after['milestones'])
assert next(r for r in milestones_after['milestones'] if r['id'] == MILESTONE)['title'] == title
save('mission-completion-metadata-after.json', after)
save('mission-live-milestones.json', milestones_after)
save('mission-completion-metadata-validation.json', {
    'verified_at_utc': datetime.now(timezone.utc).isoformat(), 'mission_id': MISSION,
    'live_description_matches': True, 'all_seven_original_milestones_complete': True,
    'formal_targets_and_links_unchanged': True,
    'description_after_sha256': hashlib.sha256(desired.encode()).hexdigest()})
print('Verified completed mission description and original milestone links.', flush=True)
