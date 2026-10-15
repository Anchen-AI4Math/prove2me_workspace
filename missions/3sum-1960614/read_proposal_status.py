"""Read the submitted mission proposal and verify its original campaign link."""
from platform import api,save
proposal=api('GET','/mission-proposals/561f5d71-28d6-4027-81f0-3fa01d5d7409')
save('proposal-current.json',proposal)
campaign=proposal.get('campaign_id') or proposal.get('campaign',{}).get('id')
assert campaign=='52073c33-5f7d-479b-b2db-238c6e280c9a'
print('Proposal:',proposal['status'],'campaign: 3sum-exponent',flush=True)
