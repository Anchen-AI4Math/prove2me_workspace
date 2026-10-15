"""Read only the precise public machine declarations needed by this port."""
from urllib.parse import quote
from platform import api,save

for key in ['Light.Meets.of_body','Light.Ends.whileBlock','Light.Ends.next',
            'APSPSource_ThreeSumApsp_Lang_Syntax','APSPSource_ThreeSumApsp_Lang_Logic']:
    data=api('GET','/theorems?q='+quote(key)+'&limit=30')
    save('machine-reuse-'+key.replace('.','_')+'.json',data)
    records=data.get('theorems',data.get('items',[]))
    print(key,[(x.get('theorem_name'),x.get('status'),x.get('theorem_id')) for x in records],flush=True)
