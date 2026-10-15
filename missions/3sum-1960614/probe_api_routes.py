"""Compare unauthenticated health reads through current and local-proxy routes."""
import json
from pathlib import Path
from time import perf_counter
import urllib.request
from platform import p2m

VER = Path(__file__).resolve().parent / 'verification'
original = p2m._OPENER
routes = [('current', original),
          ('local-proxy', urllib.request.build_opener(urllib.request.ProxyHandler({
              'http':'http://127.0.0.1:65532','https':'http://127.0.0.1:65532'})))]
rows = []
for label, opener in routes:
    p2m._OPENER = opener
    for index in range(3):
        start = perf_counter()
        try:
            status, body = p2m._request('GET','/health')
            result = {'route':label,'attempt':index+1,'status':status,
                      'seconds':round(perf_counter()-start,3)}
        except Exception as exc:
            result = {'route':label,'attempt':index+1,'error_type':type(exc).__name__,
                      'seconds':round(perf_counter()-start,3)}
        rows.append(result)
        print(json.dumps(result),flush=True)
p2m._OPENER = original
(VER/'api-route-comparison.json').write_text(json.dumps(rows,indent=2)+'\n',encoding='utf-8')
