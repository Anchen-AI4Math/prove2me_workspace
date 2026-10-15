"""Read public frontend assets for the graph API's actual query parameters.

No API credential or authenticated header is used for these public GETs.
"""
import json
from pathlib import Path
import re
from urllib.parse import urljoin, urlparse
import urllib.request

OUT = Path(__file__).resolve().parent / 'verification' / 'graph-client-readback'
OUT.mkdir(exist_ok=True)
base = 'https://prove2.me'
opener = urllib.request.build_opener()


def fetch(url):
    assert urlparse(url).netloc == 'prove2.me'
    with opener.open(url, timeout=45) as response:
        return response.read().decode('utf-8')


html = fetch(base + '/')
(OUT / 'index.html').write_text(html, encoding='utf-8')
assets = re.findall(r'<script[^>]+src="([^"]+)"', html)
print('Public script assets:', len(assets), flush=True)
hits = []
for index, asset in enumerate(assets):
    url = urljoin(base + '/', asset)
    if urlparse(url).netloc != 'prove2.me':
        continue
    source = fetch(url)
    (OUT / f'asset-{index:02}.js').write_text(source, encoding='utf-8')
    for marker in ('/graph', 'has_more_children', 'has_hidden_deprecated_sketches'):
        for match in list(re.finditer(re.escape(marker), source))[:10]:
            excerpt = source[max(0, match.start()-1000):match.end()+1500]
            hits.append({'url': url, 'marker': marker, 'excerpt': excerpt})
            print(marker, ascii(excerpt), flush=True)
(OUT / 'graph-api-excerpts.json').write_text(json.dumps(hits, indent=2) + '\n', encoding='utf-8')
