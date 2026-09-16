import urllib.request
import json
url = "https://oeis.org/search?q=A071524&fmt=json"
req = urllib.request.urlopen(url)
res = json.loads(req.read())
print(res[0]['data'])
if 'comment' in res[0]:
    for c in res[0]['comment']: print(c)
