import urllib.request
import json
url = "https://oeis.org/search?q=A046969&fmt=json"
req = urllib.request.Request(url, headers={'User-Agent': 'Mozilla/5.0'})
try:
    with urllib.request.urlopen(req) as response:
        data = json.loads(response.read().decode())
        if data:
            print(data[0]['data'])
            print(data[0].get('comments', []))
except Exception as e:
    print(e)
