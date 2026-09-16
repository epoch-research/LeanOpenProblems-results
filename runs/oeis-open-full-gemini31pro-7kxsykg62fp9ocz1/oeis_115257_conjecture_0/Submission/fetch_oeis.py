import urllib.request
import json
import re

req = urllib.request.Request("https://oeis.org/search?q=A115257&fmt=json", headers={'User-Agent': 'Mozilla/5.0'})
try:
    response = urllib.request.urlopen(req)
    data = json.loads(response.read().decode('utf-8'))
    for result in data:
        print(f"ID: {result['id']}")
        for line in result.get('comments', []):
            if 'conjecture' in line.lower() or 'irreducible' in line.lower() or 'sun' in line.lower():
                print(line)
except Exception as e:
    print("Error:", e)
