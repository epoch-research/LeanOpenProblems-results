import urllib.request
import urllib.parse
import json

url = 'http://export.arxiv.org/api/query?search_query=all:A071524&start=0&max_results=5'
try:
    response = urllib.request.urlopen(url)
    data = response.read().decode('utf-8')
    print(data)
except Exception as e:
    print(e)
