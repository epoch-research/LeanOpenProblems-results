import urllib.request
import xml.etree.ElementTree as ET

url = 'http://export.arxiv.org/api/query?search_query=all:A115257&start=0&max_results=10'
try:
    response = urllib.request.urlopen(url)
    data = response.read()
    root = ET.fromstring(data)
    for entry in root.findall('{http://www.w3.org/2005/Atom}entry'):
        title = entry.find('{http://www.w3.org/2005/Atom}title').text
        summary = entry.find('{http://www.w3.org/2005/Atom}summary').text
        print("TITLE:", title)
        print("SUMMARY:", summary)
        print("---")
except Exception as e:
    print(e)
