import os

def search():
    targets = ['1742', '22252', '51940', '2389752', '1244']
    for root, dirs, files in os.walk('/corpus/src'):
        for file in files:
            if file.endswith('.tex'):
                path = os.path.join(root, file)
                try:
                    with open(path, 'r', encoding='utf-8', errors='ignore') as f:
                        content = f.read()
                    matches = [t for t in targets if t in content]
                    if len(matches) >= 2:
                        print(f"Match found in {path}: {matches}")
                except Exception:
                    pass

search()
