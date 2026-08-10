import os
import concurrent.futures

corpus_dir = "/corpus/src"

def search_file(filepath):
    try:
        with open(filepath, 'r', encoding='utf-8', errors='ignore') as f:
            content = f.read()
            if "sqrt{n+p}" in content or "sqrt{n-p}" in content or "sqrt{n + p}" in content or "sqrt{n - p}" in content:
                return filepath
    except Exception:
        pass
    return None

def main():
    filepaths = []
    for root, dirs, files in os.walk(corpus_dir):
        for file in files:
            if file.endswith('.tex'):
                filepaths.append(os.path.join(root, file))
    
    print(f"Total tex files to search: {len(filepaths)}")
    
    results = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=32) as executor:
        for res in executor.map(search_file, filepaths, chunksize=500):
            if res:
                print(f"Found match: {res}")
                results.append(res)
                
    print(f"Search completed. Found {len(results)} matches.")

if __name__ == '__main__':
    main()
