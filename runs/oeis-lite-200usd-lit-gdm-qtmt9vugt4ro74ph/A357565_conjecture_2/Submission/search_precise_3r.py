import os
import json

corpus_dir = '/corpus/src'

def main():
    sub_dirs = os.listdir(corpus_dir)
    print(f"Total directories to search: {len(sub_dirs)}")
    found = []
    count = 0
    for sd in sub_dirs:
        full_path = os.path.join(corpus_dir, sd)
        if os.path.isdir(full_path):
            for root, dirs, files in os.walk(full_path):
                for file in files:
                    if file.endswith('.tex'):
                        file_path = os.path.join(root, file)
                        try:
                            with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
                                content = f.read()
                                if '3r+3' in content or '3r + 3' in content:
                                    if 'binom' in content or 'choose' in content:
                                        print(f"Match: {file_path}")
                                        # print 5 lines around the match
                                        lines = content.split('\n')
                                        for i, l in enumerate(lines):
                                            if '3r+3' in l or '3r + 3' in l:
                                                start = max(0, i-5)
                                                end = min(len(lines), i+6)
                                                for j in range(start, end):
                                                    print(f"  {j}: {lines[j]}")
                                                count += 1
                        except Exception:
                            pass
    print(f"Total matches: {count}")

if __name__ == '__main__':
    main()
