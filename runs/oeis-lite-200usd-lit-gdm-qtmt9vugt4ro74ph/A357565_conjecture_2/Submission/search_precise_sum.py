import re

paths = [
    "/corpus/src/2104.10754/2104.10754.tex",
    "/corpus/src/2010.13638/2010.13638.tex",
    "/corpus/src/1909.13173/1909.13173.tex",
    "/corpus/src/1812.11659/1812.11659.tex",
    "/corpus/src/1802.04616/1802.04616.tex",
    "/corpus/src/1802.01944/1802.01944.tex",
    "/corpus/src/1608.06864/Supercongruences_v2.tex",
    "/corpus/src/1504.01976/1504.01976.tex",
    "/corpus/src/1401.0854/1401.0854.tex",
    "/corpus/src/1104.3659/1104.3659.tex",
    "/corpus/src/1703.04248/Period_map_v2.tex",
    "/corpus/src/1803.01830/1803.01830.tex",
    "/corpus/src/1803.07146/1803.07146.tex",
    "/corpus/src/1805.01254/qcong4.tex",
    "/corpus/src/1903.03766/1903.03766.tex",
    "/corpus/src/1910.00779/1910.00779.tex",
    "/corpus/src/1911.01790/1911.01790.tex",
    "/corpus/src/1912.00663/1912.00663.tex",
    "/corpus/src/2003.09888/2003.09888.tex",
    "/corpus/src/2011.02757/2011.02757.tex",
    "/corpus/src/2011.02762/2011.02762.tex",
    "/corpus/src/0805.2788/0805.2788.tex",
    "/corpus/src/2202.09781/2202.09781.tex"
]

for p in paths:
    try:
        with open(p, 'r', encoding='utf-8', errors='ignore') as f:
            content = f.read()
        if '3r+3' in content or '3r + 3' in content or '3' in content and '2' in content and 'sum' in content:
            # check for binom/choose with n+k-1
            if 'n+k-1' in content or 'n + k - 1' in content:
                print(f"Match: {p}")
                # Print around n+k-1
                for m in re.finditer(r'.{1,100}n\s*\+\s*k\s*-\s*1.{1,100}', content, re.DOTALL):
                    print(f"  {m.group(0).strip()}")
    except Exception as e:
        print(f"Error {p}: {e}")
