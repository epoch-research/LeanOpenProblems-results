import os
import re

def search():
    files = [
        "/corpus/src/math_0610281/math0610281.tex",
        "/corpus/src/math_0605320/Kreweras.tex",
        "/corpus/src/2010.13638/2010.13638.tex",
        "/corpus/src/1804.02648/1804.02648.tex",
        "/corpus/src/1804.00978/SISFredkin1.tex",
        "/corpus/src/1802.01260/1802.01260.tex",
        "/corpus/src/1604.06062/1604.06062.tex",
        "/corpus/src/1601.05701/1601.05701.tex",
        "/corpus/src/1212.2950/enumer_top_arxiv_v3.tex",
        "/corpus/src/1209.5709/1209.5709.tex",
        "/corpus/src/1209.3493/SpectraRevised.tex",
        "/corpus/src/1104.3659/1104.3659.tex",
        "/corpus/src/1105.0178/1105.0178.tex",
        "/corpus/src/1512.08215/1512.08215.tex",
        "/corpus/src/1906.01812/4-partite-turan_final.tex",
        "/corpus/src/2003.11664/ChebyshevFinal.tex",
        "/corpus/src/2012.12050/Manuscript.tex",
        "/corpus/src/2107.10347/2107.10347.tex",
        "/corpus/src/math_0507430/cytab04z-app.tex"
    ]
    for path in files:
        try:
            with open(path, "r", encoding="utf-8", errors="ignore") as f:
                content = f.read()
                if "A374605" in content or "374605" in content:
                    print(f"FOUND 374605 in {path}")
                # Search for squared binomial
                if "k}^2" in content or "k}^{2}" in content or "k)**2" in content:
                    print(f"FOUND squared binomial in {path}")
        except Exception as e:
            print(f"Error reading {path}: {e}")

if __name__ == "__main__":
    search()
