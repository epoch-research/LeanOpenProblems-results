import sympy
from multiprocessing import Pool
import sys

def check_range(args):
    start, end = args
    for n in range(start, end):
        phi = sympy.totient(n)
        limit = n**2 + 1 + phi
        p = sympy.nextprime(n**2)
        if p > limit:
            print(f"COUNTEREXAMPLE FOUND: n={n}, phi={phi}, a(n)={p - n**2}", flush=True)
            return n
    return None

def main():
    start_val = 1
    end_val = 40000000
    chunk_size = 200000
    ranges = []
    for i in range(start_val, end_val, chunk_size):
        ranges.append((i, min(i + chunk_size, end_val)))
    
    print(f"Starting search on 32 cores...", flush=True)
    count = 0
    with Pool(32) as p:
        for result in p.imap_unordered(check_range, ranges):
            count += 1
            if count % 10 == 0:
                print(f"Checked {count * chunk_size} values...", flush=True)
            if result is not None:
                print(f"Found counterexample: {result}", flush=True)
                p.terminate()
                sys.exit(0)
    print("No counterexamples found.", flush=True)

if __name__ == '__main__':
    main()
