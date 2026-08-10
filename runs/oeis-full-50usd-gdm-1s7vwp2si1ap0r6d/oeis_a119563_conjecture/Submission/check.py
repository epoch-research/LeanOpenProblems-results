import sys
sys.set_int_max_str_digits(10000000)
from sage.all import *

for n in range(18):
    val = 2**(2**n) + 2**n - 1
    isp = is_prime(val)
    print(f"a({n}) (digits: {len(str(val))}): {isp}", flush=True)

