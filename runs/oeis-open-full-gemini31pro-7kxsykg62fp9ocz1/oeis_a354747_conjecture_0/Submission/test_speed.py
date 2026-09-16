import sys
import time
sys.set_int_max_str_digits(1000000)

t0 = time.time()
N = 2 * 100943 * 3**39101 - 1
a = 123456789
for i in range(60000):
    a = (a * a) % N
print("Time:", time.time() - t0)
