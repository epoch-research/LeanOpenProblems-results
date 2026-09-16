import numpy as np
import sys

def is_prime(n):
    if n < 2: return False
    if n in (2, 3): return True
    if n % 2 == 0 or n % 3 == 0: return False
    for i in range(5, int(n**0.5) + 1, 6):
        if n % i == 0 or n % (i+2) == 0: return False
    return True

for i in range(1, 10000):
    all_comp = True
    for j in range(1, i + 1): # we only check up to i, so for n=i, y goes up to n
        if is_prime(i**2 + j**2):
            all_comp = False
            break
    if all_comp:
        print(f"Row {i} is ALL ZEROS for n={i}!")
        sys.exit(0)

print("None found up to 10000.")
