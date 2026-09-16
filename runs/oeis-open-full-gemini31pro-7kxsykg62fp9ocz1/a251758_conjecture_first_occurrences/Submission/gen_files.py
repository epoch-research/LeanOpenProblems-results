import os
import math

def min_fac(n):
    if n % 2 == 0: return 2
    if n % 3 == 0: return 3
    if n % 5 == 0: return 5
    if n % 7 == 0: return 7
    if n % 11 == 0: return 11
    if n % 13 == 0: return 13
    for i in range(17, int(math.isqrt(n)) + 1, 2):
        if n % i == 0: return i
    return n

c3 = []
for n in range(17, 6678672, 2):
    if n % 3 == 0 or n % 5 == 0 or n % 7 == 0 or n % 11 == 0 or n % 13 == 0: continue
    c = 0
    temp = n
    d = 17
    while d * d <= temp:
        while (temp % d) == 0:
            c += 1
            temp //= d
        d += 2
    if temp > 1:
        c += 1
    if c >= 3:
        c3.append(n)

print(len(c3))

chunk_size = 5000
chunks = [c3[i:i + chunk_size] for i in range(0, len(c3), chunk_size)]

for idx, chunk in enumerate(chunks):
    lean_code = f"""import Mathlib

def a_fast_loop (n d fuel : ℕ) (last_d : ℕ) (sum_lower sum_upper : ℕ) : ℕ × ℕ :=
  match fuel with
  | 0 => (sum_lower, sum_upper)
  | f + 1 =>
    if d * d > n then
      (sum_lower + last_d * (n / last_d), sum_upper)
    else if n % d == 0 then
      if d * d == n then
        (sum_lower + last_d * d, sum_upper + d * (n / last_d))
      else
        a_fast_loop n (d + 2) f d (sum_lower + last_d * d) (sum_upper + (n / d) * (n / last_d))
    else
      a_fast_loop n (d + 2) f last_d sum_lower sum_upper

def a_fast4 (n : ℕ) : ℕ :=
  let (s1, s2) := a_fast_loop n 17 (n/2+2) 1 0 0
  let s := s1 + s2
  if s == 0 then 0 else n ^ 2 / s

def check_list : List ℕ → Bool
| [] => true
| (x :: xs) => a_fast4 x != 14 && check_list xs

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

def my_cands : List ℕ := {chunk}
theorem check_cands_{idx} : check_list my_cands = true := by decide
"""
    with open(f"/workspace/leanproject/Submission/CheckChunk{idx}.lean", "w") as f:
        f.write(lean_code)
        
