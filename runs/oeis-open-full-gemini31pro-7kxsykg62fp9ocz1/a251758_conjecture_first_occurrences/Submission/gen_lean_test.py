with open("/workspace/leanproject/Submission/candidates.txt") as f:
    cands = [int(x.strip()) for x in f.readlines()]

lean_code = """import Mathlib

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

"""

lean_code += f"def my_cands : List ℕ := {cands}\n"
lean_code += "theorem t1 : check_list my_cands = true := by decide\n"

with open("/workspace/leanproject/Submission/test_cands.lean", "w") as f:
    f.write(lean_code)
