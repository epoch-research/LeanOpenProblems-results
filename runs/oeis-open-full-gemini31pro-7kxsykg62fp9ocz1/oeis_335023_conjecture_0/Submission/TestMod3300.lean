import Mathlib

def M : ℕ := 1194648
def P : ℕ := 1093^1092

def F_mod_loop (n : ℕ) (k : ℕ) (F : ℕ) (fact : ℕ) : ℕ × ℕ :=
  if k = 0 then (F, fact)
  else
    let sign := if (n - k + 1) % 2 == 0 then 1 else P - 1
    let fact' := (fact * (n - k + 1)) % P
    let F' := ((n - k + 1) * F + sign * fact') % P
    F_mod_loop n (k - 1) F' fact'
termination_by k

def test_loop (n : ℕ) : ℕ × ℕ := F_mod_loop n n 0 1

theorem F_mod_P : test_loop M = (0, 0) := by decide
