import FormalConjectures.Util.ProblemImports

open Nat

-- Fast tail-recursive tribonacci
def trib_loop (n : ℕ) (a b c : ℕ) : ℕ :=
  match n with
  | 0 => a
  | 1 => b
  | 2 => c
  | n + 3 => trib_loop (n + 2) b c (a + b + c)

def tribonacci_fast (n : ℕ) : ℕ :=
  trib_loop n 0 0 1

-- Let us prove that tribonacci_fast is equal to tribonacci
-- Actually we do not even need to prove it, we can just use it inside find_counterexample
-- to see if there is any counterexample for the original tribonacci definition,
-- but wait, we want to evaluate original tribonacci.
-- Since original tribonacci is slow, we can just define a fast version for the check.
-- But wait, we want to check the original a(n).
-- So let us define original a(n) but using tribonacci_fast,
-- to check if there would be any counterexample.

def a_fast (n : ℕ) : ℕ :=
  let T := tribonacci_fast n
  if h : T ≤ 1 then
    0
  else
    let j_smsb : ℕ := T.log2 - 1
    if T.testBit j_smsb then 1 else 0

def is_maximal_run_fast (v : ℕ) (n L : ℕ) : Prop :=
  n ≥ 2 ∧ L ≥ 1 ∧
  (∀ i : ℕ, i < L → a_fast (n + i) = v) ∧
  (a_fast (n + L) ≠ v) ∧
  (a_fast (n - 1) ≠ v)

instance (v n L : ℕ) : Decidable (is_maximal_run_fast v n L) := by
  unfold is_maximal_run_fast
  infer_instance

def find_counterexample_fast (limit : ℕ) : Option (ℕ × ℕ × ℕ) :=
  (List.range limit).findSome? fun n =>
    if n < 2 then none
    else
      (List.range 20).findSome? fun l_idx =>
        let L := l_idx + 1
        if decide (is_maximal_run_fast 0 n L) && L ≠ 4 && L ≠ 5 then
          some (0, n, L)
        else if decide (is_maximal_run_fast 1 n L) && L ≠ 3 && L ≠ 4 then
          some (1, n, L)
        else
          none

#eval find_counterexample_fast 100




