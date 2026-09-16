import FormalConjectures.Util.ProblemImports

open Nat Finset

def A331343 (n : ℕ) : ℕ :=
  let L : ℕ := (Ico 1 (n + 1)).lcm id
  (Ico 1 (n + 1)).sum fun k : ℕ ↦ (L / k) * (2 ^ (k - 1) - 1)

def a (n : ℕ) : ℕ := A331343 n

#eval (List.range 100).filter (fun n => n > 3 ∧ n^3 ∣ (a n) ∧ ¬ n.Prime)
