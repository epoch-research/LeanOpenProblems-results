import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 100000

open Nat

def x_seq_tail (n : ℕ) : ℕ :=
  let rec loop : ℕ → ℕ → ℕ
    | 0, acc => acc
    | i + 1, acc => 
      if i + 1 = 1 then acc
      else loop i (2 * acc + Nat.lcm acc (i + 1))
  if n = 0 then 0 else loop (n - 1) 1

lemma dvd_109 : 109 ∣ x_seq_tail (109^2 - 1) := by decide
