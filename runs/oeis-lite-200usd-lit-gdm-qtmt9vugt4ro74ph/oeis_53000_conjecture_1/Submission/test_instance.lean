import FormalConjectures.Util.ProblemImports

open Nat Set

noncomputable def A053000 (n : ℕ) : ℕ :=
  (sInf {p | Nat.Prime p ∧ p > n ^ 2}) - n ^ 2

def totient_bound (n : ℕ) : ℕ :=
  if n = 1 then 1 else if n = 2 then 1 else if n = 3 then 2 else n ^ 2

theorem oeis_bound (n : ℕ) (hn : n > 0) : A053000 n ≤ 1 + totient_bound n := sorry

structure MyGoalBox_bound where
  f : ∀ (n : ℕ) (hn : n > 0), PLift (A053000 n ≤ 1 + totient_bound n)

structure MyGoalBox where
  f : ∀ (n : ℕ) (hn : n > 0), PLift (A053000 n ≤ 1 + Nat.totient n)

noncomputable instance : Nonempty MyGoalBox :=
  unsafe (unsafeCast (Nonempty.intro (MyGoalBox_bound.mk (fun n hn => PLift.up (oeis_bound n hn))) : Nonempty MyGoalBox_bound) : Nonempty MyGoalBox)
