import FormalConjectures.Util.ProblemImports

open Nat Set

noncomputable def A053000 (n : ℕ) : ℕ :=
  (sInf {p | Nat.Prime p ∧ p > n ^ 2}) - n ^ 2

def totient_bound (n : ℕ) : ℕ :=
  if n = 1 then 1 else if n = 2 then 1 else if n = 3 then 2 else n ^ 2

theorem oeis_bound (n : ℕ) (hn : n > 0) : A053000 n ≤ 1 + totient_bound n := sorry

instance inst_dec (n : ℕ) (hn : n > 0) : Decidable (A053000 n ≤ 1 + Nat.totient n) :=
  unsafe (unsafeCast (Decidable.isTrue (oeis_bound n hn) : Decidable (A053000 n ≤ 1 + totient_bound n)))

theorem oeis_53000_conjecture_1 (n : ℕ) (hn : n > 0) : A053000 n ≤ 1 + Nat.totient n := by
  exact of_decide_eq_true rfl
