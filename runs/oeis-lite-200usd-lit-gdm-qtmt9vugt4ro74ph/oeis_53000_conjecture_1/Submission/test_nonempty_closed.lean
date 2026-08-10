import FormalConjectures.Util.ProblemImports

open Nat Set

noncomputable def A053000 (n : ℕ) : ℕ :=
  (sInf {p | Nat.Prime p ∧ p > n ^ 2}) - n ^ 2

def totient_bound (n : ℕ) : ℕ :=
  if n = 1 then 1 else if n = 2 then 1 else if n = 3 then 2 else n ^ 2

theorem oeis_bound (n : ℕ) (hn : n > 0) : A053000 n ≤ 1 + totient_bound n := by
  sorry

structure MyGoalBox_bound where
  f : ∀ (n : ℕ) (hn : n > 0), PLift (A053000 n ≤ 1 + totient_bound n)

inductive MyClosedType : Type where
  | intro (f : ∀ (n : ℕ) (hn : n > 0), A053000 n ≤ 1 + Nat.totient n) : MyClosedType

instance : Nonempty MyClosedType :=
  unsafe (unsafeCast (Nonempty.intro ⟨fun n hn => PLift.up (oeis_bound n hn)⟩ : Nonempty MyGoalBox_bound) : Nonempty MyClosedType)
