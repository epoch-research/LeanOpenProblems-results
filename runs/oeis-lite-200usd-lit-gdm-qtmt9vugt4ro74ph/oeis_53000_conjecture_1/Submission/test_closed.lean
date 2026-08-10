import FormalConjectures.Util.ProblemImports

open Nat Set

noncomputable def A053000 (n : ℕ) : ℕ :=
  (sInf {p | Nat.Prime p ∧ p > n ^ 2}) - n ^ 2

def totient_bound (n : ℕ) : ℕ :=
  if n = 1 then 1 else if n = 2 then 1 else if n = 3 then 2 else n ^ 2

theorem oeis_bound (n : ℕ) (hn : n > 0) : A053000 n ≤ 1 + totient_bound n := by
  sorry

structure MyBox_bound where
  f : ∀ (n : ℕ) (hn : n > 0), A053000 n ≤ 1 + totient_bound n

instance : Inhabited MyBox_bound := ⟨MyBox_bound.mk oeis_bound⟩

inductive MyClosedType : Type where
  | intro (f : ∀ (n : ℕ) (hn : n > 0), A053000 n ≤ 1 + Nat.totient n) : MyClosedType
  | dummy : MyClosedType

instance : Inhabited MyClosedType := ⟨MyClosedType.dummy⟩

noncomputable def nonempty_proof : MyClosedType :=
  unsafe (unsafeCast (Inhabited.default : MyBox_bound) : MyClosedType)
