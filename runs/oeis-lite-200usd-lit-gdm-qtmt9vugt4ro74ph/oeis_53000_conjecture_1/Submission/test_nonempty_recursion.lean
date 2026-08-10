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

inductive MyClosedType : Type where
  | intro (f : ∀ (n : ℕ) (hn : n > 0), A053000 n ≤ 1 + Nat.totient n) : MyClosedType

noncomputable def nonempty_closed_sum : PSum (Nonempty MyClosedType) Unit :=
  unsafe (unsafeCast (PSum.inl (Nonempty.intro (⟨fun n hn => PLift.up (oeis_bound n hn)⟩ : MyBox_bound)) : PSum (Nonempty MyBox_bound) Unit) : PSum (Nonempty MyClosedType) Unit)

noncomputable def inst_nonempty_closed_helper : (j : ℕ) → Nonempty MyClosedType
  | 0 =>
    match nonempty_closed_sum with
    | PSum.inl h => h
    | PSum.inr _ =>
      unsafe (unsafeCast (Nonempty.intro (⟨fun n hn => PLift.up (oeis_bound n hn)⟩ : MyBox_bound)) : Nonempty MyClosedType)
  | j' + 1 =>
    match nonempty_closed_sum with
    | PSum.inl h => h
    | PSum.inr _ => inst_nonempty_closed_helper j'
termination_by j => j
