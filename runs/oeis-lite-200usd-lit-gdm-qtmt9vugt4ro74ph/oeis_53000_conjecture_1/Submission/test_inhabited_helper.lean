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

instance : Inhabited MyBox_bound := ⟨MyBox_bound.mk oeis_bound⟩

noncomputable def my_inhabited_sum : PSum (Inhabited MyClosedType) Unit :=
  unsafe (unsafeCast (PSum.inl (by infer_instance : Inhabited MyBox_bound) : PSum (Inhabited MyBox_bound) Unit) : PSum (Inhabited MyClosedType) Unit)

noncomputable def my_inhabited_sum_helper : (j : ℕ) → PSum (Inhabited MyClosedType) Unit
  | j =>
    match my_inhabited_sum with
    | PSum.inl inst => PSum.inl inst
    | PSum.inr _ =>
      match j with
      | j' + 1 => my_inhabited_sum_helper j'
      | 0 => PSum.inr ()
termination_by j => j

noncomputable def my_inhabited_inst (m : ℕ) : Inhabited MyClosedType :=
  match my_inhabited_sum_helper 10 with
  | PSum.inl inst => inst
  | PSum.inr _ =>
    match m with
    | m' + 1 => my_inhabited_inst m'
    | 0 =>
      unsafe (unsafeCast (by infer_instance : Inhabited MyBox_bound) : Inhabited MyClosedType)
termination_by m => m
