import Mathlib

def a (n : ℕ) : ℕ := 0

inductive MyType (k' : ℕ) : Type where
  | inl : Nonempty (a (6 * (k' + 5)) ≠ 4) → MyType k'
  | inr : (a (6 * (k' + 5)) = 4 → MyType k') → MyType k'

mutual
  partial def pf_inhabited (k' : ℕ) : Inhabited (MyType k') :=
    ⟨pf_inhabited_val k'⟩

  partial def pf_inhabited_val (k' : ℕ) : MyType k' :=
    pf_inhabited_val k'
end
