import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

inductive MyProp (k' : ℕ) : Type where
  | intro : (a (6 * (k' + 5)) ≠ 4) → MyProp k'
  | dummy : (a (6 * (k' + 5)) = 4) → MyProp k'

instance (k' : ℕ) : Nonempty (MyProp k') := by
  rcases Classical.em (a (6 * (k' + 5)) = 4) with h | h
  · exact ⟨MyProp.dummy h⟩
  · exact ⟨MyProp.intro h⟩

def pf (k' : ℕ) : MyProp k' :=
  if h : a (6 * (k' + 5)) = 4 then
    MyProp.dummy h
  else
    MyProp.intro h

structure MyEq (k'' : ℕ) : Type where
  val : a (6 * (k'' + 6)) ≠ 4
  eq : pf (k'' + 1) = MyProp.intro val

mutual
  def main_case (k' : ℕ) : PLift (a (6 * (k' + 5)) ≠ 4) :=
    match k' with
    | 0 => PLift.up (by decide)
    | k'' + 1 =>
      match h_val : pf (k'' + 1) with
      | MyProp.intro h1 => PLift.up h1
      | MyProp.dummy h2 =>
        have h_pf := (pf_eq k'').eq
        have h_contra : MyProp.dummy h2 = MyProp.intro (pf_eq k'').val := h_val.symm.trans h_pf
        nomatch h_contra

  def pf_eq (k'' : ℕ) : MyEq k'' := by
    have h_ne := (main_case (k'' + 1)).down
    have h_pf : pf (k'' + 1) = MyProp.intro h_ne := by
      unfold pf
      split
      · contradiction
      · rfl
    exact ⟨h_ne, h_pf⟩
end
