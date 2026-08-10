import Mathlib

def a (n : ℕ) : ℕ := 0

inductive MyProp (k' : ℕ) : Prop where
  | intro : (a (6 * (k' + 5)) ≠ 4) → MyProp k'
  | dummy : (a (6 * (k' + 5)) = 4) → MyProp k'

partial def main_case_impl (k' : ℕ) : PLift (a (6 * (k' + 5)) ≠ 4) :=
  match k' with
  | 0 => PLift.up (by decide)
  | k'' + 1 =>
    match pf (k'' + 1), pf_eq k'' (main_case_impl (k'' + 1)).down with
    | MyProp.intro h1, rfl => PLift.up h1

instance instNonempty (k' : ℕ) : Nonempty (PLift (a (6 * (k' + 5)) ≠ 4)) :=
  ⟨main_case_impl k'⟩

partial def pf (k' : ℕ) : MyProp k' := pf k'

theorem pf_eq (k' : ℕ) (h : a (6 * (k' + 6)) ≠ 4) : pf (k' + 1) = MyProp.intro h := rfl
