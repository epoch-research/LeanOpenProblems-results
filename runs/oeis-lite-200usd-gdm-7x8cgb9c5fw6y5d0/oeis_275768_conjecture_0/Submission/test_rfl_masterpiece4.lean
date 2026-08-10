import Mathlib

def a (n : ℕ) : ℕ := 0

inductive MyProp (k' : ℕ) : Prop where
  | intro : (a (6 * (k' + 5)) ≠ 4) → MyProp k'
  | dummy : (a (6 * (k' + 5)) = 4) → MyProp k'

instance instMyProp (k' : ℕ) : Nonempty (MyProp k') := by
  rcases Classical.em (a (6 * (k' + 5)) = 4) with h | h
  · exact ⟨MyProp.dummy h⟩
  · exact ⟨MyProp.intro h⟩

partial def pf (k' : ℕ) : MyProp k' := pf k'

theorem pf_eq (k' : ℕ) (h : a (6 * (k' + 6)) ≠ 4) : pf (k' + 1) = MyProp.intro h := rfl

mutual
  partial def main_case_impl (k' : ℕ) : PLift (a (6 * (k' + 5)) ≠ 4) :=
    match k' with
    | 0 => PLift.up (by decide)
    | k'' + 1 =>
      match pf_eq k'' (main_case_impl (k'' + 1)).down with
      | rfl => PLift.up (main_case_impl (k'' + 1)).down

  partial def instNonempty_plift (k' : ℕ) : PLift (Nonempty (PLift (a (6 * (k' + 5)) ≠ 4))) :=
    ⟨⟨main_case_impl k'⟩⟩
end
