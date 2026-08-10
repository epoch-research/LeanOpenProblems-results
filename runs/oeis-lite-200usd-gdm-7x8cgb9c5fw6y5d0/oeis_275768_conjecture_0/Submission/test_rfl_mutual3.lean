import Mathlib

def a (n : ℕ) : ℕ := 0

inductive MyProp (k' : ℕ) : Prop where
  | intro : (a (6 * (k' + 5)) ≠ 4) → MyProp k'
  | dummy : (a (6 * (k' + 5)) = 4) → MyProp k'

instance (k' : ℕ) : Nonempty (MyProp k') := by
  rcases Classical.em (a (6 * (k' + 5)) = 4) with h | h
  · exact ⟨MyProp.dummy h⟩
  · exact ⟨MyProp.intro h⟩

partial def pf (k' : ℕ) : MyProp k' := pf k'

mutual
  def main_case (k' : ℕ) : PLift (a (6 * (k' + 5)) ≠ 4) :=
    match k' with
    | 0 => PLift.up (by decide)
    | k'' + 1 =>
      match pf (k'' + 1), (pf_eq k'').down with
      | MyProp.intro h1, rfl => PLift.up h1

  def pf_eq (k'' : ℕ) : PLift (pf (k'' + 1) = MyProp.intro (main_case (k'' + 1)).down) :=
    PLift.up rfl
end
