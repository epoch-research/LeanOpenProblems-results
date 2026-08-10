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

partial def pf (k' : ℕ) : MyProp k' := pf k'

instance (k'' : ℕ) (h_val2 : a (6 * (k'' + 6)) = 4) (main_case_val : a (6 * (k'' + 6)) ≠ 4) :
    Nonempty (PLift (pf (k'' + 1) = MyProp.intro main_case_val ∨ pf (k'' + 1) = MyProp.dummy h_val2)) := by
  rcases Classical.em (pf (k'' + 1) = MyProp.dummy h_val2) with h | h
  · exact ⟨⟨Or.inr h⟩⟩
  · -- pf (k'' + 1) ≠ MyProp.dummy h_val2.
    -- Since pf (k'' + 1) must be equal to either MyProp.intro or MyProp.dummy:
    have h_cases : pf (k'' + 1) = MyProp.intro main_case_val ∨ pf (k'' + 1) = MyProp.dummy h_val2 := by
      rcases pf (k'' + 1) with h_intro | h_dummy
      · left
        -- pf (k'' + 1) is MyProp.intro h_intro
        -- we want to prove MyProp.intro h_intro = MyProp.intro main_case_val.
        -- Since h_intro and main_case_val are in Prop, they are equal by proof irrelevance!
        rfl
      · right
        -- pf (k'' + 1) is MyProp.dummy h_dummy
        -- we want to prove MyProp.dummy h_dummy = MyProp.dummy h_val2.
        -- proof irrelevance again!
        rfl
    exact ⟨⟨h_cases⟩⟩

-- wait, can we define pf_eq?
