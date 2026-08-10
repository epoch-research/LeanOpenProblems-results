import FormalConjectures.Util.ProblemImports
open CategoryTheory CategoryTheory.Limits

noncomputable instance : HasZeroMorphisms PUnit where
  hasZero _ _ := ⟨0⟩

noncomputable instance : HasZeroObject PUnit where
  hasZero := ⟨⟨PUnit.unit, ⟨fun X => ⟨⟨⟩⟩, fun X => ⟨⟨⟩⟩⟩⟩⟩

example : ¬ Simple (0 : PUnit) := by
  intro h
  exact CategoryTheory.zero_not_simple PUnit

-- Try to see the failed obligation for `Simple`.
example : Simple (0 : PUnit) := by
  constructor
  intro Y f hf
  constructor
  · intro hi hf0
    simp at hf0
  · intro hne
    exfalso
    apply hne
    simp
