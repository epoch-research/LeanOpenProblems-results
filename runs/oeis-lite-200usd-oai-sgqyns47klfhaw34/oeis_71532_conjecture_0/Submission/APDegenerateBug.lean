import FormalConjectures.Util.ProblemImports
open Set

#check Set.IsAPOfLengthWith.one
#check Set.IsAPOfLengthWith.zero
#check Set.IsAPOfLength.card
#print axioms Set.IsAPOfLengthWith.one

-- In PUnit additive monoid, {a + n*d | n<2} is singleton, so IsAPOfLengthWith 2 a 0 should be false by card.
example : False := by
  -- Try if simp proves a false AP with duplicate terms
  have h : Set.IsAPOfLengthWith ({PUnit.unit} : Set PUnit) 2 PUnit.unit PUnit.unit := by
    simp [Set.IsAPOfLengthWith]
  have hc := h.card
  simp at hc
