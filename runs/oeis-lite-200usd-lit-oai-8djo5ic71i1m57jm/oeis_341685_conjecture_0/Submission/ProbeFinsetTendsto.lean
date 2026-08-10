import FormalConjectures.Util.ProblemImports
open Filter
#check Finset.tendsto_card_atTop
example : False := by
  have h := Finset.tendsto_card_atTop (α := ℕ)
  -- true
  guard_target = False
  sorry
