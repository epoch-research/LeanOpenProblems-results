import FormalConjectures.Util.ProblemImports
open scoped ENat

example : False := by
  have h := Set.isAPOfLength_pair (α := ℤ) (a := (0:ℤ)) (b := 1) (by norm_num)
  -- h : ({0,1}:Set ℤ).IsAPOfLength 2
  have hc := Set.IsAPOfLength.card h
  simp at hc
  guard_target = False
  sorry

example : False := by
  have h := Set.isAPOfLengthFree_one ({0} : Set ℕ)
  -- if not AP-free? no
  guard_target = False
  sorry
