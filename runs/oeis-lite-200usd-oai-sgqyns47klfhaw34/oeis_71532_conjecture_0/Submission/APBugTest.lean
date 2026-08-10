import FormalConjectures.Util.ProblemImports
open Set
#check Set.IsAPOfLengthFree.maxCard_zero
#check Set.IsAPOfLengthFree.maxCard_one
#print axioms Set.IsAPOfLengthFree.maxCard_zero
#print axioms Set.IsAPOfLengthFree.maxCard_one
example : False := by
  have h := Set.IsAPOfLengthFree.maxCard_zero 0
  norm_num [Set.IsAPOfLengthFree.maxCard] at h
