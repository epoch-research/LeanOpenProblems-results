import FormalConjectures.Util.ProblemImports
open Set
#check Set.IsAPOfLengthWith.zero
#check Set.IsAPOfLengthWith.one
#check Set.IsAPOfLengthWith.two
#check Set.IsAPOfLengthWith.three
#check IsSidon.avoids_isAPOfLength_three

example : False := by
  have h := Set.IsAPOfLengthWith.two (s := ({0,1} : Set ℕ)) (a := 0) (d := 0)
  norm_num at h
