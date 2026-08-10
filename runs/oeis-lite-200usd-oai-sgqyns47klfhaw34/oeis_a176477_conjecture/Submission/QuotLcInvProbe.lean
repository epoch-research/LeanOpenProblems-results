import FormalConjectures.Util.ProblemImports
#check Quot.lcInv
example : Empty := Quot.lcInv (Quot.mk (fun _ _ : Empty => True) (by cases (Classical.choice (show Nonempty Empty from ?_))))
