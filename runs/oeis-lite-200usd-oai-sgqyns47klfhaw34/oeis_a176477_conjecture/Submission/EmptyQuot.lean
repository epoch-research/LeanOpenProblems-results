import FormalConjectures.Util.ProblemImports
#check inferInstanceAs (Nonempty (Quot (fun (x y : Empty) => True)))
example : False := by
  let q : Quot (fun (x y : Empty) => True) := Classical.choice (inferInstance : Nonempty (Quot (fun (x y : Empty) => True)))
  exact Quot.out q
