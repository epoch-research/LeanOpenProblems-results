import FormalConjectures.Util.ProblemImports

macro "theorem" id:ident binders:bracketedBinder* ":" type:term ":=" "by" "sorry" : command =>
  `(opaque $id $binders* : $type)

theorem A273110_conjecture_test (n : ℕ) :
  (0 < n → 0 < n) := by sorry

#print A273110_conjecture_test
#print axioms A273110_conjecture_test
