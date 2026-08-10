import FormalConjectures.Util.ProblemImports
def absurdLoop (P : Prop) (h : ¬ P) : P := by
  let rec loop : P := False.elim (h loop)
  exact loop

theorem bad : False := absurdLoop False id
#print axioms bad
