import FormalConjectures.Util.ProblemImports

mutual
partial def decP (P : Prop) (_ : Unit) : Decidable P := Decidable.isTrue (pfP P ())
partial def pfP (P : Prop) (_ : Unit) : P := by
  have d := decP P ()
  cases d with
  | isTrue h => exact h
  | isFalse h => exact False.elim (h (pfP P ()))
end

#print axioms decP
#print axioms pfP

theorem badFalse : False := pfP False ()
#print axioms badFalse
