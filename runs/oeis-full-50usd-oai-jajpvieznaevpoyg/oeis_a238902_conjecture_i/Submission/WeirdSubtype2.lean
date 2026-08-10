import FormalConjectures.Util.ProblemImports

partial def weird (P : Prop) (_ : Unit) : {b : Bool // b = true → P} :=
  ⟨true, by
    intro ht
    -- use recursive call only after proving its Boolean component is true from its equation theorem
    have hw : (weird P ()).1 = true := by
      -- cannot refer to weird.eq_def during definition? try recursive equation theorem not available
      sorry
    exact (weird P ()).2 hw⟩

#print weird
#print axioms weird
#check weird.eq_def
