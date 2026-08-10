import FormalConjectures.Util.ProblemImports

#check Homeomorph.OfDiscrete
#check IsHomeomorph.equiv_of_discreteTopology
#print axioms IsHomeomorph.equiv_of_discreteTopology

-- If it gives equivalence between PUnit and Empty, contradiction?
example : False := by
  let f : PUnit → Empty := fun x => by cases x; exact (by contradiction)
  have hf : IsHomeomorph f := by
    -- impossible due no function really
    exact? 
  exact (hf.equiv_of_discreteTopology).toFun PUnit.unit
