import FormalConjectures.Util.ProblemImports
open SimpleGraph

#check SimpleGraph.lt_chromaticNumber_iff_not_colorable
#check SimpleGraph.le_chromaticNumber_iff_not_colorable
#check SimpleGraph.not_isCritical_of_fintype_lt
#check SimpleGraph.colorable_iff_induce_eq_bot

-- empty graph on PUnit chromaticNumber likely 1; test theorem at n=0/1
example : False := by
  have h := (SimpleGraph.lt_chromaticNumber_iff_not_colorable (G := (⊥ : SimpleGraph PUnit)) (n:=0))
  -- 0 < chromaticNumber iff not colorable 0; true
  norm_num

#print axioms SimpleGraph.lt_chromaticNumber_iff_not_colorable
