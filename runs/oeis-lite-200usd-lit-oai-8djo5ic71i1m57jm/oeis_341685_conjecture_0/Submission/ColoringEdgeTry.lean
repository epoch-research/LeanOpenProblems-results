import FormalConjectures.Util.ProblemImports
open SimpleGraph
#check SimpleGraph.le_chromaticNumber_iff_colorable
#check SimpleGraph.lt_chromaticNumber_iff_not_colorable
#check SimpleGraph.le_chromaticNumber_iff_not_colorable
example : False := by
  have h := SimpleGraph.lt_chromaticNumber_iff_not_colorable (G := (⊥ : SimpleGraph PUnit)) (n:=0)
  -- chromatic number of one isolated vertex? probably 1, not contradiction
  simp at h
example : False := by
  have h := SimpleGraph.le_chromaticNumber_iff_colorable (G := (⊥ : SimpleGraph Empty)) (n:=1)
  simp at h
