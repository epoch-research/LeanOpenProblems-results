import FormalConjectures.Util.ProblemImports
open Classical
open SimpleGraph

-- Try deriving contradictions from custom graph coloring lemmas on empty/one-vertex graphs
example : True := by trivial

-- Check exact types
#check SimpleGraph.le_chromaticNumber_iff_not_colorable
#check SimpleGraph.chromaticNumber_bot
#check SimpleGraph.chromaticNumber_top
#check SimpleGraph.Colorable
#check Set.IsAPOfLengthFree.maxCard_zero
#check Set.IsAPOfLengthFree.maxCard_one

-- Some test goals (fail_if_success if theorem is safe)
example : ¬ ((⊥ : SimpleGraph (Fin 1)).IsCritical 2) := by
  exact SimpleGraph.not_isCritical_of_fintype_lt _ 2 (by norm_num)

