import FormalConjectures.Util.ProblemImports
open MeasureTheory
#print MeasureTheory.IsProbabilityMeasure
#check MeasureTheory.nonempty_of_isProbabilityMeasure
#synth MeasurableSpace Empty
#check (0 : Measure Empty)
example : False := by
  letI : MeasureTheory.IsProbabilityMeasure (0 : Measure Empty) := by
    constructor
    simp
  have h : Nonempty Empty := MeasureTheory.nonempty_of_isProbabilityMeasure (0 : Measure Empty)
  exact h.elim (by intro x; cases x)
