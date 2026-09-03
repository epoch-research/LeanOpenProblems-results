import Submission.GeneratingExplore
open scoped Classical
#check Set.indicator
#print Set.indicator
#check Summable.congr
#check Function.mem_support
example (m : ℕ) [NeZero m] (f : ℕ → ℝ) (hf : Summable f) (z : ZMod m) :
    Summable (fun n : ℕ ↦ if (n : ZMod m) = z then f n else 0) := by
  have hh := hf.indicator {n : ℕ | (n : ZMod m) = z}
  convert hh using 1
  funext n
  simp only [Set.indicator_apply, Set.mem_setOf_eq]
