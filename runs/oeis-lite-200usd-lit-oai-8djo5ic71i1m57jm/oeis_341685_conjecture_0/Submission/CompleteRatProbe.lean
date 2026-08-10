import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
#check CauSeq.IsComplete
#synth CauSeq.IsComplete ℚ (padicNorm 3)
#check CauSeq.Completion.complete
#check CauSeq.Completion.equiv_lim
#check CauSeq.Completion.lim

example (x : Padic 3) : ∃ q : ℚ, (q : Padic 3) = x := by
  induction x using Quot.inductionOn with
  | h f =>
    -- if ℚ were complete this would be easy
    apply?
