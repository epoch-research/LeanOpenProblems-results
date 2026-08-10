import FormalConjectures.Util.ProblemImports

#check Std.Do.SPred.Tactic.ProofMode.start_entails
#check Std.Do.SPred.Tactic.PropAsSPredTautology
#synth Std.Do.SPred.Tactic.PropAsSPredTautology False ?m
example : False := by
  fail_if_success exact Std.Do.SPred.Tactic.ProofMode.start_entails (P := ?_) (φ := False) ?_
  sorry
