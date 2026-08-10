import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
#check Std.Do.SPred.Tactic.ProofMode.start_entails
#check Std.Do.SPred.Tactic.PropAsSPredTautology
#check Std.Do.SPred.pure
#check Std.Do.SPred.entails
#synth Std.Do.SPred.Tactic.PropAsSPredTautology (IsAlgebraic ℚ xi_3) (Std.Do.SPred.pure True)
#synth Std.Do.SPred.Tactic.PropAsSPredTautology (IsAlgebraic ℚ xi_3) (Std.Do.SPred.pure (IsAlgebraic ℚ xi_3))
example : IsAlgebraic ℚ xi_3 := by
  refine Std.Do.SPred.Tactic.ProofMode.start_entails (P := Std.Do.SPred.pure True) ?_
  -- goal entails true?
  simp [Std.Do.SPred.entails]
