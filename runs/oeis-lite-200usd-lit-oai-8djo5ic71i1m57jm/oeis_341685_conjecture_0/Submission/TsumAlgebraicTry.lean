import FormalConjectures.Util.ProblemImports
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3_local : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
open Algebra
set_option maxHeartbeats 400000

example (k : ℕ) : IsAlgebraic ℚ ((Nat.factorial k : ℕ) : Padic 3) := by exact isAlgebraic_nat _

example : IsAlgebraic ℚ xi_3_local := by
  unfold xi_3_local
  first
  | exact isAlgebraic_tsum (fun k : ℕ => ((Nat.factorial k : ℕ) : Padic 3)) (fun k => by exact isAlgebraic_nat _)
  | apply IsAlgebraic.tsum
  | apply Algebra.IsAlgebraic.tsum
  | aesop
