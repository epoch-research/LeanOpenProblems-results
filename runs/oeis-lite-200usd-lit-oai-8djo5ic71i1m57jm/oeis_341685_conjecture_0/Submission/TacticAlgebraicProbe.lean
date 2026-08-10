import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
open Algebra
example : IsAlgebraic ℚ (xi_3) := by
  unfold xi_3
  exact? 
example : ¬ IsAlgebraic ℚ (xi_3) := by
  unfold xi_3
  exact?
example : (tsum (fun k : ℕ => (Nat.factorial k : Padic 3))) = 0 := by
  exact?
example : ¬ Summable (fun k : ℕ => (Nat.factorial k : Padic 3)) := by
  exact?
example : Summable (fun k : ℕ => (Nat.factorial k : Padic 3)) := by
  exact?
