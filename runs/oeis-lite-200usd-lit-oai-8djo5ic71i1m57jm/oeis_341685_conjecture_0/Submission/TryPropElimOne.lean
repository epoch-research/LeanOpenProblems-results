import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
open Algebra
example : ¬ IsAlgebraic ℚ xi_3 := by
  classical
  apply split_by_characteristic_domain
  all_goals first | infer_instance | norm_num | omega | simp [Sat.Valuation.mk, Sat.Valuation.implies, Sat.Fmla.proof, Sat.Fmla.one, Sat.Fmla.and, Sat.Clause.nil, Sat.Clause.cons, Sat.Valuation.satisfies, Sat.Valuation.satisfies_fmla, Sat.Fmla.reify, Sat.Clause.reify, Sat.Literal.reify] | contradiction | trivial
