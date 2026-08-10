import FormalConjectures.Util.ProblemImports
open Nat BigOperators Polynomial
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))

-- The algebra map from ℚ[X] to Padic 3 by evaluation at xi_3 exists.
noncomputable instance : Algebra (Polynomial ℚ) (Padic 3) := (Polynomial.aeval xi_3).toRingHom.toAlgebra

example : IsAlgebraic (Polynomial ℚ) xi_3 := by
  -- xi_3 is algebraic over ℚ[X] with the evaluation algebra structure: root of X - C X.
  refine ⟨Polynomial.X - Polynomial.C Polynomial.X, ?_, ?_⟩
  · intro h
    have hc := congrArg Polynomial.natDegree h
    simp at hc
  · simp [Polynomial.aeval_X]

example : IsAlgebraic ℚ xi_3 := by
  -- Try all scalar restriction suggestions.
  have hPX : IsAlgebraic (Polynomial ℚ) xi_3 := by
    refine ⟨Polynomial.X - Polynomial.C Polynomial.X, ?_, ?_⟩
    · intro h
      have hc := congrArg Polynomial.natDegree h
      simp at hc
    · simp [Polynomial.aeval_X]
  apply?
