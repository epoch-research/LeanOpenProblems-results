import FormalConjectures.Util.ProblemImports

open Nat Finset

open scoped ArithmeticFunction

def g_fn : ArithmeticFunction ℤ :=
  ((ArithmeticFunction.id : ArithmeticFunction ℤ).pmul (ArithmeticFunction.sigma 0 : ArithmeticFunction ℤ)) * (ArithmeticFunction.zeta : ArithmeticFunction ℤ)

lemma g_fn_apply (n : ℕ) (hn : n > 0) : g_fn n = n.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ)) := by
  rw [g_fn]
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  apply sum_congr rfl
  intro d _
  rw [ArithmeticFunction.pmul_apply]
  simp [ArithmeticFunction.sigma_apply]

lemma isMultiplicative_g : g_fn.IsMultiplicative := by
  have h1 : ((ArithmeticFunction.id : ArithmeticFunction ℤ).pmul (ArithmeticFunction.sigma 0 : ArithmeticFunction ℤ)).IsMultiplicative := by
    apply ArithmeticFunction.IsMultiplicative.pmul
    · exact ArithmeticFunction.isMultiplicative_id.natCast (R := ℤ)
    · exact ArithmeticFunction.isMultiplicative_sigma.natCast (R := ℤ)
  exact ArithmeticFunction.IsMultiplicative.mul h1 (ArithmeticFunction.isMultiplicative_zeta.natCast (R := ℤ))
