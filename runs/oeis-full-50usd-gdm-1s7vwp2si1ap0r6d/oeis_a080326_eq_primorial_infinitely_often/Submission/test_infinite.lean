import FormalConjectures.Util.ProblemImports

open ArithmeticFunction Finset Nat

example : moebius 6 = 1 := by
  have hcop : Coprime 2 3 := by decide
  have h6 : 6 = 2 * 3 := by decide
  rw [h6]
  rw [isMultiplicative_moebius.map_mul_of_coprime hcop]
  have h2 : moebius 2 = -1 := by exact moebius_apply_prime (by decide)
  have h3 : moebius 3 = -1 := by exact moebius_apply_prime (by decide)
  rw [h2, h3]
  decide
