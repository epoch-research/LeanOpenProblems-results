import FormalConjecturesUtil

/-!
# Erdős Problem 952

*References:*
- [erdosproblems.com/952](https://www.erdosproblems.com/952)
- [Wikipedia](https://wikipedia.org/wiki/Gaussian_moat)
-/

namespace Erdos952

/--
Is there an infinite sequence of distinct Gaussian primes $x_1,x_2,\ldots$
such that $\lvert x_{n+1}-x_n\rvert \ll 1$?
-/
theorem erdos_952 : 
  ∃ (x : ℕ → GaussianInt) (C : ℤ),
    Function.Injective x ∧
      ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C := by
  sorry

end Erdos952
