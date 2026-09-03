import FormalConjecturesUtil

/-!
# Erdős Problem 39

*Reference:* [erdosproblems.com/39](https://www.erdosproblems.com/39)
-/

namespace Erdos39

open Filter

/--
Is there an infinite Sidon set $A\subset \mathbb{N}$ such that
$\lvert A\cap \{1\ldots,N\}\rvert \gg_\epsilon N^{1/2-\epsilon}$
for all $\varepsilon > 0$?
-/
theorem erdos_39 : ∃ (A : Set ℕ), A.Infinite ∧ IsSidon A ∧
    ∀ᵉ  (ε  > (0 : ℝ)),
    (· ^ (1 / 2 - ε) : ℕ → ℝ) =O[atTop] fun N => (((Set.Icc 1 N) ∩ A).ncard : ℝ) := by
  sorry

-- TODO(firsching): add the various known bounds as variants.

end Erdos39
