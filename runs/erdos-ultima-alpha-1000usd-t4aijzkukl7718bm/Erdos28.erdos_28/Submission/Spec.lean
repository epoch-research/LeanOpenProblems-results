import FormalConjecturesUtil

/-!
# Erdős Problem 28

*Reference:* [erdosproblems.com/28](https://www.erdosproblems.com/28)
-/

open Filter Set AdditiveCombinatorics
open scoped Pointwise

namespace Erdos28

/--
If $A ⊆ \mathbb{N}$ is such that $A + A$ contains all but finitely many integers then
 $\limsup 1_A ∗ 1_A(n) = \infty$.
-/
theorem erdos_28 (A : Set ℕ) (h : (A + A)ᶜ.Finite) :
    limsup (fun (n : ℕ) => (sumRep A n : ℕ∞)) atTop = (⊤ : ℕ∞) := by
  sorry

-- TODO(firsching): add the theorems/conjectures for the comments on the page

end Erdos28
