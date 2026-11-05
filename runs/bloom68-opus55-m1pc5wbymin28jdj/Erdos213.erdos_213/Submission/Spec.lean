import FormalConjecturesUtil

/-!
# Erdős Problem 213

*Reference:* [erdosproblems.com/213](https://www.erdosproblems.com/213)
-/

open EuclideanGeometry

namespace Erdos213

/--
The predicate (on $n$) that there exist $n$ points in $\mathbb{R}^2$,
no three on a line and no four on a circle,
such that all pairwise distances are integers.
-/
def Erdos213For (n : ℕ) : Prop := ∃ S : Set ℝ², S.Finite ∧ S.ncard = n ∧
    NonTrilinear S ∧
    (∀ Q : Set ℝ², Q ⊆ S ∧ Q.ncard = 4 → ¬ EuclideanGeometry.Cospherical Q) ∧
    (S.Pairwise fun p₁ p₂ => dist p₁ p₂ ∈ Set.range Int.cast)

/--
Let $n \geq 4$. Are there $n$ points in $\mathbb{R}^2$, no three on a line and no four on a circle,
such that all pairwise distances are integers?
-/
theorem erdos_213 : ∀ n : ℕ, n ≥ 4 → Erdos213For n := by sorry

end Erdos213

theorem Erdos213.erdos_213.disproof : ¬ (type_of% @Erdos213.erdos_213) := sorry
