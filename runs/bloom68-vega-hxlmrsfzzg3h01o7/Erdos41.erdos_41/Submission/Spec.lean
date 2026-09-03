import FormalConjecturesUtil

/-!
# Erdős Problem 41

*Reference:* [erdosproblems.com/41](https://www.erdosproblems.com/41)
-/

open Filter Set

namespace Erdos41
variable {α : Type} [AddCommMonoid α]

/--
For a given set `A`, the n-tuple sums `a₁ + ... + aₙ` are all distinct for `a₁, ..., aₙ` in `A`
(aside from the trivial coincidences).
-/
def NtupleCondition (A : Set α) (n : ℕ) : Prop := ∀ (I : Finset α) (J : Finset α),
  ↑I ⊆ A ∧ ↑J ⊆ A ∧ I.card = n ∧ J.card = n ∧
  (∑ i ∈ I, i = ∑ j ∈ J, j) → I = J

/--
Let `A ⊆ ℕ` be an infinite set such that the triple sums `a + b + c` are all distinct for
`a, b, c` in `A` (aside from the trivial coincidences). Is it true that
`liminf n → ∞ |A ∩ {1, …, N}| / N^(1/3) = 0`?
-/
theorem erdos_41 (A : Set ℕ) (h_triple : NtupleCondition A 3) (h_infinite : A.Infinite) :
    Filter.atTop.liminf (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ)) = 0 := by
  sorry

end Erdos41

theorem Erdos41.erdos_41.disproof : ¬ (type_of% @Erdos41.erdos_41) := sorry
