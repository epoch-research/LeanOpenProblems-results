import FormalConjecturesUtil

/-!
# Erdős Problem 3

*Reference:* [erdosproblems.com/3](https://www.erdosproblems.com/3)
-/

namespace Erdos3

/--
If $A \subset \mathbb{N}$ has $\sum_{n \in A}\frac 1 n = \infty$, then must $A$ contain arbitrarily
long arithmetic progressions?
-/
theorem erdos_3 : ∀ A : Set ℕ,
    (¬ Summable fun a : A ↦ 1 / (a : ℝ)) →
    ∃ᶠ (k : ℕ) in Filter.atTop, ∃ S ⊆ A, S.IsAPOfLength k := by
  sorry

-- TODO(firsching): add the various known bounds as variants.

end Erdos3

theorem Erdos3.erdos_3.disproof : ¬ (type_of% @Erdos3.erdos_3) := sorry
