import FormalConjecturesUtil

/-!
# Erdős Problem 172

*Reference:* [erdosproblems.com/172](https://www.erdosproblems.com/172)
-/

namespace Erdos172

/--
Is it true that in any finite colouring of $\mathbb{N}$ there exist arbitrarily large finite $A$ such that all sums
and products of distinct elements in $A$ are the same colour?
-/
theorem erdos_172 : 
    ∀ (n : ℕ) (color : ℕ → Fin n) (m), ∃ (A : Finset ℕ), A.card ≥ m ∧ ∃ c, ∀ (S : Finset A),
    S.Nonempty → color (∑ x ∈ S, x) = c ∧ color (∏ x ∈ S, x) = c := by
  sorry

-- TODO: add the statements from the additional material
end Erdos172

theorem Erdos172.erdos_172.disproof : ¬ (type_of% @Erdos172.erdos_172) := sorry
