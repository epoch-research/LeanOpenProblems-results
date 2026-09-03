import FormalConjecturesUtil

/-!
# Erdős Problem 128

*Reference:* [erdosproblems.com/128](https://www.erdosproblems.com/128)
-/

variable {V : Type*} {G : SimpleGraph V} [Fintype V]

namespace Erdos128

/--
Let G be a graph with n vertices such that every induced subgraph on ≥ $n/2$
vertices has more than $n^2/50$ edges. Must G contain a triangle?
-/
theorem erdos_128 :
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      (∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
        50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2) → ¬ G.CliqueFree 3 := by
  sorry

end Erdos128

theorem Erdos128.erdos_128.disproof : ¬ (type_of% @Erdos128.erdos_128) := sorry
