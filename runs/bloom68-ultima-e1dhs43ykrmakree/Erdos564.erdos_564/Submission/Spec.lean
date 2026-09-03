import FormalConjecturesUtil

/-!
# Erdős Problem 564

*Reference:* [erdosproblems.com/564](https://www.erdosproblems.com/564)
-/

namespace Erdos564

open Combinatorics Real Filter

/--
Let $R_3(n)$ be the minimal $m$ such that if the edges of the $3$-uniform hypergraph on $m$
vertices are $2$-coloured then there is a monochromatic copy of the complete $3$-uniform
hypergraph on $n$ vertices.

Is there some constant $c>0$ such that
$$ R_3(n) \geq 2^{2^{cn}}? $$
-/
theorem erdos_564 : 
    ∃ c > 0, ∀ᶠ n in atTop, (2 : ℝ)^(2 : ℝ)^(c * n) ≤ hypergraphRamsey 3 n := by
  sorry

end Erdos564

theorem Erdos564.erdos_564.disproof : ¬ (type_of% @Erdos564.erdos_564) := sorry
