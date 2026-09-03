import FormalConjecturesUtil

/-!
# Erdős Problem 66

*Reference:* [erdosproblems.com/66](https://www.erdosproblems.com/66)
-/

namespace Erdos66

open Filter AdditiveCombinatorics
open scoped Topology

/--
Is there and $A \subset \mathbb{N}$ is such that
$$\lim_{n\to \infty}\frac{1_A\ast 1_A(n)}{\log n}$$
exists and is $\ne 0$?
-/
theorem erdos_66 : ∃ (A : Set ℕ) (c : ℝ), c ≠ 0 ∧
    Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c) := by
  sorry

-- TODO(firsching): add the theorems/conjectures for the comments on the page

end Erdos66
