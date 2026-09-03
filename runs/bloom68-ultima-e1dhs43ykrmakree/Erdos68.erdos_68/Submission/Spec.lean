import FormalConjecturesUtil

/-!
# Erdős Problem 68

*Reference:* [erdosproblems.com/68](https://www.erdosproblems.com/68)
-/

namespace Erdos68

/--
Is
$$\sum_{n=2}^\infty \frac{1}{n!-1}$$
irrational?
-/
theorem erdos_68 :
    Irrational (∑' n : ℕ, 1 / ((n + 2).factorial - 1 : ℝ)) := by
  sorry

end Erdos68

theorem Erdos68.erdos_68.disproof : ¬ (type_of% @Erdos68.erdos_68) := sorry
