import FormalConjecturesUtil

/-!
# Erdős Problem 376

*Reference:* [erdosproblems.com/376](https://www.erdosproblems.com/376)
-/

namespace Erdos376

/--
Are there infinitely many $n$ such that ${2n\choose n}$ is coprime to $105$?
-/
theorem erdos_376 : { (n : ℕ) | n.centralBinom.Coprime 105 }.Infinite := by
  sorry

end Erdos376

theorem Erdos376.erdos_376.disproof : ¬ (type_of% @Erdos376.erdos_376) := sorry
