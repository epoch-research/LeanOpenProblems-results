import FormalConjecturesUtil

/-!
# Erdős Problem 1003

*Reference:* [erdosproblems.com/1003](https://www.erdosproblems.com/1003)
-/

namespace Erdos1003

open scoped Nat
open Filter

/--
Are there infinitely many solutions to $\phi(n) = \phi(n+1)$, where $\phi$ is the Euler totient
function?
-/
theorem erdos_1003 : Set.Infinite {n | φ n = φ (n + 1)} := by
  sorry

end Erdos1003

theorem Erdos1003.erdos_1003.disproof : ¬ (type_of% @Erdos1003.erdos_1003) := sorry
