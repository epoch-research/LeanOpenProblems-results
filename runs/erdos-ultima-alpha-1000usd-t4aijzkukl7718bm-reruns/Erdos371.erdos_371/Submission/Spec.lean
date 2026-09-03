import FormalConjecturesUtil

/-!
# Erdős Problem 371

*Reference:* [erdosproblems.com/371](https://www.erdosproblems.com/371)
-/

namespace Erdos371

/--
Let $P(n)$ denote the largest prime factor of $n$. Show that the set of $n$
with $P(n+1) > P(n)$ has density $\frac{1}{2}$.
-/
theorem erdos_371 :
    { n | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n }.HasDensity (1/2) := by
  sorry

-- TODO: add the statements from the additional material
end Erdos371
