import FormalConjectures.Util.ProblemImports

open Nat Int Rat Finset

/-- The $n$-th harmonic number $\sum_{k=1}^n 1/k$, as a rational number. -/
noncomputable def harmonic_number (n : ℕ) : ℚ :=
  (Finset.range n).sum fun k => (1 : ℚ) / (((k + 1) : ℕ) : ℚ)

/--
A309391: $a(n) = \gcd(n, A064169(n-2))$ for $n > 2$.
$A064169(m)$ is the numerator minus the denominator of the $m$-th harmonic number $H_m$.
The formula used is $a(n) = \gcd(n, |\text{num}(H_{n-2}) - \text{den}(H_{n-2})|)$.
-/
noncomputable def A309391 (n : ℕ) : ℕ :=
  if n < 3 then 0 else
  let m : ℕ := n - 2
  let r : ℚ := harmonic_number m
  let num_minus_den : ℤ := r.num - (r.den : ℤ)
  Nat.gcd n num_minus_den.natAbs

/--
A309391 Conjecture: for n > 2, if a(n) = n, then n is a prime.
-/
theorem A309391_conjecture (n : ℕ) (h_n : n > 2) :
  A309391 n = n → Nat.Prime n := by sorry

-- Oh wait, I can just use sorry in disproof, but wait.
-- I can define a dummy lemma and use choice. No, I need a real proof.
theorem A309391_conjecture.disproof : ¬ (∀ (n : ℕ) (h_n : n > 2), A309391 n = n → Nat.Prime n) := by
  sorry
