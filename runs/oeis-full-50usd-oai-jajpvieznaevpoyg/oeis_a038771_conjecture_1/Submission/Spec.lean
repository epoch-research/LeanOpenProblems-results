import FormalConjectures.Util.ProblemImports

open Nat Finset Set
open Filter Topology Real

/--
$A038771(n)$ is the smallest composite number $c$ such that $A002110(n) + c$ is prime.
$A002110(n) = \prod_{i=1}^n p_i$ is the $n$-th primorial.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let Qn : ℕ := (range n).prod (nth Nat.Prime)
  let is_composite (c : ℕ) : Prop := c > 1 ∧ ¬ Nat.Prime c

  sInf { c : ℕ | is_composite c ∧ Nat.Prime (Qn + c) }

/--
Conjecture: $\liminf_{n\to\infty} \frac{A038771(n)}{\operatorname{prime}(n+1)^2} = 1$ and
$\limsup_{n\to\infty} \frac{A038771(n)}{\operatorname{prime}(n+1)^2} = 2$.
Here $\operatorname{prime}(n+1)$ is the $(n+1)$-th prime number.
In Mathlib's indexing, $\operatorname{prime}(n+1)$ corresponds to `Nat.nth Nat.Prime n`.
- Conjecture: lim inf_{n->oo} a(n)/prime(n+1)^2 = 1 < lim sup_{n->oo} a(n)/prime(n+1)^2 = 2. - Charles R Greathouse IV and Thomas Ordowski, Apr 24 2015
-/
theorem oeis_a038771_conjecture_1 :
  let p_next_sq (n : ℕ) : ℝ := (Nat.nth Nat.Prime n : ℝ) ^ 2
  let seq (n : ℕ) : ℝ := ((a n) : ℝ) / (p_next_sq n)
  (liminf seq atTop = 1) ∧ (limsup seq atTop = 2) := by
  sorry
