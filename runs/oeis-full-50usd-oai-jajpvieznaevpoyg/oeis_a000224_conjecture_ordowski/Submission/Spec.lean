import FormalConjectures.Util.ProblemImports
open Finset

/--
A000224: Number of squares $\bmod n$.
This is the cardinality of the set $\{k^2 \bmod n \mid k \in \{0, 1, \dots, n-1\}\}$.
-/
noncomputable def A000224 (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    Finset.card ((Finset.range n).image (fun k : ℕ => k ^ 2 % n))

/--
Conjecture: n^2 == 1 (mod a(n)*(a(n)-1)) if and only if n is an odd prime.
-/
theorem oeis_a000224_conjecture_ordowski {n : ℕ} (h_n : 1 < n) :
    (n.Prime ∧ n ≠ 2) ↔ (n * n) ≡ 1 [MOD A000224 n * (A000224 n - 1)] := by
  sorry
