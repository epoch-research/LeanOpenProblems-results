import FormalConjectures.Util.ProblemImports

open Nat Finset Set BigOperators

/--
$P_k$ is the product of the first $k$ primes.
-/
noncomputable def prod_first_k_primes (k : ℕ) : ℕ :=
  (range k).prod (fun i => Nat.nth Nat.Prime i)

/--
A210186: $a(n) = \text{least integer } m>1 \text{ such that } m \text{ divides none of } P_i + P_j$
with $0<i<j \le n$ where $P_k$ is the product of the first $k$ primes.
-/
noncomputable def A210186 (n : ℕ) : ℕ :=
  sInf { m : ℕ |
    1 < m ∧
    ∀ i j : ℕ,
      (1 ≤ i ∧ i < j ∧ j ≤ n) →
      ¬ (m ∣ (prod_first_k_primes i + prod_first_k_primes j)) }


/--
A210186 Conjecture: all the terms are primes and a(n) < n^2 for all n > 1.
- $\forall n : \mathbb{N}, \text{Prime } (A210186(n))$
- $\forall n : \mathbb{N}, n > 1 \implies A210186(n) < n^2$
-/
theorem oeis_210186_conjecture :
  (∀ n : ℕ, Nat.Prime (A210186 n)) ∧ (∀ n : ℕ, 1 < n → A210186 n < n^2) := by
  sorry
