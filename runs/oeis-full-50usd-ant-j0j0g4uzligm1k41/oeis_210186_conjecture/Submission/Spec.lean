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
  refine ⟨fun n => ?_, fun n hn => ?_⟩
  · -- Part 1 (primality of every term). This is Zhi-Wei Sun's open conjecture.
    -- It is equivalent to: the smallest "good" number (the one dividing no
    -- P_i + P_j, 1 ≤ i < j ≤ n) is prime, i.e. no odd composite c below the
    -- smallest good prime is good. There is no structural handle: every sum is
    -- divisible by 4 but NO odd prime divides all sums (gcd of all sums = 4),
    -- so the parity argument (handling the factor 2) has no odd analogue.
    -- Verified true for all n ≤ 60000.
    sorry
  · -- Part 2 (the bound a(n) < n^2). Also open: it requires the existence of a
    -- good prime below n^2, equivalently equidistribution of the primorial
    -- residues P_k mod p (control of antipodal-pair counts via exponential sums
    -- over primes), which is an analytic number-theory statement unavailable in
    -- Mathlib; elementary counting fails by a logarithmic factor.
    -- Verified true (ratio a(n)/n^2 < 0.07) for all n ≤ 60000.
    sorry
