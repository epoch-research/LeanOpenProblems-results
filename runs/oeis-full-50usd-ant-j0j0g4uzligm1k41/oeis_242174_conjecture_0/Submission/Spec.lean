import FormalConjectures.Util.ProblemImports

open Finset Nat

open scoped Classical

/--
A005260(n): The Franel numbers of order 4, $\sum_{k=0}^n \binom{n}{k}^4$.
-/
def A005260 (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), (n.choose k) ^ 4

/--
A242174: Least prime divisor of A005260(n) which does not divide any previous term A005260(k) with k < n, or 1 if such a primitive prime divisor of A005260(n) does not exist.
-/
noncomputable def A242174 (n : ℕ) : ℕ :=
  let B := A005260
  (B n).primeFactors.filter (fun p =>
    -- Primitive condition: p does not divide B(k) for all k in {1, 2, ..., n-1}
    ∀ k ∈ Finset.Ico 1 n, ¬ (p ∣ B k)
  ) |>.min.getD 1

/--
The Franel numbers of order r, $f_r(n) = \sum_{k=0}^n \binom{n}{k}^r$.
-/
def franel_r (r n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), (n.choose k) ^ r

/--
A generalization of A242174 for Franel numbers of order r:
Least prime divisor of $f_r(n)$ which does not divide any previous term $f_r(k)$ with $k < n$,
or 1 if such a primitive prime divisor of $f_r(n)$ does not exist.
-/
noncomputable def A_franel_r (r n : ℕ) : ℕ :=
  let B := franel_r r
  (B n).primeFactors.filter (fun p =>
    -- Primitive condition: p does not divide B(k) for all k in {1, 2, ..., n-1}
    ∀ k ∈ Finset.Ico 1 n, ¬ (p ∣ B k)
  ) |>.min.getD 1

/--
Auxiliary reduction lemma: for a finite set `t` of primes (i.e. `t ⊆ m.primeFactors`)
that is nonempty, the value `t.min.getD 1` is a prime.  This captures the observation
that `A242174 n` (and `A_franel_r r n`) is *automatically* prime whenever the set of
primitive prime divisors is nonempty, so the entire content of the conjecture is the
nonemptiness (existence of a primitive prime divisor).
-/
theorem minGetD_prime (t : Finset ℕ) (m : ℕ) (hsub : t ⊆ m.primeFactors)
    (hne : t.Nonempty) : (t.min.getD 1).Prime := by
  have h1 : t.min.getD 1 = t.min' hne := by
    have := Finset.coe_min' hne
    rw [← this]; rfl
  rw [h1]
  exact Nat.prime_of_mem_primeFactors (hsub (t.min'_mem hne))

/--
Conjecture: $a(n)$ is prime for any $n > 0$. In general, for any $r > 2$, if $n$ is large enough
then $f_r(n) = \sum_{k=0..n}C(n,k)^r$ has a prime divisor which does not divide any previous terms
$f_r(k)$ with $k < n$.
-/
theorem oeis_242174_conjecture_0 :
  (∀ n : ℕ, 0 < n → (A242174 n).Prime) ∧
  (∀ r : ℕ, 2 < r → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → A_franel_r r n ≠ 1) := by
  refine ⟨fun n hn => ?_, ?_⟩
  · -- First conjunct: `A242174 n` is prime for every `n > 0`.
    --
    -- By `minGetD_prime`, this reduces exactly to the statement that the set of
    -- *primitive* prime divisors of `A005260 n` is nonempty, i.e. that some prime
    -- dividing `A005260 n` divides no earlier term `A005260 k` (`1 ≤ k < n`).
    -- This is precisely Zhi-Wei Sun's conjecture (OEIS A242174), which is OPEN.
    unfold A242174
    refine minGetD_prime _ (A005260 n) ?_ ?_
    · convert Finset.filter_subset
        (fun p => ∀ k ∈ Finset.Ico 1 n, ¬ (p ∣ A005260 k)) (A005260 n).primeFactors using 2
    · -- OPEN: existence of a primitive prime divisor of the Franel number `A005260 n`.
      -- (Verified computationally for all `1 ≤ n ≤ 5000`, but no proof is known.)
      sorry
  · -- Second conjunct: for every `r > 2`, all sufficiently large Franel numbers of
    -- order `r` have a primitive prime divisor.  This is the general form of Sun's
    -- conjecture and is likewise OPEN.
    intro r hr
    sorry
