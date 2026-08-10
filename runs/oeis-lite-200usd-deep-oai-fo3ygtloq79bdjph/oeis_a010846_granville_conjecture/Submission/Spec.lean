import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A010846: Number of numbers $\le n$ whose set of prime factors is a subset of the set of prime factors of $n$.
-/
def a (n : ℕ) : ℕ :=
  (Icc 1 n).filter (fun k => primeFactors k ⊆ primeFactors n) |>.card

/--
Granville's ABC-Conjecture implies that for any $\epsilon > 0$,
the function $a(n)$ is bounded below by $(\log n)^{1 - \epsilon}$ for sufficiently large $n$.
This is a formalization of a claim implied by the context:
OEIS C: "This function of n appears in an ABC-conjecture by Andrew Granville. See Goldfeld."
Granville (via Goldfeld) showed that ABC conjecture $\iff$ $\forall \epsilon > 0, \exists N, \forall n > N, a(n) \ge (\log n)^{1-\epsilon}$.
-/
private lemma a_prime_le_two {p : ℕ} (hp : Nat.Prime p) : a p ≤ 2 := by
  unfold a
  let s := (Icc 1 p).filter fun k => primeFactors k ⊆ primeFactors p
  have hs : s ⊆ ({1, p} : Finset ℕ) := by
    intro k hk
    change k ∈ (Icc 1 p).filter (fun k => primeFactors k ⊆ primeFactors p) at hk
    rw [Finset.mem_filter] at hk
    rcases hk with ⟨hkI, hksub⟩
    rw [Finset.mem_Icc] at hkI
    by_cases hk1 : k = 1
    · simp [hk1]
    · have hkpos : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hkI.1
      have hknz : k ≠ 0 := Nat.ne_of_gt hkpos
      rcases Nat.exists_prime_and_dvd hk1 with ⟨q, hqprime, hqdvd⟩
      have hqmemk : q ∈ primeFactors k := by
        rw [Nat.mem_primeFactors]
        exact ⟨hqprime, hqdvd, hknz⟩
      have hqmemp : q ∈ primeFactors p := hksub hqmemk
      have hqeqp : q = p := by
        simpa [hp.primeFactors] using hqmemp
      subst q
      have hple : p ≤ k := Nat.le_of_dvd hkpos hqdvd
      have hkp : k = p := le_antisymm hkI.2 hple
      simp [hkp]
  calc
    s.card ≤ ({1, p} : Finset ℕ).card := Finset.card_le_card hs
    _ = 2 := Finset.card_pair (by exact hp.ne_one.symm)

theorem oeis_a010846_granville_conjecture.disproof :
  ¬ (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (Real.log n) ^ (1 - ε) ≤ a n) := by
  intro h
  rcases exists_nat_gt (Real.exp 4) with ⟨M, hM⟩
  rcases h (1 / 2) (by norm_num) with ⟨N, hN⟩
  rcases Nat.exists_infinite_primes (max N M) with ⟨p, hpge, hpprime⟩
  have hNp : N ≤ p := le_trans (le_max_left N M) hpge
  have hMp : M ≤ p := le_trans (le_max_right N M) hpge
  have hlog : (4 : ℝ) < Real.log p := by
    rw [Real.lt_log_iff_exp_lt]
    exact lt_of_lt_of_le hM (by exact_mod_cast hMp)
    exact_mod_cast hpprime.pos
  have hpow : (4 : ℝ) ^ (1 - (1 / 2 : ℝ)) < (Real.log p) ^ (1 - (1 / 2 : ℝ)) :=
    Real.rpow_lt_rpow (by norm_num) hlog (by norm_num)
  norm_num at hpow
  have hmain := hN p hNp
  have hale : ((a p : ℕ) : ℝ) ≤ 2 := by
    exact_mod_cast a_prime_le_two hpprime
  linarith
