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
theorem oeis_a010846_granville_conjecture :
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (Real.log n) ^ (1 - ε) ≤ a n :=
by sorry

/-- For a prime `p`, the only `k ∈ [1, p]` with `primeFactors k ⊆ {p}` are `1` and `p`. -/
lemma a_prime {p : ℕ} (hp : p.Prime) : a p = 2 := by
  unfold a
  have h : (Icc 1 p).filter (fun k => primeFactors k ⊆ primeFactors p) = {1, p} := by
    ext k
    simp only [mem_filter, mem_Icc, mem_insert, mem_singleton, Nat.Prime.primeFactors hp]
    constructor
    · rintro ⟨⟨hk1, hkp⟩, hsub⟩
      by_cases hk : k = 1
      · left; exact hk
      · right
        obtain ⟨q, hq, hqk⟩ := Nat.exists_prime_and_dvd hk
        have hqmem : q ∈ k.primeFactors := by
          rw [Nat.mem_primeFactors]
          exact ⟨hq, hqk, by omega⟩
        have := hsub hqmem
        rw [mem_singleton] at this
        subst this
        exact Nat.le_antisymm hkp (Nat.le_of_dvd (by omega) hqk)
    · rintro (rfl | rfl)
      · simp [hp.one_lt.le]
      · refine ⟨⟨hp.one_lt.le, le_rfl⟩, ?_⟩
        rw [Nat.Prime.primeFactors hp]
  rw [h, card_pair]
  exact hp.one_lt.ne

theorem oeis_a010846_granville_conjecture.disproof : ¬ (type_of% @oeis_a010846_granville_conjecture) := by
  intro H
  obtain ⟨N, hN⟩ := H (1/2) (by norm_num)
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (max N 60)
  have h1 := hN p (le_trans (le_max_left _ _) hpN)
  rw [a_prime hp] at h1
  have hp60 : (60 : ℝ) ≤ p := by
    have := le_trans (le_max_right N 60) hpN
    exact_mod_cast this
  have hexp : Real.exp 4 < 55 := by
    have := Real.exp_one_lt_d9
    have h4 : Real.exp 4 = (Real.exp 1) ^ 4 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [h4]
    calc (Real.exp 1) ^ 4 < (2.7182818286 : ℝ) ^ 4 := by
          apply pow_lt_pow_left₀ this (Real.exp_pos 1).le (by norm_num)
      _ < 55 := by norm_num
  have hlog : 4 < Real.log p := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    linarith
  have hlogpos : 0 ≤ Real.log p := by linarith
  have h2 : (2 : ℝ) < (Real.log p) ^ ((1 : ℝ) - 1/2) := by
    have h42 : (4:ℝ) ^ ((1:ℝ)/2) = 2 := by
      rw [show (4:ℝ) = 2^(2:ℕ) by norm_num, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    have : (4:ℝ) ^ ((1:ℝ)/2) < (Real.log p) ^ ((1:ℝ)/2) :=
      Real.rpow_lt_rpow (by norm_num) hlog (by norm_num)
    rw [h42] at this
    convert this using 2
    norm_num
  push_cast at h1
  linarith
