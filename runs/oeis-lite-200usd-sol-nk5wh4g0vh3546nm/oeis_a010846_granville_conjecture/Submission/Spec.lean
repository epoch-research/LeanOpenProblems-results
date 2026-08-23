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
theorem oeis_a010846_granville_conjecture.disproof :
  ¬ (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    (Real.log n) ^ (1 - ε) ≤ a n) := by
  intro h
  obtain ⟨N, hN⟩ := h (1 / 2) (by norm_num)
  obtain ⟨m : ℕ, hm⟩ := exists_nat_gt (Real.exp 4)
  obtain ⟨p, hp_bound, hp⟩ := Nat.exists_infinite_primes (max N m)
  have hNp : N ≤ p := le_trans (le_max_left _ _) hp_bound
  have hmp : m ≤ p := le_trans (le_max_right _ _) hp_bound
  have hp_real : Real.exp 4 < (p : ℝ) := hm.trans_le (Nat.cast_le.2 hmp)
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlog : 4 < Real.log (p : ℝ) :=
    (Real.lt_log_iff_exp_lt hp_pos).2 hp_real
  have ha : a p = 2 := by
    rw [a]
    have hset : (Icc 1 p).filter (fun k => primeFactors k ⊆ primeFactors p) = {1, p} := by
      ext k
      simp only [mem_filter, mem_Icc, mem_insert, mem_singleton]
      constructor
      · rintro ⟨⟨hk1, hkp⟩, hkfac⟩
        by_cases hk : k = 1
        · exact Or.inl hk
        · right
          apply Nat.le_antisymm hkp
          obtain ⟨q, hq, hqk⟩ := Nat.exists_prime_and_dvd hk
          have hk0 : k ≠ 0 := by omega
          have hqmem : q ∈ primeFactors k :=
            Nat.mem_primeFactors.mpr ⟨hq, hqk, hk0⟩
          have hqmem' := hkfac hqmem
          rw [hp.primeFactors] at hqmem'
          have hqp : q = p := by simpa using hqmem'
          subst q
          exact Nat.le_of_dvd (by omega) hqk
      · rintro (rfl | rfl)
        · simp [hp.one_le]
        · simp [hp, hp.one_le]
    rw [hset]
    exact Finset.card_pair hp.ne_one.symm
  have hsqrt : (2 : ℝ) < (Real.log (p : ℝ)) ^ (1 / 2 : ℝ) := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
      Real.lt_rpow_inv_iff_of_pos (by positivity) (by positivity) (by norm_num)]
    norm_num
    exact hlog
  have hclaimed := hN p hNp
  rw [ha] at hclaimed
  norm_num at hclaimed ⊢
  exact (not_le_of_gt hsqrt) hclaimed
