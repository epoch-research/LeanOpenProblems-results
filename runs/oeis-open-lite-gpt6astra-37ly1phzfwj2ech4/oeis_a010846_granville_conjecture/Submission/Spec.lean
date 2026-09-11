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

theorem oeis_a010846_granville_conjecture.disproof : ¬ (type_of% @oeis_a010846_granville_conjecture) := by
  intro h
  obtain ⟨N, hN⟩ := h (1 / 2) (by norm_num)
  obtain ⟨m, hm⟩ := exists_nat_gt (Real.exp 5)
  obtain ⟨p, hpbound, hp⟩ := Nat.exists_infinite_primes (max N m)
  have hNp : N ≤ p := (le_max_left _ _).trans hpbound
  have hmp : m ≤ p := (le_max_right _ _).trans hpbound
  have hap : a p ≤ 2 := by
    have hs : (Icc 1 p).filter (fun k => primeFactors k ⊆ primeFactors p) ⊆
        {1, p} := by
      intro k hk
      obtain ⟨hkI, hks⟩ := Finset.mem_filter.mp hk
      obtain ⟨hkpos, hkp⟩ := Finset.mem_Icc.mp hkI
      by_cases hk1 : k = 1
      · simp [hk1]
      · obtain ⟨q, hq, hqk⟩ := Nat.exists_prime_and_dvd hk1
        have hqmem := hks (hq.mem_primeFactors hqk (by omega))
        have hqp : q ∣ p := Nat.dvd_of_mem_primeFactors hqmem
        have hqe : q = p := (hp.eq_one_or_self_of_dvd q hqp).resolve_left hq.ne_one
        have hpk : p ≤ k := Nat.le_of_dvd (by omega) (hqe ▸ hqk)
        have hke : k = p := le_antisymm hkp hpk
        simp [hke]
    have hc := Finset.card_le_card hs
    have ht : ({1, p} : Finset ℕ).card ≤ 2 := by
      exact Finset.card_le_two
    exact hc.trans ht
  have hlog : 5 ≤ Real.log (p : ℝ) := by
    apply (Real.le_log_iff_exp_le (by exact_mod_cast hp.pos)).2
    exact le_trans hm.le (by exact_mod_cast hmp)
  have hb := hN p hNp
  have hsqrt : Real.sqrt (p : ℝ).log ≤ 2 := by
    have haR : (a p : ℝ) ≤ 2 := by exact_mod_cast hap
    norm_num only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at hb
    rw [← Real.sqrt_eq_rpow] at hb
    exact hb.trans haR
  have hsq := Real.sq_sqrt (show 0 ≤ Real.log (p : ℝ) by linarith)
  have hnonneg := Real.sqrt_nonneg (Real.log (p : ℝ))
  nlinarith
