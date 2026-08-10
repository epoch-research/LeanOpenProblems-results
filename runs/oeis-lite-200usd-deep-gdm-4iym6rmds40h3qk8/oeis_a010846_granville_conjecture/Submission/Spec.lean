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
lemma a_prime (p : ℕ) (hp : p.Prime) : a p = 2 := by
  have h_p_ge_2 : 2 ≤ p := hp.two_le
  have h_p_gt_1 : 1 < p := hp.one_lt
  have h_p_ge_1 : 1 ≤ p := by omega
  have h_pf_p : primeFactors p = {p} := hp.primeFactors
  unfold a
  rw [h_pf_p]
  have h_eq : (Icc 1 p).filter (fun k => primeFactors k ⊆ {p}) = {1, p} := by
    ext k
    simp only [mem_filter, mem_Icc, mem_insert, mem_singleton]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      by_cases hk1 : k = 1
      · left; exact hk1
      · right
        have hk0 : k ≠ 0 := by omega
        have h_nonempty : (primeFactors k).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty, Ne, Nat.primeFactors_eq_empty]
          tauto
        rcases h_nonempty with ⟨q, hq⟩
        have hq_in : q = p := by
          have hq_in_set : q ∈ ({p} : Finset ℕ) := h3 hq
          rwa [mem_singleton] at hq_in_set
        rw [hq_in] at hq
        rw [Nat.mem_primeFactors] at hq
        have h_dvd : p ∣ k := hq.2.1
        have h_le : p ≤ k := Nat.le_of_dvd (by omega) h_dvd
        omega
    · rintro (rfl | rfl)
      · refine ⟨⟨by omega, hp.two_le.trans' (by decide)⟩, ?_⟩
        rw [Nat.primeFactors_one]
        exact empty_subset _
      · refine ⟨⟨by omega, rfl.le⟩, ?_⟩
        rw [h_pf_p]
  rw [h_eq]
  have h_ne : 1 ≠ p := by omega
  -- let's see if simp can reduce this
  simp [h_ne]

lemma exp_four_lt_81 : Real.exp 4 < 81 := by
  have h1 : Real.exp 1 < 3 := Real.exp_one_lt_three
  have hpos : 0 < Real.exp 1 := Real.exp_pos 1
  have h4 : (4 : ℝ) = 1 + (1 + (1 + 1)) := by ring
  rw [h4]
  rw [Real.exp_add, Real.exp_add, Real.exp_add]
  have h2 : Real.exp 1 * Real.exp 1 < 9 := by
    nlinarith
  have h3 : Real.exp 1 * (Real.exp 1 * Real.exp 1) < 27 := by
    nlinarith
  nlinarith


theorem oeis_a010846_granville_conjecture.disproof :
  ¬ (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (Real.log n) ^ (1 - ε) ≤ a n) := by
  intro h
  have h_half : (0 : ℝ) < 1 / 2 := by norm_num
  rcases h (1/2) h_half with ⟨N, hN⟩
  rcases Nat.exists_infinite_primes (max N 100) with ⟨p, hp_ge, hp_prime⟩
  have h_N_le_p : N ≤ p := by
    have h_max := le_of_max_le_left hp_ge
    omega
  have h_ap := hN p h_N_le_p
  have h_ap_eq : a p = 2 := a_prime p hp_prime
  rw [h_ap_eq] at h_ap
  have h_p_ge_100 : 100 ≤ p := by
    have h_max := le_of_max_le_right hp_ge
    omega
  have h_exp_four_lt_p : Real.exp 4 < p := by
    have h_81_lt_100 : (81 : ℝ) < 100 := by norm_num
    have h_exp_four_lt_100 : Real.exp 4 < 100 := exp_four_lt_81.trans h_81_lt_100
    have h_p_real : (100 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast h_p_ge_100
    exact h_exp_four_lt_100.trans_le h_p_real
  have h_p_pos : (0 : ℝ) < p := by positivity
  have h_four_lt_log : (4 : ℝ) < Real.log p := by
    rwa [Real.lt_log_iff_exp_lt h_p_pos]
  have h_rpow_lt : (4 : ℝ) ^ (1 / 2 : ℝ) < (Real.log p) ^ (1 / 2 : ℝ) := by
    apply Real.rpow_lt_rpow
    · norm_num
    · exact h_four_lt_log
    · norm_num
  have h_four_half : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by norm_num
  rw [h_four_half] at h_rpow_lt
  have h_sub : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [h_sub] at h_ap
  linarith










