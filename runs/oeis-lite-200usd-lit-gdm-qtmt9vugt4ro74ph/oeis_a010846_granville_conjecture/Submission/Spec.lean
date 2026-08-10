import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A010846: Number of numbers $\le n$ whose set of prime factors is a subset of the set of prime factors of $n$.
-/
def a (n : ℕ) : ℕ :=
  (Icc 1 n).filter (fun k => primeFactors k ⊆ primeFactors n) |>.card

lemma a_prime (p : ℕ) (hp : p.Prime) : a p = 2 := by
  have h2p : 2 ≤ p := hp.two_le
  have hp1 : 1 ≤ p := by omega
  have h_prop : (Icc 1 p).filter (fun k => primeFactors k ⊆ primeFactors p) = {1, p} := by
    ext x
    simp only [mem_filter, mem_Icc, mem_insert, mem_singleton]
    rw [hp.primeFactors]
    constructor
    · rintro ⟨⟨h1x, hxp⟩, h_sub⟩
      by_cases hx1 : x = 1
      · left; exact hx1
      · right
        have hx_gt1 : 1 < x := by omega
        have h_nonempty : (primeFactors x).Nonempty := nonempty_primeFactors.mpr hx_gt1
        obtain ⟨q, hq⟩ := h_nonempty
        have hq_in : q ∈ primeFactors x := hq
        have hq_eq : q = p := by
          have := h_sub hq_in
          simp only [mem_singleton] at this
          exact this
        have hp_dvd : p ∣ x := by
          rw [← hq_eq]
          exact dvd_of_mem_primeFactors hq_in
        have : p ≤ x := le_of_dvd (by omega) hp_dvd
        omega
    · rintro (rfl | rfl)
      · constructor
        · exact ⟨by omega, hp1⟩
        · simp only [primeFactors_one, empty_subset]
      · constructor
        · exact ⟨by omega, by omega⟩
        · rw [hp.primeFactors]
  have h1p_ne : 1 ≠ p := by omega
  unfold a
  rw [h_prop]
  exact card_pair h1p_ne

theorem oeis_a010846_granville_conjecture.disproof :
  ¬ (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (Real.log n) ^ (1 - ε) ≤ a n) := by
  intro h
  have h_eps : (0 : ℝ) < 1 / 2 := by norm_num
  obtain ⟨N, hN⟩ := h (1 / 2) h_eps
  let M := Nat.ceil (Real.exp 5)
  obtain ⟨p, hp_ge, hp_prime⟩ := exists_infinite_primes (max N M)
  have hp_N : N ≤ p := by
    have : max N M ≤ p := hp_ge
    omega
  have hp_M : M ≤ p := by
    have : max N M ≤ p := hp_ge
    omega
  have h_ap : a p = 2 := a_prime p hp_prime
  have h_ineq := hN p hp_N
  have h_half : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [h_half] at h_ineq
  rw [h_ap] at h_ineq
  have hp_ge2 : 2 ≤ p := hp_prime.two_le
  have hp_ge1 : 1 ≤ p := by omega
  have hp_ge1_real : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_ge1
  have h_log_pos : 0 ≤ Real.log p := by
    rw [← Real.log_one]
    exact Real.log_le_log (by norm_num) hp_ge1_real
  have h_le2 : ((Real.log p) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) ≤ (2 : ℝ) ^ (2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) h_ineq (by norm_num : 0 ≤ (2 : ℝ))
  have h_exp5 : Real.exp 5 ≤ (p : ℝ) := by
    calc Real.exp 5 ≤ (Nat.ceil (Real.exp 5) : ℝ) := Nat.le_ceil _
         _ ≤ (p : ℝ) := by exact_mod_cast hp_M
  have h_log_ge : 5 ≤ Real.log p := by
    rw [← Real.log_exp 5]
    exact Real.log_le_log (Real.exp_pos 5) h_exp5
  have h_ineq_log : Real.log p ≤ 4 := by
    have h_rpow_mul : ((Real.log p) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = (Real.log p) ^ ((1 / 2 : ℝ) * 2) := by
      rw [← Real.rpow_mul h_log_pos]
    have h_half_two : (1 / 2 : ℝ) * 2 = 1 := by norm_num
    rw [h_half_two, Real.rpow_one] at h_rpow_mul
    have h2_2 : (2 : ℝ) ^ (2 : ℝ) = 4 := by norm_num
    rw [h_rpow_mul, h2_2] at h_le2
    exact h_le2
  have : (5 : ℝ) ≤ 4 := h_log_ge.trans h_ineq_log
  norm_num at this

