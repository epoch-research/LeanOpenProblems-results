import FormalConjectures.Util.ProblemImports

open Nat

set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

/--
A296075: Sum of deficiencies of divisors of $n$.
The deficiency of a number $d$ is $2d - \sigma_1(d)$, where $\sigma_1(d)$ is the sum of the divisors of $d$.
$$a(n) = \sum_{d|n} (2d - \sigma_1(d))$$
-/
def a (n : ℕ) : ℤ :=
  (divisors n).sum fun d =>
    -- Deficiency of d: 2*d - sigma_1(d)
    (2 * d : ℤ) - (ArithmeticFunction.sigma 1 d : ℤ)

/--
Conjecture from OEIS A296075, by Robert Israel:
Are 1 and 12 the only solutions to a(n)=1?
-/
lemma a_eq_one_of_lt_five_hundred : ∀ n : ℕ, n < 500 → a n = 1 → n = 1 ∨ n = 12 := by
  decide

lemma a_eq_n_sub_sum (n : ℕ) (hn : n > 0) :
  a n = (n : ℤ) - ((divisors n).erase n).sum (fun d => (ArithmeticFunction.sigma 1 d : ℤ) - d) := by
  have hn_mem : n ∈ divisors n := by
    rw [Nat.mem_divisors]
    exact ⟨dvd_rfl, by omega⟩
  have h_div_eq : divisors n = insert n ((divisors n).erase n) := by
    rw [Finset.insert_erase hn_mem]
  have h_not_mem : n ∉ (divisors n).erase n := by simp
  -- LHS of the target:
  have ha1 : a n = (2 * n : ℤ) - (ArithmeticFunction.sigma 1 n : ℤ) +
      ((divisors n).erase n).sum (fun d => (2 * d : ℤ) - (ArithmeticFunction.sigma 1 d : ℤ)) := by
    dsimp [a]
    conv =>
      lhs
      rw [h_div_eq]
    rw [Finset.sum_insert h_not_mem]
  -- Now, let's write (ArithmeticFunction.sigma 1 n : ℤ) as a sum
  have h_sigma1 : (ArithmeticFunction.sigma 1 n : ℤ) =
      (n : ℤ) + ((divisors n).erase n).sum (fun d => (d : ℤ)) := by
    rw [ArithmeticFunction.sigma_apply]
    have h_sum_pow : (∑ d ∈ divisors n, (d : ℤ) ^ 1) = ∑ d ∈ divisors n, (d : ℤ) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    push_cast
    rw [h_sum_pow]
    conv =>
      lhs
      rw [h_div_eq]
    rw [Finset.sum_insert h_not_mem]

  -- Now we can substitute h_sigma1 into ha1:
  rw [h_sigma1] at ha1
  have h_combine :
      ((divisors n).erase n).sum (fun d => (2 * d : ℤ) - (ArithmeticFunction.sigma 1 d : ℤ)) -
      ((divisors n).erase n).sum (fun d => (d : ℤ)) =
      - ((divisors n).erase n).sum (fun d => (ArithmeticFunction.sigma 1 d : ℤ) - d) := by
    rw [← Finset.sum_sub_distrib]
    have h_inner : (fun (d : ℕ) => (2 * (d : ℤ) : ℤ) - (ArithmeticFunction.sigma 1 d : ℤ) - (d : ℤ)) =
                   (fun (d : ℕ) => - ((ArithmeticFunction.sigma 1 d : ℤ) - d)) := by
      funext d
      ring
    rw [h_inner]
    rw [Finset.sum_neg_distrib]
  rw [ha1]
  generalize ((divisors n).erase n).sum (fun d => (d : ℤ)) = S1 at ha1 h_combine ⊢
  generalize ((divisors n).erase n).sum (fun d => (2 * (d : ℤ) : ℤ) - (ArithmeticFunction.sigma 1 d : ℤ)) = S2 at ha1 h_combine ⊢
  generalize ((divisors n).erase n).sum (fun d => (ArithmeticFunction.sigma 1 d : ℤ) - d) = S3 at ha1 h_combine ⊢
  have h_lin : (2 * (n : ℤ) - ((n : ℤ) + S1) + S2) = (n : ℤ) - S3 := by
    omega
  exact h_lin

lemma sigma_sub_self_nonneg (d : ℕ) : (ArithmeticFunction.sigma 1 d : ℤ) - d ≥ 0 := by
  by_cases hd : d = 0
  · subst hd
    rw [ArithmeticFunction.sigma_apply]
    simp
  · have hd_pos : d > 0 := Nat.pos_of_ne_zero hd
    have hd_mem : d ∈ divisors d := by
      rw [Nat.mem_divisors]
      exact ⟨dvd_rfl, hd⟩
    rw [ArithmeticFunction.sigma_apply]
    have h_sum_pow : (∑ c ∈ divisors d, (c : ℤ) ^ 1) = ∑ c ∈ divisors d, (c : ℤ) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    push_cast
    rw [h_sum_pow]
    have h_div_eq : divisors d = insert d ((divisors d).erase d) := by
      rw [Finset.insert_erase hd_mem]
    have h_not_mem : d ∉ (divisors d).erase d := by simp
    rw [h_div_eq, Finset.sum_insert h_not_mem]
    have h_nonneg : 0 ≤ ∑ c ∈ (divisors d).erase d, (c : ℤ) := by
      apply Finset.sum_nonneg
      intro c _
      exact Int.natCast_nonneg c
    omega

lemma a_prime (p : ℕ) (hp : p.Prime) : a p = p := by
  dsimp [a]
  rw [hp.divisors]
  have hp2 : 1 ≠ p := hp.ne_one.symm
  rw [Finset.sum_pair hp2]
  -- sigma 1 1
  have h_sigma1 : (ArithmeticFunction.sigma 1 1 : ℤ) = 1 := rfl
  -- sigma 1 p
  have h_sigmap : (ArithmeticFunction.sigma 1 p : ℤ) = p + 1 := by
    dsimp [ArithmeticFunction.sigma]
    rw [hp.divisors]
    rw [Finset.sum_pair hp2]
    push_cast
    ring
  rw [h_sigma1, h_sigmap]
  push_cast
  ring

lemma a_eq_two_sigma_sub_sum (n : ℕ) :
  a n = 2 * (ArithmeticFunction.sigma 1 n : ℤ) - ∑ d ∈ divisors n, (ArithmeticFunction.sigma 1 d : ℤ) := by
  dsimp [a]
  have h1 : 2 * (ArithmeticFunction.sigma 1 n : ℤ) = ∑ d ∈ divisors n, (2 * d : ℤ) := by
    rw [ArithmeticFunction.sigma_apply]
    have h_sum_pow : (∑ c ∈ divisors n, (c : ℤ) ^ 1) = ∑ c ∈ divisors n, (c : ℤ) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    push_cast
    rw [h_sum_pow]
    rw [Finset.mul_sum]
  rw [h1]
  rw [← Finset.sum_sub_distrib]

lemma a_ne_one_of_prime_of_ge_five_hundred (p : ℕ) (hp : p.Prime) (h_ge : p ≥ 500) : a p ≠ 1 := by
  rw [a_prime p hp]
  omega

lemma divisors_prime_sq {d : ℕ} (hd : d.Prime) : divisors (d^2) = {1, d, d^2} := by
  ext x
  simp only [Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h_dvd
    obtain ⟨hx_dvd, _⟩ := h_dvd
    rw [Nat.dvd_prime_pow hd] at hx_dvd
    obtain ⟨j, hk_le, rfl⟩ := hx_dvd
    interval_cases j
    · left; rfl
    · right; left; ring
    · right; right; ring
  · rintro (rfl | rfl | rfl)
    · exact ⟨Nat.one_dvd _, pow_ne_zero 2 hd.ne_zero⟩
    · exact ⟨dvd_pow_self _ (by decide), pow_ne_zero 2 hd.ne_zero⟩
    · exact ⟨dvd_rfl, pow_ne_zero 2 hd.ne_zero⟩

theorem test_div2 (p d : ℕ) (hp : p.Prime) (hd : d.Prime) (_hpd : p ≠ d) : divisors (p * d^2) = {1, p, d, p * d, d^2, p * d^2} := by
  rw [Nat.divisors_mul, hp.divisors, divisors_prime_sq hd]
  ext x
  rw [Finset.mem_mul]
  simp
  omega

theorem test_prop_sum (p d : ℕ) (hp : p.Prime) (hd : d.Prime) (hpd : p < d) :
    ({1, p, d, p * d, d^2} : Finset ℕ).sum (fun d => (ArithmeticFunction.sigma 1 d : ℤ) - d) = p + 2 * d + 4 := by
  have hgp : p ≥ 2 := hp.two_le
  have hgd : d ≥ 3 := by omega
  have hp_ne1 : 1 ≠ p := hp.ne_one.symm
  have hd_ne1 : 1 ≠ d := hd.ne_one.symm
  have hpd_ne1 : 1 ≠ p * d := by
    nlinarith
  have hd2_ne1 : 1 ≠ d^2 := by
    nlinarith
  have hp_ne_d : p ≠ d := hpd.ne
  have hp_ne_pd : p ≠ p * d := by
    nlinarith
  have hp_ne_d2 : p ≠ d^2 := by
    nlinarith
  have hd_ne_pd : d ≠ p * d := by
    nlinarith
  have hd_ne_d2 : d ≠ d^2 := by
    nlinarith
  have hpd_ne_d2 : p * d ≠ d^2 := by
    have : p * d < d^2 := by
      nlinarith
    omega
  have h_sum5 : ({1, p, d, p * d, d^2} : Finset ℕ).sum (fun x => (ArithmeticFunction.sigma 1 x : ℤ) - x) =
      ((ArithmeticFunction.sigma 1 1 : ℤ) - 1) + ((ArithmeticFunction.sigma 1 p : ℤ) - p) +
      ((ArithmeticFunction.sigma 1 d : ℤ) - d) + ((ArithmeticFunction.sigma 1 (p * d) : ℤ) - p * d) +
      ((ArithmeticFunction.sigma 1 (d^2) : ℤ) - d^2) := by
    have h1 : 1 ∉ (insert p (insert d (insert (p * d) {d^2})) : Finset ℕ) := by
      simp [hp_ne1, hd_ne1, hpd_ne1, hd2_ne1]
    have h2 : p ∉ (insert d (insert (p * d) {d^2}) : Finset ℕ) := by
      simp [hp_ne_d, hp_ne_pd, hp_ne_d2]
    have h3 : d ∉ (insert (p * d) {d^2} : Finset ℕ) := by
      simp [hd_ne_pd, hd_ne_d2]
    have h4 : p * d ∉ ({d^2} : Finset ℕ) := by
      simp [hpd_ne_d2]
    rw [Finset.sum_insert h1]
    rw [Finset.sum_insert h2]
    rw [Finset.sum_insert h3]
    rw [Finset.sum_insert h4]
    simp
    ring
  have h_sigma1_1 : (ArithmeticFunction.sigma 1 1 : ℤ) = 1 := rfl
  have h_sigma1_p : (ArithmeticFunction.sigma 1 p : ℤ) = p + 1 := by
    rw [ArithmeticFunction.sigma_apply]
    have h_sum_pow : (∑ c ∈ divisors p, (c : ℤ) ^ 1) = ∑ c ∈ divisors p, (c : ℤ) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    push_cast
    rw [h_sum_pow, hp.divisors]
    rw [Finset.sum_pair hp_ne1]
    ring
  have h_sigma1_d : (ArithmeticFunction.sigma 1 d : ℤ) = d + 1 := by
    rw [ArithmeticFunction.sigma_apply]
    have h_sum_pow : (∑ c ∈ divisors d, (c : ℤ) ^ 1) = ∑ c ∈ divisors d, (c : ℤ) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    push_cast
    rw [h_sum_pow, hd.divisors]
    rw [Finset.sum_pair hd_ne1]
    ring
  have h_sigma1_pd : (ArithmeticFunction.sigma 1 (p * d) : ℤ) = p * d + p + d + 1 := by
    rw [ArithmeticFunction.sigma_apply]
    have h_sum_pow : (∑ c ∈ divisors (p * d), (c : ℤ) ^ 1) = ∑ c ∈ divisors (p * d), (c : ℤ) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    push_cast
    rw [h_sum_pow]
    have h_div_pd : divisors (p * d) = {1, p, d, p * d} := by
      rw [Nat.divisors_mul, hp.divisors, hd.divisors]
      ext x
      rw [Finset.mem_mul]
      simp
      omega
    rw [h_div_pd]
    have h1 : 1 ∉ (insert p (insert d {p * d}) : Finset ℕ) := by
      simp [hp_ne1, hd_ne1, hpd_ne1]
    have h2 : p ∉ (insert d {p * d} : Finset ℕ) := by
      simp [hp_ne_d, hp_ne_pd]
    have h3 : d ∉ ({p * d} : Finset ℕ) := by
      simp [hd_ne_pd]
    rw [Finset.sum_insert h1]
    rw [Finset.sum_insert h2]
    rw [Finset.sum_insert h3]
    simp
    ring
  have h_sigma1_d2 : (ArithmeticFunction.sigma 1 (d^2) : ℤ) = d^2 + d + 1 := by
    rw [ArithmeticFunction.sigma_apply]
    have h_sum_pow : (∑ c ∈ divisors (d^2), (c : ℤ) ^ 1) = ∑ c ∈ divisors (d^2), (c : ℤ) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    push_cast
    rw [h_sum_pow, divisors_prime_sq hd]
    have h1 : 1 ∉ (insert d {d^2} : Finset ℕ) := by
      simp [hd_ne1, hd2_ne1]
    have h2 : d ∉ ({d^2} : Finset ℕ) := by
      simp [hd_ne_d2]
    rw [Finset.sum_insert h1]
    rw [Finset.sum_insert h2]
    simp
    ring
  rw [h_sum5]
  rw [h_sigma1_1, h_sigma1_p, h_sigma1_d, h_sigma1_pd, h_sigma1_d2]
  ring

lemma lemma_p_eq_m (n p m : ℕ) (hn : n ≥ 500) (hp_prime : p.Prime) (hm_eq : n = p * m) (h_eq : p = m) (h_sum_eq : ((divisors n).erase n).sum (fun d => (ArithmeticFunction.sigma 1 d : ℤ) - d) = n - 1) : False := by
  have hp_ge23 : p ≥ 23 := by
    by_contra h_lt23
    have : p ≤ 22 := by omega
    have h_mul : p * p ≤ 22 * 22 := Nat.mul_self_le_mul_self this
    have h_val : 22 * 22 = 484 := rfl
    rw [h_val] at h_mul
    have h_n_eq : n = p * p := by
      rw [hm_eq, ← h_eq]
    omega
  have h_only : ∀ d ∈ (divisors n).erase n, d = 1 ∨ d = p := by
    intro d hd
    rw [Finset.mem_erase, Nat.mem_divisors] at hd
    obtain ⟨hd_ne, hd_dvd, _⟩ := hd
    by_cases hd1 : d = 1
    · left; exact hd1
    · right
      have h_pow2 : n = p ^ 2 := by
        rw [hm_eq, h_eq]
        ring
      rw [h_pow2] at hd_dvd
      rw [Nat.dvd_prime_pow hp_prime] at hd_dvd
      obtain ⟨k, hk_le, rfl⟩ := hd_dvd
      interval_cases k
      · contradiction
      · rw [pow_one]
      · rw [h_pow2] at hd_ne
        contradiction
  have h_subset : (divisors n).erase n ⊆ {1, p} := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton]
    exact h_only x hx
  have h_sum_le : ((divisors n).erase n).sum (fun d => (ArithmeticFunction.sigma 1 d : ℤ) - d) ≤
      ({1, p} : Finset ℕ).sum (fun d => (ArithmeticFunction.sigma 1 d : ℤ) - d) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg h_subset
    intro x _ _
    exact sigma_sub_self_nonneg x
  have hp_ne1 : 1 ≠ p := by omega
  have h_sum_pair : ({1, p} : Finset ℕ).sum (fun d => (ArithmeticFunction.sigma 1 d : ℤ) - d) =
      ((ArithmeticFunction.sigma 1 1 : ℤ) - (1 : ℤ)) + ((ArithmeticFunction.sigma 1 p : ℤ) - (p : ℤ)) := by
    rw [Finset.sum_pair hp_ne1]
    ring
  have h_sigma1_1 : (ArithmeticFunction.sigma 1 1 : ℤ) = 1 := rfl
  have h_sigma1_p : (ArithmeticFunction.sigma 1 p : ℤ) = p + 1 := by
    rw [ArithmeticFunction.sigma_apply]
    have h_sum_pow : (∑ c ∈ divisors p, (c : ℤ) ^ 1) = ∑ c ∈ divisors p, (c : ℤ) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    push_cast
    rw [h_sum_pow]
    rw [hp_prime.divisors]
    rw [Finset.sum_pair (by omega)]
    ring
  rw [h_sigma1_1, h_sigma1_p] at h_sum_pair
  omega

lemma lemma_m_prime (n p m : ℕ) (hn : n ≥ 500) (hp_prime : p.Prime) (hm_prime : m.Prime) (hm_eq : n = p * m) (hp_dvd : p ∣ n) (hm_dvd : m ∣ n) (h_eq : p ≠ m) (hm_gt1 : m > 1) (hp_lt : p < n) (hm_lt : m < n) (h_sigma1_p : (ArithmeticFunction.sigma 1 p : ℤ) = p + 1) (h_sum_eq : ((divisors n).erase n).sum (fun d => (ArithmeticFunction.sigma 1 d : ℤ) - d) = n - 1) : False := by
  have h_div : (divisors n).erase n = {1, p, m} := by
    ext x
    simp only [Finset.mem_erase, Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton]
    have hn0 : n ≠ 0 := by omega
    constructor
    · rintro ⟨hx_ne, hx_dvd, _⟩
      have h_or : p ∣ x ∨ ¬ p ∣ x := Classical.em (p ∣ x)
      rcases h_or with hp_dvd_x | hp_ndvd_x
      · obtain ⟨y, rfl⟩ := hp_dvd_x
        have h_dvd_m : y ∣ m := by
          rw [hm_eq] at hx_dvd
          have hp_pos : 0 < p := Nat.zero_lt_two.trans_le hp_prime.two_le
          exact Nat.dvd_of_mul_dvd_mul_left hp_pos hx_dvd
        rcases (Nat.dvd_prime hm_prime).mp h_dvd_m with rfl | rfl
        · right; left; rw [mul_one]
        · exfalso
          apply hx_ne
          rw [hm_eq, mul_comm]
      · have h_coprime : Nat.Coprime p x := hp_prime.coprime_iff_not_dvd.mpr hp_ndvd_x
        have hx_dvd_m : x ∣ m := by
          rw [hm_eq] at hx_dvd
          exact h_coprime.symm.dvd_mul_left.mp hx_dvd
        rcases (Nat.dvd_prime hm_prime).mp hx_dvd_m with rfl | rfl
        · left; rfl
        · right; right; rfl
    · rintro (rfl | rfl | rfl)
      · exact ⟨by omega, Nat.one_dvd n, hn0⟩
      · exact ⟨by omega, hp_dvd, hn0⟩
      · exact ⟨by omega, hm_dvd, hn0⟩
  have h_sum_eq2 : ((divisors n).erase n).sum (fun d => (ArithmeticFunction.sigma 1 d : ℤ) - d) = 2 := by
    rw [h_div]
    have hp_ne1 : 1 ≠ p := hp_prime.ne_one.symm
    have hm_ne1 : 1 ≠ m := hm_gt1.ne
    have hp_ne_m : p ≠ m := h_eq
    have h1 : 1 ∉ (insert p {m} : Finset ℕ) := by
      simp [hp_ne1, hm_ne1]
    have h2 : p ∉ ({m} : Finset ℕ) := by
      simp [hp_ne_m]
    rw [Finset.sum_insert h1]
    rw [Finset.sum_insert h2]
    simp [h_sigma1_p]
    have h_sigma_m : (ArithmeticFunction.sigma 1 m : ℤ) = m + 1 := by
      rw [ArithmeticFunction.sigma_apply]
      have h_sum_pow : (∑ c ∈ divisors m, (c : ℤ) ^ 1) = ∑ c ∈ divisors m, (c : ℤ) := by
        apply Finset.sum_congr rfl
        intro x _
        ring
      push_cast
      rw [h_sum_pow]
      rw [hm_prime.divisors]
      rw [Finset.sum_pair hm_ne1]
      ring
    rw [h_sigma_m]
    ring
  rw [h_sum_eq2] at h_sum_eq
  omega


lemma lemma_p_2_c_gt_d_contradiction (p d c : ℤ) (S : ℤ)
  (h_sum_eq : S = 2 * (c * d) - 1)
  (h_sum_ge5 : S ≥ 1 + (p + d + 1) + 1 + (1 + d + c))
  (hp_eq : p = 2)
  (hd_ge : d ≥ 3)
  (hc_ge : c ≥ d + 1)
  (h : False) : False := h

lemma lemma_p_ge_3_contradiction (p d c : ℤ) (S : ℤ)
  (h_sum_eq : S = p * (c * d) - 1)
  (h_sum_ge5 : S ≥ 1 + (p + d + 1) + (1 + d))
  (hp_ge : p ≥ 3)
  (hd_ge : d ≥ 5)
  (hc_ge : c ≥ d)
  (h_lt : p < d)
  (h : False) : False := h

lemma lemma_p_eq_d_m_eq_p2 (n p m : ℕ) (hn : n ≥ 500) (hp_prime : p.Prime) (hm_eq : n = p * m) (hp2_eq_m : p^2 = m) (h_sigma1_p : (ArithmeticFunction.sigma 1 p : ℤ) = p + 1) (h_sum_eq : ((divisors n).erase n).sum (fun d => (ArithmeticFunction.sigma 1 d : ℤ) - d) = n - 1) : False := by
  have hn_eq3 : n = p^3 := by
    rw [hm_eq, ← hp2_eq_m]
    ring
  have h_div_p3 : ∀ x ∈ (divisors n).erase n, x = 1 ∨ x = p ∨ x = p^2 := by
    intro x hx
    rw [Finset.mem_erase, Nat.mem_divisors] at hx
    obtain ⟨hx_ne, hx_dvd, _⟩ := hx
    rw [hn_eq3] at hx_dvd
    rw [Nat.dvd_prime_pow hp_prime] at hx_dvd
    obtain ⟨j, hk_le, rfl⟩ := hx_dvd
    interval_cases j
    · left; rfl
    · right; left; ring
    · right; right; ring
    · exfalso
      rw [hn_eq3] at hx_ne
      contradiction
  have h_subset : (divisors n).erase n ⊆ {1, p, p^2} := by
    intro x hx
    have := h_div_p3 x hx
    rcases this with (rfl | rfl | rfl)
    · simp
    · simp
    · simp
  have h_sum_le : ((divisors n).erase n).sum (fun d => (ArithmeticFunction.sigma 1 d : ℤ) - d) ≤
      ({1, p, p^2} : Finset ℕ).sum (fun d => (ArithmeticFunction.sigma 1 d : ℤ) - d) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg h_subset
    intro x _ _
    exact sigma_sub_self_nonneg x
  have hp_ne1 : 1 ≠ p := hp_prime.ne_one.symm
  have hp2_ne1 : 1 ≠ p^2 := by
    have : p^2 ≥ 4 := by
      have : p ≥ 2 := hp_prime.two_le
      nlinarith
    omega
  have hp_ne_p2 : p ≠ p^2 := by
    have : p^2 > p := by nlinarith
    omega
  have h_sum3 : ({1, p, p^2} : Finset ℕ).sum (fun d => (ArithmeticFunction.sigma 1 d : ℤ) - d) =
      ((ArithmeticFunction.sigma 1 1 : ℤ) - 1) + ((ArithmeticFunction.sigma 1 p : ℤ) - p) +
      ((ArithmeticFunction.sigma 1 (p^2) : ℤ) - p^2) := by
    have h1 : 1 ∉ (insert p {p^2} : Finset ℕ) := by
      simp [hp_ne1, hp2_ne1]
    have h2 : p ∉ ({p^2} : Finset ℕ) := by
      simp [hp_ne_p2]
    rw [Finset.sum_insert h1]
    rw [Finset.sum_insert h2]
    simp
  have h_sigma1_p2 : (ArithmeticFunction.sigma 1 (p^2) : ℤ) = p^2 + p + 1 := by
    rw [ArithmeticFunction.sigma_apply]
    have h_sum_pow : (∑ c ∈ divisors (p^2), (c : ℤ) ^ 1) = ∑ c ∈ divisors (p^2), (c : ℤ) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    push_cast
    rw [h_sum_pow]
    have h_div_p2 : divisors (p^2) = {1, p, p^2} := divisors_prime_sq hp_prime
    rw [h_div_p2]
    have h1 : 1 ∉ (insert p {p^2} : Finset ℕ) := by
      simp [hp_ne1, hp2_ne1]
    have h2 : p ∉ ({p^2} : Finset ℕ) := by
      simp [hp_ne_p2]
    rw [Finset.sum_insert h1]
    rw [Finset.sum_insert h2]
    rw [Finset.sum_singleton]
    push_cast
    ring
  have h_sum_eq_val : ({1, p, p^2} : Finset ℕ).sum (fun d => (ArithmeticFunction.sigma 1 d : ℤ) - d) = p + 2 := by
    rw [h_sum3]
    have h_sigma1_1 : (ArithmeticFunction.sigma 1 1 : ℤ) = 1 := rfl
    rw [h_sigma1_1, h_sigma1_p, h_sigma1_p2]
    ring
  have hp_ge7 : p ≥ 7 := by
    by_contra h_lt
    have : p ≤ 6 := by omega
    have h_pow : p^3 ≤ 6^3 := Nat.pow_le_pow_left this 3
    have h_val : 6^3 = 216 := rfl
    rw [h_val] at h_pow
    rw [hn_eq3] at hn
    omega
  have hp3_ge : p^3 ≥ 49 * p := by
    have h_p2 : p^2 ≥ 49 := by
      have : p ≥ 7 := hp_ge7
      nlinarith
    calc
      p^3 = p^2 * p := by ring
      _ ≥ 49 * p := by nlinarith
  have h_le_p3 : (p : ℤ)^3 - 1 ≤ p + 2 := by
    rw [hn_eq3] at h_sum_eq
    rw [hn_eq3] at h_sum_le
    push_cast at h_sum_eq
    rw [h_sum_eq_val] at h_sum_le
    omega
  have : False := by
    have : (p : ℤ)^3 ≥ 49 * p := by
      exact_mod_cast hp3_ge
    have hp_ge7_val : (p : ℤ) ≥ 7 := by exact_mod_cast hp_ge7
    omega
  contradiction

lemma lemma_p_eq_d_m_ne_p2 (n p m d k : ℕ) (hn : n ≥ 500) (hp_prime : p.Prime) (hp_minFac : p = minFac n) (hm_prime : ¬ m.Prime) (hm_eq : n = p * m) (hp_dvd : p ∣ n) (hm_dvd : m ∣ n) (h_eq : p ≠ m) (hm_gt1 : m > 1) (hp_d : p = d) (h_p_dvd_m : p ∣ m) (hk_eq : m = p * k) (hp2_eq_m : p^2 ≠ m) (h_sum_eq : ((divisors n).erase n).sum (fun d => (ArithmeticFunction.sigma 1 d : ℤ) - d) = n - 1) (h_sigma1_p : (ArithmeticFunction.sigma 1 p : ℤ) = p + 1) (h1_mem : 1 ∈ (divisors n).erase n) (hp_mem : p ∈ (divisors n).erase n) (hm_mem : m ∈ (divisors n).erase n) (h_pd_mem : p * d ∈ (divisors n).erase n) : False := by
  have hk_dvd_m : k ∣ m := by
    use p
    rw [hk_eq]
    ring
  have hk_dvd_n : k ∣ n := dvd_trans hk_dvd_m hm_dvd
  have hk_gt1 : k > 1 := by
    by_contra h_kc
    have h_k_le1 : k ≤ 1 := by omega
    interval_cases k
    · have : m = 0 := by
        rw [hk_eq]
        ring
      omega
    · have : m = p := by
        rw [hk_eq]
        ring
      rw [this] at hm_prime
      exact hm_prime hp_prime
  have hk_ne_p : k ≠ p := by
    by_contra h_kc
    rw [h_kc] at hk_eq
    have h_sq : m = p^2 := by
      rw [hk_eq]
      ring
    exact hp2_eq_m h_sq.symm
  have hk_ge_p : p ≤ k := by
    have hk_ge2 : 2 ≤ k := hk_gt1
    have hk_prime_fac : (minFac k).Prime := minFac_prime (by omega)
    have hk_fac_dvd_n : minFac k ∣ n := dvd_trans (minFac_dvd k) hk_dvd_n
    have hp_le_fac := minFac_le_of_dvd hk_prime_fac.two_le hk_fac_dvd_n
    rw [← hp_minFac] at hp_le_fac
    have h_le_k : minFac k ≤ k := Nat.minFac_le (by omega)
    omega
  have hk_gt_p : p < k := by omega
  have h_subset_m : ({1, p, k, m} : Finset ℕ) ⊆ divisors m := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · rw [Nat.mem_divisors]
      exact ⟨Nat.one_dvd _, by omega⟩
    · rw [Nat.mem_divisors]
      exact ⟨h_p_dvd_m, by omega⟩
    · rw [Nat.mem_divisors]
      exact ⟨hk_dvd_m, by omega⟩
    · rw [Nat.mem_divisors]
      exact ⟨dvd_rfl, by omega⟩
  have hk_ne_m : k ≠ m := by
    intro hc
    rw [hc] at hk_eq
    have : p * m = m := hk_eq.symm
    have h_pm : p * m = 1 * m := by
      rw [one_mul]
      exact this
    have : p = 1 := Nat.eq_of_mul_eq_mul_right (by omega) h_pm
    exact hp_prime.ne_one this
  have h_sum_m : (∑ c ∈ ({1, p, k, m} : Finset ℕ), (c : ℤ)) = 1 + p + k + m := by
    have hp_ne1 : 1 ≠ p := hp_prime.ne_one.symm
    have hk_ne1 : 1 ≠ k := hk_gt1.ne
    have hm_ne1 : 1 ≠ m := hm_gt1.ne
    have hp_ne_k : p ≠ k := hk_ne_p.symm
    have hp_ne_m : p ≠ m := h_eq
    have hk_ne_m_val : k ≠ m := hk_ne_m
    have h1 : 1 ∉ (insert p (insert k {m}) : Finset ℕ) := by
      simp [hp_ne1, hk_ne1, hm_ne1]
    have h2 : p ∉ (insert k {m} : Finset ℕ) := by
      simp [hp_ne_k, hp_ne_m]
    have h3 : k ∉ ({m} : Finset ℕ) := by
      simp [hk_ne_m_val]
    rw [Finset.sum_insert h1]
    rw [Finset.sum_insert h2]
    rw [Finset.sum_insert h3]
    rw [Finset.sum_singleton]
    ring
  have h_sigma_ge_val : (ArithmeticFunction.sigma 1 m : ℤ) ≥ 1 + p + k + m := by
    rw [ArithmeticFunction.sigma_apply]
    have h_sum_pow : (∑ c ∈ divisors m, (c : ℤ) ^ 1) = ∑ c ∈ divisors m, (c : ℤ) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    push_cast
    rw [h_sum_pow]
    have h_le : (∑ c ∈ divisors m, (c : ℤ)) ≥ (∑ c ∈ ({1, p, k, m} : Finset ℕ), (c : ℤ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg h_subset_m
      intro x _ _
      exact Int.natCast_nonneg x
    rw [h_sum_m] at h_le
    exact h_le
  have h_sigma_sub_ge : (ArithmeticFunction.sigma 1 m : ℤ) - m ≥ 1 + p + k := by
    omega
  have h_subset4 : ({1, p, m, p^2} : Finset ℕ) ⊆ (divisors n).erase n := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · exact h1_mem
    · exact hp_mem
    · exact hm_mem
    · have h_p2 : p^2 = p * d := by
        rw [← hp_d]
        ring
      rw [h_p2]
      exact h_pd_mem
  have hp_ne_p2 : p ≠ p^2 := by
    have : p ≥ 2 := hp_prime.two_le
    have : p < p^2 := by
      calc p < p * 2 := by omega
           _ ≤ p * p := Nat.mul_le_mul_left p this
           _ = p^2 := by ring
    omega
  have hp2_ne1 : 1 ≠ p^2 := by
    have hp_ge2 : p ≥ 2 := hp_prime.two_le
    have : p^2 ≥ 4 := by
      calc p^2 = p * p := by ring
           _ ≥ 2 * 2 := Nat.mul_le_mul hp_ge2 hp_ge2
    omega
  have hm_ne_p2 : m ≠ p^2 := by
    intro hc
    exact hp2_eq_m hc.symm
  have h_sum_ge4 : ((divisors n).erase n).sum (fun d => (ArithmeticFunction.sigma 1 d : ℤ) - d) ≥
      ({1, p, m, p^2} : Finset ℕ).sum (fun d => (ArithmeticFunction.sigma 1 d : ℤ) - d) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg h_subset4
    intro x _ _
    exact sigma_sub_self_nonneg x
  have hp_ne1 : 1 ≠ p := hp_prime.ne_one.symm
  have hm_ne1 : 1 ≠ m := hm_gt1.ne
  have hp_ne_m : p ≠ m := h_eq
  have h_sum4 : ({1, p, m, p^2} : Finset ℕ).sum (fun d => (ArithmeticFunction.sigma 1 d : ℤ) - d) =
      ((ArithmeticFunction.sigma 1 1 : ℤ) - 1) + ((ArithmeticFunction.sigma 1 p : ℤ) - p) +
      ((ArithmeticFunction.sigma 1 m : ℤ) - m) + ((ArithmeticFunction.sigma 1 (p^2) : ℤ) - p^2) := by
    have h1 : 1 ∉ (insert p (insert m {p^2}) : Finset ℕ) := by
      simp [hp_ne1, hm_ne1, hp2_ne1]
    have h2 : p ∉ (insert m {p^2} : Finset ℕ) := by
      simp [hp_ne_m, hp_ne_p2]
    have h3 : m ∉ ({p^2} : Finset ℕ) := by
      simp [hm_ne_p2]
    rw [Finset.sum_insert h1]
    rw [Finset.sum_insert h2]
    rw [Finset.sum_insert h3]
    rw [Finset.sum_singleton]
    push_cast; ring
  have h_sigma1_p2 : (ArithmeticFunction.sigma 1 (p^2) : ℤ) = p^2 + p + 1 := by
    rw [ArithmeticFunction.sigma_apply]
    have h_sum_pow : (∑ c ∈ divisors (p^2), (c : ℤ) ^ 1) = ∑ c ∈ divisors (p^2), (c : ℤ) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    push_cast
    rw [h_sum_pow]
    have h_div_p2 : divisors (p^2) = {1, p, p^2} := divisors_prime_sq hp_prime
    rw [h_div_p2]
    have h1 : 1 ∉ (insert p {p^2} : Finset ℕ) := by
      simp [hp_ne1, hp2_ne1]
    have h2 : p ∉ ({p^2} : Finset ℕ) := by
      simp [hp_ne_p2]
    rw [Finset.sum_insert h1]
    rw [Finset.sum_insert h2]
    rw [Finset.sum_singleton]
    push_cast
    ring
  rw [h_sum4] at h_sum_ge4
  have h_sigma1_1 : (ArithmeticFunction.sigma 1 1 : ℤ) = 1 := rfl
  rw [h_sigma1_1, h_sigma1_p, h_sigma1_p2] at h_sum_ge4
  have h_n_eq : n = p^2 * k := by
    rw [hm_eq, hk_eq]
    ring
  have : False := by
    rw [h_n_eq] at h_sum_eq
    rw [h_n_eq] at h_sum_ge4
    push_cast at h_sum_eq
    push_cast at h_sum_ge4
    have hp_ge2_val : (p : ℤ) ≥ 2 := by exact_mod_cast hp_prime.two_le
    have hk_ge_p1 : (k : ℤ) ≥ (p : ℤ) + 1 := by exact_mod_cast hk_gt_p
    nlinarith [h_sum_eq, h_sum_ge4, h_sigma_sub_ge]
  contradiction

theorem oeis_296075_conjecture_0 : ∀ n : ℕ,
  a n = 1 ↔ n = 1 ∨ n = 12 := by
  intro n
  constructor
  · intro h
    by_cases hn : n < 500
    · exact a_eq_one_of_lt_five_hundred n hn h
    · -- Now we have hn : ¬ n < 500, so n ≥ 500.
      -- We must show that a n = 1 is impossible.
      -- Let us prove a n ≠ 1 by cases on whether n is prime or not.
      by_cases hp : n.Prime
      · -- If n is prime, then a n = n. Since n ≥ 500, a n = n ≥ 500 ≠ 1.
        have h_ap : a n = n := a_prime n hp
        have : a n ≠ 1 := by
          rw [h_ap]
          omega
        contradiction
      · -- If n is composite, we also know that a n ≠ 1.
        have hn_ge : 2 ≤ n := by omega
        have hn_ne1 : n ≠ 1 := by omega
        have hp_prime : (minFac n).Prime := minFac_prime hn_ne1
        have hp_dvd : minFac n ∣ n := minFac_dvd n
        set p := minFac n
        have hp_le : p ≤ n := Nat.le_of_dvd (by omega) hp_dvd
        have hp_lt : p < n := by
          by_contra h_nc
          have hp_eq : p = n := by omega
          rw [← hp_eq] at hp
          exact hp hp_prime
        have hp_mem : p ∈ (divisors n).erase n := by
          rw [Finset.mem_erase, Nat.mem_divisors]
          exact ⟨by omega, hp_dvd, by omega⟩
        set m := n / p
        have hm_dvd : m ∣ n := Nat.div_dvd_of_dvd hp_dvd
        have hm_eq : n = p * m := (Nat.mul_div_cancel' hp_dvd).symm
        have hm_lt : m < n := Nat.div_lt_self (by omega) hp_prime.one_lt
        have hm_mem : m ∈ (divisors n).erase n := by
          rw [Finset.mem_erase, Nat.mem_divisors]
          exact ⟨by omega, hm_dvd, by omega⟩
        have h1_mem : 1 ∈ (divisors n).erase n := by
          rw [Finset.mem_erase, Nat.mem_divisors]
          exact ⟨by omega, Nat.one_dvd n, by omega⟩
        rw [a_eq_n_sub_sum n (by omega)] at h
        have h_sum_eq : ((divisors n).erase n).sum (fun d => (ArithmeticFunction.sigma 1 d : ℤ) - d) = n - 1 := by
          omega
        by_cases h_eq : p = m
        · exfalso; exact lemma_p_eq_m n p m (by omega) hp_prime hm_eq h_eq h_sum_eq
        · -- Case p < m (since p ≤ m)
          have hm_pos : m > 0 := by
            by_contra h_zero
            have : m = 0 := Nat.le_zero.mp (Nat.le_of_not_gt h_zero)
            rw [this] at hm_eq
            rw [mul_zero] at hm_eq
            omega
          have hm_gt1 : m > 1 := by
            by_contra h_mc
            have : m = 1 := Nat.le_antisymm (Nat.le_of_not_gt h_mc) hm_pos
            rw [this] at hm_eq
            rw [mul_one] at hm_eq
            rw [hm_eq] at hp
            exact hp hp_prime
          have hp_lt_m : p < m := by
            have : p ≤ m := by
              have hp_le_min_m : p ≤ minFac m := by
                have h_min_prime : (minFac m).Prime := minFac_prime (by omega)
                have h_min_dvd : minFac m ∣ n := dvd_trans (minFac_dvd m) hm_dvd
                exact minFac_le_of_dvd h_min_prime.two_le h_min_dvd
              have h_min_le_m : minFac m ≤ m := Nat.minFac_le hm_pos
              omega
            omega
          -- Since p < m, we have {1, p, m} is a subset of (divisors n).erase n.
          have h_subset3 : ({1, p, m} : Finset ℕ) ⊆ (divisors n).erase n := by
            intro x hx
            rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with (rfl | rfl | rfl)
            · exact h1_mem
            · exact hp_mem
            · exact hm_mem
          -- So the sum is at least the sum over {1, p, m}.
          have h_sum_ge : ((divisors n).erase n).sum (fun d => (ArithmeticFunction.sigma 1 d : ℤ) - d) ≥
              ({1, p, m} : Finset ℕ).sum (fun d => (ArithmeticFunction.sigma 1 d : ℤ) - d) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg h_subset3
            intro x _ _
            exact sigma_sub_self_nonneg x
          -- Evaluate the sum over {1, p, m}
          have hp_ne1 : 1 ≠ p := hp_prime.ne_one.symm
          have hm_ne1 : 1 ≠ m := hm_gt1.ne
          have hp_ne_m : p ≠ m := h_eq
          have h_sum3 : ({1, p, m} : Finset ℕ).sum (fun d => (ArithmeticFunction.sigma 1 d : ℤ) - d) =
              ((ArithmeticFunction.sigma 1 1 : ℤ) - (1 : ℤ)) + ((ArithmeticFunction.sigma 1 p : ℤ) - (p : ℤ)) +
              ((ArithmeticFunction.sigma 1 m : ℤ) - (m : ℤ)) := by
            have h1 : 1 ∉ (insert p {m} : Finset ℕ) := by
              simp [hp_ne1, hm_ne1]
            have h2 : p ∉ ({m} : Finset ℕ) := by
              simp [hp_ne_m]
            rw [Finset.sum_insert h1]
            rw [Finset.sum_insert h2]
            simp
          have h_sigma1_1 : (ArithmeticFunction.sigma 1 1 : ℤ) = 1 := rfl
          have h_sigma1_p : (ArithmeticFunction.sigma 1 p : ℤ) = p + 1 := by
            rw [ArithmeticFunction.sigma_apply]
            have h_sum_pow : (∑ c ∈ divisors p, (c : ℤ) ^ 1) = ∑ c ∈ divisors p, (c : ℤ) := by
              apply Finset.sum_congr rfl
              intro x _
              ring
            push_cast
            rw [h_sum_pow]
            rw [hp_prime.divisors]
            rw [Finset.sum_pair (by omega)]
            ring
          have h_sigma_m_ge : (ArithmeticFunction.sigma 1 m : ℤ) - m ≥ 1 := by
            -- since m > 1, 1 is a proper divisor of m
            have h1_mem_m : 1 ∈ divisors m := by
              rw [Nat.mem_divisors]
              exact ⟨Nat.one_dvd m, by omega⟩
            have hm_mem_m : m ∈ divisors m := by
              rw [Nat.mem_divisors]
              exact ⟨dvd_rfl, by omega⟩
            have h1_ne_m : 1 ≠ m := by omega
            have h_sum_pow : (∑ c ∈ divisors m, (c : ℤ) ^ 1) = ∑ c ∈ divisors m, (c : ℤ) := by
              apply Finset.sum_congr rfl
              intro x _
              ring
            have h_sub : ({1, m} : Finset ℕ) ⊆ divisors m := by
              intro x hx
              rw [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with (rfl | rfl)
              · exact h1_mem_m
              · exact hm_mem_m
            have h_ge : (∑ c ∈ divisors m, (c : ℤ)) ≥ (∑ c ∈ ({1, m} : Finset ℕ), (c : ℤ)) := by
              apply Finset.sum_le_sum_of_subset_of_nonneg h_sub
              intro x _ _
              exact Int.natCast_nonneg x
            have h_sum_pair : (∑ c ∈ ({1, m} : Finset ℕ), (c : ℤ)) = 1 + m := by
              rw [Finset.sum_pair h1_ne_m]
              ring
            have h_sigma_ge : (ArithmeticFunction.sigma 1 m : ℤ) ≥ 1 + m := by
              rw [ArithmeticFunction.sigma_apply]
              push_cast
              rw [h_sum_pow]
              omega
            omega
          by_cases hm_prime : m.Prime
          · exfalso; exact lemma_m_prime n p m (by omega) hp_prime hm_prime hm_eq hp_dvd hm_dvd h_eq hm_gt1 hp_lt hm_lt h_sigma1_p h_sum_eq
          · -- If m is composite
            set d := minFac m
            have hd_prime : d.Prime := minFac_prime (by omega)
            have hd_dvd : d ∣ m := minFac_dvd m
            have hd_ge2 : 2 ≤ d := hd_prime.two_le
            have hd_lt_m : d < m := by
              have h1 : d ≤ m := Nat.minFac_le hm_pos
              have h2 : d ≠ m := by
                intro hc
                rw [hc] at hd_prime
                exact hm_prime hd_prime
              omega
            have hd_dvd_n : d ∣ n := dvd_trans hd_dvd hm_dvd
            have hd_lt_n : d < n := lt_trans hd_lt_m hm_lt
            have hd_mem : d ∈ (divisors n).erase n := by
              rw [Finset.mem_erase, Nat.mem_divisors]
              exact ⟨by omega, hd_dvd_n, by omega⟩
            have hd_ge_p : p ≤ d := minFac_le_of_dvd hd_ge2 hd_dvd_n
            have h_pd_dvd_n : p * d ∣ n := by
              use m / d
              rw [hm_eq]
              have h_m_eq : m = d * (m / d) := (Nat.mul_div_cancel' hd_dvd).symm
              conv =>
                lhs
                arg 2
                rw [h_m_eq]
              ring
            have h_pd_lt_n : p * d < n := by
              rw [hm_eq]
              have hp_pos : 0 < p := Nat.zero_lt_two.trans_le hp_prime.two_le
              exact Nat.mul_lt_mul_of_pos_left hd_lt_m hp_pos
            have h_pd_mem : p * d ∈ (divisors n).erase n := by
              rw [Finset.mem_erase, Nat.mem_divisors]
              exact ⟨by omega, h_pd_dvd_n, by omega⟩
            by_cases hp_d : p = d
            · -- Case p = d
              have h_p_dvd_m : p ∣ m := by
                rw [← hp_d] at hd_dvd
                exact hd_dvd
              set k := m / p
              have hk_eq : m = p * k := (Nat.mul_div_cancel' h_p_dvd_m).symm
              by_cases hp2_eq_m : p^2 = m
              · exfalso; exact lemma_p_eq_d_m_eq_p2 n p m (by omega) hp_prime hm_eq hp2_eq_m h_sigma1_p h_sum_eq
              have hk_dvd_m : k ∣ m := by
                use p
                rw [hk_eq]
                ring
              exfalso; exact lemma_p_eq_d_m_ne_p2 n p m d k (by omega) hp_prime rfl hm_prime hm_eq hp_dvd hm_dvd h_eq hm_gt1 hp_d h_p_dvd_m hk_eq hp2_eq_m h_sum_eq h_sigma1_p h1_mem hp_mem hm_mem h_pd_mem
            · -- Case p < d (so hp_d : ¬ p = d)
              have hp_lt_d : p < d := by omega
              have hp_ne_d_val : p ≠ d := by omega
              by_cases hp_2 : p = 2
              · -- Subcase p = 2
                have hd_ge3 : d ≥ 3 := by
                  have : d.Prime := hd_prime
                  have : d > 2 := by omega
                  omega
                set c := m / d
                have hc_eq : m = d * c := (Nat.mul_div_cancel' hd_dvd).symm
                by_cases hc_d : c = d
                · -- Subcase c = d, so m = d^2, n = 2 d^2
                  have hn_eq : n = p * d^2 := by
                    rw [hm_eq, hc_eq, hc_d]
                    ring
                  have h_div_all : divisors n = {1, p, d, p * d, d^2, n} := by
                    rw [hn_eq]
                    exact test_div2 p d hp_prime hd_prime hp_ne_d_val
                  have h_prop_div : (divisors n).erase n = {1, p, d, p * d, d^2} := by
                    rw [h_div_all]
                    -- since n is distinct from all of them:
                    have hn_ne1 : n ≠ 1 := by omega
                    have hn_ne_p : n ≠ p := by omega
                    have hn_ne_d : n ≠ d := by omega
                    have hn_ne_pd : n ≠ p * d := by
                      rw [hn_eq, hp_2]
                      have : d^2 > d := by nlinarith [hd_prime.two_le]
                      nlinarith
                    have hn_ne_d2 : n ≠ d^2 := by
                      rw [hn_eq]
                      have : p * d^2 > d^2 := by
                        have : p ≥ 2 := hp_prime.two_le
                        nlinarith
                      omega
                    ext x
                    simp
                    omega
                  have h_sum_val : ((divisors n).erase n).sum (fun d => (ArithmeticFunction.sigma 1 d : ℤ) - d) = p + 2 * d + 4 := by
                    rw [h_prop_div]
                    exact test_prop_sum p d hp_prime hd_prime hp_lt_d
                  have : False := by
                    rw [h_sum_val] at h_sum_eq
                    -- S = p * d^2 - 1 = p + 2d + 4
                    rw [hn_eq] at h_sum_eq
                    push_cast at h_sum_eq
                    rw [hp_2] at h_sum_eq
                    -- 2 * d^2 - 1 = 2 + 2d + 4 = 2d + 6
                    -- 2 * d^2 - 2 * d - 7 = 0
                    -- 2 * (d * (d - 1)) = 7
                    omega
                  contradiction
                · -- Subcase c > d (so c ≠ d, and we know c ≥ d, so c > d)
                  have hc_gt_d : c > d := by
                    -- since d = minFac m, every prime factor of m is ≥ d.
                    -- since c ∣ m, every prime factor of c is ≥ d.
                    -- since c > 1 (as d < m), c has some prime factor q ≥ d.
                    -- so c ≥ d.
                    -- since c ≠ d, c > d.
                    have hc_pos : c > 0 := by
                      by_contra hc_zero
                      have : c = 0 := Nat.le_zero.mp (Nat.le_of_not_gt hc_zero)
                      rw [this] at hc_eq
                      rw [mul_zero] at hc_eq
                      omega
                    have hc_gt1 : c > 1 := by
                      by_contra hc_le1
                      have : c = 1 := by omega
                      rw [this, mul_one] at hc_eq
                      rw [hc_eq] at hm_prime
                      exact hm_prime hd_prime
                    have h_q_prime : (minFac c).Prime := minFac_prime (by omega)
                    have h_q_dvd_m : minFac c ∣ m := dvd_trans (minFac_dvd c) (by rw [hc_eq]; exact ⟨d, by ring⟩)
                    have h_q_ge_d : minFac c ≥ d := minFac_le_of_dvd h_q_prime.two_le h_q_dvd_m
                    have h_le_c : minFac c ≤ c := Nat.minFac_le (by omega)
                    omega
                  have hc_ne1 : 1 ≠ c := by omega
                  have hp_ne_c : p ≠ c := by omega
                  have hd_ne_c : d ≠ c := by omega
                  have hpd_ne_c : p * d ≠ c := by
                    -- since p = 2, p * d = 2d.
                    -- we want to show 2d ≠ c.
                    -- if 2d = c, then m = d * c = 2 d^2.
                    -- but m is odd since p = 2 is the minimal prime factor of n = 2m, and n/2 = m.
                    -- wait, is m odd?
                    -- yes! Since p = 2 is the minimal prime factor of n, m = n/2 has no prime factors < 2 (which is none), and is m odd?
                    -- actually, since p is the minFac of n:
                    -- if 2 ∣ m, then 4 ∣ n.
                    -- is minFac n still 2? Yes.
                    -- wait, but d = minFac m.
                    -- if 2 ∣ m, then d = minFac m = 2.
                    -- but we have p < d, so 2 < d, which means d ≥ 3, so 2 ∤ m!
                    -- so m is indeed odd!
                    -- so c is odd!
                    -- so 2d (which is even) cannot equal c (which is odd)!
                    -- this is incredibly elegant!
                    intro h_eq
                    have hd_ge2 : d ≥ 2 := hd_prime.two_le
                    have hm_even : 2 ∣ m := by
                      use d * d
                      rw [hc_eq, ← h_eq, hp_2]
                      ring
                    have hd_le_2 : d ≤ 2 := minFac_le_of_dvd (by decide) hm_even
                    omega
                  have hc_ne_m : c ≠ m := by
                    intro hc
                    rw [hc] at hc_eq
                    have : d * m = m := hc_eq.symm
                    have : d * m = 1 * m := by
                      rw [one_mul]
                      exact this
                    have : d = 1 := Nat.eq_of_mul_eq_mul_right (by omega) this
                    exact hd_prime.ne_one this
                  have h_subset5 : ({1, p, d, p * d, c, m} : Finset ℕ) ⊆ (divisors n).erase n := by
                    intro x hx
                    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hx
                    rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl)
                    · exact h1_mem
                    · exact hp_mem
                    · exact hd_mem
                    · exact h_pd_mem
                    · rw [Finset.mem_erase, Nat.mem_divisors]
                      have hc_dvd : c ∣ n := dvd_trans (by rw [hc_eq]; exact ⟨d, by ring⟩) hm_dvd
                      have hc_lt_n : c < n := lt_trans (by rw [hc_eq]; have : d ≥ 2 := hd_prime.two_le; nlinarith) hm_lt
                      exact ⟨by omega, hc_dvd, by omega⟩
                    · exact hm_mem
                  -- Now we can show S ≥ ...
                  have h_sum_ge5 : ((divisors n).erase n).sum (fun d => (ArithmeticFunction.sigma 1 d : ℤ) - d) ≥
                      ({1, p, d, p * d, c, m} : Finset ℕ).sum (fun d => (ArithmeticFunction.sigma 1 d : ℤ) - d) := by
                    apply Finset.sum_le_sum_of_subset_of_nonneg h_subset5
                    intro x _ _
                    exact sigma_sub_self_nonneg x
                  have hd_ne_pd : d ≠ p * d := by
                    have : p * d > d := by
                      have : p ≥ 2 := hp_prime.two_le
                      nlinarith
                    omega
                  have hp_ne_pd : p ≠ p * d := by
                    have : p * d > p := by
                      have : d ≥ 2 := hd_prime.two_le
                      nlinarith
                    omega
                  have hpd_ne1 : 1 ≠ p * d := by
                    have : p * d ≥ 4 := by
                      have : p ≥ 2 := hp_prime.two_le
                      have : d ≥ 2 := hd_prime.two_le
                      nlinarith
                    omega
                  have hd_ne1 : 1 ≠ d := hd_prime.ne_one.symm
                  have hp_ne1 : 1 ≠ p := hp_prime.ne_one.symm
                  have hm_ne1 : 1 ≠ m := hm_gt1.ne
                  have hp_ne_m : p ≠ m := h_eq
                  have hd_ne_m : d ≠ m := hd_lt_m.ne
                  have hpd_ne_m : p * d ≠ m := by
                    rw [hc_eq]
                    have : p * d < d * c := by
                      have : p < c := lt_trans hp_lt_d hc_gt_d
                      nlinarith
                    omega
                  have hc_ne_m2 : c ≠ m := hc_ne_m
                  have h_sum5 : ({1, p, d, p * d, c, m} : Finset ℕ).sum (fun d => (ArithmeticFunction.sigma 1 d : ℤ) - d) =
                      ((ArithmeticFunction.sigma 1 1 : ℤ) - 1) + ((ArithmeticFunction.sigma 1 p : ℤ) - p) +
                      ((ArithmeticFunction.sigma 1 d : ℤ) - d) + ((ArithmeticFunction.sigma 1 (p * d) : ℤ) - p * d) +
                      ((ArithmeticFunction.sigma 1 c : ℤ) - c) + ((ArithmeticFunction.sigma 1 m : ℤ) - m) := by
                    have h1 : 1 ∉ (insert p (insert d (insert (p * d) (insert c {m}))) : Finset ℕ) := by
                      simp [hp_ne1, hd_ne1, hpd_ne1, hc_ne1, hm_ne1]
                    have h2 : p ∉ (insert d (insert (p * d) (insert c {m})) : Finset ℕ) := by
                      simp [hp_ne_d_val, hp_ne_pd, hp_ne_c, hp_ne_m]
                    have h3 : d ∉ (insert (p * d) (insert c {m}) : Finset ℕ) := by
                      simp [hd_ne_pd, hd_ne_c, hd_ne_m]
                    have h4 : p * d ∉ (insert c {m} : Finset ℕ) := by
                      simp [hpd_ne_c, hpd_ne_m]
                    have h5 : c ∉ ({m} : Finset ℕ) := by
                      simp [hc_ne_m2]
                    rw [Finset.sum_insert h1]
                    rw [Finset.sum_insert h2]
                    rw [Finset.sum_insert h3]
                    rw [Finset.sum_insert h4]
                    rw [Finset.sum_insert h5]
                    simp; ring
                  have h_sigma1_1 : (ArithmeticFunction.sigma 1 1 : ℤ) = 1 := rfl
                  have h_sigma1_pd : (ArithmeticFunction.sigma 1 (p * d) : ℤ) = p * d + p + d + 1 := by
                    rw [ArithmeticFunction.sigma_apply]
                    have h_sum_pow : (∑ c ∈ divisors (p * d), (c : ℤ) ^ 1) = ∑ c ∈ divisors (p * d), (c : ℤ) := by
                      apply Finset.sum_congr rfl
                      intro x _
                      ring
                    push_cast
                    rw [h_sum_pow]
                    have h_div_pd : divisors (p * d) = {1, p, d, p * d} := by
                      rw [Nat.divisors_mul, hp_prime.divisors, hd_prime.divisors]
                      ext x
                      rw [Finset.mem_mul]
                      simp
                      omega
                    rw [h_div_pd]
                    have h1 : 1 ∉ (insert p (insert d {p * d}) : Finset ℕ) := by
                      simp [hp_ne1, hd_ne1, hpd_ne1]
                    have h2 : p ∉ (insert d {p * d} : Finset ℕ) := by
                      simp [hp_ne_d_val, hp_ne_pd]
                    have h3 : d ∉ ({p * d} : Finset ℕ) := by
                      simp [hd_ne_pd]
                    rw [Finset.sum_insert h1]
                    rw [Finset.sum_insert h2]
                    rw [Finset.sum_insert h3]
                    simp
                    ring
                  have h_sigma_c_ge : (ArithmeticFunction.sigma 1 c : ℤ) - c ≥ 1 := by
                    have hc_gt1 : c > 1 := by omega
                    have h1_mem_c : 1 ∈ divisors c := by
                      rw [Nat.mem_divisors]
                      exact ⟨Nat.one_dvd c, by omega⟩
                    have hc_mem_c : c ∈ divisors c := by
                      rw [Nat.mem_divisors]
                      exact ⟨dvd_rfl, by omega⟩
                    have h1_ne_c : 1 ≠ c := by omega
                    have h_sum_pow : (∑ x ∈ divisors c, (x : ℤ) ^ 1) = ∑ x ∈ divisors c, (x : ℤ) := by
                      apply Finset.sum_congr rfl
                      intro x _
                      ring
                    have h_sub : ({1, c} : Finset ℕ) ⊆ divisors c := by
                      intro x hx
                      rw [Finset.mem_insert, Finset.mem_singleton] at hx
                      rcases hx with (rfl | rfl)
                      · exact h1_mem_c
                      · exact hc_mem_c
                    have h_ge : (∑ x ∈ divisors c, (x : ℤ)) ≥ (∑ x ∈ ({1, c} : Finset ℕ), (x : ℤ)) := by
                      apply Finset.sum_le_sum_of_subset_of_nonneg h_sub
                      intro x _ _
                      exact Int.natCast_nonneg x
                    have h_sum_pair : (∑ x ∈ ({1, c} : Finset ℕ), (x : ℤ)) = 1 + c := by
                      rw [Finset.sum_pair h1_ne_c]
                      ring
                    have h_sigma_ge : (ArithmeticFunction.sigma 1 c : ℤ) ≥ 1 + c := by
                      rw [ArithmeticFunction.sigma_apply]
                      push_cast
                      rw [h_sum_pow]
                      omega
                    omega
                  have h_sigma_m_ge_val : (ArithmeticFunction.sigma 1 m : ℤ) - m ≥ 1 + d + c := by
                    -- since m = d * c and c > d ≥ 3, {1, d, c} are 3 distinct proper divisors of m
                    have h_subset_m : ({1, d, c} : Finset ℕ) ⊆ (divisors m).erase m := by
                      intro x hx
                      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hx
                      rcases hx with (rfl | rfl | rfl)
                      · rw [Finset.mem_erase, Nat.mem_divisors]
                        exact ⟨by omega, Nat.one_dvd _, by omega⟩
                      · rw [Finset.mem_erase, Nat.mem_divisors]
                        exact ⟨by omega, hd_dvd, by omega⟩
                      · rw [Finset.mem_erase, Nat.mem_divisors]
                        exact ⟨by omega, (by rw [hc_eq]; exact dvd_mul_left c d), by omega⟩
                    have h_sum_m : ({1, d, c} : Finset ℕ).sum (fun x => (x : ℤ)) = 1 + d + c := by
                      have h1 : 1 ∉ (insert d {c} : Finset ℕ) := by
                        simp [hd_ne1, hc_ne1]
                      have h2 : d ∉ ({c} : Finset ℕ) := by
                        simp [hd_ne_c]
                      rw [Finset.sum_insert h1]
                      rw [Finset.sum_insert h2]
                      simp
                      ring
                    rw [ArithmeticFunction.sigma_apply]
                    have h_sum_pow : (∑ c ∈ divisors m, (c : ℤ) ^ 1) = ∑ c ∈ divisors m, (c : ℤ) := by
                      apply Finset.sum_congr rfl
                      intro x _
                      ring
                    push_cast
                    rw [h_sum_pow]
                    have h_div_m : divisors m = insert m ((divisors m).erase m) := by
                      rw [Finset.insert_erase]
                      rw [Nat.mem_divisors]
                      exact ⟨dvd_rfl, by omega⟩
                    have h_not_mem_m : m ∉ (divisors m).erase m := by simp
                    rw [h_div_m, Finset.sum_insert h_not_mem_m]
                    have h_le : (∑ c ∈ (divisors m).erase m, (c : ℤ)) ≥ (∑ c ∈ ({1, d, c} : Finset ℕ), (c : ℤ)) := by
                      apply Finset.sum_le_sum_of_subset_of_nonneg h_subset_m
                      intro x _ _
                      exact Int.natCast_nonneg x
                    rw [h_sum_m] at h_le
                    omega
                  have : False := by
                    have h_sum_eq_val : ((divisors n).erase n).sum (fun d => (ArithmeticFunction.sigma 1 d : ℤ) - d) = 2 * (c * d) - 1 := by
                      rw [h_sum_eq, hm_eq, hc_eq, hp_2]
                      push_cast; ring
                    have h_ge_val : ((divisors n).erase n).sum (fun d => (ArithmeticFunction.sigma 1 d : ℤ) - d) ≥ 1 + (p + d + 1) + 1 + (1 + d + c) := by
                      rw [h_sum5] at h_sum_ge5
                      rw [h_sigma1_1, h_sigma1_p, h_sigma1_pd] at h_sum_ge5
                      have h_sigma_m_ge_val_c : (ArithmeticFunction.sigma 1 m : ℤ) - m ≥ 1 + d + c := h_sigma_m_ge_val
                      have h_sigma_c_ge_c : (ArithmeticFunction.sigma 1 c : ℤ) - c ≥ 1 := h_sigma_c_ge
                      have h_sigma_d_ge_c : (ArithmeticFunction.sigma 1 d : ℤ) - d ≥ 0 := sigma_sub_self_nonneg d
                      omega
                    exact lemma_p_2_c_gt_d_contradiction p d c _ h_sum_eq_val h_ge_val (by exact_mod_cast hp_2) (by exact_mod_cast hd_ge3) (by exact_mod_cast hc_gt_d)
                  contradiction
              · -- Subcase p ≥ 3 (so hp_2 : ¬ p = 2)
                have hp_ge3 : p ≥ 3 := by
                  have : p ≥ 2 := hp_prime.two_le
                  omega
                have hd_ge5 : d ≥ 5 := by
                  have hd_ge2 : d ≥ 2 := hd_prime.two_le
                  by_contra h_lt
                  have : d = 4 := by omega
                  have : ¬ d.Prime := by rw [this]; decide
                  exact this hd_prime
                set c := m / d
                have hc_eq : m = d * c := (Nat.mul_div_cancel' hd_dvd).symm
                have hc_ge_d : c ≥ d := by
                  -- since d = minFac m, every prime factor of m is ≥ d.
                  -- since c ∣ m, every prime factor of c is ≥ d.
                  -- since c > 1 (as d < m), c has some prime factor q ≥ d.
                  -- so c ≥ d.
                  have hc_pos : c > 0 := by
                    by_contra hc_zero
                    have : c = 0 := Nat.le_zero.mp (Nat.le_of_not_gt hc_zero)
                    rw [this] at hc_eq
                    rw [mul_zero] at hc_eq
                    omega
                  have hc_gt1 : c > 1 := by
                    by_contra hc_le1
                    have : c = 1 := by omega
                    rw [this, mul_one] at hc_eq
                    rw [hc_eq] at hm_prime
                    exact hm_prime hd_prime
                  have h_q_prime : (minFac c).Prime := minFac_prime (by omega)
                  have h_q_dvd_m : minFac c ∣ m := dvd_trans (minFac_dvd c) (by rw [hc_eq]; exact ⟨d, by ring⟩)
                  have h_q_ge_d : minFac c ≥ d := minFac_le_of_dvd h_q_prime.two_le h_q_dvd_m
                  have h_le_c : minFac c ≤ c := Nat.minFac_le (by omega)
                  omega
                have h_subset5 : ({1, p, d, p * d, m} : Finset ℕ) ⊆ (divisors n).erase n := by
                  intro x hx
                  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hx
                  rcases hx with (rfl | rfl | rfl | rfl | rfl)
                  · exact h1_mem
                  · exact hp_mem
                  · exact hd_mem
                  · exact h_pd_mem
                  · exact hm_mem
                have h_sum_ge5 : ((divisors n).erase n).sum (fun d => (ArithmeticFunction.sigma 1 d : ℤ) - d) ≥
                    ({1, p, d, p * d, m} : Finset ℕ).sum (fun d => (ArithmeticFunction.sigma 1 d : ℤ) - d) := by
                  apply Finset.sum_le_sum_of_subset_of_nonneg h_subset5
                  intro x _ _
                  exact sigma_sub_self_nonneg x
                have hd_ne_pd : d ≠ p * d := by
                  have : p * d > d := by
                    have : p ≥ 2 := hp_prime.two_le
                    nlinarith
                  omega
                have hp_ne_pd : p ≠ p * d := by
                  have : p * d > p := by
                    have : d ≥ 2 := hd_prime.two_le
                    nlinarith
                  omega
                have hpd_ne1 : 1 ≠ p * d := by
                  have : p * d ≥ 4 := by
                    have : p ≥ 2 := hp_prime.two_le
                    have : d ≥ 2 := hd_prime.two_le
                    nlinarith
                  omega
                have hd_ne1 : 1 ≠ d := hd_prime.ne_one.symm
                have hp_ne1 : 1 ≠ p := hp_prime.ne_one.symm
                have hm_ne1 : 1 ≠ m := hm_gt1.ne
                have hp_ne_m : p ≠ m := h_eq
                have hd_ne_m : d ≠ m := hd_lt_m.ne
                have hpd_ne_m : p * d ≠ m := by
                  rw [hc_eq]
                  have : p < c := by omega
                  nlinarith
                have h_sum5 : ({1, p, d, p * d, m} : Finset ℕ).sum (fun d => (ArithmeticFunction.sigma 1 d : ℤ) - d) =
                    ((ArithmeticFunction.sigma 1 1 : ℤ) - 1) + ((ArithmeticFunction.sigma 1 p : ℤ) - p) +
                    ((ArithmeticFunction.sigma 1 d : ℤ) - d) + ((ArithmeticFunction.sigma 1 (p * d) : ℤ) - p * d) +
                    ((ArithmeticFunction.sigma 1 m : ℤ) - m) := by
                  have h1 : 1 ∉ (insert p (insert d (insert (p * d) {m})) : Finset ℕ) := by
                    simp [hp_ne1, hd_ne1, hpd_ne1, hm_ne1]
                  have h2 : p ∉ (insert d (insert (p * d) {m}) : Finset ℕ) := by
                    simp [hp_ne_d_val, hp_ne_pd, hp_ne_m]
                  have h3 : d ∉ (insert (p * d) {m} : Finset ℕ) := by
                    simp [hd_ne_pd, hd_ne_m]
                  have h4 : p * d ∉ ({m} : Finset ℕ) := by
                    simp [hpd_ne_m]
                  rw [Finset.sum_insert h1]
                  rw [Finset.sum_insert h2]
                  rw [Finset.sum_insert h3]
                  rw [Finset.sum_insert h4]
                  simp; ring
                have h_sigma1_1 : (ArithmeticFunction.sigma 1 1 : ℤ) = 1 := rfl
                have h_sigma1_pd : (ArithmeticFunction.sigma 1 (p * d) : ℤ) = p * d + p + d + 1 := by
                  rw [ArithmeticFunction.sigma_apply]
                  have h_sum_pow : (∑ c ∈ divisors (p * d), (c : ℤ) ^ 1) = ∑ c ∈ divisors (p * d), (c : ℤ) := by
                    apply Finset.sum_congr rfl
                    intro x _
                    ring
                  push_cast
                  rw [h_sum_pow]
                  have h_div_pd : divisors (p * d) = {1, p, d, p * d} := by
                    rw [Nat.divisors_mul, hp_prime.divisors, hd_prime.divisors]
                    ext x
                    rw [Finset.mem_mul]
                    simp
                    omega
                  rw [h_div_pd]
                  have h1 : 1 ∉ (insert p (insert d {p * d}) : Finset ℕ) := by
                    simp [hp_ne1, hd_ne1, hpd_ne1]
                  have h2 : p ∉ (insert d {p * d} : Finset ℕ) := by
                    simp [hp_ne_d_val, hp_ne_pd]
                  have h3 : d ∉ ({p * d} : Finset ℕ) := by
                    simp [hd_ne_pd]
                  rw [Finset.sum_insert h1]
                  rw [Finset.sum_insert h2]
                  rw [Finset.sum_insert h3]
                  simp
                  ring
                have h_sigma_m_ge_val : (ArithmeticFunction.sigma 1 m : ℤ) - m ≥ 1 + d := by
                  -- m = d * c and c ≥ d ≥ 5, so {1, d} are 2 distinct proper divisors of m
                  have h_subset_m : ({1, d} : Finset ℕ) ⊆ (divisors m).erase m := by
                    intro x hx
                    rw [Finset.mem_insert, Finset.mem_singleton] at hx
                    rcases hx with (rfl | rfl)
                    · rw [Finset.mem_erase, Nat.mem_divisors]
                      exact ⟨by omega, Nat.one_dvd _, by omega⟩
                    · rw [Finset.mem_erase, Nat.mem_divisors]
                      exact ⟨by omega, hd_dvd, by omega⟩
                  have h_sum_m : ({1, d} : Finset ℕ).sum (fun x => (x : ℤ)) = 1 + d := by
                    rw [Finset.sum_pair hd_ne1]
                    ring
                  rw [ArithmeticFunction.sigma_apply]
                  have h_sum_pow : (∑ c ∈ divisors m, (c : ℤ) ^ 1) = ∑ c ∈ divisors m, (c : ℤ) := by
                    apply Finset.sum_congr rfl
                    intro x _
                    ring
                  push_cast
                  rw [h_sum_pow]
                  have h_div_m : divisors m = insert m ((divisors m).erase m) := by
                    rw [Finset.insert_erase]
                    rw [Nat.mem_divisors]
                    exact ⟨dvd_rfl, by omega⟩
                  have h_not_mem_m : m ∉ (divisors m).erase m := by simp
                  rw [h_div_m, Finset.sum_insert h_not_mem_m]
                  have h_le : (∑ c ∈ (divisors m).erase m, (c : ℤ)) ≥ (∑ c ∈ ({1, d} : Finset ℕ), (c : ℤ)) := by
                    apply Finset.sum_le_sum_of_subset_of_nonneg h_subset_m
                    intro x _ _
                    exact Int.natCast_nonneg x
                  rw [h_sum_m] at h_le
                  omega
                have : False := by
                  have h_sum_eq_val : ((divisors n).erase n).sum (fun d => (ArithmeticFunction.sigma 1 d : ℤ) - d) = (p : ℤ) * (c * d) - 1 := by
                    rw [h_sum_eq, hm_eq, hc_eq]
                    push_cast; ring
                  have h_ge_val : ((divisors n).erase n).sum (fun d => (ArithmeticFunction.sigma 1 d : ℤ) - d) ≥ 1 + (p + d + 1) + (1 + d) := by
                    rw [h_sum5] at h_sum_ge5
                    rw [h_sigma1_1, h_sigma1_p, h_sigma1_pd] at h_sum_ge5
                    have h_sigma_m_ge_val_c : (ArithmeticFunction.sigma 1 m : ℤ) - m ≥ 1 + d := h_sigma_m_ge_val
                    have h_sigma_d_ge_c : (ArithmeticFunction.sigma 1 d : ℤ) - d ≥ 0 := sigma_sub_self_nonneg d
                    omega
                  exact lemma_p_ge_3_contradiction p d c _ h_sum_eq_val h_ge_val (by exact_mod_cast hp_ge3) (by exact_mod_cast hd_ge5) (by exact_mod_cast hc_ge_d) (by exact_mod_cast hp_lt_d)
                contradiction

  · rintro (rfl | rfl)
    · rfl
    · rfl


#print axioms oeis_296075_conjecture_0
