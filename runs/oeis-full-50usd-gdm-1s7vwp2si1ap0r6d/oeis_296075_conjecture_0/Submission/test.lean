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
  have h_sigma1 : (ArithmeticFunction.sigma 1 1 : ℤ) = 1 := by
    -- ArithmeticFunction.sigma 1 1 = 1
    rfl
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

#check Nat.dvd_prime_pow


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
        · -- Case p = m: n = p^2.
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
        · -- Case p < m (since p ≤ m)
          have hm_pos : m > 0 := by
            by_contra h_zero
            have : m = 0 := Nat.le_zero.mp (Nat.le_of_not_lt h_zero)
            rw [this] at hm_eq
            rw [mul_zero] at hm_eq
            omega
          have hm_gt1 : m > 1 := by
            by_contra h_mc
            have : m = 1 := Nat.le_antisymm (Nat.le_of_not_lt h_mc) hm_pos
            rw [this] at hm_eq
            rw [mul_one] at hm_eq
            omega
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
          · -- If m is prime, then (divisors n).erase n = {1, p, m}
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
            · -- Subcase m = p^2, so n = p^3
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
                have h_div_p2 : divisors (p^2) = {1, p, p^2} := by
                  ext x
                  simp only [Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton]
                  constructor
                  · intro h_dvd
                    obtain ⟨hx_dvd, _⟩ := h_dvd
                    rw [Nat.dvd_prime_pow hp_prime] at hx_dvd
                    obtain ⟨j, hk_le, rfl⟩ := hx_dvd
                    interval_cases j
                    · left; rfl
                    · right; left; ring
                    · right; right; ring
                  · rintro (rfl | rfl | rfl)
                    · exact ⟨Nat.one_dvd _, by omega⟩
                    · exact ⟨dvd_pow_self _ (by omega), by omega⟩
                    · exact ⟨dvd_rfl, by omega⟩
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
                push_cast at h_sum_eq
                rw [h_sum_eq_val] at h_sum_le
                omega
              have : False := by
                have : (p : ℤ)^3 ≥ 49 * p := by
                  exact_mod_cast hp3_ge
                omega
              contradiction
            have hk_dvd_m : k ∣ m := by
              use p
              rw [hk_eq]
              ring
            have hk_dvd_n : k ∣ n := dvd_trans hk_dvd_m hm_dvd
            have hk_gt1 : k > 1 := by
              by_contra h_kc
              have : k = 1 := by omega
              rw [this, mul_one] at hk_eq
              rw [hk_eq] at hm_prime
              exact hm_prime hp_prime
            have hk_ne_p : k ≠ p := by
              by_contra h_kc
              rw [h_kc, ← sq] at hk_eq
              exact hp2_eq_m hk_eq
            have hk_ge_p : p ≤ k := by
              have hk_ge2 : 2 ≤ k := by omega
              have hk_prime_fac : (minFac k).Prime := minFac_prime (by omega)
              have hk_fac_dvd_n : minFac k ∣ n := dvd_trans (minFac_dvd k) hk_dvd_n
              have hp_le_fac := minFac_le_of_dvd hk_prime_fac.two_le hk_fac_dvd_n
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
              have : p = 1 := by
                exact Nat.eq_of_mul_eq_mul_right (by omega) this
              exact hp_prime.ne_one this
            have h_sum_m : (∑ c ∈ ({1, p, k, m} : Finset ℕ), (c : ℤ)) = 1 + p + k + m := by
              have hp_ne1 : 1 ≠ p := hp_prime.ne_one.symm
              have hk_ne1 : 1 ≠ k := hk_gt1.ne
              have hm_ne1 : 1 ≠ m := hm_gt1.ne
              have hp_ne_k : p ≠ k := hk_ne_p.symm
              have hp_ne_m : p ≠ m := h_eq
              have hk_ne_m : k ≠ m := hk_ne_m
              have h1 : 1 ∉ (insert p (insert k {m}) : Finset ℕ) := by
                simp [hp_ne1, hk_ne1.symm, hm_ne1.symm]
              have h2 : p ∉ (insert k {m} : Finset ℕ) := by
                simp [hp_ne_k, hp_ne_m]
              have h3 : k ∉ ({m} : Finset ℕ) := by
                simp [hk_ne_m]
              rw [Finset.sum_insert h1]
              rw [Finset.sum_insert h2]
              rw [Finset.sum_insert h3]
              simp
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
              · rw [← hp_d]
                exact h_pd_mem
            have hp_ne_p2 : p ≠ p^2 := by
              have : p^2 > p := by nlinarith
              omega
            have hp2_ne1 : p^2 ≠ 1 := by
              have : p^2 ≥ 4 := by
                have : p ≥ 2 := hp_prime.two_le
                nlinarith
              omega
            have hm_ne_p2 : m ≠ p^2 := hp2_ne_m.symm
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
                simp [hp_ne1, hm_ne1, hp2_ne1.symm]
              have h2 : p ∉ (insert m {p^2} : Finset ℕ) := by
                simp [hp_ne_m, hp_ne_p2]
              have h3 : m ∉ ({p^2} : Finset ℕ) := by
                simp [hm_ne_p2]
              rw [Finset.sum_insert h1]
              rw [Finset.sum_insert h2]
              rw [Finset.sum_insert h3]
              simp
            have h_sigma1_p2 : (ArithmeticFunction.sigma 1 (p^2) : ℤ) = p^2 + p + 1 := by
              rw [ArithmeticFunction.sigma_apply]
              have h_sum_pow : (∑ c ∈ divisors (p^2), (c : ℤ) ^ 1) = ∑ c ∈ divisors (p^2), (c : ℤ) := by
                apply Finset.sum_congr rfl
                intro x _
                ring
              push_cast
              rw [h_sum_pow]
              have h_div_p2 : divisors (p^2) = {1, p, p^2} := by
                ext x
                simp only [Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton]
                constructor
                · intro h_dvd
                  obtain ⟨hx_dvd, _⟩ := h_dvd
                  rw [Nat.dvd_prime_pow hp_prime] at hx_dvd
                  obtain ⟨j, hk_le, rfl⟩ := hx_dvd
                  interval_cases j
                  · left; rfl
                  · right; left; ring
                  · right; right; ring
                · rintro (rfl | rfl | rfl)
                  · exact ⟨Nat.one_dvd _, by omega⟩
                  · exact ⟨dvd_pow_self _ (by omega), by omega⟩
                  · exact ⟨dvd_rfl, by omega⟩
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
              push_cast at h_sum_eq
              have h_sum_ge5 : sum ≥ 3 * p + k + 3 := by
                omega
              have hp_ge2 : p ≥ 2 := hp_prime.two_le
              have hk_ge_p1 : k ≥ p + 1 := by omega
              nlinarith
            contradiction
          · sorry


  · rintro (rfl | rfl)
    · rfl
    · rfl
