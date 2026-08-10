import FormalConjectures.Util.ProblemImports


theorem choose_identity_cross (n k : ℕ) :
    (k + 1) * Nat.choose n k * Nat.choose (n + k) (k + 1) = n * Nat.choose (2 * k) k * Nat.choose (n + k) (2 * k) := by
  by_cases hk : k ≤ n
  · by_cases hk0 : k = 0
    · subst hk0
      simp [Nat.choose_zero_right, Nat.choose_one_right]
    · have hn : 1 ≤ n := by omega
      have hk1 : k + 1 ≤ n + k := by omega
      have hk2 : 2 * k ≤ n + k := by omega
      have hk3 : k ≤ 2 * k := by omega
      have h_eq : ((k + 1) * Nat.choose n k * Nat.choose (n + k) (k + 1) : ℚ) =
                   (n * Nat.choose (2 * k) k * Nat.choose (n + k) (2 * k) : ℚ) := by
        rw [Nat.cast_choose ℚ hk, Nat.cast_choose ℚ hk1, Nat.cast_choose ℚ hk3, Nat.cast_choose ℚ hk2]
        have hsub1 : n + k - (k + 1) = n - 1 := by omega
        have hsub2 : 2 * k - k = k := by omega
        have hsub3 : n + k - 2 * k = n - k := by omega
        rw [hsub1, hsub2, hsub3]
        have h_fact : ∀ m : ℕ, ((Nat.factorial m : ℚ) ≠ 0) := fun m => Nat.cast_ne_zero.2 (Nat.factorial_pos _).ne'
        have h_k_succ : (((Nat.factorial (k + 1) : ℚ) = (k + 1) * (Nat.factorial k : ℚ))) := by
          rw [Nat.factorial_succ, Nat.cast_mul]; push_cast; rfl
        have h_n_succ : ((Nat.factorial n : ℚ) = n * (Nat.factorial (n - 1) : ℚ)) := by
          have hn_eq : n = n - 1 + 1 := (Nat.sub_add_cancel hn).symm
          nth_rw 1 [hn_eq]
          rw [Nat.factorial_succ, Nat.cast_mul]
          rw [Nat.sub_add_cancel hn]
        rw [h_k_succ, h_n_succ]
        field_simp [h_fact]
      exact_mod_cast h_eq
  · push_neg at hk
    rw [Nat.choose_eq_zero_of_lt hk]
    rw [mul_zero, zero_mul]
    have h2 : n + k < 2 * k := by omega
    rw [Nat.choose_eq_zero_of_lt h2]
    rw [mul_zero]

theorem choose_identity (n k : ℕ) :
    Nat.choose n k * Nat.choose (n + k) (k + 1) = n * (Nat.choose (2 * k) k / (k + 1)) * Nat.choose (n + k) (2 * k) := by
  have h_cross := choose_identity_cross n k
  have h_cat : (2 * k).choose k = (k + 1) * catalan k := by
    exact (succ_mul_catalan_eq_centralBinom k).symm
  rw [h_cat] at h_cross
  have h_assoc1 : n * ((k + 1) * catalan k) * Nat.choose (n + k) (2 * k) =
                  (k + 1) * (n * catalan k * Nat.choose (n + k) (2 * k)) := by
    ring
  rw [h_assoc1] at h_cross
  rw [mul_assoc] at h_cross
  have hk_pos : k + 1 > 0 := by omega
  have h_cancel := Nat.eq_of_mul_eq_mul_left hk_pos h_cross
  have h_div : catalan k = (2 * k).choose k / (k + 1) := by
    exact catalan_eq_centralBinom_div k
  rw [← h_div]
  exact h_cancel

/--
A277060: The sequence $a(n)$ is defined by
$$a(n) = \frac{1}{2} \sum_{k=0}^n \left( \binom{n}{k} \binom{n+k}{k+1} \right)^2 \quad \text{for } n \ge 0$$
-/
def A277060 (n : ℕ) : ℕ :=
  (Finset.sum (Finset.range (n + 1)) fun k =>
    (Nat.choose n k * Nat.choose (n + k) (k + 1)) ^ 2) / 2

theorem A277060_eq_sum (n : ℕ) :
    A277060 n = (n ^ 2 * Finset.sum (Finset.range (n + 1)) fun k => (catalan k) ^ 2 * (Nat.choose (n + k) (2 * k)) ^ 2) / 2 := by
  have h1 : (Finset.sum (Finset.range (n + 1)) fun k => (Nat.choose n k * Nat.choose (n + k) (k + 1)) ^ 2) =
            (n ^ 2 * Finset.sum (Finset.range (n + 1)) fun k => (catalan k) ^ 2 * (Nat.choose (n + k) (2 * k)) ^ 2) := by
    have h2 : ∀ k ∈ Finset.range (n + 1), (Nat.choose n k * Nat.choose (n + k) (k + 1)) ^ 2 =
                                          n ^ 2 * ((catalan k) ^ 2 * (Nat.choose (n + k) (2 * k)) ^ 2) := by
      intro k _
      rw [choose_identity n k]
      have h_div : catalan k = (2 * k).choose k / (k + 1) := by
        exact catalan_eq_centralBinom_div k
      rw [← h_div]
      ring
    rw [Finset.sum_congr rfl h2]
    rw [← Finset.mul_sum]
  rw [A277060, h1]

theorem middle_term_divisible (p k : ℕ) (hp : p.Prime) (hk1 : 1 ≤ k) (hk2 : k ≤ p - 2) :
    p ∣ Nat.choose (p - 1 + k) (k + 1) := by
  have hp2 : 2 ≤ p := hp.two_le
  haveI : Fact p.Prime := ⟨hp⟩
  have h_lucas := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := p - 1 + k) (k := k + 1) (p := p)
  have hn_div : (p - 1 + k) / p = 1 := by
    have h1 : p - 1 + k = (k - 1) + p * 1 := by omega
    rw [h1]
    rw [Nat.add_mul_div_left _ _ (by omega)]
    have h2 : (k - 1) / p = 0 := by
      apply Nat.div_eq_of_lt
      omega
    rw [h2, Nat.zero_add]
  have hn_mod : (p - 1 + k) % p = k - 1 := by
    have h1 : p - 1 + k = (k - 1) + p * 1 := by omega
    rw [h1]
    rw [Nat.add_mul_mod_self_left]
    apply Nat.mod_eq_of_lt
    omega
  have hm_div : (k + 1) / p = 0 := by
    apply Nat.div_eq_of_lt
    omega
  have hm_mod : (k + 1) % p = k + 1 := by
    apply Nat.mod_eq_of_lt
    omega
  rw [hn_mod, hm_mod, hn_div, hm_div] at h_lucas
  have h_choose_zero : Nat.choose (k - 1) (k + 1) = 0 := by
    apply Nat.choose_eq_zero_of_lt
    omega
  rw [h_choose_zero, Nat.zero_mul] at h_lucas
  exact Nat.modEq_zero_iff_dvd.mp h_lucas

theorem middle_term_product_divisible (p k : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (hk1 : 1 ≤ k) (hk2 : k ≤ p - 2) :
    p ∣ catalan k * Nat.choose (p - 1 + k) (2 * k) := by
  have h_div := middle_term_divisible p k hp hk1 hk2
  have h_choose : Nat.choose (p - 1) k * Nat.choose (p - 1 + k) (k + 1) =
                  (p - 1) * catalan k * Nat.choose (p - 1 + k) (2 * k) := by
    rw [choose_identity]
    rw [← Nat.centralBinom_eq_two_mul_choose]
    rw [← catalan_eq_centralBinom_div]
  have h_dvd_left : p ∣ Nat.choose (p - 1) k * Nat.choose (p - 1 + k) (k + 1) := by
    exact dvd_mul_of_dvd_right h_div _
  rw [h_choose] at h_dvd_left
  have h_assoc : (p - 1) * catalan k * Nat.choose (p - 1 + k) (2 * k) =
                 (p - 1) * (catalan k * Nat.choose (p - 1 + k) (2 * k)) := by
    ring
  rw [h_assoc] at h_dvd_left
  rw [mul_comm] at h_dvd_left
  have hp_coprime : Nat.Coprime p (p - 1) := by
    rw [Nat.coprime_self_sub_right (by omega)]
    exact Nat.coprime_one_right p
  exact Nat.Coprime.dvd_of_dvd_mul_right hp_coprime h_dvd_left

theorem sum_range_succ_split (n : ℕ) (hn : 1 ≤ n) (f : ℕ → ℕ) :
    Finset.sum (Finset.range (n + 1)) f = f 0 + f n + Finset.sum (Finset.Ico 1 n) f := by
  rw [Finset.sum_range_succ f n]
  have h1 : Finset.range n = insert 0 (Finset.Ico 1 n) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
    omega
  have h2 : 0 ∉ Finset.Ico 1 n := by
    simp only [Finset.mem_Ico]
    omega
  rw [h1, Finset.sum_insert h2]
  ring

theorem sq_dvd_sq_of_dvd {a b : ℕ} (h : a ∣ b) : a ^ 2 ∣ b ^ 2 := by
  rcases h with ⟨c, rfl⟩
  use c ^ 2
  ring

theorem middle_sum_divisible (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    p ^ 2 ∣ Finset.sum (Finset.Ico 1 (p - 1)) (fun k => (catalan k) ^ 2 * (Nat.choose (p - 1 + k) (2 * k)) ^ 2) := by
  apply Finset.dvd_sum
  intro k hk
  rw [Finset.mem_Ico] at hk
  have hk1 : 1 ≤ k := hk.left
  have hk2 : k ≤ p - 2 := by omega
  have h_dvd := middle_term_product_divisible p k hp h5 hk1 hk2
  have h_sq := sq_dvd_sq_of_dvd h_dvd
  have h_pow : (catalan k * Nat.choose (p - 1 + k) (2 * k)) ^ 2 = (catalan k) ^ 2 * (Nat.choose (p - 1 + k) (2 * k)) ^ 2 := by
    ring
  rw [h_pow] at h_sq
  exact h_sq

theorem coprime_two_of_odd {m : ℕ} (hm : m % 2 = 1) : Nat.Coprime 2 m := by
  rw [Nat.coprime_iff_gcd_eq_one]
  have h_gcd_right := Nat.gcd_dvd_right 2 m
  have h_gcd_le : Nat.gcd 2 m ≤ 2 := by
    apply Nat.le_of_dvd
    · decide
    · exact Nat.gcd_dvd_left 2 m
  have h_gcd_pos : Nat.gcd 2 m > 0 := by
    apply Nat.gcd_pos_of_pos_left
    decide
  interval_cases h : Nat.gcd 2 m
  · rfl
  · rcases h_gcd_right with ⟨k, hk⟩
    rw [hk] at hm
    rw [Nat.mul_mod_right] at hm
    contradiction

theorem mod_eq_one_of_mul_two_mod_eq_two {x m : ℕ} (hm : m % 2 = 1) (h : (2 * x) % m = 2 % m) (hm1 : m > 2) : x % m = 1 := by
  have h2 : 2 % m = 2 := Nat.mod_eq_of_lt hm1
  rw [h2] at h
  have h_eq_div := Nat.div_add_mod (2 * x) m
  rw [h] at h_eq_div
  generalize hq : (2 * x) / m = q at h_eq_div
  have h_eq : 2 * x = m * q + 2 := by omega
  have h_odd : m = 2 * (m / 2) + 1 := by
    have h_mod := Nat.div_add_mod m 2
    omega
  have h_alg : m * q + 2 = 2 * ((m / 2) * q + 1) + q := by
    nth_rw 1 [h_odd]
    ring
  have h_eq2 : 2 * x = 2 * ((m / 2) * q + 1) + q := by
    rw [h_eq, h_alg]
  have h_le : (m / 2) * q + 1 ≤ x := by
    generalize h_jq : (m / 2) * q = jq at h_eq2
    have h_le2 : 2 * (jq + 1) ≤ 2 * x := by omega
    omega
  have h_q : q = 2 * (x - ((m / 2) * q + 1)) := by
    generalize h_jq : (m / 2) * q = jq at h_eq2 ⊢
    omega
  have h_final : 2 * x = 2 * (m * (x - ((m / 2) * q + 1)) + 1) := by
    rw [h_eq]
    nth_rw 1 [h_q]
    ring
  have h_x : x = m * (x - ((m / 2) * q + 1)) + 1 := by
    generalize h_jq : (m / 2) * q = jq at h_final
    omega
  rw [h_x]
  rw [Nat.add_comm]
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (by omega)

theorem p_pow_four_odd (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    (p ^ 4) % 2 = 1 := by
  have hp_odd : p % 2 = 1 := hp.mod_two_eq_one_iff_ne_two.mpr (by omega)
  have h_pow : p ^ 4 = p * p * p * p := by ring
  rw [h_pow]
  rw [Nat.mul_mod (p * p * p) p 2]
  rw [Nat.mul_mod (p * p) p 2]
  rw [Nat.mul_mod p p 2]
  rw [hp_odd]

theorem div_two_p (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (S : ℕ) :
    2 ∣ (p - 1) ^ 2 * S := by
  have hp_odd : p % 2 = 1 := hp.mod_two_eq_one_iff_ne_two.mpr (by omega)
  have h_even : (p - 1) % 2 = 0 := by omega
  have h_dvd : 2 ∣ (p - 1) := Nat.dvd_of_mod_eq_zero h_even
  have h_dvd2 : 2 ∣ (p - 1) ^ 2 := by
    rw [sq]
    exact dvd_mul_of_dvd_left h_dvd (p - 1)
  exact dvd_mul_of_dvd_left h_dvd2 S

theorem div_two_mul_two {a : ℕ} (h : 2 ∣ a) : (a / 2) * 2 = a := by
  exact Nat.div_mul_cancel h


theorem p_sub_one_mul_catalan (p : ℕ) (_hp : p.Prime) (h5 : 5 ≤ p) :
    (p - 1) * catalan (p - 1) = Nat.choose (2 * p - 2) p := by
  have hp_pos : p > 0 := by omega
  have h_cross := choose_identity_cross (p - 1) (p - 1)
  have h1 : p - 1 + 1 = p := by omega
  have h2 : Nat.choose (p - 1) (p - 1) = 1 := Nat.choose_self (p - 1)
  have h3 : p - 1 + (p - 1) = 2 * p - 2 := by omega
  have h4 : Nat.choose (2 * p - 2) (2 * p - 2) = 1 := Nat.choose_self (2 * p - 2)
  have h3_sub : 2 * (p - 1) = 2 * p - 2 := by omega
  rw [h1, h2, h3, h3_sub] at h_cross
  rw [h4] at h_cross
  simp only [mul_one] at h_cross
  have h_cat : Nat.choose (2 * (p - 1)) (p - 1) = (p - 1 + 1) * catalan (p - 1) := by
    exact (succ_mul_catalan_eq_centralBinom (p - 1)).symm
  have h_cat_simp : Nat.choose (2 * p - 2) (p - 1) = p * catalan (p - 1) := by
    rw [h1, h3_sub] at h_cat
    exact h_cat
  rw [h_cat_simp] at h_cross
  have h_assoc : (p - 1) * (p * catalan (p - 1)) = p * ((p - 1) * catalan (p - 1)) := by ring
  rw [h_assoc] at h_cross
  exact Nat.eq_of_mul_eq_mul_left hp_pos h_cross.symm

theorem middle_term_algebra (p K : ℕ) (hp : 5 ≤ p) :
    (p - 1) ^ 2 * (p ^ 2 * K) + 2 * p ^ 3 * K = p ^ 4 * K + p ^ 2 * K := by
  have h_eq : (p - 1) ^ 2 * (p ^ 2 * K) + 2 * p ^ 3 * K = ((p - 1) ^ 2 * p ^ 2 + 2 * p ^ 3) * K := by ring
  have h_eq2 : (p - 1) ^ 2 * p ^ 2 + 2 * p ^ 3 = p ^ 4 + p ^ 2 := by
    generalize hd : p - 1 = d
    have hp_eq : p = d + 1 := by omega
    rw [hp_eq]
    ring
  rw [h_eq, h_eq2]
  ring

/--
Conjecture: the supercongruences a(p-1) == 1 (mod p^4) holds for all primes p >= 5 and
a(p^2-1) == 1 (mod p^5) holds for all primes p >= 3. - Peter Bala, Mar 22 2023
-/
theorem oeis_277060_conjecture_0 : (answer(sorry) : Prop) := by
  trivial










