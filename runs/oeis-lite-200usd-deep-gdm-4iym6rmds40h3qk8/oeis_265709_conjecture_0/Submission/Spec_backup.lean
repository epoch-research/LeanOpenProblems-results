import FormalConjectures.Util.ProblemImports

open Nat Finset ArithmeticFunction

/--
A265709: $a(n) = \mathrm{numerator}\left(\sum_{d|n} \frac{1}{\sigma(d)}\right)$.
$\sigma(d)$ is the sum of the divisors of $d$, $\sigma(d) = \sum_{k|d} k$.
-/
def A265709 (n : ℕ) : ℕ :=
  -- The sum \sum_{d|n} 1/\sigma(d), calculated in the rational numbers ℚ.
  let sum_of_reciprocals : ℚ :=
    n.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)

  -- The numerator of the minimal representation of the rational number, converted from ℤ to ℕ.
  sum_of_reciprocals.num.toNat

theorem geom_sum_base_two (n : ℕ) :
  ∑ i ∈ range n, (2 : ℚ) ^ i = (2 : ℚ) ^ n - 1 := by
  have h := geom_sum_eq (by norm_num : (2 : ℚ) ≠ 1) n
  rw [h]
  ring

theorem sigma_one_two_pow (i : ℕ) :
  (↑((sigma 1) (2 ^ i)) : ℚ) = (2 : ℚ) ^ (i + 1) - 1 := by
  rw [sigma_one_apply_prime_pow Nat.prime_two]
  push_cast
  exact geom_sum_base_two (i + 1)

theorem S_two_pow_split (a : ℕ) :
  (range (a + 1)).sum (fun i => (1 : ℚ) / (↑((sigma 1) (2 ^ i)) : ℚ)) =
  1 + (range a).sum (fun i => (1 : ℚ) / ((2 : ℚ) ^ (i + 2) - 1)) := by
  rw [sum_range_succ']
  -- Let's do it carefully
  have h0 : (1 : ℚ) / (↑((sigma 1) (2 ^ 0)) : ℚ) = 1 := by
    simp [sigma_one]
  rw [h0]
  nth_rw 1 [add_comm]
  have h_inj (X Y : ℚ) : 1 + X = 1 + Y ↔ X = Y := by
    exact add_left_cancel_iff
  rw [h_inj]
  apply sum_congr rfl
  intro x _
  rw [sigma_one_two_pow (x + 1)]

theorem sum_term_pos (i : ℕ) :
  (0 : ℚ) < (2 : ℚ) ^ (i + 2) - 1 := by
  have : (1 : ℚ) < (2 : ℚ) ^ (i + 2) := by
    have h3 : (2 : ℚ) ^ (i + 2) ≥ 4 := by
      calc (2 : ℚ) ^ (i + 2) = 4 * 2 ^ i := by ring
      _ ≥ 4 * 1 := by
        apply mul_le_mul_of_nonneg_left
        · exact one_le_pow₀ (by norm_num : (1 : ℚ) ≤ 2)
        · norm_num
      _ = 4 := by ring
    linarith
  linarith

theorem sum_term_le_geom (i : ℕ) :
  (1 : ℚ) / ((2 : ℚ) ^ (i + 2) - 1) < (1 : ℚ) / (2 : ℚ) ^ (i + 1) := by
  have h1 : (0 : ℚ) < (2 : ℚ) ^ (i + 1) := by
    apply pow_pos
    norm_num
  have h2 : (0 : ℚ) < (2 : ℚ) ^ (i + 2) - 1 := sum_term_pos i
  rw [div_lt_div_iff₀ h2 h1]
  simp only [one_mul]
  have : (2 : ℚ) ^ (i + 2) = 2 * 2 ^ (i + 1) := by ring
  rw [this]
  have h3 : (2 : ℚ) ^ (i + 1) ≥ 2 := by
    calc (2 : ℚ) ^ (i + 1) = 2 * 2 ^ i := by ring
    _ ≥ 2 * 1 := by
      apply mul_le_mul_of_nonneg_left
      · exact one_le_pow₀ (by norm_num : (1 : ℚ) ≤ 2)
      · norm_num
    _ = 2 := by ring
  linarith

theorem geom_sum_half (a : ℕ) :
  ∑ i ∈ range a, (1 : ℚ) / (2 : ℚ) ^ (i + 1) = 1 - (1 / 2) ^ a := by
  -- rewrite (1 : ℚ) / (2 : ℚ) ^ (i + 1) to (1 / 2) * (1 / 2) ^ i
  have h1 : ∑ i ∈ range a, (1 : ℚ) / (2 : ℚ) ^ (i + 1) = ∑ i ∈ range a, (1 / 2 : ℚ) * (1 / 2 : ℚ) ^ i := by
    apply sum_congr rfl
    intro i _
    have : (2 : ℚ) ^ (i + 1) = 2 * 2 ^ i := by ring
    rw [this]
    simp [one_div]
    ring
  rw [h1]
  rw [← mul_sum]
  have h2 := geom_sum_eq (by norm_num : (1 / 2 : ℚ) ≠ 1) a
  rw [h2]
  ring

theorem geom_sum_half_lt_one (a : ℕ) :
  ∑ i ∈ range a, (1 : ℚ) / (2 : ℚ) ^ (i + 1) < 1 := by
  rw [geom_sum_half]
  have h_pos : (0 : ℚ) < (1 / 2 : ℚ) ^ a := by
    apply pow_pos
    norm_num
  linarith

theorem sum_term_lt_one (a : ℕ) :
  ∑ i ∈ range a, (1 : ℚ) / ((2 : ℚ) ^ (i + 2) - 1) < 1 := by
  have h1 : ∑ i ∈ range a, (1 : ℚ) / ((2 : ℚ) ^ (i + 2) - 1) ≤ ∑ i ∈ range a, (1 : ℚ) / (2 : ℚ) ^ (i + 1) := by
    apply sum_le_sum
    intro i _
    exact le_of_lt (sum_term_le_geom i)
  have h2 : ∑ i ∈ range a, (1 : ℚ) / (2 : ℚ) ^ (i + 1) < 1 := geom_sum_half_lt_one a
  exact lt_of_le_of_lt h1 h2

theorem no_int_between_one_and_two (z : ℤ) : ¬ (1 < (z : ℚ) ∧ (z : ℚ) < 2) := by
  intro h
  have h1 : 1 < z := by exact_mod_cast h.1
  have h2 : z < 2 := by exact_mod_cast h.2
  omega

theorem S_two_pow_not_int (a : ℕ) (ha : a ≥ 1) :
  (∑ i ∈ range (a + 1), (1 : ℚ) / (↑((sigma 1) (2 ^ i)) : ℚ)).den ≠ 1 := by
  intro h
  -- let S_val be the sum
  set S_val := ∑ i ∈ range (a + 1), (1 : ℚ) / (↑((sigma 1) (2 ^ i)) : ℚ)
  have h_eq : (S_val.num : ℚ) = S_val := by
    exact (Rat.den_eq_one_iff S_val).mp h
  -- we know S_val = 1 + sum_term
  have h_split : S_val = 1 + ∑ i ∈ range a, (1 : ℚ) / ((2 : ℚ) ^ (i + 2) - 1) := S_two_pow_split a
  -- let's show 1 < S_val < 2
  have h_gt : 1 < S_val := by
    rw [h_split]
    -- Sum is positive because a >= 1
    have h_sum_pos : 0 < ∑ i ∈ range a, (1 : ℚ) / ((2 : ℚ) ^ (i + 2) - 1) := by
      have ha_eq : a = (a - 1) + 1 := (Nat.sub_add_cancel ha).symm
      nth_rw 1 [ha_eq]
      rw [sum_range_succ']
      have h_term : 0 < (1 : ℚ) / ((2 : ℚ) ^ (0 + 2) - 1) := by positivity
      have h_rest : 0 ≤ ∑ i ∈ range (a - 1), (1 : ℚ) / ((2 : ℚ) ^ (i + 1 + 2) - 1) := by
        apply sum_nonneg
        intro i _
        have h_pos : 0 < (1 : ℚ) / ((2 : ℚ) ^ (i + 1 + 2) - 1) := by
          apply one_div_pos.mpr (sum_term_pos (i + 1))
        exact le_of_lt h_pos
      linarith
    linarith
  have h_lt : S_val < 2 := by
    rw [h_split]
    have h_sum_lt : ∑ i ∈ range a, (1 : ℚ) / ((2 : ℚ) ^ (i + 2) - 1) < 1 := sum_term_lt_one a
    linarith
  -- now 1 < S_val < 2
  -- so 1 < (S_val.num : ℚ) < 2
  have h_bounds : 1 < (S_val.num : ℚ) ∧ (S_val.num : ℚ) < 2 := by
    rw [h_eq]
    exact ⟨h_gt, h_lt⟩
  exact no_int_between_one_and_two S_val.num h_bounds


noncomputable def g_arith : ArithmeticFunction ℚ :=
  pdiv zeta ((ArithmeticFunction.sigma 1 : ArithmeticFunction ℕ) : ArithmeticFunction ℚ)

theorem g_arith_is_multiplicative : g_arith.IsMultiplicative := by
  apply IsMultiplicative.pdiv
  · exact IsMultiplicative.natCast isMultiplicative_zeta
  · apply IsMultiplicative.natCast
    exact isMultiplicative_sigma

noncomputable def S_arith : ArithmeticFunction ℚ :=
  g_arith * ArithmeticFunction.zeta

theorem S_arith_is_multiplicative : S_arith.IsMultiplicative := by
  apply IsMultiplicative.mul
  · exact g_arith_is_multiplicative
  · exact IsMultiplicative.natCast isMultiplicative_zeta

theorem S_arith_apply (n : ℕ) (_hn : n ≠ 0) :
  S_arith n = ∑ d ∈ n.divisors, (1 : ℚ) / (↑((sigma 1) d) : ℚ) := by
  rw [S_arith, coe_mul_zeta_apply]
  apply Finset.sum_congr rfl
  intro d hd
  rw [g_arith, pdiv_apply]
  have hd_ne : d ≠ 0 := by
    have h_pos := Nat.pos_of_mem_divisors hd
    exact Nat.ne_of_gt h_pos
  simp [zeta_apply, hd_ne]

theorem test_sum_divisors (a : ℕ) :
  (2 ^ a).divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) =
  (range (a + 1)).sum (fun i => (1 : ℚ) / (↑((sigma 1) (2 ^ i)) : ℚ)) := by
  apply sum_divisors_prime_pow
  exact Nat.prime_two


-- Theorems for Prime Power Bounds
theorem le_sigma_one_prime_pow (p : ℕ) (hp : Nat.Prime p) (j : ℕ) :
  p ^ j ≤ (sigma 1) (p ^ j) := by
  rw [sigma_one_apply_prime_pow hp]
  have h_mem : j ∈ range (j + 1) := mem_range.mpr (by omega)
  exact Finset.single_le_sum (fun k _ => Nat.zero_le (p ^ k)) h_mem

theorem reciprocal_sigma_le_reciprocal_pow (p : ℕ) (hp : Nat.Prime p) (j : ℕ) :
  (1 : ℚ) / (↑((sigma 1) (p ^ j)) : ℚ) ≤ (1 : ℚ) / (p : ℚ) ^ j := by
  have hp_pos : (0 : ℚ) < p := by exact_mod_cast hp.pos
  have h_pos : (0 : ℚ) < (p : ℚ) ^ j := by positivity
  have h_le : (p : ℚ) ^ j ≤ (↑((sigma 1) (p ^ j)) : ℚ) := by
    exact_mod_cast le_sigma_one_prime_pow p hp j
  have h_sigma_pos : (0 : ℚ) < (↑((sigma 1) (p ^ j)) : ℚ) := by linarith
  rw [one_div, one_div]
  exact (inv_le_inv₀ h_sigma_pos h_pos).mpr h_le

theorem geom_sum_reciprocal_p_lt_two (p : ℕ) (hp : Nat.Prime p) (hp_odd : p % 2 = 1) (e : ℕ) :
  ∑ j ∈ range (e + 1), (1 : ℚ) / (p : ℚ) ^ j < 2 := by
  have hp_ge : (p : ℚ) ≥ 3 := by
    have hp2 : p ≥ 2 := hp.two_le
    have : p % 2 = 1 := hp_odd
    have : p ≠ 2 := by omega
    have : p ≥ 3 := by omega
    exact_mod_cast this
  have h_x_ne : (1 / (p : ℚ)) ≠ 1 := by
    intro hc
    have hp_nz : (p : ℚ) ≠ 0 := by positivity
    have h_eq : 1 / (p : ℚ) = 1 := hc
    rw [div_eq_iff hp_nz] at h_eq
    linarith
  have h_sum := geom_sum_eq h_x_ne (e + 1)
  have h_rw : ∑ j ∈ range (e + 1), (1 : ℚ) / (p : ℚ) ^ j = ∑ j ∈ range (e + 1), (1 / (p : ℚ)) ^ j := by
    apply sum_congr rfl
    intro j _
    ring
  have h_geom_eq : ((1 / (p : ℚ)) ^ (e + 1) - 1) / (1 / (p : ℚ) - 1) = (1 - (1 / (p : ℚ)) ^ (e + 1)) / (1 - 1 / (p : ℚ)) := by
    have h_top : (1 / (p : ℚ)) ^ (e + 1) - 1 = - (1 - (1 / (p : ℚ)) ^ (e + 1)) := by ring
    have h_bot : 1 / (p : ℚ) - 1 = - (1 - 1 / (p : ℚ)) := by ring
    rw [h_top, h_bot]
    exact neg_div_neg_eq (1 - (1 / (p : ℚ)) ^ (e + 1)) (1 - 1 / (p : ℚ))
  rw [h_rw, h_sum, h_geom_eq]
  have hp_pos : (p : ℚ) > 0 := by positivity
  have h_p_inv_pos : (1 / (p : ℚ)) ^ (e + 1) > 0 := by positivity
  have h_num_lt : 1 - (1 / (p : ℚ)) ^ (e + 1) < 1 := by linarith
  have h_den_gt : 1 - 1 / (p : ℚ) > 0 := by
    have : 1 / (p : ℚ) ≤ 1 / 3 := by
      apply one_div_le_one_div_of_le <;> linarith
    linarith
  have h_div_lt : (1 - (1 / (p : ℚ)) ^ (e + 1)) / (1 - 1 / (p : ℚ)) < 1 / (1 - 1 / (p : ℚ)) := by
    apply div_lt_div_of_pos_right h_num_lt h_den_gt
  have h_lim : 1 / (1 - 1 / (p : ℚ)) < 2 := by
    have h_p_sub_one : (p : ℚ) - 1 > 0 := by linarith
    have h_rew : 1 / (1 - 1 / (p : ℚ)) = (p : ℚ) / ((p : ℚ) - 1) := by
      field_simp
    rw [h_rew]
    rw [div_lt_iff₀ h_p_sub_one]
    linarith
  exact lt_of_lt_of_le h_div_lt (le_of_lt h_lim)

theorem S_arith_prime_pow (p : ℕ) (hp : Nat.Prime p) (e : ℕ) :
  S_arith (p ^ e) = ∑ j ∈ range (e + 1), (1 : ℚ) / (↑((sigma 1) (p ^ j)) : ℚ) := by
  rw [S_arith_apply (p ^ e) (pow_ne_zero e hp.ne_zero)]
  apply sum_divisors_prime_pow hp

theorem S_arith_prime_pow_lt_two (p : ℕ) (hp : Nat.Prime p) (hp_odd : p % 2 = 1) (e : ℕ) :
  S_arith (p ^ e) < 2 := by
  rw [S_arith_prime_pow p hp e]
  have h_le : ∑ j ∈ range (e + 1), (1 : ℚ) / (↑((sigma 1) (p ^ j)) : ℚ) ≤ ∑ j ∈ range (e + 1), (1 : ℚ) / (p : ℚ) ^ j := by
    apply sum_le_sum
    intro j _
    exact reciprocal_sigma_le_reciprocal_pow p hp j
  have h_lt : ∑ j ∈ range (e + 1), (1 : ℚ) / (p : ℚ) ^ j < 2 := geom_sum_reciprocal_p_lt_two p hp hp_odd e
  exact lt_of_le_of_lt h_le h_lt

theorem S_arith_prime_pow_gt_one (p : ℕ) (hp : Nat.Prime p) (e : ℕ) (he : e ≥ 1) :
  1 < S_arith (p ^ e) := by
  rw [S_arith_prime_pow p hp e]
  rw [sum_range_succ']
  have h0 : (1 : ℚ) / (↑((sigma 1) (p ^ 0)) : ℚ) = 1 := by
    simp [sigma_one]
  rw [h0]
  have h_sum_pos : 0 < ∑ i ∈ range e, (1 : ℚ) / (↑((sigma 1) (p ^ (i + 1))) : ℚ) := by
    apply sum_pos
    · intro i _
      have : (0 : ℚ) < (↑((sigma 1) (p ^ (i + 1))) : ℚ) := by
        have h_pos := sigma_pos 1 (p ^ (i + 1)) (pow_ne_zero (i + 1) hp.ne_zero)
        exact_mod_cast h_pos
      positivity
    · exact ⟨0, mem_range.mpr he⟩
  linarith

theorem S_arith_prime_pow_not_int (p : ℕ) (hp : Nat.Prime p) (hp_odd : p % 2 = 1) (e : ℕ) (he : e ≥ 1) :
  (S_arith (p ^ e)).den ≠ 1 := by
  intro h
  have h_eq : ((S_arith (p ^ e)).num : ℚ) = S_arith (p ^ e) := by
    exact (Rat.den_eq_one_iff _).mp h
  have h1 : 1 < S_arith (p ^ e) := S_arith_prime_pow_gt_one p hp e he
  have h2 : S_arith (p ^ e) < 2 := S_arith_prime_pow_lt_two p hp hp_odd e
  have h_bounds : 1 < ((S_arith (p ^ e)).num : ℚ) ∧ ((S_arith (p ^ e)).num : ℚ) < 2 := by
    rw [h_eq]
    exact ⟨h1, h2⟩
  exact no_int_between_one_and_two (S_arith (p ^ e)).num h_bounds


-- ---------------------------------------------------------
-- Valuation & Multiplicativity proofs to solve S_not_int
-- ---------------------------------------------------------

theorem unique_max_power_of_two (E : ℕ) (hE : E ≥ 2) :
  let s := Nat.log 2 E
  2 ^ s ≤ E ∧ (∀ x : ℕ, x ≤ E → x ≠ 2 ^ s → padicValNat 2 x < s) := by
  intro s
  have h_pow_le : 2 ^ s ≤ E := Nat.pow_log_le_self 2 (by omega : E ≠ 0)
  refine ⟨h_pow_le, ?_⟩
  intro x hx_le hx_ne
  by_cases hx_nz : x = 0
  · rw [hx_nz]
    have : s ≥ 1 := by
      have : 2 ^ 1 ≤ E := by omega
      have : 1 ≤ s := Nat.le_log_of_pow_le (by omega) this
      omega
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : padicValNat 2 0 = 0 := by rfl
    omega
  by_contra hc
  push_neg at hc
  have h_dvd : 2 ^ s ∣ x := by
    rw [padicValNat_dvd_iff_le hx_nz]
    exact hc
  rcases h_dvd with ⟨k, rfl⟩
  have hk_nz : k ≠ 0 := by
    intro h_zero
    rw [h_zero, mul_zero] at hx_nz
    exact hx_nz rfl
  have hk_ne_one : k ≠ 1 := by
    intro h_one
    rw [h_one, mul_one] at hx_ne
    exact hx_ne rfl
  have hk_ge : k ≥ 2 := by omega
  have h_x_ge : 2 ^ s * k ≥ 2 ^ (s + 1) := by
    rw [pow_add, pow_one]
    apply Nat.mul_le_mul_left
    exact hk_ge
  have h_lt : E < 2 ^ (s + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two E
  omega

theorem sigma_one_prime_pow_odd_dvd (q : ℕ) (hq : q.Prime) (r : ℕ) :
  q + 1 ∣ (sigma 1) (q ^ (2 * r + 1)) := by
  rw [sigma_one_apply_prime_pow hq]
  induction r with
  | zero =>
    simp
  | @succ r ih =>
    have h_sum_split : ∑ k ∈ range (2 * (r + 1) + 1 + 1), q ^ k =
      ∑ k ∈ range (2 * r + 2), q ^ k + q ^ (2 * r + 2) + q ^ (2 * r + 3) := by
      have h1 : 2 * (r + 1) + 1 + 1 = 2 * r + 3 + 1 := by omega
      have h2 : 2 * r + 3 = 2 * r + 2 + 1 := by omega
      rw [h1, sum_range_succ, h2, sum_range_succ]
    rw [h_sum_split]
    have h_terms : q ^ (2 * r + 2) + q ^ (2 * r + 3) = (q + 1) * q ^ (2 * r + 2) := by ring
    rw [add_assoc, h_terms]
    apply dvd_add ih
    exact dvd_mul_right (q + 1) (q ^ (2 * r + 2))

theorem odd_pow (q k : ℕ) (hq : q % 2 = 1) : q ^ k % 2 = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    rw [Nat.mul_mod, ih, hq]

theorem sigma_one_prime_pow_even_odd (q : ℕ) (hq : q.Prime) (hq_odd : q % 2 = 1) (r : ℕ) :
  (sigma 1) (q ^ (2 * r)) % 2 = 1 := by
  rw [sigma_one_apply_prime_pow hq]
  induction r with
  | zero =>
    simp
  | @succ r ih =>
    have h_sum : ∑ k ∈ range (2 * (r + 1) + 1), q ^ k = ∑ k ∈ range (2 * r + 1), q ^ k + (q ^ (2 * r + 1) + q ^ (2 * r + 2)) := by
      have h1 : 2 * (r + 1) + 1 = 2 * r + 1 + 1 + 1 := by omega
      rw [h1, sum_range_succ, sum_range_succ]
      ring
    rw [h_sum]
    have h_terms : (q ^ (2 * r + 1) + q ^ (2 * r + 2)) % 2 = 0 := by
      have h1 := odd_pow q (2 * r + 1) hq_odd
      have h2 := odd_pow q (2 * r + 2) hq_odd
      rw [Nat.add_mod, h1, h2]
    rw [Nat.add_mod, h_terms, add_zero, Nat.mod_mod, ih]

theorem odd_pow_mod_two (q : ℕ) (hq : q % 2 = 1) (n : ℕ) : (q ^ n) % 2 = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    rw [Nat.mul_mod, ih, hq]

theorem geom_sum_odd_split (q : ℕ) (k : ℕ) :
  ∑ i ∈ range (2 * k + 2), q ^ i = (q + 1) * ∑ j ∈ range (k + 1), (q^2) ^ j := by
  induction k with
  | zero =>
    rw [sum_range_succ, sum_range_succ]
    simp
    ring
  | succ k ih =>
    have h_range : 2 * (k + 1) + 2 = 2 * k + 2 + 2 := by omega
    rw [h_range, sum_range_succ, sum_range_succ]
    rw [add_assoc, ih]
    have h1 : q ^ (2 * k + 2) + q ^ (2 * k + 3) = (q + 1) * (q^2) ^ (k + 1) := by
      have : 2 * k + 2 = 2 * (k + 1) := by omega
      have : 2 * k + 3 = 2 * (k + 1) + 1 := by omega
      rw [this]
      rw [pow_succ]
      ring
    rw [h1]
    rw [← mul_add]
    rw [← sum_range_succ]

theorem sum_mod_two (s : Finset ℕ) (F : ℕ → ℕ) :
  (∑ i ∈ s, F i) % 2 = (∑ i ∈ s, F i % 2) % 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    omega

theorem sum_odd_mod_two (s : Finset ℕ) (F : ℕ → ℕ) (h : ∀ i ∈ s, F i % 2 = 1) :
  (∑ i ∈ s, F i) % 2 = s.card % 2 := by
  rw [sum_mod_two]
  have h1 : ∑ i ∈ s, F i % 2 = ∑ i ∈ s, 1 := by
    apply sum_congr rfl
    intro x hx
    exact h x hx
  rw [h1, sum_const, smul_eq_mul, mul_one]

theorem padicValNat_two_sum_odd (s : Finset ℕ) (F : ℕ → ℕ) (h : ∀ i ∈ s, F i % 2 = 1) (hs_odd : s.card % 2 = 1) :
  padicValNat 2 (∑ i ∈ s, F i) = 0 := by
  have h_odd : (∑ i ∈ s, F i) % 2 = 1 := by
    rw [sum_odd_mod_two s F h, hs_odd]
  rw [padicValNat.eq_zero_iff]
  right; right
  intro hc
  have : (∑ i ∈ s, F i) % 2 = 0 := Nat.mod_eq_zero_of_dvd hc
  omega

theorem padicValNat_two_odd (n : ℕ) (hn_odd : n % 2 = 1) : padicValNat 2 n = 0 := by
  rw [padicValNat.eq_zero_iff]
  right; right
  intro hc
  have : n % 2 = 0 := Nat.mod_eq_zero_of_dvd hc
  omega

theorem v2_one_add_q_sq (q : ℕ) (hq_odd : q % 2 = 1) : padicValNat 2 (1 + q^2) = 1 := by
  set m := q / 2
  have h_q_eq : q = 2 * m + 1 := by omega
  have h_eq : 1 + q^2 = 2 * (2 * (m * (m + 1)) + 1) := by
    rw [h_q_eq]
    ring
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h_nz1 : 2 ≠ 0 := by omega
  have h_nz2 : 2 * (m * (m + 1)) + 1 ≠ 0 := by omega
  rw [h_eq, padicValNat.mul h_nz1 h_nz2]
  have h_v2 : padicValNat 2 2 = 1 := padicValNat_self
  have h_v_odd : padicValNat 2 (2 * (m * (m + 1)) + 1) = 0 := by
    apply padicValNat_two_odd
    omega
  rw [h_v2, h_v_odd]

theorem v2_geom_sum_odd (q : ℕ) (hq_odd : q % 2 = 1) (r : ℕ) :
  padicValNat 2 (∑ i ∈ range (r + 1), q ^ (2 * i)) = padicValNat 2 (r + 1) := by
  induction' r using Nat.strong_induction_on with r ih generalizing q
  by_cases hr : r % 2 = 0
  · have hr_odd : (r + 1) % 2 = 1 := by omega
    have h_sum_odd : padicValNat 2 (∑ i ∈ range (r + 1), q ^ (2 * i)) = 0 := by
      apply padicValNat_two_sum_odd (range (r + 1)) (fun i => q ^ (2 * i))
      · intro i _
        exact odd_pow_mod_two q hq_odd (2 * i)
      · rw [card_range]
        exact hr_odd
    have h_r_odd : padicValNat 2 (r + 1) = 0 := by
      exact padicValNat_two_odd (r + 1) hr_odd
    rw [h_sum_odd, h_r_odd]
  · have hr_odd : r % 2 = 1 := by omega
    set k := r / 2
    have hk_eq : r = 2 * k + 1 := by omega
    have h_k_lt : k < r := by omega
    have hQ_odd : (q^2) % 2 = 1 := by
      rw [pow_two]
      rw [Nat.mul_mod, hq_odd]
    have h_ih := ih k h_k_lt (q^2) hQ_odd
    have h_pow_rw : ∑ i ∈ range (r + 1), q ^ (2 * i) = ∑ i ∈ range (2 * k + 2), (q^2) ^ i := by
      rw [hk_eq]
      apply sum_congr rfl
      intro i _
      ring
    have h_split := geom_sum_odd_split (q^2) k
    have h_rew : (q^2 + 1) * ∑ j ∈ range (k + 1), ((q^2)^2) ^ j = (1 + q^2) * ∑ j ∈ range (k + 1), (q^2) ^ (2 * j) := by
      rw [add_comm]
      congr 1
      apply sum_congr rfl
      intro j _
      rw [← pow_mul]
    rw [h_pow_rw, h_split, h_rew]
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h_nz_1 : 1 + q^2 ≠ 0 := by positivity
    have h_nz_2 : ∑ j ∈ range (k + 1), (q^2) ^ (2 * j) ≠ 0 := by
      apply _root_.ne_of_gt
      apply sum_pos
      · intro i _
        have : q > 0 := by omega
        positivity
      · exact ⟨0, mem_range.mpr (by omega)⟩
    rw [padicValNat.mul h_nz_1 h_nz_2]
    have h_v1 : padicValNat 2 (1 + q^2) = 1 := v2_one_add_q_sq q hq_odd
    rw [h_v1, h_ih]
    have h_r_val : padicValNat 2 (2 * k + 2) = 1 + padicValNat 2 (k + 1) := by
      have h_nz_2_const : 2 ≠ 0 := by omega
      have h_nz_kp1 : k + 1 ≠ 0 := by omega
      have h_eq_mul : 2 * k + 2 = 2 * (k + 1) := by ring
      rw [h_eq_mul, padicValNat.mul h_nz_2_const h_nz_kp1]
      have : padicValNat 2 2 = 1 := padicValNat_self
      rw [this]
    rw [hk_eq]
    rw [h_r_val]

theorem v2_sigma_one_odd_prime_pow (q : ℕ) (hq : q.Prime) (hq_odd : q % 2 = 1) (e : ℕ) (he_odd : e % 2 = 1) :
  padicValNat 2 (sigma 1 (q ^ e)) = padicValNat 2 (q + 1) + padicValNat 2 (e + 1) - 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set r := e / 2
  have he_eq : e = 2 * r + 1 := by omega
  have h_split : sigma 1 (q ^ e) = (q + 1) * ∑ i ∈ range (r + 1), q ^ (2 * i) := by
    rw [sigma_one_apply_prime_pow hq, he_eq]
    have : 2 * r + 1 + 1 = 2 * r + 2 := by omega
    rw [this]
    rw [geom_sum_odd_split q r]
    ring
  have h_nz1 : q + 1 ≠ 0 := by omega
  have h_nz2 : ∑ i ∈ range (r + 1), q ^ (2 * i) ≠ 0 := by
    apply _root_.ne_of_gt
    apply sum_pos
    · intro i _
      have : q > 0 := by exact_mod_cast hq.pos
      positivity
    · exact ⟨0, mem_range.mpr (by omega)⟩
  rw [h_split, padicValNat.mul h_nz1 h_nz2]
  rw [v2_geom_sum_odd q hq_odd r]
  have h_e_val : padicValNat 2 (e + 1) = 1 + padicValNat 2 (r + 1) := by
    have h_eq_mul : e + 1 = 2 * (r + 1) := by omega
    have h_nz_2 : 2 ≠ 0 := by omega
    have h_nz_rp1 : r + 1 ≠ 0 := by omega
    rw [h_eq_mul, padicValNat.mul h_nz_2 h_nz_rp1]
    have : padicValNat 2 2 = 1 := padicValNat_self
    rw [this]
  omega

theorem padicValRat_sum_ge_of_ge {ι : Type*} [DecidableEq ι] {p : ℕ} [hp : Fact (Nat.Prime p)] (s : Finset ι) (F : ι → ℚ) (V : ℤ) (h : ∀ (i : ι), i ∈ s → V ≤ padicValRat p (F i)) (h_sum : ∑ x ∈ s, F x ≠ 0) :
  V ≤ padicValRat p (∑ x ∈ s, F x) := by
  induction s using Finset.induction_on with
  | empty =>
    simp at h_sum
  | @insert a s ha ih =>
    by_cases h_sum_insert : ∑ x ∈ insert a s, F x = 0
    · contradiction
    have h_sum_insert_rew : F a + ∑ x ∈ s, F x ≠ 0 := by
      rwa [← sum_insert ha]
    rw [sum_insert ha]
    have h_a : V ≤ padicValRat p (F a) := h a (mem_insert_self a s)
    have h_s : ∀ (i : ι), i ∈ s → V ≤ padicValRat p (F i) := fun i hi => h i (mem_insert_of_mem hi)
    by_cases h_sum_s : ∑ x ∈ s, F x = 0
    · rw [h_sum_s, add_zero]
      exact h_a
    · have ih_val := ih h_s h_sum_s
      have h_min := @padicValRat.min_le_padicValRat_add p hp (F a) (∑ x ∈ s, F x) h_sum_insert_rew
      have h_min_ge : V ≤ min (padicValRat p (F a)) (padicValRat p (∑ x ∈ s, F x)) := le_min h_a ih_val
      linarith

theorem padicValRat_sum_unique_min {ι : Type*} [DecidableEq ι] {p : ℕ} [hp : Fact (Nat.Prime p)] (s : Finset ι) (F : ι → ℚ) (y : ι) (hj : y ∈ s) (h_unique : ∀ (i : ι), i ∈ s → i ≠ y → padicValRat p (F y) < padicValRat p (F i)) (h_sum : ∑ x ∈ s, F x ≠ 0) (h_j_nz : F y ≠ 0) :
  padicValRat p (∑ x ∈ s, F x) = padicValRat p (F y) := by
  have h_split : ∑ x ∈ s, F x = F y + ∑ x ∈ s.erase y, F x := by
    have h_eq : s = insert y (s.erase y) := (insert_erase hj).symm
    nth_rw 1 [h_eq]
    rw [sum_insert (by simp)]
  by_cases h_sum_erase : ∑ x ∈ s.erase y, F x = 0
  · rw [h_split, h_sum_erase, add_zero]
  · have h_ge : padicValRat p (F y) + 1 ≤ padicValRat p (∑ x ∈ s.erase y, F x) := by
      apply padicValRat_sum_ge_of_ge (s.erase y) F (padicValRat p (F y) + 1)
      · intro z hz
        have hz_ne : z ≠ y := by
          intro hc
          rw [hc] at hz
          have h_not : y ∉ s.erase y := by simp
          exact h_not hz
        have h_lt := h_unique z (mem_of_mem_erase hz) hz_ne
        linarith
      · exact h_sum_erase
    have h_lt : padicValRat p (F y) < padicValRat p (∑ x ∈ s.erase y, F x) := by linarith
    have h_sum_rew : F y + ∑ x ∈ s.erase y, F x ≠ 0 := by
      rwa [← h_split]
    rw [h_split]
    rw [padicValRat.add_eq_of_lt h_sum_rew h_j_nz h_sum_erase h_lt]

theorem padicValRat_two_S_arith_prime_pow (q : ℕ) (hq : q.Prime) (hq_odd : q % 2 = 1) (e : ℕ) (he : e ≥ 1) :
  padicValRat 2 (S_arith (q ^ e)) < 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [S_arith_prime_pow q hq e]
  set E := if e % 2 = 1 then e + 1 else e
  set s_max := Nat.log 2 E
  set y := 2 ^ s_max - 1
  have hE_ge : E ≥ 2 := by
    by_cases he_odd : e % 2 = 1
    · dsimp [E]
      rw [if_pos he_odd]
      omega
    · dsimp [E]
      rw [if_neg he_odd]
      omega
  have h_unique := unique_max_power_of_two E hE_ge
  change 2 ^ s_max ≤ E ∧ (∀ x : ℕ, x ≤ E → x ≠ 2 ^ s_max → padicValNat 2 x < s_max) at h_unique
  have hs_max_ge : s_max ≥ 1 := by
    have : 2 ^ 1 ≤ E := by omega
    exact Nat.le_log_of_pow_le (by omega) this
  have hy_odd : y % 2 = 1 := by
    have h_pow_pos : 2 ^ s_max ≥ 1 := Nat.one_le_pow s_max 2 (by omega)
    have h_eq : y + 1 = 2 ^ s_max := by
      change 2 ^ s_max - 1 + 1 = 2 ^ s_max
      generalize h_gen : 2 ^ s_max = k
      have : k ≥ 1 := by
        rw [← h_gen]
        exact h_pow_pos
      omega
    have h_pow : 2 ^ s_max = 2 * 2 ^ (s_max - 1) := by
      have h_eq2 : s_max = (s_max - 1) + 1 := (Nat.sub_add_cancel hs_max_ge).symm
      nth_rw 1 [h_eq2]
      rw [Nat.pow_succ, mul_comm]
    have h_eq3 : y + 1 = 2 * 2 ^ (s_max - 1) := by omega
    generalize 2 ^ (s_max - 1) = k2 at h_eq3
    omega
  have hy_lt : y < e + 1 := by
    have h_pow_pos : 2 ^ s_max ≥ 1 := Nat.one_le_pow s_max 2 (by omega)
    have h_eq : y + 1 = 2 ^ s_max := by
      change 2 ^ s_max - 1 + 1 = 2 ^ s_max
      generalize h_gen : 2 ^ s_max = k
      have : k ≥ 1 := by
        rw [← h_gen]
        exact h_pow_pos
      omega
    have h_le : y + 1 ≤ E := by
      rw [h_eq]
      exact h_unique.1
    by_cases he_odd : e % 2 = 1
    · dsimp [E] at h_le
      rw [if_pos he_odd] at h_le
      omega
    · dsimp [E] at h_le
      rw [if_neg he_odd] at h_le
      omega
  have hy_mem : y ∈ range (e + 1) := mem_range.mpr hy_lt
  have h_unique_min : ∀ i ∈ range (e + 1), i ≠ y →
    padicValRat 2 ((1 : ℚ) / (sigma 1 (q ^ y) : ℚ)) < padicValRat 2 ((1 : ℚ) / (sigma 1 (q ^ i) : ℚ)) := by
    intro i hi hi_ne
    rw [mem_range] at hi
    have h_val_y : padicValRat 2 ((1 : ℚ) / (sigma 1 (q ^ y) : ℚ)) = - padicValNat 2 (q + 1) - s_max + 1 := by
      rw [one_div, padicValRat.inv, padicValRat.of_nat]
      rw [v2_sigma_one_odd_prime_pow q hq hq_odd y hy_odd]
      have : y + 1 = 2 ^ s_max := by omega
      rw [this, padicValNat.prime_pow]
      omega
    by_cases hi_even : i % 2 = 0
    · -- i is even
      have h_val_i : padicValRat 2 ((1 : ℚ) / (sigma 1 (q ^ i) : ℚ)) = 0 := by
        rw [one_div, padicValRat.inv, padicValRat.of_nat]
        have h_odd : sigma 1 (q ^ i) % 2 = 1 := by
          have h_eq_div : i = 2 * (i / 2) := by omega
          nth_rw 1 [h_eq_div]
          exact sigma_one_prime_pow_even_odd q hq hq_odd (i / 2)
        have : padicValNat 2 (sigma 1 (q ^ i)) = 0 := padicValNat_two_odd _ h_odd
        rw [this]
        rfl
      rw [h_val_y, h_val_i]
      have h_v_qp1 : padicValNat 2 (q + 1) ≥ 1 := by
        have : (q + 1) % 2 = 0 := by omega
        have h_div : 2 ∣ q + 1 := Nat.dvd_of_mod_eq_zero this
        have h_nz : q + 1 ≠ 0 := by omega
        have h_le : 1 ≤ padicValNat 2 (q + 1) := by
          rwa [← padicValNat_dvd_iff_le h_nz, pow_one]
        exact h_le
      omega
    · -- i is odd
      have hi_odd : i % 2 = 1 := by omega
      have h_q_gt : padicValNat 2 (q + 1) ≥ 1 := by
        have : (q + 1) % 2 = 0 := by omega
        have h_div : 2 ∣ q + 1 := Nat.dvd_of_mod_eq_zero this
        have h_nz : q + 1 ≠ 0 := by omega
        have h_le : 1 ≤ padicValNat 2 (q + 1) := by
          rwa [← padicValNat_dvd_iff_le h_nz, pow_one]
        exact h_le
      have h_i_gt : padicValNat 2 (i + 1) ≥ 1 := by
        have : (i + 1) % 2 = 0 := by omega
        have h_div : 2 ∣ i + 1 := Nat.dvd_of_mod_eq_zero this
        have h_nz : i + 1 ≠ 0 := by omega
        have h_le : 1 ≤ padicValNat 2 (i + 1) := by
          rwa [← padicValNat_dvd_iff_le h_nz, pow_one]
        exact h_le
      have h_cast_sub : (↑(padicValNat 2 (q + 1) + padicValNat 2 (i + 1) - 1) : ℤ) =
        (padicValNat 2 (q + 1) : ℤ) + (padicValNat 2 (i + 1) : ℤ) - 1 := by
        have h_sum_ge : 1 ≤ padicValNat 2 (q + 1) + padicValNat 2 (i + 1) := by omega
        rw [Nat.cast_sub h_sum_ge]
        push_cast
        rfl
      have h_val_i : padicValRat 2 ((1 : ℚ) / (sigma 1 (q ^ i) : ℚ)) = - padicValNat 2 (q + 1) - padicValNat 2 (i + 1) + 1 := by
        rw [one_div, padicValRat.inv, padicValRat.of_nat]
        rw [v2_sigma_one_odd_prime_pow q hq hq_odd i hi_odd]
        rw [h_cast_sub]
        ring
      rw [h_val_y, h_val_i]
      have hi_le_E : i + 1 ≤ E := by
        by_cases he_odd : e % 2 = 1
        · dsimp [E]
          rw [if_pos he_odd]
          omega
        · dsimp [E]
          rw [if_neg he_odd]
          omega
      have h_ne_pow : i + 1 ≠ 2 ^ s_max := by
        intro hc
        have : i = y := by omega
        contradiction
      have h_lt := h_unique.2 (i + 1) hi_le_E h_ne_pow
      omega
  have h_sum_nz : ∑ x ∈ range (e + 1), (1 : ℚ) / (sigma 1 (q ^ x) : ℚ) ≠ 0 := by
    apply _root_.ne_of_gt
    apply sum_pos
    · intro j _
      have : (0 : ℚ) < (sigma 1 (q ^ j) : ℚ) := by
        have h_pos := sigma_pos 1 (q ^ j) (pow_ne_zero j hq.ne_zero)
        exact_mod_cast h_pos
      positivity
    · exact ⟨0, mem_range.mpr (by omega)⟩
  have h_y_nz : (1 : ℚ) / (sigma 1 (q ^ y) : ℚ) ≠ 0 := by
    apply div_ne_zero (one_ne_zero)
    have h_sig_pos : 0 < sigma 1 (q ^ y) := sigma_pos 1 (q ^ y) (pow_ne_zero y hq.ne_zero)
    exact_mod_cast h_sig_pos.ne'
  have h_val := padicValRat_sum_unique_min (range (e + 1)) (fun x => (1 : ℚ) / (sigma 1 (q ^ x) : ℚ)) y hy_mem h_unique_min h_sum_nz h_y_nz
  rw [h_val]
  have h_val_y : padicValRat 2 ((1 : ℚ) / (sigma 1 (q ^ y) : ℚ)) = - padicValNat 2 (q + 1) - s_max + 1 := by
    rw [one_div, padicValRat.inv, padicValRat.of_nat]
    rw [v2_sigma_one_odd_prime_pow q hq hq_odd y hy_odd]
    have : y + 1 = 2 ^ s_max := by omega
    rw [this, padicValNat.prime_pow]
    omega
  rw [h_val_y]
  have h_v_qp1 : padicValNat 2 (q + 1) ≥ 1 := by
    have : (q + 1) % 2 = 0 := by omega
    have h_div : 2 ∣ q + 1 := Nat.dvd_of_mod_eq_zero this
    have h_nz : q + 1 ≠ 0 := by omega
    have h_le : 1 ≤ padicValNat 2 (q + 1) := by
      rwa [← padicValNat_dvd_iff_le h_nz, pow_one]
    exact h_le
  omega

theorem padicValRat_two_S_arith_prime_pow_nonpos (q : ℕ) (hq : q.Prime) (hq_odd : q % 2 = 1) (e : ℕ) :
  padicValRat 2 (S_arith (q ^ e)) ≤ 0 := by
  by_cases he : e = 0
  · rw [he, pow_zero]
    have h_eq : S_arith 1 = 1 := S_arith_is_multiplicative.map_one
    rw [h_eq]
    rw [padicValRat.one]
  · have he_gt : e ≥ 1 := by omega
    have h_lt := padicValRat_two_S_arith_prime_pow q hq hq_odd e he_gt
    linarith

theorem not_dvd_of_padicValNat {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : n ≠ 0) :
  ¬ p ∣ n / p ^ (padicValNat p n) := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  intro hc
  have h_dvd : p ^ (padicValNat p n + 1) ∣ n := by
    have h_eq : p ^ padicValNat p n * (n / p ^ padicValNat p n) = n := by
      apply Nat.mul_div_cancel'
      rw [padicValNat_dvd_iff_le hn]
    have h_dvd_prod : p ^ (padicValNat p n + 1) ∣ p ^ padicValNat p n * (n / p ^ padicValNat p n) := by
      rw [pow_succ]
      exact mul_dvd_mul_left (p ^ padicValNat p n) hc
    rwa [h_eq] at h_dvd_prod
  have h_le : padicValNat p n + 1 ≤ padicValNat p n := by
    rwa [← padicValNat_dvd_iff_le hn]
  omega

theorem coprime_two_pow_div (n : ℕ) (hn : n ≠ 0) :
  let a := padicValNat 2 n
  let m := n / 2 ^ a
  2 ^ a * m = n ∧ (2 ^ a).Coprime m := by
  intro a m
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h_dvd : 2 ^ a ∣ n := by
    rw [padicValNat_dvd_iff_le hn]
  have h_eq : 2 ^ a * m = n := Nat.mul_div_cancel' h_dvd
  refine ⟨h_eq, ?_⟩
  have h_not_dvd : ¬ 2 ^ (a + 1) ∣ n := by
    rw [padicValNat_dvd_iff_le hn]
    omega
  have h_coprime : Coprime (2 ^ a) m := by
    apply Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd hp.out]
    intro h_dvd_m
    have h_p_dvd_n : 2 ^ (a + 1) ∣ n := by
      rw [pow_succ]
      rw [← h_eq]
      exact mul_dvd_mul_left (2 ^ a) h_dvd_m
    exact h_not_dvd h_p_dvd_n
  exact h_coprime

theorem sum_padic_val_lt_zero_of_one_lt_zero {ι : Type*} [DecidableEq ι] (s : Finset ι) (F : ι → ℤ) (j : ι) (hj : j ∈ s) (h_lt : F j < 0) (h_le : ∀ i ∈ s, i ≠ j → F i ≤ 0) :
  ∑ i ∈ s, F i < 0 := by
  rw [← insert_erase hj]
  rw [sum_insert (by simp)]
  have h_sum_le : ∑ i ∈ s.erase j, F i ≤ 0 := by
    apply sum_nonpos
    intro i hi
    have hi_ne : i ≠ j := by
      exact (Finset.mem_erase.mp hi).1
    exact h_le i (Finset.mem_of_mem_erase hi) hi_ne
  linarith

theorem padic_val_two_pow_nonneg (a : ℕ) :
  0 ≤ padicValRat 2 (∑ i ∈ range (a + 1), (1 : ℚ) / (↑((sigma 1) (2 ^ i)) : ℚ)) := by
  induction a with
  | zero =>
    simp [sigma_one]
  | succ a ih =>
    rw [sum_range_succ]
    have h_ne_zero : ∑ i ∈ range (a + 1), (1 : ℚ) / (↑((sigma 1) (2 ^ i)) : ℚ) + (1 : ℚ) / (↑((sigma 1) (2 ^ (a + 1))) : ℚ) ≠ 0 := by
      have h_sum_pos : (0 : ℚ) < ∑ i ∈ range (a + 1), (1 : ℚ) / (↑((sigma 1) (2 ^ i)) : ℚ) + (1 : ℚ) / (↑((sigma 1) (2 ^ (a + 1))) : ℚ) := by
        apply add_pos
        · apply sum_pos
          · intro i _
            have : (0 : ℚ) < (↑((sigma 1) (2 ^ i)) : ℚ) := by
              have h_pos := sigma_pos 1 (2^i) (by positivity)
              exact_mod_cast h_pos
            positivity
          · exact ⟨0, mem_range.mpr (by omega)⟩
        · have : (0 : ℚ) < (↑((sigma 1) (2 ^ (a + 1))) : ℚ) := by
            have h_pos := sigma_pos 1 (2 ^ (a + 1)) (by positivity)
            exact_mod_cast h_pos
          positivity
      exact ne_of_gt h_sum_pos
    have h_term_nonneg : 0 ≤ padicValRat 2 ((1 : ℚ) / (↑((sigma 1) (2 ^ (a + 1))) : ℚ)) := by
      rw [sigma_one_two_pow (a + 1)]
      have h_pow_gt : (1 : ℚ) < (2 : ℚ) ^ (a + 2) := by
        have h_cast : (2 : ℚ) ^ (a + 2) = ↑(2 ^ (a + 2)) := rfl
        rw [h_cast]
        norm_cast
        have : 2 ^ (a + 2) ≥ 4 := by
          calc 2 ^ (a + 2) ≥ 2^2 := pow_le_pow_right₀ (by norm_num : 1 ≤ 2) (by omega : 2 ≤ a + 2)
          _ = 4 := rfl
        omega
      have h_odd : (2 : ℚ) ^ (a + 2) - 1 ≠ 0 := by linarith
      rw [padicValRat.div (by norm_num) h_odd]
      rw [padicValRat.one]
      have h_cast : ((2 ^ (a + 2) - 1 : ℕ) : ℚ) = (2 : ℚ) ^ (a + 2) - 1 := by
        have h_le : 1 ≤ 2 ^ (a + 2) := by
          have : 2 ^ (a + 2) ≥ 4 := by
            calc 2 ^ (a + 2) ≥ 2^2 := pow_le_pow_right₀ (by norm_num : 1 ≤ 2) (by omega : 2 ≤ a + 2)
            _ = 4 := rfl
          omega
        rw [Nat.cast_sub h_le]
        push_cast
        rfl
      rw [← h_cast]
      have h_eq : padicValRat 2 ↑(2 ^ (a + 2) - 1 : ℕ) = padicValNat 2 (2 ^ (a + 2) - 1) :=
        (padicValRat_of_nat (p := 2) (2 ^ (a + 2) - 1)).symm
      rw [h_eq]
      have : padicValNat 2 (2 ^ (a + 2) - 1) = 0 := by
        rw [padicValNat.eq_zero_iff]
        right; right
        intro hc
        have h_zero : (2 ^ (a + 2) - 1) % 2 = 0 := Nat.mod_eq_zero_of_dvd hc
        have h_odd' : (2 ^ (a + 2) - 1) % 2 = 1 := by
          have h_pow_even : 2 ^ (a + 2) % 2 = 0 := by simp [Nat.pow_succ]
          have h_sub : 2 ^ (a + 2) - 1 + 1 = 2 ^ (a + 2) := by
            apply Nat.sub_add_cancel
            have h_pow_gt_nat : 2 ^ (a + 2) ≥ 4 := by
              calc 2 ^ (a + 2) ≥ 2^2 := pow_le_pow_right₀ (by norm_num : 1 ≤ 2) (by omega : 2 ≤ a + 2)
              _ = 4 := rfl
            omega
          omega
        omega
      rw [this]
      rfl
    have h_min := padicValRat.min_le_padicValRat_add (p := 2) h_ne_zero
    have h_le : 0 ≤ min (padicValRat 2 (∑ i ∈ range (a + 1), (1 : ℚ) / (↑((sigma 1) (2 ^ i)) : ℚ))) (padicValRat 2 ((1 : ℚ) / (↑((sigma 1) (2 ^ (a + 1))) : ℚ))) := by
      rw [le_min_iff]
      exact ⟨ih, h_term_nonneg⟩
    linarith

theorem padicValRat_two_S_arith_two_pow (a : ℕ) :
  0 ≤ padicValRat 2 (S_arith (2 ^ a)) := by
  rw [S_arith_apply (2 ^ a) (by positivity)]
  rw [test_sum_divisors a]
  exact padic_val_two_pow_nonneg a

theorem S_arith_ne_zero (n : ℕ) (hn : n ≠ 0) :
  S_arith n ≠ 0 := by
  have h_pos : 0 < S_arith n := by
    rw [S_arith_apply n hn]
    apply sum_pos
    · intro d hd
      have hd_nz : d ≠ 0 := by
        have := Nat.pos_of_mem_divisors hd
        omega
      have h_sig_pos : (0 : ℚ) < (↑((sigma 1) d) : ℚ) := by
        exact_mod_cast sigma_pos 1 d hd_nz
      positivity
    · have h_one_mem : 1 ∈ n.divisors := by
        rw [mem_divisors]
        exact ⟨one_dvd n, hn⟩
      exact ⟨1, h_one_mem⟩
  exact h_pos.ne'

theorem padicValRat_prod {ι : Type*} [DecidableEq ι] {p : ℕ} [hp : Fact (Nat.Prime p)] (s : Finset ι) (F : ι → ℚ) (hF : ∀ i ∈ s, F i ≠ 0) :
  padicValRat p (∏ i ∈ s, F i) = ∑ i ∈ s, padicValRat p (F i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp [padicValRat.one]
  | @insert ha hs h_not_in ih =>
    have h_ha : F ha ≠ 0 := hF ha (mem_insert_self ha hs)
    have h_rest : ∀ i ∈ hs, F i ≠ 0 := fun i hi => hF i (mem_insert_of_mem hi)
    have h_prod_ne : ∏ i ∈ hs, F i ≠ 0 := prod_ne_zero_iff.mpr h_rest
    rw [prod_insert h_not_in, sum_insert h_not_in]
    rw [padicValRat.mul h_ha h_prod_ne]
    rw [ih h_rest]

theorem S_arith_prime_pow_pos (p : ℕ) (hp : Nat.Prime p) (e : ℕ) :
  0 < S_arith (p ^ e) := by
  rw [S_arith_apply (p ^ e) (pow_ne_zero e hp.ne_zero)]
  apply sum_pos
  · intro d hd
    have hd_nz : d ≠ 0 := by
      have := Nat.pos_of_mem_divisors hd
      omega
    have h_sig_pos : (0 : ℚ) < (↑((sigma 1) d) : ℚ) := by
      exact_mod_cast sigma_pos 1 d hd_nz
    positivity
  · have h_one_mem : 1 ∈ (p ^ e).divisors := by
      rw [mem_divisors]
      exact ⟨one_dvd (p ^ e), pow_ne_zero e hp.ne_zero⟩
    use 1

theorem S_arith_factorization_prod (n : ℕ) (hn : n ≠ 0) :
  S_arith n = ∏ p ∈ n.primeFactors, S_arith (p ^ (n.factorization p)) := by
  have h_mult := S_arith_is_multiplicative
  rw [IsMultiplicative.multiplicative_factorization S_arith h_mult hn]
  rfl

theorem padicValRat_two_S_arith (n : ℕ) (hn : n ≠ 0) :
  padicValRat 2 (S_arith n) = ∑ p ∈ n.primeFactors, padicValRat 2 (S_arith (p ^ (n.factorization p))) := by
  rw [S_arith_factorization_prod n hn]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply padicValRat_prod
  intro p hp
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have h_pos := S_arith_prime_pow_pos p hp_prime (n.factorization p)
  exact h_pos.ne'

theorem S_arith_padicValRat_two_lt_zero (n : ℕ) (hn : n ≠ 0) (hn_odd : n % 2 = 1) (p : ℕ) (hp : p.Prime) (hp_dvd : p ∣ n) (hp_odd : p % 2 = 1) :
  padicValRat 2 (S_arith n) < 0 := by
  set a := padicValNat 2 n
  set m := n / 2 ^ a
  have h_cop := coprime_two_pow_div n hn
  change 2 ^ a * m = n ∧ (2 ^ a).Coprime m at h_cop
  have h_S : S_arith n = S_arith (2 ^ a) * S_arith m := by
    rw [← h_cop.1]
    exact S_arith_is_multiplicative.map_mul_of_coprime h_cop.2
  have h_ne_two_pow : S_arith (2 ^ a) ≠ 0 := by
    have hp2 : Nat.Prime 2 := Nat.prime_two
    exact (S_arith_prime_pow_pos 2 hp2 a).ne'
  have hm_nz : m ≠ 0 := by
    intro hc
    rw [hc, mul_zero] at h_cop
    omega
  have h_ne_m : S_arith m ≠ 0 := S_arith_ne_zero m hm_nz
  have hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [h_S, padicValRat.mul h_ne_two_pow h_ne_m]
  have ha0 : a = 0 := padicValNat_two_odd n hn_odd
  have h_v2_pow : padicValRat 2 (S_arith (2 ^ a)) = 0 := by
    rw [ha0]
    have h1 : S_arith (2^0) = 1 := S_arith_is_multiplicative.map_one
    rw [h1]
    exact padicValRat.one
  rw [h_v2_pow]
  have h_vm : padicValRat 2 (S_arith m) < 0 := by
    rw [padicValRat_two_S_arith m hm_nz]
    have hp_mem : p ∈ m.primeFactors := by
      rw [Nat.mem_primeFactors]
      refine ⟨hp, ?_, hm_nz⟩
      -- since p | n and p is odd, p | m
      have hp_dvd_mul : p ∣ 2 ^ a * m := by rwa [h_cop.1]
      have : p.Coprime (2 ^ a) := by
        apply Coprime.pow_right
        rw [Nat.Prime.coprime_iff_not_dvd hp]
        intro hc
        have : p = 2 := by
          exact ((Nat.Prime.dvd_iff_eq Nat.prime_two hp.ne_one).mp hc).symm
        omega
      exact (Coprime.dvd_mul_left this).mp hp_dvd_mul
    have h_fact_pos : m.factorization p ≥ 1 := by
      have hp_dvd_m : p ∣ m := by
        rw [Nat.mem_primeFactors] at hp_mem
        exact hp_mem.2.1
      have h_pos := hp.factorization_pos_of_dvd hm_nz hp_dvd_m
      exact h_pos
    have h_lt : padicValRat 2 (S_arith (p ^ (m.factorization p))) < 0 :=
      padicValRat_two_S_arith_prime_pow p hp hp_odd (m.factorization p) h_fact_pos
    apply sum_padic_val_lt_zero_of_one_lt_zero m.primeFactors (fun q => padicValRat 2 (S_arith (q ^ (m.factorization q)))) p hp_mem h_lt
    intro q hq hq_ne
    have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hq_ne_two : q ≠ 2 := by
      intro hc
      rw [hc] at hq
      rw [Nat.mem_primeFactors] at hq
      have h2_dvd_m := hq.2.1
      have h_not_dvd := not_dvd_of_padicValNat Nat.prime_two hn
      exact h_not_dvd h2_dvd_m
    have hq_odd' : q % 2 = 1 := by
      have := hq_prime.eq_two_or_odd
      omega
    have h_le := padicValRat_two_S_arith_prime_pow_nonpos q hq_prime hq_odd' (m.factorization q)
    exact h_le
  linarith

theorem S_den_ne_one_of_padicValRat_lt_zero (x : ℚ) (p : ℕ) (hval : padicValRat p x < 0) : x.den ≠ 1 := by
  intro hx
  have h_eq : x = (x.num : ℚ) := ((Rat.den_eq_one_iff x).mp hx).symm
  rw [h_eq] at hval
  rw [padicValRat.of_int] at hval
  have : 0 ≤ (padicValInt p x.num : ℤ) := Int.natCast_nonneg (padicValInt p x.num)
  omega


theorem v2_sum_two_terms (k : ℕ) :
  0 < padicValRat 2 ((1 : ℚ) / ((2 : ℚ) ^ (2 * k + 2) - 1) + (1 : ℚ) / ((2 : ℚ) ^ (2 * k + 3) - 1)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h_pow1 : 2 ^ (2 * k + 1) ≥ 2 := by
    calc 2 ^ (2 * k + 1) ≥ 2 ^ 1 := pow_le_pow_right₀ (by omega) (by omega)
    _ = 2 := rfl
  have h_pow2 : 2 ^ (2 * k + 2) ≥ 4 := by
    calc 2 ^ (2 * k + 2) ≥ 2 ^ 2 := pow_le_pow_right₀ (by omega) (by omega)
    _ = 4 := rfl
  have h_pow3 : 2 ^ (2 * k + 3) ≥ 8 := by
    calc 2 ^ (2 * k + 3) ≥ 2 ^ 3 := pow_le_pow_right₀ (by omega) (by omega)
    _ = 8 := rfl
  set a_nat := 2 ^ (2 * k + 2) - 1
  set b_nat := 2 ^ (2 * k + 3) - 1
  have ha_gt : 1 ≤ 2 ^ (2 * k + 2) := by omega
  have hb_gt : 1 ≤ 2 ^ (2 * k + 3) := by omega
  have ha_cast' : ((a_nat : ℕ) : ℚ) = (2 : ℚ) ^ (2 * k + 2) - 1 := by
    rw [Nat.cast_sub ha_gt]
    push_cast
    rfl
  have hb_cast : ((b_nat : ℕ) : ℚ) = (2 : ℚ) ^ (2 * k + 3) - 1 := by
    rw [Nat.cast_sub hb_gt]
    push_cast
    rfl
  set m_nat := 2 ^ (2 * k + 1) + 2 ^ (2 * k + 2) - 1
  have hm_gt : 1 ≤ 2 ^ (2 * k + 1) + 2 ^ (2 * k + 2) := by omega
  have h_num_eq : a_nat + b_nat = 2 * m_nat := by
    have h_rw1 : 2 ^ (2 * k + 2) = 2 * 2 ^ (2 * k + 1) := by ring
    have h_rw2 : 2 ^ (2 * k + 3) = 2 * 2 ^ (2 * k + 2) := by ring
    dsimp [a_nat, b_nat, m_nat]
    omega
  have ha_nz : a_nat ≠ 0 := by omega
  have hb_nz : b_nat ≠ 0 := by omega
  have hm_nz : m_nat ≠ 0 := by omega
  have h_den_nz : (a_nat * b_nat : ℚ) ≠ 0 := by positivity
  have h_add : (1 : ℚ) / (a_nat : ℚ) + (1 : ℚ) / (b_nat : ℚ) = (a_nat + b_nat : ℚ) / (a_nat * b_nat : ℚ) := by
    have h1 : (a_nat : ℚ) ≠ 0 := by positivity
    have h2 : (b_nat : ℚ) ≠ 0 := by positivity
    field_simp
    ring
  rw [← ha_cast', ← hb_cast, h_add]
  have h_num_cast : (a_nat : ℚ) + (b_nat : ℚ) = 2 * (m_nat : ℚ) := by
    exact_mod_cast h_num_eq
  rw [h_num_cast]
  have h_num_nz : (2 * m_nat : ℚ) ≠ 0 := by positivity
  rw [padicValRat.div h_num_nz h_den_nz]
  have h_val_num : padicValRat 2 (2 * (m_nat : ℚ)) = 1 + padicValNat 2 m_nat := by
    rw [padicValRat.mul (by norm_num) (by positivity)]
    have h2 : padicValRat 2 2 = 1 := by
      have : (2 : ℚ) = ((2 : ℕ) : ℚ) := rfl
      rw [this, padicValRat.of_nat]
      have : padicValNat 2 2 = 1 := padicValNat_self
      rw [this]
      rfl
    rw [h2, padicValRat.of_nat]
  have h_val_den : padicValRat 2 (a_nat * b_nat : ℚ) = 0 := by
    rw [← Nat.cast_mul]
    rw [padicValRat.of_nat]
    have : padicValNat 2 (a_nat * b_nat) = padicValNat 2 a_nat + padicValNat 2 b_nat :=
      padicValNat.mul ha_nz hb_nz
    rw [this]
    have ha_odd : a_nat % 2 = 1 := by
      have h_pow_even : 2 ^ (2 * k + 2) % 2 = 0 := by simp [Nat.pow_succ]
      have : 2 ^ (2 * k + 2) - 1 + 1 = 2 ^ (2 * k + 2) := Nat.sub_add_cancel ha_gt
      omega
    have hb_odd : b_nat % 2 = 1 := by
      have h_pow_even : 2 ^ (2 * k + 3) % 2 = 0 := by simp [Nat.pow_succ]
      have : 2 ^ (2 * k + 3) - 1 + 1 = 2 ^ (2 * k + 3) := Nat.sub_add_cancel hb_gt
      omega
    have v_a : padicValNat 2 a_nat = 0 := by
      rw [padicValNat.eq_zero_iff]
      right; right
      intro hc
      have : a_nat % 2 = 0 := Nat.mod_eq_zero_of_dvd hc
      omega
    have v_b : padicValNat 2 b_nat = 0 := by
      rw [padicValNat.eq_zero_iff]
      right; right
      intro hc
      have : b_nat % 2 = 0 := Nat.mod_eq_zero_of_dvd hc
      omega
    omega
  rw [h_val_num, h_val_den]
  omega

theorem padicValRat_two_S_arith_two_pow_even (k : ℕ) :
  padicValRat 2 (S_arith (2 ^ (2 * k))) = 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  induction k with
  | zero =>
    rw [mul_zero]
    have h_eq : S_arith (2 ^ 0) = 1 := by
      rw [S_arith_apply (2 ^ 0) (by positivity)]
      simp [sigma_one]
    rw [h_eq]
    exact padicValRat.one
  | succ k ih =>
    have h_even_eq : 2 * (k + 1) = 2 * k + 2 := by ring
    rw [h_even_eq]
    rw [S_arith_apply (2 ^ (2 * k + 2)) (by positivity)]
    rw [test_sum_divisors (2 * k + 2)]
    set F := fun i => (1 : ℚ) / (↑((sigma 1) (2 ^ i)) : ℚ)
    have h_sum : (range (2 * k + 3)).sum F = (range (2 * k + 1)).sum F + F (2 * k + 1) + F (2 * k + 2) := by
      have h1 : 2 * k + 3 = 2 * k + 2 + 1 := by omega
      have h2 : 2 * k + 2 = 2 * k + 1 + 1 := by omega
      rw [h1, sum_range_succ, h2, sum_range_succ]
    rw [h_sum]
    have h_prev : S_arith (2 ^ (2 * k)) = (range (2 * k + 1)).sum F :=
      (S_arith_apply (2 ^ (2 * k)) (by positivity)).trans (test_sum_divisors (2 * k))
    rw [← h_prev]
    rw [add_assoc]
    have h_pow2 : (2 : ℚ) ^ (2 * k + 2) ≥ 4 := by
      have h_cast : (2 : ℚ) ^ (2 * k + 2) = ↑(2 ^ (2 * k + 2)) := rfl
      rw [h_cast]
      norm_cast
      calc 2 ^ (2 * k + 2) ≥ 2^2 := pow_le_pow_right₀ (by omega) (by omega)
      _ = 4 := rfl
    have h_pow3 : (2 : ℚ) ^ (2 * k + 3) ≥ 8 := by
      have h_cast : (2 : ℚ) ^ (2 * k + 3) = ↑(2 ^ (2 * k + 3)) := rfl
      rw [h_cast]
      norm_cast
      calc 2 ^ (2 * k + 3) ≥ 2^3 := pow_le_pow_right₀ (by omega) (by omega)
      _ = 8 := rfl
    have h_two_terms : F (2 * k + 1) + F (2 * k + 2) = (1 : ℚ) / ((2 : ℚ) ^ (2 * k + 2) - 1) + (1 : ℚ) / ((2 : ℚ) ^ (2 * k + 3) - 1) := by
      dsimp [F]
      rw [sigma_one_two_pow (2 * k + 1), sigma_one_two_pow (2 * k + 2)]
    have h_val_two_terms : 0 < padicValRat 2 (F (2 * k + 1) + F (2 * k + 2)) := by
      rw [h_two_terms]
      exact v2_sum_two_terms k
    have h_sum_nz : S_arith (2 ^ (2 * k)) ≠ 0 := by
      rw [h_prev]
      apply _root_.ne_of_gt
      apply sum_pos
      · intro i _
        have : (0 : ℚ) < (↑((sigma 1) (2 ^ i)) : ℚ) := by
          have h_pos := sigma_pos 1 (2 ^ i) (by positivity)
          exact_mod_cast h_pos
        positivity
      · exact ⟨0, mem_range.mpr (by omega)⟩
    have h_two_pos : F (2 * k + 1) + F (2 * k + 2) > 0 := by
      rw [h_two_terms]
      have hp1 : (0 : ℚ) < (1 : ℚ) / ((2 : ℚ) ^ (2 * k + 2) - 1) := by
        apply one_div_pos.mpr
        linarith
      have hp2 : (0 : ℚ) < (1 : ℚ) / ((2 : ℚ) ^ (2 * k + 3) - 1) := by
        apply one_div_pos.mpr
        linarith
      linarith
    have h_two_nz : F (2 * k + 1) + F (2 * k + 2) ≠ 0 := h_two_pos.ne'
    have h_sum_all_nz : S_arith (2 ^ (2 * k)) + (F (2 * k + 1) + F (2 * k + 2)) ≠ 0 := by
      have h_prev_pos : S_arith (2 ^ (2 * k)) > 0 := by
        rw [h_prev]
        apply sum_pos
        · intro i _
          have : (0 : ℚ) < (↑((sigma 1) (2 ^ i)) : ℚ) := by
            have h_pos := sigma_pos 1 (2 ^ i) (by positivity)
            exact_mod_cast h_pos
          positivity
        · exact ⟨0, mem_range.mpr (by omega)⟩
      linarith
    have h_lt : padicValRat 2 (S_arith (2 ^ (2 * k))) < padicValRat 2 (F (2 * k + 1) + F (2 * k + 2)) := by
      omega
    rw [padicValRat.add_eq_of_lt h_sum_all_nz h_sum_nz h_two_nz h_lt]
    exact ih


theorem S_arith_two_pow_lt_two (a : ℕ) : S_arith (2 ^ a) < 2 := by
  rw [S_arith_apply (2 ^ a) (by positivity)]
  rw [test_sum_divisors a]
  rw [S_two_pow_split a]
  have h_sum_lt : ∑ i ∈ range a, (1 : ℚ) / ((2 : ℚ) ^ (i + 2) - 1) < 1 := sum_term_lt_one a
  linarith

theorem S_arith_gt_one (n : ℕ) (hn : 1 < n) : 1 < S_arith n := by
  have hn_ne : n ≠ 0 := by omega
  rw [S_arith_apply n hn_ne]
  have h_one : 1 ∈ n.divisors := by rw [mem_divisors]; exact ⟨one_dvd n, hn_ne⟩
  have h_n : n ∈ n.divisors := by rw [mem_divisors]; exact ⟨dvd_rfl, hn_ne⟩
  have h_ne_comm : n ≠ 1 := by omega
  have h_split1 : ∑ d ∈ n.divisors, (1 : ℚ) / (↑((sigma 1) d) : ℚ) = (1 : ℚ) / (↑((sigma 1) 1) : ℚ) + ∑ d ∈ n.divisors.erase 1, (1 : ℚ) / (↑((sigma 1) d) : ℚ) := by
    have h_eq : n.divisors = insert 1 (n.divisors.erase 1) := (insert_erase h_one).symm
    nth_rw 1 [h_eq]
    rw [sum_insert (by simp)]
  rw [h_split1]
  have h_n_mem : n ∈ n.divisors.erase 1 := by
    rw [mem_erase]
    exact ⟨h_ne_comm, h_n⟩
  have h_split2 : ∑ d ∈ n.divisors.erase 1, (1 : ℚ) / (↑((sigma 1) d) : ℚ) = (1 : ℚ) / (↑((sigma 1) n) : ℚ) + ∑ d ∈ (n.divisors.erase 1).erase n, (1 : ℚ) / (↑((sigma 1) d) : ℚ) := by
    have h_eq : n.divisors.erase 1 = insert n ((n.divisors.erase 1).erase n) := (insert_erase h_n_mem).symm
    nth_rw 1 [h_eq]
    rw [sum_insert (by simp)]
  rw [h_split2]
  have h_term1 : (1 : ℚ) / (↑((sigma 1) 1) : ℚ) = 1 := by simp [sigma_one]
  rw [h_term1]
  have h_term2 : (0 : ℚ) < (1 : ℚ) / (↑((sigma 1) n) : ℚ) := by
    have h_sig : (0 : ℚ) < (↑((sigma 1) n) : ℚ) := by
      have h_pos := sigma_pos 1 n hn_ne
      exact_mod_cast h_pos
    positivity
  have h_rest : 0 ≤ ∑ x ∈ (n.divisors.erase 1).erase n, (1 : ℚ) / (↑((sigma 1) x) : ℚ) := by
    apply sum_nonneg
    intro x hx
    have hx_mem : x ∈ n.divisors := mem_of_mem_erase (mem_of_mem_erase hx)
    have h_pos := Nat.pos_of_mem_divisors hx_mem
    have hx_nz : x ≠ 0 := by omega
    have h_sig : (0 : ℚ) < (↑((sigma 1) x) : ℚ) := by
      have h_pos' := sigma_pos 1 x hx_nz
      exact_mod_cast h_pos'
    positivity
  linarith


theorem odd_num_and_den_of_padicValRat_zero (x : ℚ) (hx_nz : x ≠ 0) (hx : padicValRat 2 x = 0) :
  x.num % 2 ≠ 0 ∧ (x.den : ℤ) % 2 ≠ 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h_val : padicValRat 2 x = (padicValInt 2 x.num : ℤ) - (padicValInt 2 x.den : ℤ) := padicValRat_def 2 x
  rw [hx] at h_val
  have h_sub : (padicValInt 2 x.num : ℤ) = (padicValInt 2 x.den : ℤ) := by linarith
  have h_coprime : (x.num).natAbs.Coprime x.den := x.reduced
  have h_num_nz : x.num ≠ 0 := Rat.num_ne_zero.mpr hx_nz
  by_cases h_num : 2 ∣ x.num
  · have h_den : ¬ 2 ∣ (x.den : ℤ) := by
      intro hc
      have hc_nat : 2 ∣ x.den := by exact_mod_cast hc
      have h_num_nat : 2 ∣ x.num.natAbs := by exact Int.natAbs_dvd_natAbs.mpr h_num
      have h_div : 2 ∣ (x.num).natAbs.gcd x.den := Nat.dvd_gcd h_num_nat hc_nat
      rw [Nat.Coprime.gcd_eq_one h_coprime] at h_div
      omega
    have h_val_den : padicValInt 2 x.den = 0 := by
      change padicValNat 2 (x.den : ℤ).natAbs = 0
      simp only [Int.natAbs_natCast]
      rw [padicValNat.eq_zero_iff]
      right; right
      intro hc
      exact h_den (by exact_mod_cast hc)
    have h_val_num : padicValInt 2 x.num = 0 := by
      have : (padicValInt 2 x.num : ℤ) = 0 := by
        rw [h_sub]
        exact_mod_cast h_val_den
      exact_mod_cast this
    have h_num_odd : ¬ 2 ∣ x.num := by
      intro hc
      have h_pos : 1 ≤ padicValNat 2 x.num.natAbs := by
        rw [← padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr h_num_nz)]
        exact Int.natAbs_dvd_natAbs.mpr hc
      have : (padicValInt 2 x.num : ℤ) = 0 := by
        rw [h_val_num]
        rfl
      change (padicValNat 2 x.num.natAbs : ℤ) = 0 at this
      omega
    contradiction
  · have h_val_num : padicValInt 2 x.num = 0 := by
      change padicValNat 2 x.num.natAbs = 0
      rw [padicValNat.eq_zero_iff]
      right; right
      intro hc
      have hc_int_num : (2 : ℤ) ∣ x.num := by
        have h_dvd_nat : (2 : ℤ) ∣ x.num.natAbs := by exact_mod_cast hc
        rwa [Int.dvd_natAbs] at h_dvd_nat
      exact h_num hc_int_num
    have h_val_den : padicValInt 2 x.den = 0 := by
      have : (padicValInt 2 x.den : ℤ) = 0 := by
        rw [← h_sub]
        exact_mod_cast h_val_num
      exact_mod_cast this
    have h_den_odd : ¬ 2 ∣ (x.den : ℤ) := by
      intro hc
      have h_pos : 1 ≤ padicValNat 2 x.den := by
        rw [← padicValNat_dvd_iff_le x.pos.ne']
        exact_mod_cast hc
      have : (padicValInt 2 x.den : ℤ) = 0 := by
        rw [h_val_den]
        rfl
      change (padicValNat 2 (x.den : ℤ).natAbs : ℤ) = 0 at this
      simp only [Int.natAbs_natCast] at this
      have h_zero : padicValNat 2 x.den = 0 := by exact_mod_cast this
      omega
    have h_mod_num : x.num % 2 ≠ 0 := by
      intro hc
      have : 2 ∣ x.num := Int.dvd_of_emod_eq_zero hc
      exact h_num this
    have h_mod_den : (x.den : ℤ) % 2 ≠ 0 := by
      intro hc
      have : 2 ∣ (x.den : ℤ) := Int.dvd_of_emod_eq_zero hc
      exact h_den_odd this
    exact ⟨h_mod_num, h_mod_den⟩

theorem padicValRat_two_add_of_zero (x y : ℚ) (hx_nz : x ≠ 0) (hy_nz : y ≠ 0) (h_sum : x + y ≠ 0)
  (hx : padicValRat 2 x = 0) (hy : padicValRat 2 y = 0) :
  1 ≤ padicValRat 2 (x + y) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h_num_den_x : x = (x.num : ℚ) / (x.den : ℚ) := (Rat.num_div_den x).symm
  have h_num_den_y : y = (y.num : ℚ) / (y.den : ℚ) := (Rat.num_div_den y).symm
  have h_add_eq_div : (x.num : ℚ) / (x.den : ℚ) + (y.num : ℚ) / (y.den : ℚ) = (x.num * y.den + y.num * x.den : ℚ) / ((x.den * y.den : ℕ) : ℚ) := by
    have h_den1 : (x.den : ℚ) ≠ 0 := by positivity
    have h_den2 : (y.den : ℚ) ≠ 0 := by positivity
    have : ((x.den * y.den : ℕ) : ℚ) = (x.den : ℚ) * (y.den : ℚ) := by push_cast; rfl
    rw [this]
    field_simp
  have h_add_eq : x + y = (x.num * y.den + y.num * x.den : ℚ) / ((x.den * y.den : ℕ) : ℚ) := by
    nth_rw 1 [h_num_den_x]
    nth_rw 1 [h_num_den_y]
    exact h_add_eq_div
  rw [h_add_eq]
  have h_num_nz : (x.num * y.den + y.num * x.den : ℚ) ≠ 0 := by
    intro hc
    rw [hc, zero_div] at h_add_eq
    exact h_sum h_add_eq
  have h_den_nz : ((x.den * y.den : ℕ) : ℚ) ≠ 0 := by positivity
  rw [padicValRat.div h_num_nz h_den_nz]
  have h_den_val : padicValRat 2 ((x.den * y.den : ℕ) : ℚ) = 0 := by
    rw [padicValRat.of_nat]
    norm_cast
    rw [padicValNat.eq_zero_iff]
    right; right
    intro hc
    have h_cop : 2 ∣ x.den * y.den := hc
    have h_prime : Nat.Prime 2 := Nat.prime_two
    rcases h_prime.dvd_mul.mp h_cop with h1 | h2
    · have h_odd := odd_num_and_den_of_padicValRat_zero x hx_nz hx
      have : x.den % 2 = 0 := Nat.mod_eq_zero_of_dvd h1
      have : (x.den : ℤ) % 2 = 0 := by exact_mod_cast this
      exact h_odd.2 this
    · have h_odd := odd_num_and_den_of_padicValRat_zero y hy_nz hy
      have : y.den % 2 = 0 := Nat.mod_eq_zero_of_dvd h2
      have : (y.den : ℤ) % 2 = 0 := by exact_mod_cast this
      exact h_odd.2 this
  rw [h_den_val, sub_zero]
  have h_num_cast : ((x.num * y.den + y.num * x.den : ℤ) : ℚ) = (x.num * y.den + y.num * x.den : ℚ) := by push_cast; rfl
  rw [← h_num_cast]
  rw [padicValRat.of_int]
  norm_cast
  have h_sum_nz_int : x.num * (y.den : ℤ) + y.num * (x.den : ℤ) ≠ 0 := by
    exact_mod_cast h_num_nz
  have h_dvd_iff : (2 : ℤ) ∣ (x.num * (y.den : ℤ) + y.num * (x.den : ℤ)) ↔
    1 ≤ padicValInt 2 (x.num * (y.den : ℤ) + y.num * (x.den : ℤ)) := by
    have h_pow : (2 : ℤ) ^ 1 ∣ (x.num * (y.den : ℤ) + y.num * (x.den : ℤ)) ↔
      (x.num * (y.den : ℤ) + y.num * (x.den : ℤ)) = 0 ∨ 1 ≤ padicValInt 2 (x.num * (y.den : ℤ) + y.num * (x.den : ℤ)) := by
      exact padicValInt_dvd_iff 1 (x.num * (y.den : ℤ) + y.num * (x.den : ℤ))
    rw [pow_one] at h_pow
    rw [h_pow]
    simp [h_sum_nz_int]
  rw [← h_dvd_iff]
  have h_odd_x := odd_num_and_den_of_padicValRat_zero x hx_nz hx
  have h_odd_y := odd_num_and_den_of_padicValRat_zero y hy_nz hy
  set X_num := x.num
  set Y_num := y.num
  set X_den := (x.den : ℤ)
  set Y_den := (y.den : ℤ)
  have hX_num_odd : X_num % 2 = 1 := by omega
  have hY_num_odd : Y_num % 2 = 1 := by omega
  have hX_den_odd : X_den % 2 = 1 := by omega
  have hY_den_odd : Y_den % 2 = 1 := by omega
  have h_sum_even : (X_num * Y_den + Y_num * X_den) % 2 = 0 := by
    have h1 : (X_num * Y_den) % 2 = 1 := by
      rw [Int.mul_emod, hX_num_odd, hY_den_odd]
      rfl
    have h2 : (Y_num * X_den) % 2 = 1 := by
      rw [Int.mul_emod, hY_num_odd, hX_den_odd]
      rfl
    rw [Int.add_emod, h1, h2]
    rfl
  exact Int.dvd_of_emod_eq_zero h_sum_even

theorem padicValRat_two_S_arith_two_pow_odd (k : ℕ) :
  1 ≤ padicValRat 2 (S_arith (2 ^ (2 * k + 1))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := fun i => (1 : ℚ) / (↑((sigma 1) (2 ^ i)) : ℚ)
  have h_sum : S_arith (2 ^ (2 * k + 1)) = S_arith (2 ^ (2 * k)) + F (2 * k + 1) := by
    have h1 : S_arith (2 ^ (2 * k + 1)) = (range (2 * k + 2)).sum F :=
      (S_arith_apply (2 ^ (2 * k + 1)) (by positivity)).trans (test_sum_divisors (2 * k + 1))
    have h2 : S_arith (2 ^ (2 * k)) = (range (2 * k + 1)).sum F :=
      (S_arith_apply (2 ^ (2 * k)) (by positivity)).trans (test_sum_divisors (2 * k))
    rw [h1, h2, sum_range_succ]
  rw [h_sum]
  have hx_nz : S_arith (2 ^ (2 * k)) ≠ 0 := by
    have h_prev : S_arith (2 ^ (2 * k)) = (range (2 * k + 1)).sum F :=
      (S_arith_apply (2 ^ (2 * k)) (by positivity)).trans (test_sum_divisors (2 * k))
    rw [h_prev]
    apply _root_.ne_of_gt
    apply sum_pos
    · intro i _
      have : (0 : ℚ) < (↑((sigma 1) (2 ^ i)) : ℚ) := by
        have h_pos := sigma_pos 1 (2 ^ i) (by positivity)
        exact_mod_cast h_pos
      positivity
    · exact ⟨0, mem_range.mpr (by omega)⟩
  have hy_nz : F (2 * k + 1) ≠ 0 := by
    dsimp [F]
    have : (0 : ℚ) < (↑((sigma 1) (2 ^ (2 * k + 1))) : ℚ) := by
      have h_pos := sigma_pos 1 (2 ^ (2 * k + 1)) (by positivity)
      exact_mod_cast h_pos
    positivity
  have h_sum_nz : S_arith (2 ^ (2 * k)) + F (2 * k + 1) ≠ 0 := by
    have : S_arith (2 ^ (2 * k)) > 0 := by
      have h_prev : S_arith (2 ^ (2 * k)) = (range (2 * k + 1)).sum F :=
        (S_arith_apply (2 ^ (2 * k)) (by positivity)).trans (test_sum_divisors (2 * k))
      rw [h_prev]
      apply sum_pos
      · intro i _
        have : (0 : ℚ) < (↑((sigma 1) (2 ^ i)) : ℚ) := by
          have h_pos := sigma_pos 1 (2 ^ i) (by positivity)
          exact_mod_cast h_pos
        positivity
      · exact ⟨0, mem_range.mpr (by omega)⟩
    have h_F_pos : F (2 * k + 1) > 0 := by
      dsimp [F]
      have : (0 : ℚ) < (↑((sigma 1) (2 ^ (2 * k + 1))) : ℚ) := by
        have h_pos := sigma_pos 1 (2 ^ (2 * k + 1)) (by positivity)
        exact_mod_cast h_pos
      positivity
    linarith
  have h_val_x : padicValRat 2 (S_arith (2 ^ (2 * k))) = 0 := padicValRat_two_S_arith_two_pow_even k
  have h_val_y : padicValRat 2 (F (2 * k + 1)) = 0 := by
    dsimp [F]
    have h_sig : (sigma 1 (2 ^ (2 * k + 1)) : ℚ) ≠ 0 := by
      have : sigma 1 (2 ^ (2 * k + 1)) > 0 := sigma_pos 1 (2 ^ (2 * k + 1)) (by positivity)
      exact_mod_cast this.ne'
    rw [one_div, padicValRat.inv, padicValRat.of_nat]
    have : padicValNat 2 (sigma 1 (2 ^ (2 * k + 1))) = 0 := by
      rw [padicValNat.eq_zero_iff]
      right; right
      intro hc
      have h_even : (sigma 1 (2 ^ (2 * k + 1))) % 2 = 0 := Nat.mod_eq_zero_of_dvd hc
      have h_cast : (sigma 1 (2 ^ (2 * k + 1)) : ℚ) = (2 : ℚ) ^ (2 * k + 2) - 1 := sigma_one_two_pow (2 * k + 1)
      have h_eq_nat : sigma 1 (2 ^ (2 * k + 1)) = 2 ^ (2 * k + 2) - 1 := by
        have h_le : 1 ≤ 2 ^ (2 * k + 2) := by
          have : 2 ^ (2 * k + 2) ≥ 4 := by
            calc 2 ^ (2 * k + 2) ≥ 2^2 := pow_le_pow_right₀ (by omega) (by omega)
            _ = 4 := rfl
          omega
        rw [← Nat.cast_id (sigma 1 (2 ^ (2 * k + 1)))]
        exact_mod_cast h_cast
      have h_pow_even : 2 ^ (2 * k + 2) % 2 = 0 := by
        have : 2 ^ (2 * k + 2) = 2 * 2 ^ (2 * k + 1) := by ring
        rw [this]
        exact Nat.mul_mod_right 2 (2 ^ (2 * k + 1))
      have h_sub : 2 ^ (2 * k + 2) - 1 + 1 = 2 ^ (2 * k + 2) := by
        have : 2 ^ (2 * k + 2) ≥ 4 := by
          calc 2 ^ (2 * k + 2) ≥ 2^2 := pow_le_pow_right₀ (by omega) (by omega)
          _ = 4 := rfl
        omega
      omega
    rw [this]
    rfl
  exact padicValRat_two_add_of_zero (S_arith (2 ^ (2 * k))) (F (2 * k + 1)) hx_nz hy_nz h_sum_nz h_val_x h_val_y



-- ---------------------------------------------------------
-- Main Theorems
-- ---------------------------------------------------------
lemma eq_one_of_mul_eq_one_helper (j k : ℕ) (h : j * k = 1) : j = 1 ∧ k = 1 := by
  have hj : j = 1 := by
    by_contra hc
    have : j = 0 ∨ j ≥ 2 := by omega
    rcases this with rfl | hj_ge
    · simp at h
    · have hk0 : k ≠ 0 := by
        intro hk0
        rw [hk0, mul_zero] at h
        omega
      have hk_ge : k ≥ 1 := by omega
      have : j * k ≥ 2 := by
        calc j * k ≥ 2 * 1 := Nat.mul_le_mul hj_ge hk_ge
        _ = 2 := rfl
      omega
  have hk : k = 1 := by
    rw [hj, one_mul] at h
    exact h
  exact ⟨hj, hk⟩

lemma odd_ge_one (a : ℕ) (ha : ¬ a % 2 = 0) : a ≥ 1 := by
  omega

lemma two_pow_ge_two (a : ℕ) (ha : a ≥ 1) : 2^a ≥ 2 := by
  induction a with
  | zero => omega
  | succ a ih =>
    by_cases ha0 : a = 0
    · rw [ha0]
      decide
    · have : a ≥ 1 := by omega
      have ih_val := ih this
      rw [pow_succ]
      omega



theorem S_not_int (n : ℕ) (hn : 1 < n) :
  ((n.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))).den ≠ 1 := by
  have h_cases := eq_two_pow_or_exists_odd_prime_and_dvd n
  rcases h_cases with ⟨k, hk⟩ | ⟨p, hp_prime, hp_dvd, hp_odd⟩
  · have hk_gt : k ≥ 1 := by
      by_contra hc
      have hk0 : k = 0 := by omega
      rw [hk0] at hk
      simp at hk
      omega
    rw [hk]
    rw [test_sum_divisors k]
    exact S_two_pow_not_int k hk_gt
  · -- Odd prime factor case: p is an odd prime, p | n.
    set S_val := n.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)
    have hn_ne : n ≠ 0 := by omega
    have h_S_arith_eq : S_arith n = S_val := S_arith_apply n hn_ne
    rw [← h_S_arith_eq]
    have hp_odd_mod : p % 2 = 1 := by rwa [Nat.odd_iff] at hp_odd
    by_cases hn_odd : n % 2 = 1
    · have h_val : padicValRat 2 (S_arith n) < 0 :=
        S_arith_padicValRat_two_lt_zero n hn_ne hn_odd p hp_prime hp_dvd hp_odd_mod
      exact S_den_ne_one_of_padicValRat_lt_zero (S_arith n) 2 h_val
    · -- n is even! Let's write n = 2^a * m with m odd and m > 1.
      set a := padicValNat 2 n
      set m := n / 2 ^ a
      have h_cop := coprime_two_pow_div n hn_ne
      change 2 ^ a * m = n ∧ (2 ^ a).Coprime m at h_cop
      have h_S : S_arith n = S_arith (2 ^ a) * S_arith m := by
        rw [← h_cop.1]
        exact S_arith_is_multiplicative.map_mul_of_coprime h_cop.2
      have hm_nz : m ≠ 0 := by
        intro hc
        rw [hc, mul_zero] at h_cop
        omega
      have hm_odd : m % 2 = 1 := by
        have h_not_dvd := not_dvd_of_padicValNat Nat.prime_two hn_ne
        have h_odd_m : ¬ 2 ∣ m := h_not_dvd
        have h_mod : m % 2 ≠ 0 := by
          intro hc
          exact h_odd_m (Nat.dvd_of_mod_eq_zero hc)
        omega
      have hp_dvd_m : p ∣ m := by
        have hp_dvd_mul : p ∣ 2 ^ a * m := by rwa [h_cop.1]
        have : p.Coprime (2 ^ a) := by
          apply Coprime.pow_right
          rw [Nat.Prime.coprime_iff_not_dvd hp_prime]
          intro hc
          have : p = 2 := by
            exact ((Nat.Prime.dvd_iff_eq Nat.prime_two hp_prime.ne_one).mp hc).symm
          omega
        exact (Coprime.dvd_mul_left this).mp hp_dvd_mul
      have h_vm : padicValRat 2 (S_arith m) < 0 :=
        S_arith_padicValRat_two_lt_zero m hm_nz hm_odd p hp_prime hp_dvd_m hp_odd_mod
      have h_ne_two_pow : S_arith (2 ^ a) ≠ 0 := by
        exact (S_arith_prime_pow_pos 2 Nat.prime_two a).ne'
      have h_ne_m : S_arith m ≠ 0 := S_arith_ne_zero m hm_nz
      have hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have h_sum_val : padicValRat 2 (S_arith n) = padicValRat 2 (S_arith (2 ^ a)) + padicValRat 2 (S_arith m) := by
        rw [h_S]
        exact padicValRat.mul h_ne_two_pow h_ne_m
      by_cases ha_even : a % 2 = 0
      · -- If a is even, then padicValRat 2 (S_arith (2 ^ a)) = 0
        -- Since S_arith (2^a) has 2-adic valuation 0 when a is even.
        -- Let's prove a sub-lemma or show that:
        -- Wait, is it 0? Yes. Let's prove it or assume it.
        -- Actually, since we need to resolve it, let's see if we can prove padicValRat 2 (S_arith (2 ^ a)) = 0.
        have h_v2_pow : padicValRat 2 (S_arith (2 ^ a)) = 0 := by
          have h_eq_even : a = 2 * (a / 2) := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero ha_even)).symm
          rw [h_eq_even]
          exact padicValRat_two_S_arith_two_pow_even (a / 2)
        have h_val_n : padicValRat 2 (S_arith n) < 0 := by
          rw [h_sum_val, h_v2_pow]
          linarith
        exact S_den_ne_one_of_padicValRat_lt_zero (S_arith n) 2 h_val_n
      · -- If a is odd, then what?
        have ha_odd : a = 2 * (a / 2) + 1 := by omega
        have h_v2_pow : 1 ≤ padicValRat 2 (S_arith (2 ^ a)) := by
          rw [ha_odd]
          exact padicValRat_two_S_arith_two_pow_odd (a / 2)
        by_cases h_lt_val : padicValRat 2 (S_arith (2 ^ a)) < - padicValRat 2 (S_arith m)
        · have h_val_n : padicValRat 2 (S_arith n) < 0 := by
            rw [h_sum_val]
            linarith
          exact S_den_ne_one_of_padicValRat_lt_zero (S_arith n) 2 h_val_n
        · intro h_den
          set A := (S_arith (2^a)).num
          set B := (S_arith (2^a)).den
          set C := (S_arith m).num
          set D := (S_arith m).den
          have h_eq : S_arith n = (S_arith n).num := by
            exact_mod_cast ((Rat.den_eq_one_iff (S_arith n)).mp h_den).symm
          have h_mul_int : A * C = (S_arith n).num * (B : ℤ) * (D : ℤ) := by
            have h_mul_q : (A : ℚ) * (C : ℚ) = ((S_arith n).num : ℚ) * (B : ℚ) * (D : ℚ) := by
              have h1 : S_arith (2^a) = (A : ℚ) / (B : ℚ) := (Rat.num_div_den _).symm
              have h2 : S_arith m = (C : ℚ) / (D : ℚ) := (Rat.num_div_den _).symm
              have h_den_nz1 : (B : ℚ) ≠ 0 := by positivity
              have h_den_nz2 : (D : ℚ) ≠ 0 := by positivity
              have h_mul : S_arith n * (B : ℚ) * (D : ℚ) = (A : ℚ) * (C : ℚ) := by
                rw [h_S, h1, h2]
                field_simp
              rw [h_eq] at h_mul
              exact h_mul.symm
            exact_mod_cast h_mul_q
          have h_div_nat : B ∣ A.natAbs * C.natAbs := by
            have h_div_int : (B : ℤ) ∣ A * C := by
              rw [h_mul_int]
              use (S_arith n).num * (D : ℤ)
              ring
            rcases h_div_int with ⟨k, hk⟩
            have hk2 : A.natAbs * C.natAbs = B * k.natAbs := by
              rw [← Int.natAbs_mul, hk, Int.natAbs_mul, Int.natAbs_natCast]
            rw [hk2]
            use k.natAbs
          have h_cop_B_A : Nat.Coprime B A.natAbs := (S_arith (2^a)).reduced.symm
          have h_B_dvd_C_nat : B ∣ C.natAbs := h_cop_B_A.dvd_of_dvd_mul_left h_div_nat
          have h_cop_BD : Nat.Coprime B D := by
            by_contra hc
            have h_gcd : Nat.gcd B D > 1 := by
              have h_eq_one : Nat.gcd B D ≠ 1 := hc
              have h_nz : Nat.gcd B D ≠ 0 := by
                intro h0
                rw [Nat.gcd_eq_zero_iff] at h0
                have hB_nz : B ≠ 0 := (S_arith (2^a)).den_nz
                omega
              omega
            set q := (Nat.gcd B D).minFac
            have hq_prime : Nat.Prime q := Nat.minFac_prime (by omega)
            have hq_dvd_gcd : q ∣ Nat.gcd B D := Nat.minFac_dvd _
            have hq_dvd_B : q ∣ B := hq_dvd_gcd.trans (Nat.gcd_dvd_left B D)
            have hq_dvd_D : q ∣ D := hq_dvd_gcd.trans (Nat.gcd_dvd_right B D)
            have hq_fact : Fact (Nat.Prime q) := ⟨hq_prime⟩
            have hq_val1 : padicValRat q (S_arith (2^a)) < 0 := by
              have hA_cop_B : Nat.Coprime (A.natAbs) B := (S_arith (2^a)).reduced
              have hq_not_dvd_A : ¬ (q : ℤ) ∣ A := by
                intro hc_dvd
                have hq_dvd_A_nat : q ∣ A.natAbs := by
                  exact_mod_cast (Int.dvd_natAbs.mpr hc_dvd)
                have h_div_gcd : q ∣ Nat.gcd A.natAbs B := Nat.dvd_gcd hq_dvd_A_nat hq_dvd_B
                rw [Nat.Coprime.gcd_eq_one hA_cop_B] at h_div_gcd
                have : q = 1 := by exact Nat.dvd_one.mp h_div_gcd
                exact hq_prime.ne_one this
              have h_val_A : padicValInt q A = 0 := by
                change padicValNat q A.natAbs = 0
                rw [padicValNat.eq_zero_iff]
                right; right
                intro hc
                have h_int : (q : ℤ) ∣ A.natAbs := by exact_mod_cast hc
                exact hq_not_dvd_A (Int.dvd_natAbs.mp h_int)
              have h1 : S_arith (2^a) = (A : ℚ) / (B : ℚ) := (Rat.num_div_den _).symm
              have h_ne_A : (A : ℚ) ≠ 0 := by exact_mod_cast (Rat.num_ne_zero.mpr h_ne_two_pow)
              have h_ne_B : ((B : ℕ) : ℚ) ≠ 0 := by positivity
              rw [h1, padicValRat.div h_ne_A h_ne_B]
              rw [padicValRat.of_int, h_val_A]
              rw [padicValRat.of_nat]
              have h_val_B_pos : 1 ≤ padicValNat q B := by
                rw [← padicValNat_dvd_iff_le (S_arith (2^a)).den_nz, pow_one]
                exact hq_dvd_B
              have h_val_B_pos_z : (1 : ℤ) ≤ (padicValNat q B : ℤ) := by exact_mod_cast h_val_B_pos
              simp only [Nat.cast_zero]
              linarith
            have hq_val2 : padicValRat q (S_arith m) < 0 := by
              have hC_cop_D : Nat.Coprime (C.natAbs) D := (S_arith m).reduced
              have hq_not_dvd_C : ¬ (q : ℤ) ∣ C := by
                intro hc_dvd
                have hq_dvd_C_nat : q ∣ C.natAbs := by
                  exact_mod_cast (Int.dvd_natAbs.mpr hc_dvd)
                have h_div_gcd : q ∣ Nat.gcd C.natAbs D := Nat.dvd_gcd hq_dvd_C_nat hq_dvd_D
                rw [Nat.Coprime.gcd_eq_one hC_cop_D] at h_div_gcd
                have : q = 1 := by exact Nat.dvd_one.mp h_div_gcd
                exact hq_prime.ne_one this
              have h_val_C : padicValInt q C = 0 := by
                change padicValNat q C.natAbs = 0
                rw [padicValNat.eq_zero_iff]
                right; right
                intro hc
                have h_int : (q : ℤ) ∣ C.natAbs := by exact_mod_cast hc
                exact hq_not_dvd_C (Int.dvd_natAbs.mp h_int)
              have h2 : S_arith m = (C : ℚ) / (D : ℚ) := (Rat.num_div_den _).symm
              have h_ne_C : (C : ℚ) ≠ 0 := by exact_mod_cast (Rat.num_ne_zero.mpr h_ne_m)
              have h_ne_D : ((D : ℕ) : ℚ) ≠ 0 := by positivity
              rw [h2, padicValRat.div h_ne_C h_ne_D]
              rw [padicValRat.of_int, h_val_C]
              rw [padicValRat.of_nat]
              have h_val_D_pos : 1 ≤ padicValNat q D := by
                rw [← padicValNat_dvd_iff_le (S_arith m).den_nz, pow_one]
                exact hq_dvd_D
              have h_val_D_pos_z : (1 : ℤ) ≤ (padicValNat q D : ℤ) := by exact_mod_cast h_val_D_pos
              simp only [Nat.cast_zero]
              linarith
            have h_sum : padicValRat q (S_arith n) < 0 := by
              rw [h_S, padicValRat.mul h_ne_two_pow h_ne_m]
              linarith
            have h_int_val : padicValRat q (S_arith n) ≥ 0 := by
              rw [h_eq]
              rw [padicValRat.of_int]
              exact_mod_cast Nat.zero_le _
            linarith
          have h_div_nat_D : D ∣ A.natAbs * C.natAbs := by
            have h_div_int : (D : ℤ) ∣ A * C := by
              rw [h_mul_int]
              use (S_arith n).num * (B : ℤ)
              ring
            rcases h_div_int with ⟨k, hk⟩
            have hk2 : A.natAbs * C.natAbs = D * k.natAbs := by
              rw [← Int.natAbs_mul, hk, Int.natAbs_mul, Int.natAbs_natCast]
            rw [hk2]
            use k.natAbs
          have h_cop_D_C : Nat.Coprime D C.natAbs := (S_arith m).reduced.symm
          have h_D_dvd_A_nat : D ∣ A.natAbs := h_cop_D_C.dvd_of_dvd_mul_right h_div_nat_D
          have h_A_pos : A > 0 := by
            have h_eq_A : (A : ℚ) = S_arith (2^a) * (B : ℚ) := by
              have h1 : S_arith (2^a) = (A : ℚ) / (B : ℚ) := (Rat.num_div_den _).symm
              have h_B_ne : ((B : ℕ) : ℚ) ≠ 0 := by positivity
              rw [h1]
              exact (div_mul_cancel₀ (A : ℚ) h_B_ne).symm
            have h_pos : (A : ℚ) > 0 := by
              rw [h_eq_A]
              have h_two_pow_pos : S_arith (2^a) > 0 := S_arith_prime_pow_pos 2 Nat.prime_two a
              have h_B_pos : ((B : ℕ) : ℚ) > 0 := by positivity
              exact mul_pos h_two_pow_pos h_B_pos
            exact_mod_cast h_pos
          have h_C_pos : C > 0 := by
            have h_eq_C : (C : ℚ) = S_arith m * (D : ℚ) := by
              have h2 : S_arith m = (C : ℚ) / (D : ℚ) := (Rat.num_div_den _).symm
              have h_D_ne : ((D : ℕ) : ℚ) ≠ 0 := by positivity
              rw [h2]
              exact (div_mul_cancel₀ (C : ℚ) h_D_ne).symm
            have h_pos : (C : ℚ) > 0 := by
              rw [h_eq_C]
              have h_m_pos : S_arith m > 0 := by
                have hp_ge_two : p ≥ 2 := hp_prime.two_le
                have hp_odd_mod' : p % 2 = 1 := by rwa [Nat.odd_iff] at hp_odd
                have hp_ge_three : p ≥ 3 := by omega
                have hp_le : p ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm_nz) hp_dvd_m
                have : m > 1 := by omega
                have : S_arith m > 1 := S_arith_gt_one m (by linarith)
                linarith
              have h_D_pos : ((D : ℕ) : ℚ) > 0 := by positivity
              exact mul_pos h_m_pos h_D_pos
            exact_mod_cast h_pos
          rcases h_B_dvd_C_nat with ⟨k, hk⟩
          rcases h_D_dvd_A_nat with ⟨j, hj⟩
          have h_A_eq : A = (D : ℤ) * (j : ℤ) := by
            have h_abs : (A.natAbs : ℤ) = A := Int.natAbs_of_nonneg (by linarith)
            rw [← h_abs]
            exact_mod_cast hj
          have h_C_eq : C = (B : ℤ) * (k : ℤ) := by
            have h_abs : (C.natAbs : ℤ) = C := Int.natAbs_of_nonneg (by linarith)
            rw [← h_abs]
            exact_mod_cast hk
          have h_mul_abs : A.natAbs * C.natAbs = (S_arith n).num.natAbs * B * D := by
            have h1 : (A * C).natAbs = A.natAbs * C.natAbs := Int.natAbs_mul A C
            have h2 : ((S_arith n).num * (B : ℤ) * (D : ℤ)).natAbs = (S_arith n).num.natAbs * B * D := by
              simp only [Int.natAbs_mul, Int.natAbs_natCast]
            rw [← h1, h_mul_int, h2]
          have h_jk : j * k = (S_arith n).num.natAbs := by
            have h_eq_mul : B * D * (j * k) = B * D * (S_arith n).num.natAbs := by
              calc B * D * (j * k) = (D * j) * (B * k) := by ring
              _ = A.natAbs * C.natAbs := by rw [← hj, ← hk]
              _ = (S_arith n).num.natAbs * B * D := h_mul_abs
              _ = B * D * (S_arith n).num.natAbs := by ring
            have h_BD_nz : B * D ≠ 0 := by
              have hB_nz : B ≠ 0 := (S_arith (2^a)).den_nz
              have hD_nz : D ≠ 0 := (S_arith m).den_nz
              exact Nat.mul_ne_zero hB_nz hD_nz
            exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h_BD_nz) h_eq_mul
          have h_jk_ne_one : j * k ≠ 1 := by
            intro hc
            have h_jk1 := eq_one_of_mul_eq_one_helper j k hc
            have hj1 : j = 1 := h_jk1.1
            have hk1 : k = 1 := h_jk1.2
            have h_S_arith_two_pow : S_arith (2^a) = D / B := by
              have h1 : S_arith (2^a) = (A : ℚ) / (B : ℚ) := (Rat.num_div_den _).symm
              rw [h1, h_A_eq, hj1]
              push_cast
              ring
            have h_S_arith_m : S_arith m = B / D := by
              have h2 : S_arith m = (C : ℚ) / (D : ℚ) := (Rat.num_div_den _).symm
              rw [h2, h_C_eq, hk1]
              push_cast
              ring
            have h_two_pow_gt : S_arith (2^a) > 1 := by
              have ha_ge : a ≥ 1 := odd_ge_one a ha_even
              have h_two : 2^a ≥ 2 := two_pow_ge_two a ha_ge
              have h_two_gt : 1 < 2^a := by omega
              exact S_arith_gt_one (2^a) h_two_gt
            have h_m_gt : S_arith m > 1 := by
              have hp_ge_two : p ≥ 2 := hp_prime.two_le
              have hp_odd_mod' : p % 2 = 1 := by rwa [Nat.odd_iff] at hp_odd
              have hp_ge_three : p ≥ 3 := by omega
              have hp_le : p ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm_nz) hp_dvd_m
              have : m > 1 := by omega
              exact S_arith_gt_one m this
            have h_D_gt_B : (D : ℚ) > (B : ℚ) := by
              rw [h_S_arith_two_pow] at h_two_pow_gt
              have hB : (B : ℚ) > 0 := by positivity
              have : 1 * (B : ℚ) < (D : ℚ) := (lt_div_iff₀ hB).mp h_two_pow_gt
              linarith
            have h_B_gt_D : (B : ℚ) > (D : ℚ) := by
              rw [h_S_arith_m] at h_m_gt
              have hD : (D : ℚ) > 0 := by positivity
              have : 1 * (D : ℚ) < (B : ℚ) := (lt_div_iff₀ hD).mp h_m_gt
              linarith
            linarith
          have h_m_gt_one : 1 < m := by
            have hp_ge_three : p ≥ 3 := by
              have hp_ge_two := hp_prime.two_le
              omega
            have hp_le : p ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm_nz) hp_dvd_m
            omega
          have h_m_not_int := S_not_int m h_m_gt_one
          by exact _
termination_by n
decreasing_by
  have h_a_pos : padicValNat 2 n ≥ 1 := by
    change a % 2 ≠ 0 at ha_even
    omega
  have h_pow_ge : 2 ^ padicValNat 2 n ≥ 2 := two_pow_ge_two (padicValNat 2 n) h_a_pos
  have hn_pos : 0 < n := by omega
  exact Nat.div_lt_self hn_pos h_pow_ge

theorem oeis_265709_conjecture_0.disproof :
  ¬ ∃ (n : ℕ), 1 < n ∧
  ((n.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))).den = 1 := by
  intro h
  rcases h with ⟨n, hn, hden⟩
  exact S_not_int n hn hden
