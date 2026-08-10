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

lemma sigma_one_prime {p : ℕ} (hp : p.Prime) : (sigma 1) p = p + 1 := by
  rw [sigma_one_apply, hp.divisors]
  have h1 : 1 ≠ p := hp.ne_one.symm
  rw [sum_insert (by simp [h1]), sum_singleton, add_comm]

lemma prime_den (p : ℕ) (hp : p.Prime) :
  ((p : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)).den ≠ 1 := by
  have hsigma1 : (sigma 1) 1 = 1 := by
    rw [sigma_one_apply, divisors_one, sum_singleton]
  rw [hp.divisors]
  have h1 : 1 ≠ p := hp.ne_one.symm
  rw [sum_insert (by simp [h1]), sum_singleton, hsigma1, sigma_one_prime hp]
  simp only [Nat.cast_one, div_one]
  rw [Nat.cast_add_one]
  rw [add_comm]
  have h2 : (1 / (↑p + 1 : ℚ) + 1).den = (1 / (↑p + 1 : ℚ)).den := by
    exact Rat.add_natCast_den (1 / (↑p + 1 : ℚ)) 1
  rw [h2]
  have hdiv : (1 : ℚ) / (↑p + 1) = ((p + 1 : ℕ) : ℚ)⁻¹ := by
    rw [Nat.cast_add_one]
    simp only [one_div]
  rw [hdiv]
  rw [Rat.inv_natCast_den_of_pos (by omega)]
  have hp2 : p ≥ 2 := hp.two_le
  omega

def g : ArithmeticFunction ℚ := {
  toFun := fun n => if n = 0 then 0 else (1 : ℚ) / (↑((sigma 1) n) : ℚ)
  map_zero' := by simp
}

def zeta_ℚ : ArithmeticFunction ℚ := {
  toFun := fun n => if n = 0 then 0 else 1
  map_zero' := by simp
}

lemma zeta_ℚ_is_multiplicative : zeta_ℚ.IsMultiplicative := by
  constructor
  · rfl
  · intro m n h
    by_cases hm : m = 0
    · subst m
      simp at h; subst n
      simp [zeta_ℚ]
    · by_cases hn : n = 0
      · subst n
        simp at h; subst m
        simp [zeta_ℚ]
      · have hmn : m * n ≠ 0 := mul_ne_zero hm hn
        simp [zeta_ℚ, hm, hn, hmn]

lemma g_is_multiplicative : g.IsMultiplicative := by
  constructor
  · simp [g]
  · intro m n h
    by_cases hm : m = 0
    · subst m
      simp at h; subst n
      simp [g]
    · by_cases hn : n = 0
      · subst n
        simp at h; subst m
        simp [g]
      · have hmn : m * n ≠ 0 := mul_ne_zero hm hn
        simp [g, hm, hn, hmn]
        have h_sigma : (sigma 1) (m * n) = (sigma 1) m * (sigma 1) n := by
          exact ArithmeticFunction.IsMultiplicative.map_mul_of_coprime isMultiplicative_sigma h
        rw [h_sigma]
        push_cast
        rw [mul_inv, mul_comm]

lemma F_eq_g_mul_zeta (n : ℕ) (hn : n > 0) :
  ∑ d ∈ n.divisors, (1 : ℚ) / (sigma 1 d) = (g * zeta_ℚ) n := by
  symm
  rw [ArithmeticFunction.mul_apply]
  rw [Nat.sum_divisorsAntidiagonal (fun a b => g a * zeta_ℚ b)]
  symm
  have h1 : ∑ i ∈ n.divisors, g i * zeta_ℚ (n / i) = ∑ i ∈ n.divisors, (1 : ℚ) / (sigma 1 i) := by
    apply sum_congr rfl
    intro d hd
    have hd_pos : d > 0 := Nat.pos_of_mem_divisors hd
    have h_g : g d = (1 : ℚ) / (sigma 1 d) := by
      simp [g, hd_pos.ne']
    have h_zeta : zeta_ℚ (n / d) = 1 := by
      have h_div_pos : n / d > 0 := by
        apply Nat.div_pos (Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hd)) hd_pos
      simp [zeta_ℚ, h_div_pos.ne']
    rw [h_g, h_zeta, mul_one]
  rw [h1]

lemma sum_divisors_multiplicative {m n : ℕ} (hm : m > 0) (hn : n > 0) (h : m.Coprime n) :
  ∑ d ∈ (m * n).divisors, (1 : ℚ) / (sigma 1 d) =
  (∑ d ∈ m.divisors, (1 : ℚ) / (sigma 1 d)) * (∑ d ∈ n.divisors, (1 : ℚ) / (sigma 1 d)) := by
  rw [F_eq_g_mul_zeta (m * n) (mul_pos hm hn)]
  rw [F_eq_g_mul_zeta m hm]
  rw [F_eq_g_mul_zeta n hn]
  exact (ArithmeticFunction.IsMultiplicative.mul g_is_multiplicative zeta_ℚ_is_multiplicative).map_mul_of_coprime h

lemma exists_pow_two_mul_odd (n : ℕ) (hn : n ≠ 0) :
  ∃ (a m : ℕ), n = 2^a * m ∧ ¬ 2 ∣ m := by
  use n.factorization 2
  use ordCompl[2] n
  constructor
  · exact (ordProj_mul_ordCompl_eq_self n 2).symm
  · exact not_dvd_ordCompl Nat.prime_two hn

lemma exists_odd_prime_factor (m : ℕ) (hm1 : 1 < m) (hm2 : ¬ 2 ∣ m) :
  ∃ p, p.Prime ∧ p ≠ 2 ∧ p ∣ m := by
  use m.minFac
  refine ⟨minFac_prime hm1.ne', ?_, minFac_dvd m⟩
  intro hp2
  have h_dvd : 2 ∣ m := by
    rw [← hp2]
    exact minFac_dvd m
  exact hm2 h_dvd

lemma odd_sigma_two_pow (k : ℕ) : ¬ 2 ∣ (sigma 1 (2^k)) := by
  rw [sigma_one_apply, Nat.divisors_prime_pow Nat.prime_two k]
  rw [sum_map]
  rw [sum_range_succ']
  simp
  have h_sum : ∑ x ∈ range k, 2 ^ (x + 1) = 2 * ∑ x ∈ range k, 2 ^ x := by
    simp_rw [pow_succ]
    rw [← sum_mul]
    rw [mul_comm]
  rw [h_sum]
  rw [add_comm]
  rw [Nat.add_mul_mod_self_left]
  rfl

lemma my_geom_sum_eq (a : ℕ) :
  ∑ x ∈ range a, (1 : ℚ) / 2^(x+1) = 1 - (1 / 2^a) := by
  induction a with
  | zero =>
    simp
  | succ a ih =>
    rw [sum_range_succ]
    rw [ih]
    have h2a : (2^a : ℚ) ≠ 0 := by positivity
    have h_pow : (2^(a+1) : ℚ) = 2^a * 2 := by
      simp [pow_succ]
    rw [h_pow]
    generalize hX_eq : (2^a : ℚ) = X
    have hX : X ≠ 0 := by
      rw [← hX_eq]
      exact h2a
    field_simp
    ring

lemma S_two_pow_bounds (a : ℕ) (ha : a ≥ 1) :
  1 < ∑ j ∈ range (a+1), (1 : ℚ) / (sigma 1 (2^j)) ∧
  ∑ j ∈ range (a+1), (1 : ℚ) / (sigma 1 (2^j)) < 2 := by
  constructor
  · rw [sum_range_succ']
    simp
    apply sum_pos
    · intro j hj
      have h_sigma : (sigma 1) (2^(j+1)) > 0 := sigma_pos 1 (2^(j+1)) (pow_ne_zero _ (by omega))
      positivity
    · rw [nonempty_range_iff]; omega
  · rw [sum_range_succ']
    simp
    have h_bound : ∑ x ∈ range a, (1 : ℚ) / ↑((sigma 1) (2 ^ (x + 1))) ≤ ∑ x ∈ range a, (1 : ℚ) / 2^(x+1) := by
      apply sum_le_sum
      intro j hj
      have h2 : 2^(j+1) ≤ (sigma 1) (2^(j+1)) := by
        rw [sigma_one_apply]
        apply Finset.single_le_sum (f := fun x => x)
        · intro i hi; exact Nat.zero_le i
        · rw [Nat.mem_divisors]; exact ⟨dvd_rfl, by positivity⟩
      have h2_cast : (2^(j+1) : ℚ) ≤ ↑((sigma 1) (2^(j+1))) := by
        exact_mod_cast h2
      have h_sig_pos : (↑((sigma 1) (2^(j+1))) : ℚ) > 0 := by
        have : (sigma 1) (2^(j+1)) > 0 := sigma_pos 1 (2^(j+1)) (pow_ne_zero _ (by omega))
        positivity
      have h_two_pos : (2^(j+1) : ℚ) > 0 := by positivity
      exact one_div_le_one_div_of_le h_two_pos h2_cast
    have h_geom : ∑ x ∈ range a, (1 : ℚ) / 2^(x+1) < 1 := by
      rw [my_geom_sum_eq a]
      have h_div_pos : (1 / 2^a : ℚ) > 0 := by positivity
      exact sub_lt_self 1 h_div_pos
    have h_lt : ∑ x ∈ range a, (1 : ℚ) / ↑((sigma 1) (2 ^ (x + 1))) < 1 := h_bound.trans_lt h_geom
    simp_rw [inv_eq_one_div]
    linarith

lemma not_integer_of_bounds {q : ℚ} (h1 : 1 < q) (h2 : q < 2) : q.den ≠ 1 := by
  intro h_den
  have h_eq : q = q.num := by
    rw [← Rat.num_div_den q]
    rw [h_den]
    simp
  rw [h_eq] at h1 h2
  norm_cast at h1 h2
  omega


lemma padicVal_prime_one_neg (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
  padicValRat 2 (∑ j ∈ range 2, (1 : ℚ) / (sigma 1 (p^j))) < 0 := by
  -- range 2 is {0, 1}
  have h_sum : ∑ j ∈ range 2, (1 : ℚ) / (sigma 1 (p^j)) = (p + 2 : ℚ) / (p + 1 : ℚ) := by
    rw [sum_range_succ]
    rw [sum_range_one]
    simp only [pow_zero, pow_one]
    have hsigma1 : (sigma 1) 1 = 1 := by
      rw [sigma_one_apply, divisors_one, sum_singleton]
    rw [hsigma1]
    have hsigma_p : (sigma 1) p = p + 1 := by
      rw [sigma_one_apply, hp.divisors]
      have h1 : 1 ≠ p := hp.ne_one.symm
      rw [sum_insert (by simp [h1]), sum_singleton, add_comm]
    rw [hsigma_p]
    push_cast
    have hp1_pos : (p : ℚ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  rw [h_sum]
  rw [padicValRat.div]
  · have h_cast : (p + 2 : ℚ) = ↑(p + 2) := by push_cast; rfl
    have h_num : padicValRat 2 (p + 2 : ℚ) = 0 := by
      rw [h_cast]
      rw [← padicValRat_of_nat]
      rw [← factorization_def _ Nat.prime_two]
      have h_odd : ¬ 2 ∣ (p + 2) := by
        intro hdvd
        have : 2 ∣ p := by omega
        have hp2_eq : p = 2 := (hp.eq_one_or_self_of_dvd 2 this).resolve_left (by decide) |>.symm
        exact hp2 hp2_eq
      rw [factorization_eq_zero_of_not_dvd h_odd]
      rfl
    have h_cast2 : (p + 1 : ℚ) = ↑(p + 1) := by push_cast; rfl
    have h_den : padicValRat 2 (p + 1 : ℚ) ≥ 1 := by
      rw [h_cast2]
      rw [← padicValRat_of_nat]
      rw [← factorization_def _ Nat.prime_two]
      have h_even : 2 ∣ (p + 1) := by
        -- since p is prime and p ≠ 2, p is odd
        have hp_odd : p % 2 = 1 := hp.mod_two_eq_one_iff_ne_two.mpr hp2
        have h_eq : (p + 1) % 2 = 0 := by
          rw [Nat.add_mod, hp_odd]
        exact Nat.dvd_of_mod_eq_zero h_eq
      -- since 2 ∣ p+1, factorization 2 (p+1) >= 1
      -- we can use factorization_prime_le_iff_dvd
      have hp1_ne : p + 1 ≠ 0 := by omega
      have hp_le := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hp1_ne).mp h_even
      exact_mod_cast hp_le
    omega
  · positivity
  · positivity


lemma sum_pow_mod_two (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (c : ℕ) :
  (∑ x ∈ range (c+1), p^x) % 2 = (c+1) % 2 := by
  have hp_odd : p % 2 = 1 := hp.mod_two_eq_one_iff_ne_two.mpr hp2
  have hp_pow_odd (k : ℕ) : p^k % 2 = 1 := by rw [Nat.pow_mod, hp_odd, Nat.one_pow]
  induction c with
  | zero =>
    simp
  | succ c ih =>
    rw [sum_range_succ]
    rw [Nat.add_mod]
    rw [ih]
    rw [hp_pow_odd]
    omega

lemma odd_sigma_of_even_power (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (c : ℕ) (hc : Even c) :
  ¬ 2 ∣ sigma 1 (p^c) := by
  rw [sigma_one_apply, Nat.divisors_prime_pow hp c]
  rw [sum_map]
  intro hdvd
  have h_mod : (∑ x ∈ range (c+1), p^x) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd
  rw [sum_pow_mod_two p hp hp2 c] at h_mod
  rcases hc with ⟨k, rfl⟩
  rw [← Nat.two_mul] at h_mod
  omega

lemma even_sigma_of_odd_power (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (c : ℕ) (hc : ¬ Even c) :
  2 ∣ sigma 1 (p^c) := by
  rw [sigma_one_apply, Nat.divisors_prime_pow hp c]
  rw [sum_map]
  simp only [Function.Embedding.coeFn_mk]
  apply Nat.dvd_of_mod_eq_zero
  rw [sum_pow_mod_two p hp hp2 c]
  have h_odd : c % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one c with h0 | h1
    · exfalso
      apply hc
      exact Nat.even_iff.mpr h0
    · exact h1
  omega


lemma my_den_ne_one_of_padicVal_neg {q : ℚ} (h : padicValRat 2 q < 0) : q.den ≠ 1 := by
  intro hden
  have hq : q = (q.num : ℚ) := by
    nth_rw 1 [← Rat.num_div_den q]
    rw [hden]
    simp
  rw [hq] at h
  rw [padicValRat.of_int] at h
  have h_ge : (padicValInt 2 q.num : ℤ) ≥ 0 := Nat.cast_nonneg _
  omega

lemma padicVal_prime_power_neg (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (c : ℕ) (hc : c ≥ 1) :
  padicValRat 2 (∑ j ∈ range (c+1), (1 : ℚ) / (sigma 1 (p^j))) < 0 := by
  sorry
lemma padicValRat_sum_ge_zero {α : Type*} (f : α → ℚ) (s : Finset α) (h : ∀ x ∈ s, padicValRat 2 (f x) ≥ 0) :
  padicValRat 2 (∑ x ∈ s, f x) ≥ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp
  | @insert a s ha ih =>
    rw [sum_insert ha]
    have h_fa : padicValRat 2 (f a) ≥ 0 := h a (mem_insert_self a s)
    have h_sum : padicValRat 2 (∑ x ∈ s, f x) ≥ 0 := by
      apply ih
      intro x hx
      exact h x (mem_insert_of_mem hx)
    by_cases h_zero : f a + ∑ x ∈ s, f x = 0
    · rw [h_zero]
      simp
    · have h_min := padicValRat.min_le_padicValRat_add (p := 2) h_zero
      have h_min_ge : min (padicValRat 2 (f a)) (padicValRat 2 (∑ x ∈ s, f x)) ≥ 0 := by
        rw [ge_iff_le, le_min_iff]
        exact ⟨h_fa, h_sum⟩
      omega


lemma padicVal_S_two_pow_ge_zero (a : ℕ) :
  padicValRat 2 (∑ j ∈ range (a+1), (1 : ℚ) / (sigma 1 (2^j))) ≥ 0 := by
  apply padicValRat_sum_ge_zero
  intro j hj
  have h_odd : ¬ 2 ∣ sigma 1 (2^j) := odd_sigma_two_pow j
  have h_cast : (sigma 1 (2^j) : ℚ) = ↑(sigma 1 (2^j)) := by rfl
  have h_val : padicValRat 2 (sigma 1 (2^j) : ℚ) = 0 := by
    rw [h_cast]
    rw [← padicValRat_of_nat]
    rw [← factorization_def _ Nat.prime_two]
    rw [factorization_eq_zero_of_not_dvd h_odd]
    rfl
  rw [one_div, padicValRat.inv, h_val, neg_zero]

lemma padicVal_odd_neg (m : ℕ) (hm1 : 1 < m) (hm2 : ¬ 2 ∣ m) :
  padicValRat 2 (∑ d ∈ m.divisors, (1 : ℚ) / (sigma 1 d)) < 0 := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    let p := m.minFac
    have hp : p.Prime := minFac_prime (by omega)
    have hp2 : p ≠ 2 := by
      intro hp_eq
      have h2 : 2 ∣ m := by
        rw [← hp_eq]
        exact minFac_dvd m
      exact hm2 h2
    let c := m.factorization p
    have hc : c ≥ 1 := by
      have : 0 < m.factorization p := hp.factorization_pos_of_dvd (by omega) (minFac_dvd m)
      omega
    let d' := ordCompl[p] m
    have h_m_eq : m = p^c * d' := by
      symm
      exact ordProj_mul_ordCompl_eq_self m p
    have h_coprime : (p^c).Coprime d' := by
      apply Nat.Coprime.pow_left
      exact Nat.coprime_ordCompl hp (by omega)
    have h_sum : ∑ d ∈ m.divisors, (1 : ℚ) / (sigma 1 d) =
      (∑ d ∈ (p^c).divisors, (1 : ℚ) / (sigma 1 d)) * (∑ d ∈ d'.divisors, (1 : ℚ) / (sigma 1 d)) := by
      rw [h_m_eq]
      apply sum_divisors_multiplicative
      · have : p^c > 0 := Nat.pos_of_ne_zero (pow_ne_zero c hp.ne_zero)
        exact this
      · have hd_pos : d' > 0 := ordCompl_pos p (by omega)
        exact hd_pos
      · exact h_coprime
    by_cases hd1 : d' = 1
    · rw [hd1] at h_sum
      have h_sum_one : ∑ d ∈ (1 : ℕ).divisors, (1 : ℚ) / (sigma 1 d) = 1 := by
        simp [divisors_one]
      rw [h_sum_one, mul_one] at h_sum
      rw [h_sum]
      have h_div_eq : ∑ d ∈ (p^c).divisors, (1 : ℚ) / (sigma 1 d) = ∑ j ∈ range (c+1), (1 : ℚ) / (sigma 1 (p^j)) := by
        rw [Nat.divisors_prime_pow hp c]
        rw [sum_map]
        rfl
      rw [h_div_eq]
      exact padicVal_prime_power_neg p hp hp2 c hc
    · -- d' > 1
      have hd_gt : 1 < d' := by
        have hd_pos : d' > 0 := ordCompl_pos p (by omega)
        omega
      have hd_odd : ¬ 2 ∣ d' := by
        intro hd2
        have : 2 ∣ m := by
          rw [h_m_eq]
          exact dvd_mul_of_dvd_right hd2 (p^c)
        exact hm2 this
      have hd_lt : d' < m := by
        rw [h_m_eq]
        have h_pc : p^c > 1 := by
          have hp_ge : p ≥ 3 := by
            have : p ≥ 2 := hp.two_le
            omega
          have : p^c ≥ p := Nat.le_self_pow (by omega) p
          omega
        have hd_pos : d' > 0 := ordCompl_pos p (by omega)
        nlinarith
      have ih_d' := ih d' hd_lt hd_gt hd_odd
      rw [h_sum]
      rw [padicValRat.mul]
      · have h_pc_neg : padicValRat 2 (∑ d ∈ (p^c).divisors, (1 : ℚ) / (sigma 1 d)) < 0 := by
          have h_div_eq : ∑ d ∈ (p^c).divisors, (1 : ℚ) / (sigma 1 d) = ∑ j ∈ range (c+1), (1 : ℚ) / (sigma 1 (p^j)) := by
            rw [Nat.divisors_prime_pow hp c]
            rw [sum_map]
            rfl
          rw [h_div_eq]
          exact padicVal_prime_power_neg p hp hp2 c hc
        omega
      · apply _root_.ne_of_gt
        apply sum_pos
        · intro j hj
          have : sigma 1 j > 0 := @sigma_pos 1 j (Nat.pos_of_mem_divisors hj).ne'
          positivity
        · rw [nonempty_divisors]
          have : p^c > 0 := Nat.pos_of_ne_zero (pow_ne_zero c hp.ne_zero)
          omega
      · apply _root_.ne_of_gt
        apply sum_pos
        · intro j hj
          have : sigma 1 j > 0 := @sigma_pos 1 j (Nat.pos_of_mem_divisors hj).ne'
          positivity
        · rw [nonempty_divisors]
          have hd_pos : d' > 0 := ordCompl_pos p (by omega)
          omega

/--
Conjecture A265709: Are there numbers $n > 1$ such that $\\sum_{d|n} 1/\\sigma(d)$ is an integer?
-/

theorem oeis_265709_conjecture_0.disproof :
  ¬ ∃ (n : ℕ), 1 < n ∧
  ((n.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))).den = 1 := by
  intro h_exists
  rcases h_exists with ⟨n, hn1, h_den⟩
  have hn0 : n ≠ 0 := by omega
  rcases exists_pow_two_mul_odd n hn0 with ⟨a, m, h_n_eq, h_odd⟩
  have h_coprime : (2^a).Coprime m := by
    apply Nat.Coprime.pow_left
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h_odd
  have h_sum_mult : ∑ d ∈ n.divisors, (1 : ℚ) / (sigma 1 d) =
    (∑ d ∈ (2^a).divisors, (1 : ℚ) / (sigma 1 d)) * (∑ d ∈ m.divisors, (1 : ℚ) / (sigma 1 d)) := by
    rw [h_n_eq]
    apply sum_divisors_multiplicative
    · positivity
    · have : m > 0 := by
        by_contra h_zero
        have : m = 0 := by omega
        subst m
        simp at h_n_eq; subst n
        omega
      exact this
    · exact h_coprime
  by_cases hm1 : m = 1
  · subst m
    rw [mul_one] at h_n_eq
    rw [h_n_eq] at hn1 h_den
    have ha1 : a ≥ 1 := by
      by_contra hc
      have : a = 0 := by omega
      subst a
      simp at hn1
    have h_bounds := S_two_pow_bounds a ha1
    have h_not_int := not_integer_of_bounds h_bounds.1 h_bounds.2
    have h_div_eq : ∑ d ∈ (2^a).divisors, (1 : ℚ) / (sigma 1 d) = ∑ j ∈ range (a+1), (1 : ℚ) / (sigma 1 (2^j)) := by
      rw [Nat.divisors_prime_pow Nat.prime_two a]
      rw [sum_map]
      rfl
    rw [h_div_eq] at h_den
    exact h_not_int h_den
  · have hm_gt : 1 < m := by
      have : m > 0 := by
        by_contra h_zero
        have : m = 0 := by omega
        subst m
        simp at h_n_eq; subst n
        omega
      omega
    by_cases ha0 : a = 0
    · subst a
      simp only [pow_zero, one_mul] at h_n_eq
      subst n
      have h_bounds := padicVal_odd_neg m hm_gt h_odd
      exact my_den_ne_one_of_padicVal_neg h_bounds h_den
    · -- Even and composite case
      sorry
