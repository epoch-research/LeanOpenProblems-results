import FormalConjectures.Util.ProblemImports

set_option maxHeartbeats 10000000

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

/--
Conjecture A265709: Are there numbers $n > 1$ such that $\sum_{d|n} 1/\sigma(d)$ is an integer?
-/
lemma padicValRat_of_den_eq_one {p : ℕ} (hp : p.Prime) {q : ℚ} (hq : q.den = 1) : 0 ≤ padicValRat p q := by
  rw [padicValRat_def, hq]
  have h1 : padicValNat p 1 = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro h
    have := Nat.le_of_dvd (by decide) h
    have : 2 ≤ p := hp.two_le
    omega
  rw [h1]
  simp


lemma not_integer_of_padicVal_neg {p : ℕ} (hp : p.Prime) {q : ℚ} (hval : padicValRat p q < 0) : q.den ≠ 1 := by
  intro hq
  have h := padicValRat_of_den_eq_one hp hq
  omega


lemma coprime_self_succ (n : ℕ) : Nat.Coprime n (n + 1) := by
  rw [Nat.coprime_self_add_right]
  exact Nat.coprime_one_right n

lemma coprime_succ_self (n : ℕ) : Nat.Coprime (n + 1) n :=
  (coprime_self_succ n).symm

lemma den_div_prime_plus_one {p : ℕ} :
  ((((p + 2 : ℕ) : ℤ) : ℚ) / (((p + 1 : ℕ) : ℤ) : ℚ)).den = p + 1 := by
  have h_pos : 0 < ((p + 1 : ℕ) : ℤ) := by omega
  have h_coprime : Nat.Coprime ((p + 2 : ℕ) : ℤ).natAbs ((p + 1 : ℕ) : ℤ).natAbs := by
    rw [Int.natAbs_natCast, Int.natAbs_natCast]
    exact coprime_succ_self (p + 1)
  have h_den_int := Rat.den_div_eq_of_coprime h_pos h_coprime
  exact_mod_cast h_den_int

lemma S_prime {p : ℕ} (hp : p.Prime) :
  (p.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = (p + 2 : ℚ) / (p + 1 : ℚ) := by
  rw [hp.divisors]
  rw [Finset.sum_pair hp.ne_one.symm]
  have h1 : (sigma 1) 1 = 1 := by simp [sigma_one]
  have hp_sigma : (sigma 1) p = p + 1 := by
    rw [sigma_one_apply, hp.divisors, Finset.sum_pair hp.ne_one.symm]
    ring
  rw [h1, hp_sigma]
  simp
  have h_pos : (p : ℚ) + 1 ≠ 0 := by
    have : 2 ≤ p := hp.two_le
    positivity
  field_simp
  ring


lemma sigma_one_apply_prime {p : ℕ} (hp : p.Prime) : (sigma 1) p = p + 1 := by
  rw [sigma_one_apply, hp.divisors, Finset.sum_pair hp.ne_one.symm]
  ring

lemma prime_not_int {p : ℕ} (hp : p.Prime) :
  ((p.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))).den ≠ 1 := by
  rw [S_prime hp]
  have h_eq : (p + 2 : ℚ) / (p + 1 : ℚ) = ((((p + 2 : ℕ) : ℤ) : ℚ) / (((p + 1 : ℕ) : ℤ) : ℚ)) := by
    push_cast
    rfl
  rw [h_eq, den_div_prime_plus_one]
  have : 2 ≤ p := hp.two_le
  omega

lemma sigma_one_two_pow (x : ℕ) :
  (↑((sigma 1) (2 ^ x)) : ℚ) = (2 : ℚ) ^ (x + 1) - 1 := by
  have h1 : (sigma 1) (2 ^ x) = ∑ k ∈ range (x + 1), 2 ^ k := sigma_one_apply_prime_pow Nat.prime_two
  rw [h1]
  push_cast
  have h2 := geom_sum_mul (2 : ℚ) (x + 1)
  -- since 2 - 1 = 1, h2 simplifies to the sum being 2^(x+1) - 1
  have h3 : (2 : ℚ) - 1 = 1 := by norm_num
  rw [h3, mul_one] at h2
  exact h2

lemma S_two_pow_eq (k : ℕ) :
  ((2^k).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) =
  (range (k + 1)).sum (fun j => (1 : ℚ) / ((2 : ℚ) ^ (j + 1) - 1)) := by
  rw [sum_divisors_prime_pow Nat.prime_two]
  congr 1
  ext x
  rw [sigma_one_two_pow]

lemma pow_two_ge_four (j : ℕ) : (4 : ℚ) ≤ (2 : ℚ) ^ (j + 2) := by
  induction j with
  | zero =>
    norm_num
  | succ j ih =>
    have h1 : (2 : ℚ) ^ (j + 3) = (2 : ℚ) ^ (j + 2) * 2 := by ring
    rw [h1]
    linarith

lemma term_pos (j : ℕ) : 0 < (1 : ℚ) / ((2 : ℚ) ^ (j + 2) - 1) := by
  have h1 : (4 : ℚ) ≤ (2 : ℚ) ^ (j + 2) := pow_two_ge_four j
  have h2 : 0 < (2 : ℚ) ^ (j + 2) - 1 := by linarith
  exact div_pos (by norm_num) h2

lemma term_denom_ge (j : ℕ) : 3 * (2 : ℚ) ^ j ≤ (2 : ℚ) ^ (j + 2) - 1 := by
  have h1 : (2 : ℚ) ^ (j + 2) = 4 * (2 : ℚ) ^ j := by ring
  rw [h1]
  have h2 : (2 : ℚ) ^ j ≥ 1 := by
    have h_pow := Nat.one_le_pow j 2 (by decide)
    exact_mod_cast h_pow
  linarith

lemma term_le_geom (j : ℕ) : (1 : ℚ) / ((2 : ℚ) ^ (j + 2) - 1) ≤ (1 / 3) * (1 / 2) ^ j := by
  have h_denom : 3 * (2 : ℚ) ^ j ≤ (2 : ℚ) ^ (j + 2) - 1 := term_denom_ge j
  have h_pos : 0 < 3 * (2 : ℚ) ^ j := by positivity
  have h_div : (1 : ℚ) / ((2 : ℚ) ^ (j + 2) - 1) ≤ (1 : ℚ) / (3 * (2 : ℚ) ^ j) := by
    apply div_le_div_of_nonneg_left (by norm_num) h_pos h_denom
  have h_eq : (1 : ℚ) / (3 * (2 : ℚ) ^ j) = (1 / 3) * (1 / 2) ^ j := by
    field_simp
    rw [← mul_pow]
    norm_num
  rwa [h_eq] at h_div

lemma sum_half_pow_eq (k : ℕ) : (range k).sum (fun j => (1 / 2 : ℚ) ^ j) = 2 - 2 * (1 / 2) ^ k := by
  induction k with
  | zero =>
    norm_num
  | succ k ih =>
    rw [sum_range_succ, ih]
    ring

lemma sum_geom_less_one (k : ℕ) : (range k).sum (fun j => (1 / 3 : ℚ) * (1 / 2) ^ j) < 1 := by
  rw [← mul_sum]
  rw [sum_half_pow_eq]
  have h_half_pos : 0 < (1 / 2 : ℚ) ^ k := by positivity
  linarith

lemma den_neq_one_of_between {q : ℚ} (h1 : 1 < q) (h2 : q < 2) : q.den ≠ 1 := by
  intro h_den
  have h_eq : q = (q.num : ℚ) := by
    rw [← Rat.num_div_den q, h_den]
    simp
  rw [h_eq] at h1 h2
  have h1' : 1 < q.num := by exact_mod_cast h1
  have h2' : q.num < 2 := by exact_mod_cast h2
  omega

lemma den_neq_one_of_between_two_three {q : ℚ} (h1 : 2 < q) (h2 : q < 3) : q.den ≠ 1 := by
  intro h_den
  have h_eq : q = (q.num : ℚ) := by
    rw [← Rat.num_div_den q, h_den]
    simp
  rw [h_eq] at h1 h2
  have h1' : 2 < q.num := by exact_mod_cast h1
  have h2' : q.num < 3 := by exact_mod_cast h2
  omega


lemma S_two_pow_split (k : ℕ) :
  (range (k + 1)).sum (fun j => (1 : ℚ) / ((2 : ℚ) ^ (j + 1) - 1)) =
  1 + (range k).sum (fun j => (1 : ℚ) / ((2 : ℚ) ^ (j + 2) - 1)) := by
  rw [sum_range_succ']
  dsimp
  ring

lemma S_two_pow_lt_two (k : ℕ) :
  (range (k + 1)).sum (fun j => (1 : ℚ) / ((2 : ℚ) ^ (j + 1) - 1)) < 2 := by
  rw [S_two_pow_split]
  have h_le : (range k).sum (fun j => (1 : ℚ) / ((2 : ℚ) ^ (j + 2) - 1)) ≤ (range k).sum (fun j => (1 / 3 : ℚ) * (1 / 2) ^ j) := by
    apply sum_le_sum
    intro j hj
    exact term_le_geom j
  have h_lt : (range k).sum (fun j => (1 / 3 : ℚ) * (1 / 2) ^ j) < 1 := sum_geom_less_one k
  linarith

lemma S_two_pow_gt_one (k : ℕ) (hk : 1 ≤ k) :
  1 < (range (k + 1)).sum (fun j => (1 : ℚ) / ((2 : ℚ) ^ (j + 1) - 1)) := by
  rw [S_two_pow_split]
  have h_pos : 0 < (range k).sum (fun j => (1 : ℚ) / ((2 : ℚ) ^ (j + 2) - 1)) := by
    apply Finset.sum_pos
    · intro j hj
      exact term_pos j
    · rw [nonempty_range_iff]
      omega
  linarith


lemma S_two_pow_not_int (k : ℕ) (hk : 1 ≤ k) :
  ((2^k).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)).den ≠ 1 := by
  rw [S_two_pow_eq]
  apply den_neq_one_of_between
  · exact S_two_pow_gt_one k hk
  · exact S_two_pow_lt_two k

lemma pow_two_or_odd_prime_dvd (n : ℕ) (hn : 1 < n) : (∃ k, n = 2^k) ∨ (∃ p, p.Prime ∧ p ∣ n ∧ p ≠ 2) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h_prime : n.Prime
    · by_cases h2 : n = 2
      · left
        use 1
        rw [h2]
        rfl
      · right
        exact ⟨n, h_prime, dvd_rfl, h2⟩
    · -- n is composite
      -- so we can find a divisor a of n with 1 < a < n
      have h_comp : ∃ a, 1 < a ∧ a < n ∧ a ∣ n := by
        have h_ne : n ≠ 1 := _root_.ne_of_gt hn
        have ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd h_ne
        use p
        have hp_lt_n : p < n := by
          by_contra! h_ge
          have hp_eq_n : p = n := by
            have := Nat.le_of_dvd (by omega) hdvd
            omega
          subst hp_eq_n
          exact h_prime hp
        exact ⟨hp.two_le, hp_lt_n, hdvd⟩
      have ⟨a, ha1, han, ha_dvd⟩ := h_comp
      -- now apply IH on a
      have ih_a := ih a han ha1
      rcases ih_a with ⟨k_a, rfl⟩ | ⟨p, hp, hdvd, hp2⟩
      · -- a is a power of 2: a = 2^k_a
        -- we can write n = a * b
        have ⟨b, hb_eq⟩ := ha_dvd
        -- b is also a divisor, with 1 < b < n
        have hb1 : 1 < b := by
          by_contra! h_le
          interval_cases b
          · rw [mul_zero] at hb_eq
            omega
          · rw [mul_one] at hb_eq
            omega
        have hbn : b < n := by
          by_contra! h_ge
          have h_le : 2 ≤ 2^k_a := by
            -- prove 2 <= 2^k_a when k_a >= 1 (since ha1 : 1 < 2^k_a)
            have hk_pos : k_a ≠ 0 := by
              rintro rfl
              norm_num at ha1
            induction k_a with
            | zero => contradiction
            | succ k =>
              rw [pow_succ]
              exact Nat.le_mul_of_pos_left 2 (by positivity)
          have h_mul : n ≥ 2 * b := by
            rw [hb_eq]
            gcongr
          omega
        have ih_b := ih b hbn hb1
        rcases ih_b with ⟨k_b, rfl⟩ | ⟨p, hp, hdvd, hp2⟩
        · -- b is a power of 2: b = 2^k_b
          -- so n = a * b = 2^k_a * 2^k_b = 2^(k_a + k_b)
          left
          use k_a + k_b
          rw [pow_add]
          exact hb_eq
        · -- b has an odd prime factor p
          right
          use p
          refine ⟨hp, ?_, hp2⟩
          -- p | b, and b | n => p | n
          have hb_dvd : b ∣ n := by
            rw [hb_eq]
            exact dvd_mul_left b (2^k_a)
          exact dvd_trans hdvd hb_dvd
      · -- a has an odd prime factor p
        right
        use p
        refine ⟨hp, ?_, hp2⟩
        exact dvd_trans hdvd ha_dvd

def f : ArithmeticFunction ℚ :=
  ⟨fun d => if d = 0 then 0 else (1 : ℚ) / (sigma 1 d : ℚ), rfl⟩

lemma f_isMultiplicative : f.IsMultiplicative := by
  constructor
  · -- f 1 = 1
    dsimp [f]
    have h1 : (sigma 1 1 : ℚ) = 1 := by
      rfl
    rw [h1]
    norm_num
  · -- f (m * n) = f m * f n for coprime m, n
    intro m n h_coprime
    dsimp [f]
    by_cases hm : m = 0
    · subst hm
      simp
    by_cases hn : n = 0
    · subst hn
      simp
    have hmn : m * n ≠ 0 := Nat.mul_ne_zero hm hn
    rw [if_neg hm, if_neg hn, if_neg hmn]
    have h_sig := isMultiplicative_sigma (k := 1)
    have h_sig_mul := h_sig.2 h_coprime
    rw [h_sig_mul]
    push_cast
    ring

lemma f_mul_zeta_apply (x : ℕ) : (f * zeta) x = ∑ i ∈ divisors x, f i := by
  exact coe_mul_zeta_apply

lemma sum_f_eq_sum_recip (n : ℕ) (hn : 1 < n) :
  ∑ i ∈ divisors n, f i = n.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ) := by
  apply sum_congr rfl
  intro d hd
  have hd_ne : d ≠ 0 := by
    rintro rfl
    have : 0 ∈ n.divisors := hd
    rw [mem_divisors] at this
    omega
  dsimp [f]
  rw [if_neg hd_ne]

lemma padicValRat_two_S_prime_one {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
  padicValRat 2 ((p^1).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) < 0 := by
  have hp : p.Prime := Fact.out
  have h_eq : (p^1).divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = (p + 2 : ℚ) / (p + 1 : ℚ) := by
    have h_div : (p^1) = p := by ring
    rw [h_div]
    rw [hp.divisors]
    rw [Finset.sum_pair hp.ne_one.symm]
    have h1 : (sigma 1) 1 = 1 := by simp [sigma_one]
    have hp_sigma : (sigma 1) p = p + 1 := by
      rw [sigma_one_apply, hp.divisors, Finset.sum_pair hp.ne_one.symm]
      ring
    rw [h1, hp_sigma]
    simp
    have h_pos : (p : ℚ) + 1 ≠ 0 := by
      have : 2 ≤ p := hp.two_le
      positivity
    field_simp
    ring
  rw [h_eq]
  rw [padicValRat.div (by positivity) (by positivity)]
  have h_odd : ¬ 2 ∣ (p + 2) := by
    intro h_dvd
    rw [add_comm] at h_dvd
    have h_dvd_p : 2 ∣ p := (Nat.dvd_add_right dvd_rfl).mp h_dvd
    have h_eq_2 : p = 2 := by
      rcases hp.eq_one_or_self_of_dvd 2 h_dvd_p with h_one | h_self
      · contradiction
      · exact h_self.symm
    exact hp2 h_eq_2
  have h_val_num : padicValRat 2 ((p + 2 : ℕ) : ℚ) = 0 := by
    rw [padicValRat.of_nat]
    have h_val_nat : padicValNat 2 (p + 2) = 0 := padicValNat.eq_zero_of_not_dvd h_odd
    rw [h_val_nat]
    rfl
  have h_pos : 0 < p + 1 := by omega
  have h_val_den : 1 ≤ padicValNat 2 (p + 1) := by
    have h_even : 2 ∣ (p + 1) := by
      have : p % 2 = 1 := hp.mod_two_eq_one_iff_ne_two.mpr hp2
      have : (p + 1) % 2 = 0 := by omega
      exact Nat.dvd_of_mod_eq_zero this
    exact one_le_padicValNat_of_dvd (by omega) h_even
  have h_val_den' : 1 ≤ padicValRat 2 ((p + 1 : ℕ) : ℚ) := by
    rw [padicValRat.of_nat]
    exact_mod_cast h_val_den
  push_cast at h_val_num
  push_cast at h_val_den'
  rw [h_val_num]
  omega

lemma S_isMultiplicative : (f * zeta).IsMultiplicative :=
  f_isMultiplicative.mul isMultiplicative_zeta.natCast

lemma S_mul_of_coprime {x y : ℕ} (h : x.Coprime y) :
  (f * zeta) (x * y) = (f * zeta) x * (f * zeta) y := by
  exact S_isMultiplicative.map_mul_of_coprime h


lemma S_prime_power_eq {p : ℕ} (hp : p.Prime) (a : ℕ) :
  ((p^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) =
  (range (a + 1)).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^j)) : ℚ)) := by
  rw [sum_divisors_prime_pow hp]

lemma sigma_one_prime_pow_step (p : ℕ) (hp : p.Prime) (n : ℕ) :
  sigma 1 (p ^ (n + 2)) = sigma 1 (p ^ n) + p ^ (n + 1) + p ^ (n + 2) := by
  have h1 : sigma 1 (p ^ (n + 2)) = ∑ i ∈ range (n + 3), p ^ i := sigma_one_apply_prime_pow hp
  have h2 : sigma 1 (p ^ n) = ∑ i ∈ range (n + 1), p ^ i := sigma_one_apply_prime_pow hp
  rw [h1, h2]
  rw [sum_range_succ, sum_range_succ]


lemma sigma_odd_power_eq (p : ℕ) (hp : p.Prime) (k : ℕ) :
  sigma 1 (p ^ (2 * k + 1)) = (p + 1) * ∑ i ∈ range (k + 1), p ^ (2 * i) := by
  induction k with
  | zero =>
    have hp_sigma : sigma 1 p = p + 1 := by
      rw [sigma_one_apply, hp.divisors, Finset.sum_pair hp.ne_one.symm]
      ring
    simp only [mul_zero, zero_add, pow_one]
    rw [hp_sigma]
    simp
  | succ k ih =>
    have h_eq : 2 * (k + 1) + 1 = 2 * k + 1 + 2 := by ring
    rw [h_eq]
    rw [sigma_one_prime_pow_step p hp (2 * k + 1)]
    rw [ih]
    have h_exp1 : 2 * k + 1 + 1 = 2 * k + 2 := by ring
    have h_exp2 : 2 * k + 1 + 2 = 2 * k + 3 := by ring
    rw [h_exp1, h_exp2]
    have h_ring : (p + 1) * (∑ i ∈ range (k + 1), p ^ (2 * i)) + p ^ (2 * k + 2) + p ^ (2 * k + 3) =
      (p + 1) * (∑ i ∈ range (k + 1), p ^ (2 * i) + p ^ (2 * (k + 1))) := by
      have h_eq2 : p ^ (2 * k + 2) + p ^ (2 * k + 3) = (p + 1) * p ^ (2 * (k + 1)) := by
        have h1 : 2 * (k + 1) = 2 * k + 2 := by ring
        have h2 : 2 * k + 3 = 2 * k + 2 + 1 := by ring
        rw [h1, h2, pow_succ]
        ring
      rw [add_assoc, h_eq2, ← mul_add]
    rw [h_ring]
    rw [sum_range_succ (fun i => p ^ (2 * i)) (k + 1)]

lemma even_sum_pow_odd_prime (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (n : ℕ) :
  2 ∣ (p ^ (n + 1) + p ^ (n + 2)) := by
  have h_eq : p ^ (n + 1) + p ^ (n + 2) = p ^ (n + 1) * (1 + p) := by
    rw [pow_succ]
    ring
  rw [h_eq]
  apply dvd_mul_of_dvd_right
  have h_even : 2 ∣ (p + 1) := by
    have : p % 2 = 1 := hp.mod_two_eq_one_iff_ne_two.mpr hp2
    have : (p + 1) % 2 = 0 := by omega
    exact Nat.dvd_of_mod_eq_zero this
  rw [add_comm]
  exact h_even

lemma sigma_odd_of_two_mul (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (k : ℕ) :
  ¬ 2 ∣ sigma 1 (p ^ (2 * k)) := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    have h_eq : 2 * (k + 1) = 2 * k + 2 := by ring
    rw [h_eq]
    rw [sigma_one_prime_pow_step p hp (2 * k)]
    have h_dvd : 2 ∣ (p ^ (2 * k + 1) + p ^ (2 * k + 2)) := even_sum_pow_odd_prime p hp hp2 (2 * k)
    intro h_sum
    rw [add_assoc] at h_sum
    have h_dvd_left : 2 ∣ sigma 1 (p ^ (2 * k)) := by omega
    exact ih h_dvd_left

lemma sigma_odd_of_even_power {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (j : ℕ) (hj : j % 2 = 0) :
  ¬ 2 ∣ sigma 1 (p ^ j) := by
  have h_eq : j = 2 * (j / 2) := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hj)).symm
  rw [h_eq]
  exact sigma_odd_of_two_mul p hp hp2 (j / 2)

lemma padicValRat_two_recip_sigma_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (j : ℕ) (hj : j % 2 = 0) :
  padicValRat 2 ((1 : ℚ) / (↑((sigma 1) (p^j)) : ℚ)) = 0 := by
  have h_sig : 0 < sigma 1 (p^j) := sigma_pos 1 (p^j) (pow_ne_zero j hp.ne_zero)
  have h_pos : (↑((sigma 1) (p^j)) : ℚ) ≠ 0 := by
    have h_gt : 0 < (↑((sigma 1) (p^j)) : ℚ) := Nat.cast_pos.mpr h_sig
    exact ne_of_gt h_gt
  rw [padicValRat.div (by positivity) h_pos]
  rw [padicValRat.one]
  have h_val : padicValRat 2 ((↑((sigma 1) (p^j)) : ℕ) : ℚ) = 0 := by
    rw [padicValRat.of_nat]
    have h_odd := sigma_odd_of_even_power hp hp2 j hj
    rw [padicValNat.eq_zero_of_not_dvd h_odd]
    rfl
  rw [h_val]
  rfl


lemma S_prime_power_pos {p : ℕ} (hp : p.Prime) (a : ℕ) :
  0 < (range (a + 1)).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^j)) : ℚ)) := by
  apply Finset.sum_pos
  · intro j hj
    have h_sig : 0 < sigma 1 (p^j) := sigma_pos 1 (p^j) (pow_ne_zero j hp.ne_zero)
    have h_sig_q : 0 < (↑((sigma 1) (p^j)) : ℚ) := Nat.cast_pos.mpr h_sig
    exact div_pos zero_lt_one h_sig_q
  · rw [nonempty_range_iff]
    omega

lemma S_prime_power_gt_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a : ℕ) (ha : 1 ≤ a) :
  1 < (range (a + 1)).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^j)) : ℚ)) := by
  rw [sum_range_succ']
  have h_pos : 0 < (range a).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^(j + 1))) : ℚ)) := by
    apply Finset.sum_pos
    · intro j hj
      have h_sig : 0 < sigma 1 (p^(j + 1)) := sigma_pos 1 (p^(j + 1)) (pow_ne_zero (j + 1) hp.ne_zero)
      have h_sig_q : 0 < (↑((sigma 1) (p^(j + 1))) : ℚ) := Nat.cast_pos.mpr h_sig
      exact div_pos zero_lt_one h_sig_q
    · rw [nonempty_range_iff]
      omega
  simp at h_pos ⊢
  linarith

lemma sigma_ge_geom (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (j : ℕ) :
  3 * 2^j ≤ sigma 1 (p ^ (j + 1)) := by
  have hp3 : 3 ≤ p := by
    have : p % 2 = 1 := hp.mod_two_eq_one_iff_ne_two.mpr hp2
    have : 2 < p := hp.two_le.lt_of_ne hp2.symm
    omega
  have h1 : sigma 1 (p ^ (j + 1)) = ∑ i ∈ range (j + 2), p ^ i := sigma_one_apply_prime_pow hp
  rw [h1]
  rw [sum_range_succ]
  have h2 : p ^ (j + 1) ≤ ∑ i ∈ range (j + 1), p ^ i + p ^ (j + 1) := by omega
  have h3 : 3 * 2^j ≤ p ^ (j + 1) := by
    have h_pow : 3 * 2^j ≤ p * 2^j := by gcongr
    have h_pow2 : 2^j ≤ p^j := by
      gcongr
      omega
    have h_mul : p * 2^j ≤ p * p^j := by gcongr
    have h_eq : p * p^j = p^(j + 1) := by ring
    omega
  omega

lemma term_le_geom_p {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (j : ℕ) :
  (1 : ℚ) / (↑((sigma 1) (p^(j + 1))) : ℚ) ≤ (1 / 3) * (1 / 2) ^ j := by
  have h_denom : (3 : ℚ) * (2 : ℚ) ^ j ≤ (↑((sigma 1) (p^(j + 1))) : ℚ) := by
    have := sigma_ge_geom p hp hp2 j
    exact_mod_cast this
  have h_pos : 0 < (3 : ℚ) * (2 : ℚ) ^ j := by positivity
  have h_div : (1 : ℚ) / (↑((sigma 1) (p^(j + 1))) : ℚ) ≤ (1 : ℚ) / ((3 : ℚ) * (2 : ℚ) ^ j) := by
    apply div_le_div_of_nonneg_left (by norm_num) h_pos h_denom
  have h_eq : (1 : ℚ) / ((3 : ℚ) * (2 : ℚ) ^ j) = (1 / 3) * (1 / 2) ^ j := by
    field_simp
    rw [← mul_pow]
    norm_num
  rwa [h_eq] at h_div

lemma S_prime_power_lt_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a : ℕ) :
  (range (a + 1)).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^j)) : ℚ)) < 2 := by
  rw [sum_range_succ']
  have h_le : (range a).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^(j + 1))) : ℚ)) ≤ (range a).sum (fun j => (1 / 3 : ℚ) * (1 / 2) ^ j) := by
    apply sum_le_sum
    intro j hj
    exact term_le_geom_p hp hp2 j
  have h_lt : (range a).sum (fun j => (1 / 3 : ℚ) * (1 / 2) ^ j) < 1 := sum_geom_less_one a
  simp at h_le h_lt ⊢
  linarith


lemma sigma_ge_geom_p5 (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (j : ℕ) :
  5 * 5^j ≤ sigma 1 (p ^ (j + 1)) := by
  have h1 : sigma 1 (p ^ (j + 1)) = ∑ i ∈ range (j + 2), p ^ i := sigma_one_apply_prime_pow hp
  rw [h1]
  rw [sum_range_succ]
  have h2 : p ^ (j + 1) ≤ ∑ i ∈ range (j + 1), p ^ i + p ^ (j + 1) := by omega
  have h3 : 5 * 5^j ≤ p ^ (j + 1) := by
    have h_pow2 : 5^j ≤ p^j := by
      gcongr
    have h_mul : 5 * 5^j ≤ p * p^j := by gcongr
    have h_eq : p * p^j = p^(j + 1) := by ring
    omega
  omega

lemma term_le_geom_p5 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (j : ℕ) :
  (1 : ℚ) / (↑((sigma 1) (p^(j + 1))) : ℚ) ≤ (1 / 5) * (1 / 5) ^ j := by
  have h_denom : (5 : ℚ) * (5 : ℚ) ^ j ≤ (↑((sigma 1) (p^(j + 1))) : ℚ) := by
    have := sigma_ge_geom_p5 p hp hp5 j
    exact_mod_cast this
  have h_pos : 0 < (5 : ℚ) * (5 : ℚ) ^ j := by positivity
  have h_div : (1 : ℚ) / (↑((sigma 1) (p^(j + 1))) : ℚ) ≤ (1 : ℚ) / ((5 : ℚ) * (5 : ℚ) ^ j) := by
    apply div_le_div_of_nonneg_left (by norm_num) h_pos h_denom
  have h_eq : (1 : ℚ) / ((5 : ℚ) * (5 : ℚ) ^ j) = (1 / 5) * (1 / 5) ^ j := by
    field_simp
    rw [← mul_pow]
    norm_num
  rwa [h_eq] at h_div

lemma sum_fifth_pow_eq (k : ℕ) : (range k).sum (fun j => (1 / 5 : ℚ) ^ j) = 5 / 4 - 5 / 4 * (1 / 5) ^ k := by
  induction k with
  | zero =>
    norm_num
  | succ k ih =>
    rw [sum_range_succ, ih]
    ring

lemma S_prime_power_lt_one_and_half {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (a : ℕ) :
  (range (a + 1)).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^j)) : ℚ)) < 3 / 2 := by
  rw [sum_range_succ']
  have h_le : (range a).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^(j + 1))) : ℚ)) ≤ (range a).sum (fun j => (1 / 5 : ℚ) * (1 / 5) ^ j) := by
    apply sum_le_sum
    intro j hj
    exact term_le_geom_p5 hp hp5 j
  have h_lt : (range a).sum (fun j => (1 / 5 : ℚ) * (1 / 5) ^ j) < 1 / 4 := by
    rw [← mul_sum]
    rw [sum_fifth_pow_eq]
    have : 0 < (1 / 5 : ℚ) ^ a := by positivity
    linarith
  simp at h_le h_lt ⊢
  linarith


lemma S_prime_power_lt_six_fifths {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (a : ℕ) :
  (range (a + 1)).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^j)) : ℚ)) < 5 / 4 := by
  rw [sum_range_succ']
  have h_le : (range a).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^(j + 1))) : ℚ)) ≤ (range a).sum (fun j => (1 / 5 : ℚ) * (1 / 5) ^ j) := by
    apply sum_le_sum
    intro j hj
    exact term_le_geom_p5 hp hp5 j
  have h_lt : (range a).sum (fun j => (1 / 5 : ℚ) * (1 / 5) ^ j) < 1 / 4 := by
    rw [← mul_sum]
    rw [sum_fifth_pow_eq]
    have : 0 < (1 / 5 : ℚ) ^ a := by positivity
    linarith
  simp at h_le h_lt ⊢
  linarith

lemma sigma_p_pow_ge {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (j : ℕ) :
  6 * 5^j ≤ sigma 1 (p ^ (j + 1)) := by
  have h1 : sigma 1 (p ^ (j + 1)) = ∑ i ∈ range (j + 2), p ^ i := sigma_one_apply_prime_pow hp
  rw [h1]
  rw [sum_range_succ, sum_range_succ]
  have h2 : p^j + p^(j + 1) ≤ ∑ i ∈ range j, p ^ i + p^j + p^(j + 1) := by omega
  have h3 : 6 * 5^j ≤ p^j + p^(j + 1) := by
    have h_eq : p^j + p^(j + 1) = (p + 1) * p^j := by ring
    rw [h_eq]
    have h4 : 6 ≤ p + 1 := by omega
    have h5 : 5^j ≤ p^j := by
      gcongr
    exact Nat.mul_le_mul h4 h5
  omega

lemma term_le_geom_p5_2 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (j : ℕ) :
  (1 : ℚ) / (↑((sigma 1) (p^(j + 1))) : ℚ) ≤ (1 / 6) * (1 / 5) ^ j := by
  have h_denom : (6 : ℚ) * (5 : ℚ) ^ j ≤ (↑((sigma 1) (p^(j + 1))) : ℚ) := by
    have := sigma_p_pow_ge hp hp5 j
    exact_mod_cast this
  have h_pos : 0 < (6 : ℚ) * (5 : ℚ) ^ j := by positivity
  have h_div : (1 : ℚ) / (↑((sigma 1) (p^(j + 1))) : ℚ) ≤ (1 : ℚ) / ((6 : ℚ) * (5 : ℚ) ^ j) := by
    apply div_le_div_of_nonneg_left (by norm_num) h_pos h_denom
  have h_eq : (1 : ℚ) / ((6 : ℚ) * (5 : ℚ) ^ j) = (1 / 6) * (1 / 5) ^ j := by
    field_simp
    rw [← mul_pow]
    norm_num
  rwa [h_eq] at h_div

lemma S_prime_power_lt_twenty_nine_twenty_fourths {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (a : ℕ) :
  (range (a + 1)).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^j)) : ℚ)) < 29 / 24 := by
  rw [sum_range_succ']
  have h1 : (sigma 1) (p^0) = 1 := by
    rw [pow_zero]
    rfl
  have h_le : (range a).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^(j + 1))) : ℚ)) ≤ (range a).sum (fun j => (1 / 6 : ℚ) * (1 / 5) ^ j) := by
    apply sum_le_sum
    intro j hj
    exact term_le_geom_p5_2 hp hp5 j
  have h_lt : (range a).sum (fun j => (1 / 6 : ℚ) * (1 / 5) ^ j) < 5 / 24 := by
    rw [← mul_sum]
    rw [sum_fifth_pow_eq]
    have : 0 < (1 / 5 : ℚ) ^ a := by positivity
    linarith
  simp [h1] at h_le h_lt ⊢
  linarith


lemma S_prime_power_not_int (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (a : ℕ) (ha : 1 ≤ a) :
  ((p^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)).den ≠ 1 := by
  rw [S_prime_power_eq hp]
  apply den_neq_one_of_between
  · exact S_prime_power_gt_one hp hp2 a ha
  · exact S_prime_power_lt_two hp hp2 a



lemma padicValNat_two_one_add_sq_odd {p : ℕ} (hp : p % 2 = 1) : padicValNat 2 (1 + p^2) = 1 := by
  have h_eq : 1 + p^2 = 2 * (2 * (p / 2 * (p / 2) + p / 2) + 1) := by
    have hp_eq : p = 2 * (p / 2) + 1 := by
      have := Nat.div_add_mod p 2
      omega
    nth_rw 1 [hp_eq]
    ring
  rw [h_eq]
  have h_mul : padicValNat 2 (2 * (2 * (p / 2 * (p / 2) + p / 2) + 1)) =
    padicValNat 2 2 + padicValNat 2 (2 * (p / 2 * (p / 2) + p / 2) + 1) := by
    apply padicValNat.mul (by decide) (by omega)
  rw [h_mul]
  have h_two : padicValNat 2 2 = 1 := padicValNat.self (by decide)
  have h_odd : padicValNat 2 (2 * (p / 2 * (p / 2) + p / 2) + 1) = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro h_dvd
    have h_mod : (2 * (p / 2 * (p / 2) + p / 2) + 1) % 2 = 1 := by omega
    have h_dvd_mod := Nat.mod_eq_zero_of_dvd h_dvd
    omega
  rw [h_two, h_odd]

lemma sum_pow_two_mul (p : ℕ) (m : ℕ) :
  ∑ i ∈ range (2 * m), p ^ (2 * i) = (1 + p ^ 2) * ∑ i ∈ range m, (p ^ 2) ^ (2 * i) := by
  induction m with
  | zero =>
    simp
  | succ m ih =>
    have h_lhs : 2 * (m + 1) = 2 * m + 2 := by ring
    rw [h_lhs]
    rw [sum_range_succ, sum_range_succ]
    rw [ih]
    rw [sum_range_succ]
    rw [mul_add]
    ring

lemma sum_pow_odd_mod_two (p : ℕ) (hp_odd : p % 2 = 1) (k : ℕ) :
  (∑ i ∈ range k, p ^ (2 * i)) % 2 = k % 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ]
    rw [Nat.add_mod]
    rw [ih]
    have hp_pow_odd : (p ^ (2 * k)) % 2 = 1 := by
      rw [Nat.pow_mod]
      rw [hp_odd]
      simp
    rw [hp_pow_odd]
    have : (k % 2 + 1) % 2 = (k + 1) % 2 := by omega
    exact this

lemma padicValNat_two_sum_pow_odd_helper (k : ℕ) :
  ∀ (p : ℕ) (hp_odd : p % 2 = 1), padicValNat 2 (∑ i ∈ range k, p ^ (2 * i)) = padicValNat 2 k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro p hp_odd
    by_cases hk_zero : k = 0
    · subst hk_zero
      simp
    · by_cases hk_even : k % 2 = 0
      · -- Case 1: k is even
        have h_eq_2m : k = 2 * (k / 2) := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hk_even)).symm
        have hm_lt : k / 2 < k := by
          have : k ≠ 0 := hk_zero
          omega
        have h_ih := ih (k / 2) hm_lt (p ^ 2)
        -- LHS
        nth_rw 1 [h_eq_2m]
        rw [sum_pow_two_mul]
        have h_mul : padicValNat 2 ((1 + p ^ 2) * ∑ i ∈ range (k / 2), (p ^ 2) ^ (2 * i)) =
          padicValNat 2 (1 + p ^ 2) + padicValNat 2 (∑ i ∈ range (k / 2), (p ^ 2) ^ (2 * i)) := by
          apply padicValNat.mul (by omega)
          -- sum is non-zero
          apply _root_.ne_of_gt
          apply Finset.sum_pos
          · intro i hi
            have hp_ne : p ≠ 0 := by omega
            have hp2_ne : p^2 ≠ 0 := pow_ne_zero 2 hp_ne
            exact Nat.pos_of_ne_zero (pow_ne_zero (2 * i) hp2_ne)
          · rw [nonempty_range_iff]
            omega
        rw [h_mul]
        rw [padicValNat_two_one_add_sq_odd hp_odd]
        -- apply ih to p^2 which is also odd
        have hp2_odd : (p ^ 2) % 2 = 1 := by
          rw [pow_two, Nat.mul_mod, hp_odd]
        rw [h_ih hp2_odd]
        -- RHS
        nth_rw 2 [h_eq_2m]
        have h_rhs_mul : padicValNat 2 (2 * (k / 2)) = padicValNat 2 2 + padicValNat 2 (k / 2) := by
          apply padicValNat.mul (by decide) (by omega)
        rw [h_rhs_mul]
        have : padicValNat 2 2 = 1 := padicValNat.self (by decide)
        rw [this]
      · -- Case 2: k is odd
        -- then the sum has an odd number of terms, all odd, so the sum is odd.
        have h_odd_sum : (∑ i ∈ range k, p ^ (2 * i)) % 2 = 1 := by
          rw [sum_pow_odd_mod_two p hp_odd]
          exact Nat.mod_two_ne_zero.mp hk_even
        have h_val_sum : padicValNat 2 (∑ i ∈ range k, p ^ (2 * i)) = 0 := by
          apply padicValNat.eq_zero_of_not_dvd
          intro h_dvd
          have h_even : (∑ i ∈ range k, p ^ (2 * i)) % 2 = 0 := Nat.mod_eq_zero_of_dvd h_dvd
          omega
        have h_val_k : padicValNat 2 k = 0 := by
          apply padicValNat.eq_zero_of_not_dvd
          intro h_dvd
          have h_even : k % 2 = 0 := Nat.mod_eq_zero_of_dvd h_dvd
          omega
        rw [h_val_sum, h_val_k]

lemma padicValNat_two_sum_pow_odd (p : ℕ) (hp_odd : p % 2 = 1) (k : ℕ) :
  padicValNat 2 (∑ i ∈ range k, p ^ (2 * i)) = padicValNat 2 k :=
  padicValNat_two_sum_pow_odd_helper k p hp_odd

lemma log2_mono {a b : ℕ} (h : a ≤ b) : a.log2 ≤ b.log2 := by
  by_cases ha : a = 0
  · subst ha; simp [log2_zero]
  · have hb : b ≠ 0 := by omega
    rw [le_log2 hb]
    have := log2_self_le ha
    omega

lemma padicValNat_le_log2 (k : ℕ) : padicValNat 2 (k + 1) ≤ Nat.log2 (k + 1) := by
  have h_ne : k + 1 ≠ 0 := by omega
  rw [Nat.le_log2 h_ne]
  exact Nat.le_of_dvd (by omega) pow_padicValNat_dvd

lemma log2_ne_padicValNat (k : ℕ) (hk : 1 ≤ k) : Nat.log2 k ≠ padicValNat 2 (k + 1) := by
  generalize hv : padicValNat 2 (k + 1) = v
  intro h_eq
  have h_dvd : 2^v ∣ (k + 1) := by
    rw [← hv]
    exact pow_padicValNat_dvd
  have h_le : 2^v ≤ k + 1 := Nat.le_of_dvd (by omega) h_dvd
  by_cases h_eq2 : 2^v = k + 1
  · -- Case 1: 2^v = k+1
    have h_k : k = 2^v - 1 := by omega
    have hv_pos : v ≠ 0 := by
      intro hv_zero
      simp [hv_zero] at h_eq2
      omega
    have hv_ge_1 : 1 ≤ v := Nat.pos_of_ne_zero hv_pos
    have h_log : Nat.log2 (2^v - 1) = v - 1 := by
      -- 2^(v-1) <= 2^v - 1 and 2^v - 1 < 2^v
      have h_lt : 2^v - 1 < 2^(v-1+1) := by
        have : v = v - 1 + 1 := (Nat.sub_add_cancel hv_ge_1).symm
        rw [← this]
        omega
      have h_le2 : 2^(v-1) ≤ 2^v - 1 := by
        have : 2^v = 2^(v-1) * 2 := by
          have h_eq_v : v = v - 1 + 1 := (Nat.sub_add_cancel hv_ge_1).symm
          nth_rw 1 [h_eq_v]
          rw [pow_succ]
        rw [this]
        have h_two_pow : 1 ≤ 2^(v-1) := Nat.one_le_pow (v-1) 2 (by decide)
        omega
      rw [Nat.log2_eq_iff]
      · exact ⟨h_le2, h_lt⟩
      · omega
    rw [h_k, h_log] at h_eq
    have h_lt_v : v - 1 < v := Nat.sub_lt hv_ge_1 (by decide)
    omega
  · -- Case 2: 2^v < k+1
    have h_lt : 2^v < k + 1 := lt_of_le_of_ne h_le h_eq2
    have ⟨d, hd⟩ := h_dvd
    have hd_ge_2 : 2 ≤ d := by
      by_contra! h_lt2
      interval_cases d
      · simp [hd] at h_lt
      · simp [hd] at h_lt
    have hd_ne_2 : d ≠ 2 := by
      rintro rfl
      have h_eq3 : k + 1 = 2^(v+1) := by
        rw [hd]
        ring
      have h_val : padicValNat 2 (k + 1) = v + 1 := by
        rw [h_eq3, padicValNat.prime_pow]
      omega
    have hd_ge_3 : 3 ≤ d := by omega
    have hk2 : 2^(v+1) ≤ k := by
      have h_k2 : k = 2^v * d - 1 := by omega
      rw [h_k2]
      have : 2^(v+1) = 2^v * 2 := by ring
      rw [this]
      have h_le_mul : 2^v * 3 ≤ 2^v * d := by gcongr
      have h_two_pow_pos : 1 ≤ 2^v := Nat.one_le_pow v 2 (by decide)
      omega
    have h_log2 : v + 1 ≤ Nat.log2 k := by
      rw [Nat.le_log2]
      · exact hk2
      · omega
    omega



lemma padicValRat_two_S_even_power_eq {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (k : ℕ) (hk : 1 ≤ k) :
  padicValRat 2 ((range (2 * k + 1)).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^j)) : ℚ))) =
  - padicValRat 2 ((p + 1 : ℕ) : ℚ) - (Nat.log2 k : ℤ) := by
  have hp : p.Prime := Fact.out
  have hp_odd : p % 2 = 1 := hp.mod_two_eq_one_iff_ne_two.mpr hp2
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk1 : k = 1
    · subst hk1
      have h_eq : (range 3).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^j)) : ℚ)) =
        (p + 2 : ℚ) / (p + 1 : ℚ) + (1 : ℚ) / (↑((sigma 1) (p^2)) : ℚ) := by
        rw [sum_range_succ, sum_range_succ, sum_range_succ, sum_range_zero]
        rw [pow_one]
        have hp_sigma : (sigma 1) p = p + 1 := by
          rw [sigma_one_apply, hp.divisors, Finset.sum_pair hp.ne_one.symm]
          ring
        rw [hp_sigma]
        simp
        have h_pos : (p : ℚ) + 1 ≠ 0 := by
          have : 2 ≤ p := hp.two_le
          positivity
        field_simp
        ring
      rw [h_eq]
      -- valuation of the first term is -v_2(p+1) < 0
      have h_val_1 : padicValRat 2 ((p + 2 : ℚ) / (p + 1 : ℚ)) = - padicValRat 2 ((p + 1 : ℕ) : ℚ) := by
        rw [padicValRat.div (by positivity) (by positivity)]
        have h_odd : ¬ 2 ∣ (p + 2) := by
          intro h_dvd
          rw [add_comm] at h_dvd
          have h_dvd_p : 2 ∣ p := (Nat.dvd_add_right dvd_rfl).mp h_dvd
          have h_eq_2 : p = 2 := by
            rcases hp.eq_one_or_self_of_dvd 2 h_dvd_p with h_one | h_self
            · contradiction
            · exact h_self.symm
          exact hp2 h_eq_2
        have h_val_num : padicValRat 2 ((p + 2 : ℕ) : ℚ) = 0 := by
          rw [padicValRat.of_nat]
          have h_val_nat : padicValNat 2 (p + 2) = 0 := padicValNat.eq_zero_of_not_dvd h_odd
          rw [h_val_nat]
          rfl
        push_cast at h_val_num ⊢
        rw [h_val_num]
        ring
      have h_val_2 : padicValRat 2 ((1 : ℚ) / (↑((sigma 1) (p^2)) : ℚ)) = 0 := by
        exact padicValRat_two_recip_sigma_odd hp hp2 2 (by decide)
      have h_sum_pos : 0 < (p + 2 : ℚ) / (p + 1 : ℚ) := by positivity
      have h_term_pos : 0 < (1 : ℚ) / (↑((sigma 1) (p^2)) : ℚ) := by
        have h_sig : 0 < sigma 1 (p^2) := sigma_pos 1 (p^2) (pow_ne_zero 2 hp.ne_zero)
        have h_sig_q : 0 < (↑((sigma 1) (p^2)) : ℚ) := Nat.cast_pos.mpr h_sig
        exact div_pos zero_lt_one h_sig_q
      have h_sum_ne : (p + 2 : ℚ) / (p + 1 : ℚ) + (1 : ℚ) / (↑((sigma 1) (p^2)) : ℚ) ≠ 0 := _root_.ne_of_gt (add_pos h_sum_pos h_term_pos)
      have h_x_ne : (p + 2 : ℚ) / (p + 1 : ℚ) ≠ 0 := _root_.ne_of_gt h_sum_pos
      have h_y_ne : (1 : ℚ) / (↑((sigma 1) (p^2)) : ℚ) ≠ 0 := _root_.ne_of_gt h_term_pos
      have h_val_1_neg : padicValRat 2 ((p + 2 : ℚ) / (p + 1 : ℚ)) < 0 := by
        rw [h_val_1]
        have h_even : 2 ∣ (p + 1) := by
          have : (p + 1) % 2 = 0 := by omega
          exact Nat.dvd_of_mod_eq_zero this
        have h_val_den : 1 ≤ padicValNat 2 (p + 1) := one_le_padicValNat_of_dvd (by omega) h_even
        have h_val_den' : 1 ≤ padicValRat 2 ((p + 1 : ℕ) : ℚ) := by
          rw [padicValRat.of_nat]
          exact_mod_cast h_val_den
        omega
      have h_val_1_lt_2 : padicValRat 2 ((p + 2 : ℚ) / (p + 1 : ℚ)) < padicValRat 2 ((1 : ℚ) / (↑((sigma 1) (p^2)) : ℚ)) := by
        rw [h_val_2]
        exact h_val_1_neg
      rw [padicValRat.add_eq_of_lt h_sum_ne h_x_ne h_y_ne h_val_1_lt_2]
      rw [h_val_1]
      have : (Nat.log2 1 : ℤ) = 0 := rfl
      rw [this]
      ring
    · have hk_ge : 2 ≤ k := by omega
      have h_split : (range (2 * k + 1)).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^j)) : ℚ)) =
        (range (2 * (k - 1) + 1)).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^j)) : ℚ)) +
        (1 : ℚ) / (↑((sigma 1) (p^(2 * k - 1))) : ℚ) +
        (1 : ℚ) / (↑((sigma 1) (p^(2 * k))) : ℚ) := by
        have hk_eq : k = (k - 1) + 1 := by omega
        have h1 : 2 * k + 1 = 2 * (k - 1) + 1 + 1 + 1 := by
          nth_rw 1 [hk_eq]
          ring
        rw [h1, sum_range_succ, sum_range_succ]
        have h2 : 2 * (k - 1) + 1 = 2 * k - 1 := by omega
        have h3 : 2 * (k - 1) + 1 + 1 = 2 * k := by omega
        rw [h2, h3]
      rw [h_split]
      -- Let A = sum_{j=0}^{2k-2}, B = 1/\sigma(p^{2k-1}), C = 1/\sigma(p^{2k})
      -- we want to find valuation of (A + B) + C
      have h_ih : padicValRat 2 ((range (2 * (k - 1) + 1)).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^j)) : ℚ))) =
        - padicValRat 2 ((p + 1 : ℕ) : ℚ) - (Nat.log2 (k - 1) : ℤ) := by
        exact ih (k - 1) (by omega) (by omega)
      -- Valuation of B:
      have h_val_B : padicValRat 2 ((1 : ℚ) / (↑((sigma 1) (p^(2 * k - 1))) : ℚ)) =
        - padicValRat 2 ((p + 1 : ℕ) : ℚ) - (padicValNat 2 k : ℤ) := by
        -- \sigma(p^{2k-1}) = (p+1) * \sum_{i=0}^{k-1} p^{2i}
        have h_sig_eq : sigma 1 (p^(2 * k - 1)) = (p + 1) * ∑ i ∈ range k, p^(2 * i) := by
          have h_pow : 2 * k - 1 = 2 * (k - 1) + 1 := by omega
          have h_sig := sigma_odd_power_eq p hp (k - 1)
          have h_range : k - 1 + 1 = k := by omega
          rw [h_range] at h_sig
          rw [h_pow]
          exact h_sig
        have h_sig_q : (↑((sigma 1) (p^(2 * k - 1))) : ℚ) = ((p + 1 : ℕ) : ℚ) * ((∑ i ∈ range k, p^(2 * i) : ℕ) : ℚ) := by
          push_cast
          rw [h_sig_eq]
          push_cast
          rfl
        have h_div : (1 : ℚ) / (↑((sigma 1) (p^(2 * k - 1))) : ℚ) = 1 / (((p + 1 : ℕ) : ℚ) * ((∑ i ∈ range k, p^(2 * i) : ℕ) : ℚ)) := by
          congr 1
        rw [h_div]
        have hp1_ne : ((p + 1 : ℕ) : ℚ) ≠ 0 := by positivity
        have h_sum_nz : (∑ i ∈ range k, p^(2 * i) : ℕ) ≠ 0 := by
          apply _root_.ne_of_gt
          apply Finset.sum_pos
          · intro i hi
            have hp_pos : p > 0 := by omega
            positivity
          · rw [nonempty_range_iff]
            omega
        have hsum_ne : ((∑ i ∈ range k, p^(2 * i) : ℕ) : ℚ) ≠ 0 := by exact_mod_cast h_sum_nz
        rw [padicValRat.div (by positivity) (by positivity)]
        rw [padicValRat.one]
        have h_mul_val : padicValRat 2 (((p + 1 : ℕ) : ℚ) * ((∑ i ∈ range k, p^(2 * i) : ℕ) : ℚ)) =
          padicValRat 2 ((p + 1 : ℕ) : ℚ) + padicValRat 2 (((∑ i ∈ range k, p^(2 * i) : ℕ) : ℚ)) := by
          apply padicValRat.mul hp1_ne hsum_ne
        rw [h_mul_val]
        have h_sum_val : padicValRat 2 (((∑ i ∈ range k, p^(2 * i) : ℕ) : ℚ)) = (padicValNat 2 k : ℤ) := by
          rw [padicValRat.of_nat]
          rw [padicValNat_two_sum_pow_odd p hp_odd k]
        rw [h_sum_val]
        ring
      -- Valuation of C:
      have h_val_C : padicValRat 2 ((1 : ℚ) / (↑((sigma 1) (p^(2 * k))) : ℚ)) = 0 := by
        exact padicValRat_two_recip_sigma_odd hp hp2 (2 * k) (by omega)
      -- Valuation of A + B:
      -- Since v_2(A) != v_2(B) (log2 (k-1) != v_2(k) by log2_ne_padicValNat)
      have h_log_ne' := log2_ne_padicValNat (k - 1) (by omega)
      have h_range : k - 1 + 1 = k := by omega
      rw [h_range] at h_log_ne'
      have h_log_ne : (Nat.log2 (k - 1) : ℤ) ≠ (padicValNat 2 k : ℤ) := by exact_mod_cast h_log_ne'
      have h_val_A_ne_B : padicValRat 2 ((range (2 * (k - 1) + 1)).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^j)) : ℚ))) ≠
        padicValRat 2 ((1 : ℚ) / (↑((sigma 1) (p^(2 * k - 1))) : ℚ)) := by
        rw [h_ih, h_val_B]
        omega
      -- terms positive so non-zero
      have h_A_pos : 0 < (range (2 * (k - 1) + 1)).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^j)) : ℚ)) := S_prime_power_pos hp (2 * (k - 1))
      have h_B_pos : 0 < (1 : ℚ) / (↑((sigma 1) (p^(2 * k - 1))) : ℚ) := by
        have h_sig : 0 < sigma 1 (p^(2 * k - 1)) := sigma_pos 1 (p^(2 * k - 1)) (pow_ne_zero (2 * k - 1) hp.ne_zero)
        have h_sig_q : 0 < (↑((sigma 1) (p^(2 * k - 1))) : ℚ) := Nat.cast_pos.mpr h_sig
        exact div_pos zero_lt_one h_sig_q
      have h_AB_ne : (range (2 * (k - 1) + 1)).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^j)) : ℚ)) +
        (1 : ℚ) / (↑((sigma 1) (p^(2 * k - 1))) : ℚ) ≠ 0 := _root_.ne_of_gt (add_pos h_A_pos h_B_pos)
      have h_A_ne : (range (2 * (k - 1) + 1)).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^j)) : ℚ)) ≠ 0 := _root_.ne_of_gt h_A_pos
      have h_B_ne : (1 : ℚ) / (↑((sigma 1) (p^(2 * k - 1))) : ℚ) ≠ 0 := _root_.ne_of_gt h_B_pos
      have h_val_AB : padicValRat 2 ((range (2 * (k - 1) + 1)).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^j)) : ℚ)) +
        (1 : ℚ) / (↑((sigma 1) (p^(2 * k - 1))) : ℚ) : ℚ) =
        - padicValRat 2 ((p + 1 : ℕ) : ℚ) - (Nat.log2 k : ℤ) := by
        have h_val_A : padicValRat 2 ((range (2 * (k - 1) + 1)).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^j)) : ℚ))) =
          - padicValRat 2 ((p + 1 : ℕ) : ℚ) - (Nat.log2 (k - 1) : ℤ) := h_ih
        have h_val_B' := h_val_B
        by_cases h_lt : - padicValRat 2 ((p + 1 : ℕ) : ℚ) - (Nat.log2 (k - 1) : ℤ) < - padicValRat 2 ((p + 1 : ℕ) : ℚ) - (padicValNat 2 k : ℤ)
        · have h_lt_val : padicValRat 2 ((range (2 * (k - 1) + 1)).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^j)) : ℚ))) <
            padicValRat 2 ((1 : ℚ) / (↑((sigma 1) (p^(2 * k - 1))) : ℚ)) := by
            rwa [h_val_A, h_val_B']
          rw [padicValRat.add_eq_of_lt h_AB_ne h_A_ne h_B_ne h_lt_val]
          rw [h_ih]
          have h_max_eq : Max.max (Nat.log2 (k - 1)) (padicValNat 2 k) = Nat.log2 k := by
            have h_le_log : padicValNat 2 k ≤ Nat.log2 k := by
              have hk_ne : k ≠ 0 := by omega
              have h_dvd : 2^(padicValNat 2 k) ∣ k := pow_padicValNat_dvd
              have h_le := Nat.le_of_dvd (Nat.pos_of_ne_zero hk_ne) h_dvd
              exact (le_log2 hk_ne).mpr h_le
            by_cases h_eq : Nat.log2 (k - 1) = Nat.log2 k
            · rw [h_eq]
              exact max_eq_left h_le_log
            · have h_lt_log2 : Nat.log2 (k - 1) < Nat.log2 k := lt_of_le_of_ne (log2_mono (by omega)) h_eq
              have hk_pow : padicValNat 2 k = Nat.log2 k := by
                by_contra h_ne
                have h_lt_log : padicValNat 2 k < Nat.log2 k := lt_of_le_of_ne h_le_log h_ne
                have h_pow_le : 2^(Nat.log2 k) ≤ k - 1 := by
                  have h_lt_pow : 2^(Nat.log2 k) < k := by
                    apply lt_of_le_of_ne (Nat.log2_self_le (by omega))
                    intro h_eq_pow
                    have : padicValNat 2 (2^(Nat.log2 k)) = Nat.log2 k := by
                      exact @padicValNat.prime_pow 2 _ (Nat.log2 k)
                    rw [h_eq_pow] at this
                    omega
                  omega
                have h_log_le : Nat.log2 k ≤ Nat.log2 (k - 1) := by
                  have hk_sub_ne : k - 1 ≠ 0 := by omega
                  exact (le_log2 hk_sub_ne).mpr h_pow_le
                omega
              rw [hk_pow]
              exact max_eq_right (by omega)
          have h_max : Max.max (Nat.log2 (k - 1)) (padicValNat 2 k) = Nat.log2 (k - 1) := by omega
          have h_eq : Nat.log2 (k - 1) = Nat.log2 k := by rw [← h_max_eq, h_max]
          rw [h_eq]
        · have h_lt_val_rev : padicValRat 2 ((1 : ℚ) / (↑((sigma 1) (p^(2 * k - 1))) : ℚ)) <
            padicValRat 2 ((range (2 * (k - 1) + 1)).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^j)) : ℚ))) := by
            apply lt_of_le_of_ne
            · omega
            · exact h_val_A_ne_B.symm
          rw [add_comm]
          rw [padicValRat.add_eq_of_lt (by rw [add_comm]; exact h_AB_ne) h_B_ne h_A_ne h_lt_val_rev]
          rw [h_val_B]
          have h_max_eq : Max.max (Nat.log2 (k - 1)) (padicValNat 2 k) = Nat.log2 k := by
            have h_le_log : padicValNat 2 k ≤ Nat.log2 k := by
              have hk_ne : k ≠ 0 := by omega
              have h_dvd : 2^(padicValNat 2 k) ∣ k := pow_padicValNat_dvd
              have h_le := Nat.le_of_dvd (Nat.pos_of_ne_zero hk_ne) h_dvd
              exact (le_log2 hk_ne).mpr h_le
            by_cases h_eq : Nat.log2 (k - 1) = Nat.log2 k
            · rw [h_eq]
              exact max_eq_left h_le_log
            · have h_lt_log2 : Nat.log2 (k - 1) < Nat.log2 k := lt_of_le_of_ne (log2_mono (by omega)) h_eq
              have hk_pow : padicValNat 2 k = Nat.log2 k := by
                by_contra h_ne
                have h_lt_log : padicValNat 2 k < Nat.log2 k := lt_of_le_of_ne h_le_log h_ne
                have h_pow_le : 2^(Nat.log2 k) ≤ k - 1 := by
                  have h_lt_pow : 2^(Nat.log2 k) < k := by
                    apply lt_of_le_of_ne (Nat.log2_self_le (by omega))
                    intro h_eq_pow
                    have : padicValNat 2 (2^(Nat.log2 k)) = Nat.log2 k := by
                      exact @padicValNat.prime_pow 2 _ (Nat.log2 k)
                    rw [h_eq_pow] at this
                    omega
                  omega
                have h_log_le : Nat.log2 k ≤ Nat.log2 (k - 1) := by
                  have hk_sub_ne : k - 1 ≠ 0 := by omega
                  exact (le_log2 hk_sub_ne).mpr h_pow_le
                omega
              rw [hk_pow]
              exact max_eq_right (by omega)
          have h_max : Max.max (Nat.log2 (k - 1)) (padicValNat 2 k) = padicValNat 2 k := by omega
          have h_eq : padicValNat 2 k = Nat.log2 k := by rw [← h_max_eq, h_max]
          rw [h_eq]
      -- Finally, add C:
      -- Valuation of AB is negative (-v_2(p+1) - log2 k < 0), Valuation of C is 0.
      -- So we can use add_eq_of_lt!
      have h_C_pos : 0 < (1 : ℚ) / (↑((sigma 1) (p^(2 * k))) : ℚ) := by
        have h_sig : 0 < sigma 1 (p^(2 * k)) := sigma_pos 1 (p^(2 * k)) (pow_ne_zero (2 * k) hp.ne_zero)
        have h_sig_q : 0 < (↑((sigma 1) (p^(2 * k))) : ℚ) := Nat.cast_pos.mpr h_sig
        exact div_pos zero_lt_one h_sig_q
      have h_ABC_pos : 0 < (range (2 * (k - 1) + 1)).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^j)) : ℚ)) +
        (1 : ℚ) / (↑((sigma 1) (p^(2 * k - 1))) : ℚ) +
        (1 : ℚ) / (↑((sigma 1) (p^(2 * k))) : ℚ) := by linarith
      have h_ABC_ne : (range (2 * (k - 1) + 1)).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^j)) : ℚ)) +
        (1 : ℚ) / (↑((sigma 1) (p^(2 * k - 1))) : ℚ) +
        (1 : ℚ) / (↑((sigma 1) (p^(2 * k))) : ℚ) ≠ 0 := ne_of_gt h_ABC_pos
      have h_AB_ne' : (range (2 * (k - 1) + 1)).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^j)) : ℚ)) +
        (1 : ℚ) / (↑((sigma 1) (p^(2 * k - 1))) : ℚ) ≠ 0 := h_AB_ne
      have h_C_ne : (1 : ℚ) / (↑((sigma 1) (p^(2 * k))) : ℚ) ≠ 0 := ne_of_gt h_C_pos
      rw [padicValRat.add_eq_of_lt h_ABC_ne h_AB_ne' h_C_ne]
      · exact h_val_AB
      · -- valuation of AB is < 0, valuation of C is 0
        rw [h_val_AB, h_val_C]
        have h_even : 2 ∣ (p + 1) := by
          have : (p + 1) % 2 = 0 := by omega
          exact Nat.dvd_of_mod_eq_zero this
        have h_val_den : 1 ≤ padicValNat 2 (p + 1) := one_le_padicValNat_of_dvd (by omega) h_even
        have h_val_den' : 1 ≤ padicValRat 2 ((p + 1 : ℕ) : ℚ) := by
          rw [padicValRat.of_nat]
          exact_mod_cast h_val_den
        omega


lemma padicValRat_two_recip_sigma_odd_power {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (k : ℕ) (hk : 1 ≤ k) :
  padicValRat 2 ((1 : ℚ) / (↑((sigma 1) (p^(2 * k - 1))) : ℚ)) =
  - padicValRat 2 ((p + 1 : ℕ) : ℚ) - (padicValNat 2 k : ℤ) := by
  have hp : p.Prime := Fact.out
  have hp_odd : p % 2 = 1 := hp.mod_two_eq_one_iff_ne_two.mpr hp2
  have h_sig_eq : sigma 1 (p^(2 * k - 1)) = (p + 1) * ∑ i ∈ range k, p^(2 * i) := by
    have h_pow : 2 * k - 1 = 2 * (k - 1) + 1 := by omega
    have h_sig := sigma_odd_power_eq p hp (k - 1)
    have h_range : k - 1 + 1 = k := by omega
    rw [h_range] at h_sig
    rw [h_pow]
    exact h_sig
  have h_sig_q : (↑((sigma 1) (p^(2 * k - 1))) : ℚ) = ((p + 1 : ℕ) : ℚ) * ((∑ i ∈ range k, p^(2 * i) : ℕ) : ℚ) := by
    push_cast
    rw [h_sig_eq]
    push_cast
    rfl
  have h_div : (1 : ℚ) / (↑((sigma 1) (p^(2 * k - 1))) : ℚ) = 1 / (((p + 1 : ℕ) : ℚ) * ((∑ i ∈ range k, p^(2 * i) : ℕ) : ℚ)) := by
    congr 1
  rw [h_div]
  have hp1_ne : ((p + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have h_sum_nz : (∑ i ∈ range k, p^(2 * i) : ℕ) ≠ 0 := by
    apply _root_.ne_of_gt
    apply Finset.sum_pos
    · intro i hi
      have hp_pos : p > 0 := by omega
      positivity
    · rw [nonempty_range_iff]
      omega
  have hsum_ne : ((∑ i ∈ range k, p^(2 * i) : ℕ) : ℚ) ≠ 0 := by exact_mod_cast h_sum_nz
  rw [padicValRat.div (by positivity) (by positivity)]
  rw [padicValRat.one]
  have h_mul_val : padicValRat 2 (((p + 1 : ℕ) : ℚ) * ((∑ i ∈ range k, p^(2 * i) : ℕ) : ℚ)) =
    padicValRat 2 ((p + 1 : ℕ) : ℚ) + padicValRat 2 (((∑ i ∈ range k, p^(2 * i) : ℕ) : ℚ)) := by
    apply padicValRat.mul hp1_ne hsum_ne
  rw [h_mul_val]
  have h_sum_val : padicValRat 2 (((∑ i ∈ range k, p^(2 * i) : ℕ) : ℚ)) = (padicValNat 2 k : ℤ) := by
    rw [padicValRat.of_nat]
    rw [padicValNat_two_sum_pow_odd p hp_odd k]
  rw [h_sum_val]
  ring

lemma padicValRat_two_S_prime_power_neg {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (a : ℕ) (ha : 1 ≤ a) :
  padicValRat 2 ((p^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) < 0 := by
  have hp : p.Prime := Fact.out
  rw [S_prime_power_eq hp]
  induction a using Nat.strong_induction_on with
  | h a ih =>
    by_cases ha1 : a = 1
    · subst ha1
      have h_eq : (range 2).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^j)) : ℚ)) = (p + 2 : ℚ) / (p + 1 : ℚ) := by
        rw [sum_range_succ, sum_range_succ, sum_range_zero]
        rw [pow_one]
        have hp_sigma : (sigma 1) p = p + 1 := by
          rw [sigma_one_apply, hp.divisors, Finset.sum_pair hp.ne_one.symm]
          ring
        rw [hp_sigma]
        simp
        have h_pos : (p : ℚ) + 1 ≠ 0 := by
          have : 2 ≤ p := hp.two_le
          positivity
        field_simp
        ring
      rw [h_eq]
      rw [padicValRat.div (by positivity) (by positivity)]
      have h_odd : ¬ 2 ∣ (p + 2) := by
        intro h_dvd
        rw [add_comm] at h_dvd
        have h_dvd_p : 2 ∣ p := (Nat.dvd_add_right dvd_rfl).mp h_dvd
        have h_eq_2 : p = 2 := by
          rcases hp.eq_one_or_self_of_dvd 2 h_dvd_p with h_one | h_self
          · contradiction
          · exact h_self.symm
        exact hp2 h_eq_2
      have h_val_num : padicValRat 2 ((p + 2 : ℕ) : ℚ) = 0 := by
        rw [padicValRat.of_nat]
        have h_val_nat : padicValNat 2 (p + 2) = 0 := padicValNat.eq_zero_of_not_dvd h_odd
        rw [h_val_nat]
        rfl
      have h_val_den : 1 ≤ padicValNat 2 (p + 1) := by
        have h_even : 2 ∣ (p + 1) := by
          have : p % 2 = 1 := hp.mod_two_eq_one_iff_ne_two.mpr hp2
          have : (p + 1) % 2 = 0 := by omega
          exact Nat.dvd_of_mod_eq_zero this
        exact one_le_padicValNat_of_dvd (by omega) h_even
      have h_val_den' : 1 ≤ padicValRat 2 ((p + 1 : ℕ) : ℚ) := by
        rw [padicValRat.of_nat]
        exact_mod_cast h_val_den
      push_cast at h_val_num
      push_cast at h_val_den'
      rw [h_val_num]
      omega
    · have ha_ge : 2 ≤ a := by omega
      by_cases ha_even : a % 2 = 0
      · have h_split : (range (a + 1)).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^j)) : ℚ)) =
          (range a).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^j)) : ℚ)) + (1 : ℚ) / (↑((sigma 1) (p^a)) : ℚ) := by
          rw [sum_range_succ]
        rw [h_split]
        have h_ih : padicValRat 2 ((range a).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^j)) : ℚ))) < 0 := by
          have h_eq : a - 1 + 1 = a := by omega
          have := ih (a - 1) (by omega) (by omega)
          rwa [h_eq] at this
        have h_y : padicValRat 2 ((1 : ℚ) / (↑((sigma 1) (p^a)) : ℚ)) = 0 := by
          exact padicValRat_two_recip_sigma_odd hp hp2 a ha_even
        have h_sum_pos : 0 < (range a).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^j)) : ℚ)) := by
          have h_eq : a - 1 + 1 = a := by omega
          have := S_prime_power_pos hp (a - 1)
          rwa [h_eq] at this
        have h_term_pos : 0 < (1 : ℚ) / (↑((sigma 1) (p^a)) : ℚ) := by
          have h_sig : 0 < sigma 1 (p^a) := sigma_pos 1 (p^a) (pow_ne_zero a hp.ne_zero)
          have h_sig_q : 0 < (↑((sigma 1) (p^a)) : ℚ) := Nat.cast_pos.mpr h_sig
          exact div_pos zero_lt_one h_sig_q
        have h_sum_ne : (range a).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^j)) : ℚ)) + (1 : ℚ) / (↑((sigma 1) (p^a)) : ℚ) ≠ 0 := by
          exact_mod_cast ne_of_gt (add_pos h_sum_pos h_term_pos)
        have h_x_ne : (range a).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^j)) : ℚ)) ≠ 0 := ne_of_gt h_sum_pos
        have h_y_ne : (1 : ℚ) / (↑((sigma 1) (p^a)) : ℚ) ≠ 0 := ne_of_gt h_term_pos
        rw [padicValRat.add_eq_of_lt h_sum_ne h_x_ne h_y_ne (by omega)]
        exact h_ih
      · have ha_odd : a % 2 = 1 := Nat.mod_two_ne_zero.mp ha_even
        have hp_odd : p % 2 = 1 := hp.mod_two_eq_one_iff_ne_two.mpr hp2
        let k := (a + 1) / 2
        have hk_eq : 2 * k = a + 1 := by
          have h_mod : (a + 1) % 2 = 0 := by omega
          exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h_mod)
        have hk_ge : 2 ≤ k := by omega
        have hk : 1 ≤ k := by omega
        have h_a_eq_k : a = 2 * (k - 1) + 1 := by omega
        have h_a_eq_k' : a = 2 * k - 1 := by omega
        have h_split : (range (a + 1)).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^j)) : ℚ)) =
          (range a).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^j)) : ℚ)) + (1 : ℚ) / (↑((sigma 1) (p^a)) : ℚ) := by
          rw [sum_range_succ]
        rw [h_split]
        have h_x_eq : (range a).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^j)) : ℚ)) =
          (range (2 * (k - 1) + 1)).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^j)) : ℚ)) := by
          rw [h_a_eq_k]
        have h_y_eq : (1 : ℚ) / (↑((sigma 1) (p^a)) : ℚ) = (1 : ℚ) / (↑((sigma 1) (p^(2 * k - 1))) : ℚ) := by
          rw [h_a_eq_k']
        have h_val_x : padicValRat 2 ((range a).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^j)) : ℚ))) =
          - padicValRat 2 ((p + 1 : ℕ) : ℚ) - (Nat.log2 (k - 1) : ℤ) := by
          rw [h_x_eq]
          exact padicValRat_two_S_even_power_eq hp2 (k - 1) (by omega)
        have h_val_y : padicValRat 2 ((1 : ℚ) / (↑((sigma 1) (p^a)) : ℚ)) =
          - padicValRat 2 ((p + 1 : ℕ) : ℚ) - (padicValNat 2 k : ℤ) := by
          rw [h_y_eq]
          exact padicValRat_two_recip_sigma_odd_power hp2 k hk
        have h_log_ne' := log2_ne_padicValNat (k - 1) (by omega)
        have h_range : k - 1 + 1 = k := by omega
        rw [h_range] at h_log_ne'
        have h_val_ne : padicValRat 2 ((range a).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^j)) : ℚ))) ≠
          padicValRat 2 ((1 : ℚ) / (↑((sigma 1) (p^a)) : ℚ)) := by
          rw [h_val_x, h_val_y]
          intro h_eq
          have : (Nat.log2 (k - 1) : ℤ) = (padicValNat 2 k : ℤ) := by omega
          have : Nat.log2 (k - 1) = padicValNat 2 k := by exact_mod_cast this
          exact h_log_ne' this
        have h_sum_pos : 0 < (range a).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^j)) : ℚ)) := by
          have h_eq : a - 1 + 1 = a := by omega
          have := S_prime_power_pos hp (a - 1)
          rwa [h_eq] at this
        have h_term_pos : 0 < (1 : ℚ) / (↑((sigma 1) (p^a)) : ℚ) := by
          have h_sig : 0 < sigma 1 (p^a) := sigma_pos 1 (p^a) (pow_ne_zero a hp.ne_zero)
          have h_sig_q : 0 < (↑((sigma 1) (p^a)) : ℚ) := Nat.cast_pos.mpr h_sig
          exact div_pos zero_lt_one h_sig_q
        have h_sum_ne : (range a).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^j)) : ℚ)) + (1 : ℚ) / (↑((sigma 1) (p^a)) : ℚ) ≠ 0 := by
          exact_mod_cast ne_of_gt (add_pos h_sum_pos h_term_pos)
        have h_x_ne : (range a).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^j)) : ℚ)) ≠ 0 := ne_of_gt h_sum_pos
        have h_y_ne : (1 : ℚ) / (↑((sigma 1) (p^a)) : ℚ) ≠ 0 := ne_of_gt h_term_pos
        have h_val_x_neg : padicValRat 2 ((range a).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^j)) : ℚ))) < 0 := by
          have h_eq : a - 1 + 1 = a := by omega
          have := ih (a - 1) (by omega) (by omega)
          rwa [h_eq] at this
        have h_val_y_neg : padicValRat 2 ((1 : ℚ) / (↑((sigma 1) (p^a)) : ℚ)) < 0 := by
          rw [h_val_y]
          have h_even : 2 ∣ (p + 1) := by
            have : (p + 1) % 2 = 0 := by omega
            exact Nat.dvd_of_mod_eq_zero this
          have h_val_den : 1 ≤ padicValNat 2 (p + 1) := one_le_padicValNat_of_dvd (by omega) h_even
          have h_val_den' : 1 ≤ padicValRat 2 ((p + 1 : ℕ) : ℚ) := by
            rw [padicValRat.of_nat]
            exact_mod_cast h_val_den
          have h_val_k : 0 ≤ padicValNat 2 k := by omega
          have h_val_k' : 0 ≤ (padicValNat 2 k : ℤ) := by exact_mod_cast h_val_k
          omega
        by_cases h_lt : padicValRat 2 ((range a).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^j)) : ℚ))) <
          padicValRat 2 ((1 : ℚ) / (↑((sigma 1) (p^a)) : ℚ))
        · rw [padicValRat.add_eq_of_lt h_sum_ne h_x_ne h_y_ne h_lt]
          exact h_val_x_neg
        · have h_lt_rev : padicValRat 2 ((1 : ℚ) / (↑((sigma 1) (p^a)) : ℚ)) <
            padicValRat 2 ((range a).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^j)) : ℚ))) := by
            apply lt_of_le_of_ne
            · omega
            · exact h_val_ne.symm
          rw [add_comm]
          rw [padicValRat.add_eq_of_lt (by rw [add_comm]; exact h_sum_ne) h_y_ne h_x_ne h_lt_rev]
          exact h_val_y_neg



lemma padicValRat_two_S_three_pow_le_neg_two (a : ℕ) (ha : 1 ≤ a) :
  padicValRat 2 ((3^a : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≤ -2 := by
  have hp3 : (3 : ℕ).Prime := by decide
  rw [S_prime_power_eq hp3]
  induction a using Nat.strong_induction_on with
  | h a ih =>
    by_cases ha1 : a = 1
    · subst ha1
      have h_eq : (range 2).sum (fun j => (1 : ℚ) / (↑((sigma 1) ((3 : ℕ)^j)) : ℚ)) = (((5 : ℕ) : ℚ) / ((4 : ℕ) : ℚ)) := by
        rw [sum_range_succ, sum_range_succ, sum_range_zero]
        rw [pow_one]
        have hp_sigma : (sigma 1) 3 = 3 + 1 := by rfl
        rw [hp_sigma]
        norm_num
      rw [h_eq]
      have h_val_5_4 : padicValRat 2 (((5 : ℕ) : ℚ) / ((4 : ℕ) : ℚ)) = -2 := by
        rw [padicValRat.div (by positivity) (by positivity)]
        rw [padicValRat.of_nat, padicValRat.of_nat]
        have h5 : padicValNat 2 5 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
        have h4 : padicValNat 2 4 = 2 := by
          have : (4 : ℕ) = 2^2 := by rfl
          rw [this]
          exact @padicValNat.prime_pow 2 _ 2
        rw [h5, h4]
        rfl
      rw [h_val_5_4]
    · have ha_ge : 2 ≤ a := by omega
      by_cases ha_even : a % 2 = 0
      · have h_split : (range (a + 1)).sum (fun j => (1 : ℚ) / (↑((sigma 1) ((3 : ℕ)^j)) : ℚ)) =
          (range a).sum (fun j => (1 : ℚ) / (↑((sigma 1) ((3 : ℕ)^j)) : ℚ)) + (1 : ℚ) / (↑((sigma 1) ((3 : ℕ)^a)) : ℚ) := by
          rw [sum_range_succ]
        rw [h_split]
        have h_ih : padicValRat 2 ((range a).sum (fun j => (1 : ℚ) / (↑((sigma 1) ((3 : ℕ)^j)) : ℚ))) ≤ -2 := by
          have h_eq : a - 1 + 1 = a := by omega
          have := ih (a - 1) (by omega) (by omega)
          rwa [h_eq] at this
        have h_y : padicValRat 2 ((1 : ℚ) / (↑((sigma 1) ((3 : ℕ)^a)) : ℚ)) = 0 := by
          have hp3_prime : Nat.Prime 3 := by decide
          have h3_ne2 : 3 ≠ 2 := by decide
          exact padicValRat_two_recip_sigma_odd hp3_prime h3_ne2 a ha_even
        have h_sum_pos : 0 < (range a).sum (fun j => (1 : ℚ) / (↑((sigma 1) ((3 : ℕ)^j)) : ℚ)) := by
          have h_eq : a - 1 + 1 = a := by omega
          have := S_prime_power_pos hp3 (a - 1)
          rwa [h_eq] at this
        have h_term_pos : 0 < (1 : ℚ) / (↑((sigma 1) ((3 : ℕ)^a)) : ℚ) := by
          have h_sig : 0 < sigma 1 ((3 : ℕ)^a) := sigma_pos 1 ((3 : ℕ)^a) (pow_ne_zero a (by decide))
          have h_sig_q : 0 < (↑((sigma 1) ((3 : ℕ)^a)) : ℚ) := Nat.cast_pos.mpr h_sig
          exact div_pos zero_lt_one h_sig_q
        have h_sum_ne : (range a).sum (fun j => (1 : ℚ) / (↑((sigma 1) ((3 : ℕ)^j)) : ℚ)) + (1 : ℚ) / (↑((sigma 1) ((3 : ℕ)^a)) : ℚ) ≠ 0 := by
          exact_mod_cast ne_of_gt (add_pos h_sum_pos h_term_pos)
        have h_x_ne : (range a).sum (fun j => (1 : ℚ) / (↑((sigma 1) ((3 : ℕ)^j)) : ℚ)) ≠ 0 := ne_of_gt h_sum_pos
        have h_y_ne : (1 : ℚ) / (↑((sigma 1) ((3 : ℕ)^a)) : ℚ) ≠ 0 := ne_of_gt h_term_pos
        rw [padicValRat.add_eq_of_lt h_sum_ne h_x_ne h_y_ne (by omega)]
        exact h_ih
      · have ha_odd : a % 2 = 1 := Nat.mod_two_ne_zero.mp ha_even
        let k := (a + 1) / 2
        have hk_eq : 2 * k = a + 1 := by
          have h_mod : (a + 1) % 2 = 0 := by omega
          exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h_mod)
        have hk_ge : 2 ≤ k := by omega
        have hk : 1 ≤ k := by omega
        have h_a_eq_k : a = 2 * (k - 1) + 1 := by omega
        have h_a_eq_k' : a = 2 * k - 1 := by omega
        have h_split : (range (a + 1)).sum (fun j => (1 : ℚ) / (↑((sigma 1) ((3 : ℕ)^j)) : ℚ)) =
          (range a).sum (fun j => (1 : ℚ) / (↑((sigma 1) ((3 : ℕ)^j)) : ℚ)) + (1 : ℚ) / (↑((sigma 1) ((3 : ℕ)^a)) : ℚ) := by
          rw [sum_range_succ]
        rw [h_split]
        have h_x_eq : (range a).sum (fun j => (1 : ℚ) / (↑((sigma 1) ((3 : ℕ)^j)) : ℚ)) =
          (range (2 * (k - 1) + 1)).sum (fun j => (1 : ℚ) / (↑((sigma 1) ((3 : ℕ)^j)) : ℚ)) := by
          rw [h_a_eq_k]
        have h_y_eq : (1 : ℚ) / (↑((sigma 1) ((3 : ℕ)^a)) : ℚ) = (1 : ℚ) / (↑((sigma 1) ((3 : ℕ)^(2 * k - 1))) : ℚ) := by
          rw [h_a_eq_k']
        have h_val_x : padicValRat 2 ((range a).sum (fun j => (1 : ℚ) / (↑((sigma 1) ((3 : ℕ)^j)) : ℚ))) =
          - padicValRat 2 ((3 + 1 : ℕ) : ℚ) - (Nat.log2 (k - 1) : ℤ) := by
          rw [h_x_eq]
          have : 3 ≠ 2 := by decide
          exact padicValRat_two_S_even_power_eq this (k - 1) (by omega)
        have h_val_y : padicValRat 2 ((1 : ℚ) / (↑((sigma 1) ((3 : ℕ)^a)) : ℚ)) =
          - padicValRat 2 ((3 + 1 : ℕ) : ℚ) - (padicValNat 2 k : ℤ) := by
          rw [h_y_eq]
          have : 3 ≠ 2 := by decide
          exact padicValRat_two_recip_sigma_odd_power this k hk
        have h_log_ne' := log2_ne_padicValNat (k - 1) (by omega)
        have h_range : k - 1 + 1 = k := by omega
        rw [h_range] at h_log_ne'
        have h_val_ne : padicValRat 2 ((range a).sum (fun j => (1 : ℚ) / (↑((sigma 1) ((3 : ℕ)^j)) : ℚ))) ≠
          padicValRat 2 ((1 : ℚ) / (↑((sigma 1) ((3 : ℕ)^a)) : ℚ)) := by
          rw [h_val_x, h_val_y]
          intro h_eq
          have : (Nat.log2 (k - 1) : ℤ) = (padicValNat 2 k : ℤ) := by omega
          have : Nat.log2 (k - 1) = padicValNat 2 k := by exact_mod_cast this
          exact h_log_ne' this
        have h_sum_pos : 0 < (range a).sum (fun j => (1 : ℚ) / (↑((sigma 1) ((3 : ℕ)^j)) : ℚ)) := by
          have h_eq : a - 1 + 1 = a := by omega
          have := S_prime_power_pos hp3 (a - 1)
          rwa [h_eq] at this
        have h_term_pos : 0 < (1 : ℚ) / (↑((sigma 1) ((3 : ℕ)^a)) : ℚ) := by
          have h_sig : 0 < sigma 1 ((3 : ℕ)^a) := sigma_pos 1 ((3 : ℕ)^a) (pow_ne_zero a (by decide))
          have h_sig_q : 0 < (↑((sigma 1) ((3 : ℕ)^a)) : ℚ) := Nat.cast_pos.mpr h_sig
          exact div_pos zero_lt_one h_sig_q
        have h_sum_ne : (range a).sum (fun j => (1 : ℚ) / (↑((sigma 1) ((3 : ℕ)^j)) : ℚ)) + (1 : ℚ) / (↑((sigma 1) ((3 : ℕ)^a)) : ℚ) ≠ 0 := by
          exact_mod_cast ne_of_gt (add_pos h_sum_pos h_term_pos)
        have h_x_ne : (range a).sum (fun j => (1 : ℚ) / (↑((sigma 1) ((3 : ℕ)^j)) : ℚ)) ≠ 0 := ne_of_gt h_sum_pos
        have h_y_ne : (1 : ℚ) / (↑((sigma 1) ((3 : ℕ)^a)) : ℚ) ≠ 0 := ne_of_gt h_term_pos
        have h_val_x_neg : padicValRat 2 ((range a).sum (fun j => (1 : ℚ) / (↑((sigma 1) ((3 : ℕ)^j)) : ℚ))) ≤ -2 := by
          have h_eq : a - 1 + 1 = a := by omega
          have := ih (a - 1) (by omega) (by omega)
          rwa [h_eq] at this
        have h_val_y_neg : padicValRat 2 ((1 : ℚ) / (↑((sigma 1) ((3 : ℕ)^a)) : ℚ)) ≤ -2 := by
          rw [h_val_y]
          have h_four : padicValRat 2 ((3 + 1 : ℕ) : ℚ) = 2 := by
            change padicValRat 2 ((4 : ℕ) : ℚ) = 2
            rw [padicValRat.of_nat]
            have : (4 : ℕ) = 2^2 := by rfl
            rw [this]
            have : padicValNat 2 (2^2) = 2 := @padicValNat.prime_pow 2 _ 2
            exact_mod_cast this
          rw [h_four]
          have h_val_k : 0 ≤ padicValNat 2 k := by omega
          have h_val_k' : 0 ≤ (padicValNat 2 k : ℤ) := by exact_mod_cast h_val_k
          omega
        by_cases h_lt : padicValRat 2 ((range a).sum (fun j => (1 : ℚ) / (↑((sigma 1) ((3 : ℕ)^j)) : ℚ))) <
          padicValRat 2 ((1 : ℚ) / (↑((sigma 1) ((3 : ℕ)^a)) : ℚ))
        · rw [padicValRat.add_eq_of_lt h_sum_ne h_x_ne h_y_ne h_lt]
          exact h_val_x_neg
        · have h_lt_rev : padicValRat 2 ((1 : ℚ) / (↑((sigma 1) ((3 : ℕ)^a)) : ℚ)) <
            padicValRat 2 ((range a).sum (fun j => (1 : ℚ) / (↑((sigma 1) ((3 : ℕ)^j)) : ℚ))) := by
            apply lt_of_le_of_ne
            · omega
            · exact h_val_ne.symm
          rw [add_comm]
          rw [padicValRat.add_eq_of_lt (by rw [add_comm]; exact h_sum_ne) h_y_ne h_x_ne h_lt_rev]
          exact h_val_y_neg

lemma S_pos (x : ℕ) (hx : 1 ≤ x) :
  0 < x.divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := by
  apply Finset.sum_pos
  · intro d hd
    have h_sig_pos : 0 < sigma 1 d := by
      have : d ∈ x.divisors := hd
      have hd_nz : d ≠ 0 := by
        intro hd_zero
        subst hd_zero
        have := Nat.dvd_of_mem_divisors hd
        omega
      exact sigma_pos 1 d (by positivity)
    have h_sig_q : 0 < (↑((sigma 1) d) : ℚ) := Nat.cast_pos.mpr h_sig_pos
    exact div_pos zero_lt_one h_sig_q
  · use 1
    rw [mem_divisors]
    omega


lemma S_le_S_of_dvd {x y : ℕ} (hx : x ≠ 0) (hy : 1 ≤ y) (hdvd : y ∣ x) :
  (y.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≤ (x.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Nat.divisors_subset_of_dvd hx hdvd)
  intro d hd h_not
  have h_sig : 0 < sigma 1 d := sigma_pos 1 d (by
    have : d ∈ x.divisors := hd
    have : d ≠ 0 := by
      intro h0
      subst h0
      have := Nat.dvd_of_mem_divisors hd
      omega
    positivity)
  have h_sig_q : 0 < (↑((sigma 1) d) : ℚ) := Nat.cast_pos.mpr h_sig
  exact le_of_lt (div_pos zero_lt_one h_sig_q)


lemma S_ge_one (x : ℕ) (hx : 1 ≤ x) :
  1 ≤ (x.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := by
  have h1 : 1 ∈ x.divisors := Nat.one_mem_divisors.mpr (by omega)
  have h_sum := Finset.single_le_sum (f := fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) (by
    intro d hd
    have h_sig : 0 < sigma 1 d := sigma_pos 1 d (by
      have : d ∈ x.divisors := hd
      have : d ≠ 0 := by
        intro h0
        subst h0
        have := Nat.dvd_of_mem_divisors hd
        omega
      positivity)
    have h_sig_q : 0 < (↑((sigma 1) d) : ℚ) := Nat.cast_pos.mpr h_sig
    exact le_of_lt (div_pos zero_lt_one h_sig_q)) h1
  have h_beta : (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) 1 = (1 : ℚ) / (↑((sigma 1) 1) : ℚ) := rfl
  rw [h_beta] at h_sum
  have h_one : (sigma 1) 1 = 1 := rfl
  rw [h_one] at h_sum
  norm_num at h_sum
  simp_rw [one_div]
  exact h_sum

lemma S_prime_power_ge {p : ℕ} (hp : p.Prime) (a : ℕ) (ha : 1 ≤ a) :
  1 + 1 / ((p : ℚ) + 1) ≤ ((p^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := by
  have hp_pos : p^a ≠ 0 := by
    have : 2 ≤ p := hp.two_le
    positivity
  have h_subset : {1, p} ⊆ (p^a).divisors := by
    intro y hy
    rw [mem_insert, mem_singleton] at hy
    rcases hy with h1 | h2
    · rw [h1]
      rw [mem_divisors]
      exact ⟨one_dvd _, hp_pos⟩
    · rw [h2]
      rw [mem_divisors]
      have : p ∣ p^a := dvd_pow_self p (by omega)
      exact ⟨this, hp_pos⟩
  have h_sum := Finset.sum_le_sum_of_subset_of_nonneg (f := fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) h_subset (by
    intro d hd h_not
    have h_sig : 0 < sigma 1 d := sigma_pos 1 d (by
      have : d ∈ (p^a).divisors := hd
      have : d ≠ 0 := by
        intro h0
        subst h0
        have := Nat.dvd_of_mem_divisors hd
        omega
      positivity)
    have h_sig_q : 0 < (↑((sigma 1) d) : ℚ) := Nat.cast_pos.mpr h_sig
    exact le_of_lt (div_pos zero_lt_one h_sig_q))
  rw [sum_insert (by simp [hp.ne_one.symm]), sum_singleton] at h_sum
  have h_one : (sigma 1) 1 = 1 := rfl
  have h_p : (sigma 1) p = p + 1 := by
    rw [sigma_one_apply, hp.divisors, sum_pair hp.ne_one.symm]
    ring
  rw [h_one, h_p] at h_sum
  norm_num at h_sum
  simp_rw [one_div]
  exact h_sum

lemma S_three_power_ge_two (a : ℕ) (ha : 2 ≤ a) :
  69 / 52 ≤ ((3^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := by
  have hp_pos : 3^a ≠ 0 := by positivity
  have h_subset : {1, 3, 9} ⊆ (3^a).divisors := by
    intro y hy
    rw [mem_insert, mem_insert, mem_singleton] at hy
    rcases hy with h1 | h2 | h3
    · rw [h1]; rw [mem_divisors]; exact ⟨one_dvd _, hp_pos⟩
    · rw [h2]; rw [mem_divisors]; exact ⟨dvd_pow_self 3 (by omega), hp_pos⟩
    · rw [h3]; rw [mem_divisors]
      have : 9 = 3^2 := by rfl
      rw [this]
      exact ⟨pow_dvd_pow 3 ha, hp_pos⟩
  have h_sum := Finset.sum_le_sum_of_subset_of_nonneg (f := fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) h_subset (by
    intro d hd h_not
    have h_sig : 0 < sigma 1 d := sigma_pos 1 d (by
      have : d ∈ (3^a).divisors := hd
      have : d ≠ 0 := by
        intro h0
        subst h0
        have := Nat.dvd_of_mem_divisors hd
        omega
      positivity)
    have h_sig_q : 0 < (↑((sigma 1) d) : ℚ) := Nat.cast_pos.mpr h_sig
    exact le_of_lt (div_pos zero_lt_one h_sig_q))
  rw [sum_insert (by simp), sum_insert (by simp), sum_singleton] at h_sum
  have h1 : (sigma 1) 1 = 1 := rfl
  have h3 : (sigma 1) 3 = 4 := rfl
  have h9 : (sigma 1) 9 = 13 := rfl
  rw [h1, h3, h9] at h_sum
  norm_num at h_sum
  simp_rw [one_div]
  exact h_sum

lemma sum_recip_pow_eq (q : ℕ) (hq : 2 ≤ q) (b : ℕ) :
  (range (b + 1)).sum (fun j => (1 : ℚ) / (q : ℚ)^j) + 1 / (((q : ℚ) - 1) * (q : ℚ)^b) = (q : ℚ) / ((q : ℚ) - 1) := by
  have h_q_ge : (q : ℚ) ≥ 2 := by exact_mod_cast hq
  induction b with
  | zero =>
    simp
    have : (q : ℚ) - 1 ≠ 0 := by linarith
    field_simp; ring
  | succ b ih =>
    rw [sum_range_succ, add_assoc]
    have hq_min_one : (q : ℚ) - 1 ≠ 0 := by linarith
    have hq_val : (q : ℚ) ≠ 0 := by linarith
    have hq_pow : (q : ℚ)^b ≠ 0 := by positivity
    have h_sub : (1 : ℚ) / (q : ℚ)^(b+1) + 1 / (((q : ℚ) - 1) * (q : ℚ)^(b+1)) = 1 / (((q : ℚ) - 1) * (q : ℚ)^b) := by
      field_simp
      ring
    rw [h_sub]
    exact ih

lemma S_le_sum_recip_pow (q : ℕ) (hq : q.Prime) (b : ℕ) :
  ((q^b).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≤ (range (b + 1)).sum (fun j => (1 : ℚ) / (q : ℚ)^j) := by
  have hq_pos : (q : ℚ) > 0 := by
    have : q ≥ 2 := hq.two_le
    exact_mod_cast (by omega : q > 0)
  rw [S_prime_power_eq hq]
  apply Finset.sum_le_sum
  intro j hj
  have h_sig : (sigma 1) (q^j) ≥ q^j := by
    rw [sigma_one_apply]
    have h_div : q^j ∈ (q^j).divisors := by
      rw [mem_divisors]
      exact ⟨dvd_rfl, pow_ne_zero j hq.ne_zero⟩
    exact Finset.single_le_sum (fun d _ => Nat.zero_le d) h_div
  have h_sig_q : (↑((sigma 1) (q^j)) : ℚ) ≥ (q : ℚ)^j := by
    exact_mod_cast h_sig
  have hq_pow_pos : (q : ℚ)^j > 0 := by
    have : q^j > 0 := by
      have : q ≥ 2 := hq.two_le
      positivity
    exact_mod_cast this
  have h_sig_pos : (↑((sigma 1) (q^j)) : ℚ) > 0 := by
    have : (sigma 1) (q^j) > 0 := by omega
    exact_mod_cast this
  exact div_le_div_of_nonneg_left (by norm_num) hq_pow_pos h_sig_q

lemma S_lt_q_sub_one (q : ℕ) (hq : q.Prime) (b : ℕ) :
  ((q^b).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) < (q : ℚ) / ((q : ℚ) - 1) := by
  have hq_ge2 : 2 ≤ q := hq.two_le
  have hq_pos : (q : ℚ) > 0 := by
    exact_mod_cast (by omega : q > 0)
  have h_le := S_le_sum_recip_pow q hq b
  have h_sum := sum_recip_pow_eq q hq_ge2 b
  have h_pos : 1 / (((q : ℚ) - 1) * (q : ℚ)^b) > 0 := by
    have hq_min_one : (q : ℚ) - 1 > 0 := by
      have : (q : ℚ) ≥ 2 := by exact_mod_cast hq_ge2
      linarith
    have hq_pow : (q : ℚ)^b > 0 := by
      have : q^b > 0 := by positivity
      exact_mod_cast this
    positivity
  linarith

lemma padicValRat_two_S_odd_neg (n : ℕ) (hn : 1 < n) (hn_odd : n % 2 = 1) :
  padicValRat 2 ((n.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) < 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h_prime : n.Prime
    · have : Fact n.Prime := ⟨h_prime⟩
      have hp2 : n ≠ 2 := by omega
      have := padicValRat_two_S_prime_power_neg hp2 1 (by omega)
      rwa [pow_one] at this
    · by_cases h_pow : ∃ (p : ℕ) (hp : p.Prime) (a : ℕ), n = p^a
      · rcases h_pow with ⟨p, hp, a, rfl⟩
        have : Fact p.Prime := ⟨hp⟩
        have ha : 1 ≤ a := by
          by_contra! h_lt
          have : a = 0 := by omega
          subst this
          norm_num at hn
        have hp2 : p ≠ 2 := by
          intro hp2
          subst hp2
          have ha_nz : a ≠ 0 := by omega
          have : 2 ∣ (2 : ℕ)^a := dvd_pow_self 2 ha_nz
          have h_mod : (2 : ℕ)^a % 2 = 0 := Nat.mod_eq_zero_of_dvd this
          omega
        exact padicValRat_two_S_prime_power_neg hp2 a ha
      · have h_ne : n ≠ 1 := by omega
        have ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd h_ne
        let a := padicValNat p n
        have hp_fact : Fact p.Prime := ⟨hp⟩
        have ha : 1 ≤ a := one_le_padicValNat_of_dvd (by omega) hdvd
        have hn_nz : n ≠ 0 := by omega
        let m := n / p^a
        have hdvd_pa : p^a ∣ n := pow_padicValNat_dvd
        have hn_eq : n = p^a * m := by
          exact (Nat.mul_div_cancel' hdvd_pa).symm
        have h_coprime : Nat.Coprime (p^a) m := by
          have h_cop_pm : Nat.Coprime p m := by
            rw [hp.coprime_iff_not_dvd]
            intro hp_dvd_m
            rcases hp_dvd_m with ⟨k, hk⟩
            have h_div : p^(a + 1) ∣ n := by
              rw [hn_eq, hk]
              use k
              ring
            have h_not := pow_succ_padicValNat_not_dvd (p := p) hn_nz
            exact h_not h_div
          exact h_cop_pm.pow_left a
        have hm_gt_one : 1 < m := by
          by_contra! h_le
          interval_cases m
          · rw [mul_zero] at hn_eq
            omega
          · rw [mul_one] at hn_eq
            have : n = p^a := hn_eq
            exact h_pow ⟨p, hp, a, this⟩
        have h_pa_gt_one : 1 < p^a := by
          have hp_pos : 2 ≤ p := hp.two_le
          have : p^1 ≤ p^a := Nat.pow_le_pow_right (by omega) ha
          rw [pow_one] at this
          omega
        have h_pa_lt_n : p^a < n := by
          rw [hn_eq, mul_comm]
          have h_pa_pos : 0 < p^a := by positivity
          have h_mul := Nat.mul_lt_mul_of_pos_right hm_gt_one h_pa_pos
          rwa [one_mul] at h_mul
        have hm_lt_n : m < n := by
          rw [hn_eq]
          have hm_pos : 0 < m := by omega
          have h_mul := Nat.mul_lt_mul_of_pos_right h_pa_gt_one hm_pos
          rwa [one_mul] at h_mul
        have h_pa_odd : (p^a) % 2 = 1 := by
          have : (p^a * m) % 2 = 1 := by rwa [← hn_eq]
          rw [Nat.mul_mod] at this
          by_contra! h_even
          have h_zero : p^a % 2 = 0 := by omega
          rw [h_zero, zero_mul, Nat.zero_mod] at this
          omega
        have hm_odd : m % 2 = 1 := by
          have : (p^a * m) % 2 = 1 := by rwa [← hn_eq]
          rw [Nat.mul_mod] at this
          by_contra! h_even
          have h_zero : m % 2 = 0 := by omega
          rw [h_zero, mul_zero, Nat.zero_mod] at this
          omega
        have ih1 := ih (p^a) h_pa_lt_n h_pa_gt_one h_pa_odd
        have ih2 := ih m hm_lt_n hm_gt_one hm_odd
        have h_S_eq : (n.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) =
          ((p^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) *
          (m.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := by
          rw [← sum_f_eq_sum_recip n hn]
          rw [← sum_f_eq_sum_recip (p^a) h_pa_gt_one]
          rw [← sum_f_eq_sum_recip m hm_gt_one]
          rw [← f_mul_zeta_apply n]
          rw [← f_mul_zeta_apply (p^a)]
          rw [← f_mul_zeta_apply m]
          rw [hn_eq]
          exact S_mul_of_coprime h_coprime
        rw [h_S_eq]
        rw [padicValRat.mul]
        · omega
        · have hp2 : p ≠ 2 := by
            intro hp2
            subst hp2
            have ha_nz : a ≠ 0 := by omega
            have : 2 ∣ (2 : ℕ)^a := dvd_pow_self 2 ha_nz
            have h_mod : (2 : ℕ)^a % 2 = 0 := Nat.mod_eq_zero_of_dvd this
            omega
          have : 0 < (range (a + 1)).sum (fun j => (1 : ℚ) / (↑((sigma 1) (p^j)) : ℚ)) := S_prime_power_pos hp a
          rw [← S_prime_power_eq hp] at this
          exact ne_of_gt this
        · have hm_pos : 1 ≤ m := by omega
          have : 0 < m.divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := S_pos m hm_pos
          exact ne_of_gt this

lemma padicValRat_two_recip_add_recip_even (a b : ℕ) (ha : a % 2 = 1) (hb : b % 2 = 1) (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
  1 ≤ padicValRat 2 ((1 : ℚ) / (a : ℚ) + (1 : ℚ) / (b : ℚ)) := by
  have h_sum : (1 : ℚ) / (a : ℚ) + (1 : ℚ) / (b : ℚ) = (a + b : ℚ) / (a * b : ℚ) := by
    have ha_q : (a : ℚ) ≠ 0 := by exact_mod_cast ha0
    have hb_q : (b : ℚ) ≠ 0 := by exact_mod_cast hb0
    field_simp
    ring
  rw [h_sum]
  have h_cast : (a * b : ℚ) = ((a * b : ℕ) : ℚ) := by push_cast; rfl
  have h_cast_add : (a + b : ℚ) = ((a + b : ℕ) : ℚ) := by push_cast; rfl
  rw [h_cast_add, h_cast]
  have h_ab_pos' : ((a * b : ℕ) : ℚ) ≠ 0 := by
    have : a * b ≠ 0 := Nat.mul_ne_zero ha0 hb0
    exact_mod_cast this
  rw [padicValRat.div (by positivity) h_ab_pos']
  have h_val_ab : padicValRat 2 ((a * b : ℕ) : ℚ) = 0 := by
    rw [padicValRat.of_nat]
    have h_odd : ¬ 2 ∣ a * b := by
      intro hdvd
      have h_mod : (a * b) % 2 = 0 := Nat.mod_eq_zero_of_dvd hdvd
      rw [Nat.mul_mod, ha, hb] at h_mod
      omega
    rw [padicValNat.eq_zero_of_not_dvd h_odd]
    rfl
  rw [h_val_ab, sub_zero]
  rw [padicValRat.of_nat]
  have h_even : 2 ∣ a + b := by omega
  have h_val_nat : 1 ≤ padicValNat 2 (a + b) := one_le_padicValNat_of_dvd (by omega) h_even
  exact_mod_cast h_val_nat

lemma padicValRat_two_add_of_zero_and_ge_one {x y : ℚ} (hx : padicValRat 2 x = 0) (hy : 1 ≤ padicValRat 2 y) (hx_ne : x ≠ 0) (hy_ne : y ≠ 0) (hsum_ne : x + y ≠ 0) :
  padicValRat 2 (x + y) = 0 := by
  have h_lt : padicValRat 2 x < padicValRat 2 y := by omega
  rw [padicValRat.add_eq_of_lt hsum_ne hx_ne hy_ne h_lt]
  exact hx

lemma sum_range_split_two {β : Type*} [AddCommMonoid β] (f : ℕ → β) (n : ℕ) :
  (range (n + 2)).sum f = (range n).sum f + f n + f (n + 1) := by
  rw [sum_range_succ, sum_range_succ, add_assoc]

lemma padicValRat_two_S_two_pow_even_helper (r : ℕ) :
  padicValRat 2 ((range (2 * r + 1)).sum (fun j => (1 : ℚ) / ((2 : ℚ) ^ (j + 1) - 1))) = 0 := by
  induction r with
  | zero =>
    norm_num
  | succ r ih =>
    have h_split : (range (2 * (r + 1) + 1)).sum (fun j => (1 : ℚ) / ((2 : ℚ) ^ (j + 1) - 1)) =
      (range (2 * r + 1)).sum (fun j => (1 : ℚ) / ((2 : ℚ) ^ (j + 1) - 1)) +
      (1 : ℚ) / ((2 : ℚ) ^ (2 * r + 1 + 1) - 1) +
      (1 : ℚ) / ((2 : ℚ) ^ (2 * r + 1 + 2) - 1) := by
      have h_eq : 2 * (r + 1) + 1 = 2 * r + 1 + 2 := by ring
      rw [h_eq]
      exact sum_range_split_two (fun j => (1 : ℚ) / ((2 : ℚ) ^ (j + 1) - 1)) (2 * r + 1)
    rw [h_split]
    -- regroup as x + (y1 + y2)
    rw [add_assoc]
    let x := (range (2 * r + 1)).sum (fun j => (1 : ℚ) / ((2 : ℚ) ^ (j + 1) - 1))
    let y1 := (1 : ℚ) / ((2 : ℚ) ^ (2 * r + 2) - 1)
    let y2 := (1 : ℚ) / ((2 : ℚ) ^ (2 * r + 3) - 1)
    have hy1 : y1 = (1 : ℚ) / (((2 ^ (2 * r + 2) - 1 : ℕ) : ℚ)) := by
      have h_le : 1 ≤ 2 ^ (2 * r + 2) := Nat.one_le_pow _ 2 (by decide)
      push_cast [Nat.cast_sub h_le]
      rfl
    have hy2 : y2 = (1 : ℚ) / (((2 ^ (2 * r + 3) - 1 : ℕ) : ℚ)) := by
      have h_le : 1 ≤ 2 ^ (2 * r + 3) := Nat.one_le_pow _ 2 (by decide)
      push_cast [Nat.cast_sub h_le]
      rfl
    have hy_sum : y1 + y2 = (1 : ℚ) / ((2 ^ (2 * r + 2) - 1 : ℕ) : ℚ) + (1 : ℚ) / ((2 ^ (2 * r + 3) - 1 : ℕ) : ℚ) := by
      rw [hy1, hy2]
    have h_val_y : 1 ≤ padicValRat 2 (y1 + y2) := by
      rw [hy_sum]
      have ha_le : 1 ≤ 2 ^ (2 * r + 2) := Nat.one_le_pow _ 2 (by decide)
      have hb_le : 1 ≤ 2 ^ (2 * r + 3) := Nat.one_le_pow _ 2 (by decide)
      have ha_odd : (2 ^ (2 * r + 2) - 1) % 2 = 1 := by
        have h_pow : 2 ^ (2 * r + 2) = 2 * 2 ^ (2 * r + 1) := by ring
        have h_even : 2 ∣ 2 ^ (2 * r + 2) := by
          rw [h_pow]
          exact dvd_mul_right 2 _
        have h_mod : 2 ^ (2 * r + 2) % 2 = 0 := Nat.mod_eq_zero_of_dvd h_even
        omega
      have hb_odd : (2 ^ (2 * r + 3) - 1) % 2 = 1 := by
        have h_pow : 2 ^ (2 * r + 3) = 2 * 2 ^ (2 * r + 2) := by ring
        have h_even : 2 ∣ 2 ^ (2 * r + 3) := by
          rw [h_pow]
          exact dvd_mul_right 2 _
        have h_mod : 2 ^ (2 * r + 3) % 2 = 0 := Nat.mod_eq_zero_of_dvd h_even
        omega
      have ha0 : 2 ^ (2 * r + 2) - 1 ≠ 0 := by omega
      have hb0 : 2 ^ (2 * r + 3) - 1 ≠ 0 := by omega
      exact padicValRat_two_recip_add_recip_even _ _ ha_odd hb_odd ha0 hb0
    -- now apply padicValRat_two_add_of_zero_and_ge_one
    have hx_pos : 0 < x := by
      apply Finset.sum_pos
      · intro j hj
        have h_pos_nat : 0 < 2 ^ (j + 1) - 1 := by
          have h_le : 2 ≤ 2 ^ (j + 1) := by
            have h_le := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 1 ≤ j + 1 by omega)
            rw [pow_one] at h_le
            exact h_le
          omega
        have h_le : 1 ≤ 2 ^ (j + 1) := Nat.one_le_pow (j + 1) 2 (by decide)
        have : (2 : ℚ) ^ (j + 1) - 1 = ((2 ^ (j + 1) - 1 : ℕ) : ℚ) := by
          push_cast [Nat.cast_sub h_le]
          rfl
        rw [this]
        exact div_pos (by norm_num) (by exact_mod_cast h_pos_nat)
      · rw [nonempty_range_iff]
        omega
    have hy1_pos : 0 < y1 := by
      rw [hy1]
      have h_pos_nat : 0 < 2 ^ (2 * r + 2) - 1 := by
        have : 2 ≤ 2 ^ (2 * r + 2) := by
          have : 1 ≤ 2 * r + 2 := by omega
          have h_pow := Nat.pow_le_pow_right (show 0 < 2 by decide) this
          rw [pow_one] at h_pow
          exact h_pow
        omega
      exact div_pos (by norm_num) (by exact_mod_cast h_pos_nat)
    have hy2_pos : 0 < y2 := by
      rw [hy2]
      have h_pos_nat : 0 < 2 ^ (2 * r + 3) - 1 := by
        have : 2 ≤ 2 ^ (2 * r + 3) := by
          have : 1 ≤ 2 * r + 3 := by omega
          have h_pow := Nat.pow_le_pow_right (show 0 < 2 by decide) this
          rw [pow_one] at h_pow
          exact h_pow
        omega
      exact div_pos (by norm_num) (by exact_mod_cast h_pos_nat)
    have hsum_ne : x + (y1 + y2) ≠ 0 := by
      have : 0 < x + (y1 + y2) := add_pos hx_pos (add_pos hy1_pos hy2_pos)
      exact ne_of_gt this
    exact padicValRat_two_add_of_zero_and_ge_one ih h_val_y (ne_of_gt hx_pos) (ne_of_gt (add_pos hy1_pos hy2_pos)) hsum_ne

lemma padicValRat_two_S_two_pow_even (k : ℕ) (hk : k % 2 = 0) :
  padicValRat 2 ((2^k).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = 0 := by
  rw [S_two_pow_eq]
  have h_eq : k + 1 = 2 * (k / 2) + 1 := by
    have h_div : k = 2 * (k / 2) := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hk)).symm
    omega
  rw [h_eq]
  exact padicValRat_two_S_two_pow_even_helper (k / 2)

lemma padicValRat_two_recip_pow_two_minus_one (k : ℕ) :
  padicValRat 2 ((1 : ℚ) / ((2 : ℚ) ^ (k + 1) - 1)) = 0 := by
  have h_pos_nat : 0 < 2 ^ (k + 1) - 1 := by
    have h_le : 2 ≤ 2 ^ (k + 1) := by
      have h_le := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 1 ≤ k + 1 by omega)
      rw [pow_one] at h_le
      exact h_le
    omega
  have h_pos : ((2 : ℚ) ^ (k + 1) - 1) ≠ 0 := by
    have h_gt : 0 < (2 : ℚ) ^ (k + 1) - 1 := by
      have h_le : 1 ≤ 2 ^ (k + 1) := Nat.one_le_pow (k + 1) 2 (by decide)
      have : (2 : ℚ) ^ (k + 1) - 1 = ((2 ^ (k + 1) - 1 : ℕ) : ℚ) := by
        push_cast [Nat.cast_sub h_le]
        rfl
      rw [this]
      exact_mod_cast h_pos_nat
    exact ne_of_gt h_gt
  rw [padicValRat.div (by positivity) h_pos]
  rw [padicValRat.one]
  have h_val : padicValRat 2 ((2 : ℚ) ^ (k + 1) - 1) = 0 := by
    have h_le : 1 ≤ 2 ^ (k + 1) := Nat.one_le_pow (k + 1) 2 (by decide)
    have h_eq : (2 : ℚ) ^ (k + 1) - 1 = ((2 ^ (k + 1) - 1 : ℕ) : ℚ) := by
      push_cast [Nat.cast_sub h_le]
      rfl
    rw [h_eq]
    rw [padicValRat.of_nat]
    have h_odd : ¬ 2 ∣ 2 ^ (k + 1) - 1 := by
      intro hdvd
      have h_eq2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      generalize h_pow : 2 ^ k = X
      have hX : 1 ≤ X := by
        rw [← h_pow]
        exact Nat.one_le_pow k 2 (by decide)
      have h_mod : (2 ^ (k + 1) - 1) % 2 = 0 := Nat.mod_eq_zero_of_dvd hdvd
      rw [h_eq2] at h_mod
      omega
    rw [padicValNat.eq_zero_of_not_dvd h_odd]
    rfl
  rw [h_val]
  rfl

lemma padicValRat_two_sum_range_ge_zero (k : ℕ) :
  0 ≤ padicValRat 2 ((range k).sum (fun j => (1 : ℚ) / ((2 : ℚ) ^ (j + 1) - 1))) := by
  induction k with
  | zero =>
    rw [sum_range_zero, padicValRat.zero]
  | succ k ih =>
    rw [sum_range_succ]
    by_cases h_sum : (range k).sum (fun j => (1 : ℚ) / ((2 : ℚ) ^ (j + 1) - 1)) + (1 : ℚ) / ((2 : ℚ) ^ (k + 1) - 1) = 0
    · rw [h_sum, padicValRat.zero]
    · have h_add := padicValRat.min_le_padicValRat_add (p := 2) h_sum
      have hB : padicValRat 2 ((1 : ℚ) / ((2 : ℚ) ^ (k + 1) - 1)) = 0 := padicValRat_two_recip_pow_two_minus_one k
      have h_min : 0 ≤ min (padicValRat 2 ((range k).sum (fun j => (1 : ℚ) / ((2 : ℚ) ^ (j + 1) - 1)))) (padicValRat 2 ((1 : ℚ) / ((2 : ℚ) ^ (k + 1) - 1))) := by
        rw [hB]
        exact le_min ih (by omega)
      omega

lemma padicValRat_two_S_two_pow_ge_zero (k : ℕ) :
  0 ≤ padicValRat 2 ((2^k).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := by
  rw [S_two_pow_eq]
  exact padicValRat_two_sum_range_ge_zero (k + 1)

lemma n_split_of_odd_prime_dvd {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ n) (hn : 1 < n) :
  ∃ (k : ℕ) (m : ℕ), n = 2^k * m ∧ m % 2 = 1 ∧ 1 < m ∧ (2^k).Coprime m := by
  let k := padicValNat 2 n
  have hn_nz : n ≠ 0 := by omega
  have hdvd_2k : 2^k ∣ n := pow_padicValNat_dvd
  rcases hdvd_2k with ⟨m, hn_eq⟩
  have hm_nz : m ≠ 0 := by
    intro hm
    subst hm
    rw [mul_zero] at hn_eq
    omega
  have hm_odd : m % 2 = 1 := by
    by_contra! h_even
    have h_even_zero : m % 2 = 0 := by omega
    have hdvd_m : 2 ∣ m := Nat.dvd_of_mod_eq_zero h_even_zero
    rcases hdvd_m with ⟨d, rfl⟩
    have hdvd_n : 2^(k + 1) ∣ n := by
      rw [hn_eq]
      use d
      ring
    have h_not := pow_succ_padicValNat_not_dvd (p := 2) hn_nz
    exact h_not hdvd_n
  have hp_dvd_m : p ∣ m := by
    have hdvd_mul : p ∣ 2^k * m := by rwa [← hn_eq]
    have hp_prime : _root_.Prime p := Nat.Prime.prime hp
    rcases hp_prime.dvd_mul.mp hdvd_mul with hdvd_pow | hdvd_m
    · have hdvd_two : p ∣ 2 := hp_prime.dvd_of_dvd_pow hdvd_pow
      rcases Nat.prime_two.eq_one_or_self_of_dvd p hdvd_two with h_one | h_self
      · exfalso
        have : 2 ≤ p := hp.two_le
        omega
      · exfalso; exact hp2 h_self
    · exact hdvd_m
  have hm_gt_one : 1 < m := by
    rcases hp_dvd_m with ⟨d, rfl⟩
    have hp_pos : 2 ≤ p := hp.two_le
    have hd_pos : 1 ≤ d := by
      by_contra! hd_zero
      have : d = 0 := by omega
      subst this
      simp at hm_nz
    have : p * 1 ≤ p * d := by gcongr
    rw [mul_one] at this
    omega
  have h_coprime : Nat.Coprime (2^k) m := by
    have h_odd' : Odd m := Nat.odd_iff.mpr hm_odd
    have h_cop_two : Nat.Coprime 2 m := Nat.coprime_two_left.mpr h_odd'
    exact Nat.Coprime.pow_left k h_cop_two
  exact ⟨k, m, hn_eq, hm_odd, hm_gt_one, h_coprime⟩


lemma sum_geom_less_two_thirds (k : ℕ) : (range k).sum (fun j => (1 / 3 : ℚ) * (1 / 2) ^ j) < 2 / 3 := by
  rw [← mul_sum]
  rw [sum_half_pow_eq]
  have h_half_pos : 0 < (1 / 2 : ℚ) ^ k := by positivity
  linarith

lemma S_two_pow_lt_five_thirds (k : ℕ) :
  ((2^k).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) < 5 / 3 := by
  rw [S_two_pow_eq]
  rw [S_two_pow_split]
  have h_le : (range k).sum (fun j => (1 : ℚ) / ((2 : ℚ) ^ (j + 2) - 1)) ≤ (range k).sum (fun j => (1 / 3 : ℚ) * (1 / 2) ^ j) := by
    apply sum_le_sum
    intro j hj
    exact term_le_geom j
  have h_lt := sum_geom_less_two_thirds k
  linarith


lemma term_denom_ge_4 (j : ℕ) : 15 * (2 : ℚ) ^ j ≤ (2 : ℚ) ^ (j + 4) - 1 := by
  have h1 : (2 : ℚ) ^ (j + 4) = 16 * (2 : ℚ) ^ j := by ring
  rw [h1]
  have h2 : (2 : ℚ) ^ j ≥ 1 := by
    have h_pow := Nat.one_le_pow j 2 (by decide)
    exact_mod_cast h_pow
  linarith

lemma term_le_geom_4 (j : ℕ) : (1 : ℚ) / ((2 : ℚ) ^ (j + 4) - 1) ≤ (1 / 15) * (1 / 2) ^ j := by
  have h_denom : 15 * (2 : ℚ) ^ j ≤ (2 : ℚ) ^ (j + 4) - 1 := term_denom_ge_4 j
  have h_pos : 0 < 15 * (2 : ℚ) ^ j := by positivity
  have h_div : (1 : ℚ) / ((2 : ℚ) ^ (j + 4) - 1) ≤ (1 : ℚ) / (15 * (2 : ℚ) ^ j) := by
    apply div_le_div_of_nonneg_left (by norm_num) h_pos h_denom
  have h_eq : (1 : ℚ) / (15 * (2 : ℚ) ^ j) = (1 / 15) * (1 / 2) ^ j := by
    field_simp
    rw [← mul_pow]
    norm_num
  rwa [h_eq] at h_div

lemma S_two_pow_split_three (k : ℕ) (hk : 3 ≤ k) :
  (range (k + 1)).sum (fun j => (1 : ℚ) / ((2 : ℚ) ^ (j + 1) - 1)) =
  1 + 1 / 3 + 1 / 7 + (range (k - 2)).sum (fun j => (1 : ℚ) / ((2 : ℚ) ^ (j + 4) - 1)) := by
  rw [sum_range_succ']
  have h_eq1 : (range k).sum (fun j => (1 : ℚ) / ((2 : ℚ) ^ (j + 2) - 1)) =
    1 / 3 + (range (k - 1)).sum (fun j => (1 : ℚ) / ((2 : ℚ) ^ (j + 3) - 1)) := by
    have hk_pos : 0 < k := by omega
    have h_split : (range (k - 1 + 1)).sum (fun j => (1 : ℚ) / ((2 : ℚ) ^ (j + 2) - 1)) =
      (1 / 3 : ℚ) + (range (k - 1)).sum (fun j => (1 : ℚ) / ((2 : ℚ) ^ (j + 3) - 1)) := by
      rw [sum_range_succ']
      dsimp
      ring
    have h_sub : k - 1 + 1 = k := by omega
    rw [h_sub] at h_split
    exact h_split
  rw [h_eq1]
  have h_eq2 : (range (k - 1)).sum (fun j => (1 : ℚ) / ((2 : ℚ) ^ (j + 3) - 1)) =
    1 / 7 + (range (k - 2)).sum (fun j => (1 : ℚ) / ((2 : ℚ) ^ (j + 4) - 1)) := by
    have hk_pos2 : 0 < k - 1 := by omega
    have h_split : (range (k - 2 + 1)).sum (fun j => (1 : ℚ) / ((2 : ℚ) ^ (j + 3) - 1)) =
      (1 / 7 : ℚ) + (range (k - 2)).sum (fun j => (1 : ℚ) / ((2 : ℚ) ^ (j + 4) - 1)) := by
      rw [sum_range_succ']
      dsimp
      ring
    have h_sub2 : k - 2 + 1 = k - 1 := by omega
    rw [h_sub2] at h_split
    exact h_split
  rw [h_eq2]
  ring

lemma S_two_pow_lt_thirteen_eighths (k : ℕ) (hk : 3 ≤ k) :
  ((2^k).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) < 13 / 8 := by
  rw [S_two_pow_eq]
  rw [S_two_pow_split_three k hk]
  have h_le : (range (k - 2)).sum (fun j => (1 : ℚ) / ((2 : ℚ) ^ (j + 4) - 1)) ≤ (range (k - 2)).sum (fun j => (1 / 15 : ℚ) * (1 / 2) ^ j) := by
    apply sum_le_sum
    intro j hj
    exact term_le_geom_4 j
  have h_lt : (range (k - 2)).sum (fun j => (1 / 15 : ℚ) * (1 / 2) ^ j) < 2 / 15 := by
    rw [← mul_sum]
    rw [sum_half_pow_eq]
    have : 0 < (1 / 2 : ℚ) ^ (k - 2) := by positivity
    linarith
  linarith


lemma sigma_three_pow_ge (j : ℕ) :
  12 * 2^j ≤ sigma 1 (3 ^ (j + 2)) := by
  have hp : Nat.Prime 3 := by decide
  have h1 : sigma 1 (3 ^ (j + 2)) = ∑ i ∈ range (j + 3), 3 ^ i := sigma_one_apply_prime_pow hp
  rw [h1]
  rw [sum_range_succ, sum_range_succ]
  have h2 : 3^(j + 1) + 3^(j + 2) ≤ ∑ i ∈ range (j + 1), 3 ^ i + 3^(j + 1) + 3^(j + 2) := by omega
  have h3 : 12 * 2^j ≤ 3^(j + 1) + 3^(j + 2) := by
    have h_eq : 3^(j + 1) + 3^(j + 2) = 12 * 3^j := by ring
    rw [h_eq]
    have h4 : 2^j ≤ 3^j := by
      gcongr
      decide
    gcongr
  omega

lemma term_le_geom_p3 (j : ℕ) :
  (1 : ℚ) / (↑((sigma 1) (3^(j + 2))) : ℚ) ≤ (1 / 12) * (1 / 2) ^ j := by
  have h_denom : (12 : ℚ) * (2 : ℚ) ^ j ≤ (↑((sigma 1) (3^(j + 2))) : ℚ) := by
    have := sigma_three_pow_ge j
    exact_mod_cast this
  have h_pos : 0 < (12 : ℚ) * (2 : ℚ) ^ j := by positivity
  have h_div : (1 : ℚ) / (↑((sigma 1) (3^(j + 2))) : ℚ) ≤ (1 : ℚ) / ((12 : ℚ) * (2 : ℚ) ^ j) := by
    apply div_le_div_of_nonneg_left (by norm_num) h_pos h_denom
  have h_eq : (1 : ℚ) / ((12 : ℚ) * (2 : ℚ) ^ j) = (1 / 12) * (1 / 2) ^ j := by
    field_simp
    rw [← mul_pow]
    norm_num
  rwa [h_eq] at h_div

lemma S_three_pow_lt_three_halves (a : ℕ) :
  (range (a + 1)).sum (fun j => (1 : ℚ) / (↑((sigma 1) (3^j)) : ℚ)) < 3 / 2 := by
  by_cases ha0 : a = 0
  · subst ha0
    rw [sum_range_one]
    simp
    norm_num
  · have ha_ge : 1 ≤ a := by omega
    have ha_eq : a = a - 1 + 1 := by omega
    nth_rw 1 [ha_eq]
    rw [sum_range_succ']
    have h_sig0 : (↑((sigma 1) (3^0)) : ℚ) = 1 := by decide
    rw [h_sig0, div_one]
    have ha_eq_rev : a - 1 + 1 = a := by omega
    rw [ha_eq_rev]
    have h_split : (range a).sum (fun j => (1 : ℚ) / (↑((sigma 1) (3^(j + 1))) : ℚ)) =
      (1 : ℚ) / 4 + (range (a - 1)).sum (fun j => (1 : ℚ) / (↑((sigma 1) (3^(j + 2))) : ℚ)) := by
      have ha_eq2 : a = a - 1 + 1 := by omega
      nth_rw 1 [ha_eq2]
      rw [sum_range_succ']
      have h_sig3 : (sigma 1) 3 = 4 := by decide
      have h_sig3_q : (↑((sigma 1) (3^1)) : ℚ) = 4 := by exact_mod_cast h_sig3
      rw [h_sig3_q]
      rw [add_comm]
    rw [h_split]
    have h_le : (range (a - 1)).sum (fun j => (1 : ℚ) / (↑((sigma 1) (3^(j + 2))) : ℚ)) ≤
      (range (a - 1)).sum (fun j => (1 / 12 : ℚ) * (1 / 2) ^ j) := by
      apply sum_le_sum
      intro j hj
      exact term_le_geom_p3 j
    have h_lt : (range (a - 1)).sum (fun j => (1 / 12 : ℚ) * (1 / 2) ^ j) < 1 / 6 := by
      have h_geom : (range (a - 1)).sum (fun j => (1 / 12 : ℚ) * (1 / 2) ^ j) = 1/4 * (range (a - 1)).sum (fun j => (1 / 3 : ℚ) * (1 / 2) ^ j) := by
        rw [← mul_sum]
        rw [← mul_sum]
        ring
      rw [h_geom]
      have h_less := sum_geom_less_two_thirds (a - 1)
      linarith
    simp at h_le h_lt ⊢
    linarith

lemma S_two_mul_three_pow_lt_two (a : ℕ) :
  (((2 * 3^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) < 2 := by
  by_cases ha0 : a = 0
  · subst ha0
    have h_eq : 2 * 3^0 = 2^1 := by rfl
    rw [h_eq]
    rw [S_two_pow_eq]
    rw [sum_range_succ, sum_range_succ, sum_range_zero]
    norm_num
  · have ha_ge : 1 ≤ a := by omega
    have h_cop : Nat.Coprime 2 (3^a) := Nat.Coprime.pow_right a (by decide)
    have h_S_eq : (((2 * 3^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) =
      (divisors 2).sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) *
      ((3^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := by
      rw [← sum_f_eq_sum_recip (2 * 3^a) (by
        have h_pow := Nat.pow_le_pow_right (show 0 < 3 by decide) ha_ge
        have h_pow' : 3 ≤ 3^a := h_pow
        omega)]
      rw [← sum_f_eq_sum_recip 2 (by decide)]
      rw [← sum_f_eq_sum_recip (3^a) (by
        have h_pow := Nat.pow_le_pow_right (show 0 < 3 by decide) ha_ge
        have h_pow' : 3 ≤ 3^a := h_pow
        omega)]
      rw [← f_mul_zeta_apply (2 * 3^a)]
      rw [← f_mul_zeta_apply 2]
      rw [← f_mul_zeta_apply (3^a)]
      exact S_mul_of_coprime h_cop
    rw [h_S_eq]
    rw [show (divisors 2).sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = (divisors (2^1)).sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) by rfl]
    have h_S2 : ((2^1).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = 4 / 3 := by
      rw [S_two_pow_eq]
      rw [sum_range_succ, sum_range_succ, sum_range_zero]
      norm_num
    rw [h_S2]
    have h_S3 : ((3^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = (range (a + 1)).sum (fun j => (1 : ℚ) / (↑((sigma 1) (3^j)) : ℚ)) := by
      exact S_prime_power_eq (by decide) a
    rw [h_S3]
    have h_lt := S_three_pow_lt_three_halves a
    nlinarith

lemma padicValRat_two_S_two_pow_odd_helper (r : ℕ) :
  1 ≤ padicValRat 2 ((range (2 * r + 2)).sum (fun j => (1 : ℚ) / ((2 : ℚ) ^ (j + 1) - 1))) := by
  induction r with
  | zero =>
    have h_sum : (range 2).sum (fun j => (1 : ℚ) / ((2 : ℚ) ^ (j + 1) - 1)) = 4 / 3 := by
      rw [sum_range_succ, sum_range_succ, sum_range_zero]
      norm_num
    rw [h_sum]
    have h_div : (4 / 3 : ℚ) = ((4 : ℕ) : ℚ) / ((3 : ℕ) : ℚ) := by norm_num
    rw [h_div]
    rw [padicValRat.div (by positivity) (by positivity)]
    rw [padicValRat.of_nat, padicValRat.of_nat]
    have h_four : padicValNat 2 4 = 2 := by
      have : (4 : ℕ) = 2^2 := by rfl
      rw [this]
      exact @padicValNat.prime_pow 2 _ 2
    have h_three : padicValNat 2 3 = 0 := by
      apply padicValNat.eq_zero_of_not_dvd
      decide
    rw [h_four, h_three]
    omega
  | succ r ih =>
    have h_split : (range (2 * (r + 1) + 2)).sum (fun j => (1 : ℚ) / ((2 : ℚ) ^ (j + 1) - 1)) =
      (range (2 * r + 2)).sum (fun j => (1 : ℚ) / ((2 : ℚ) ^ (j + 1) - 1)) +
      (1 : ℚ) / ((2 : ℚ) ^ (2 * r + 2 + 1) - 1) +
      (1 : ℚ) / ((2 : ℚ) ^ (2 * r + 2 + 2) - 1) := by
      have h_eq : 2 * (r + 1) + 2 = 2 * r + 2 + 2 := by ring
      rw [h_eq]
      exact sum_range_split_two (fun j => (1 : ℚ) / ((2 : ℚ) ^ (j + 1) - 1)) (2 * r + 2)
    rw [h_split]
    -- regroup as x + (y1 + y2)
    rw [add_assoc]
    let x := (range (2 * r + 2)).sum (fun j => (1 : ℚ) / ((2 : ℚ) ^ (j + 1) - 1))
    let y1 := (1 : ℚ) / ((2 : ℚ) ^ (2 * r + 3) - 1)
    let y2 := (1 : ℚ) / ((2 : ℚ) ^ (2 * r + 4) - 1)
    have hy1 : y1 = (1 : ℚ) / (((2 ^ (2 * r + 3) - 1 : ℕ) : ℚ)) := by
      have h_le : 1 ≤ 2 ^ (2 * r + 3) := Nat.one_le_pow _ 2 (by decide)
      push_cast [Nat.cast_sub h_le]
      rfl
    have hy2 : y2 = (1 : ℚ) / (((2 ^ (2 * r + 4) - 1 : ℕ) : ℚ)) := by
      have h_le : 1 ≤ 2 ^ (2 * r + 4) := Nat.one_le_pow _ 2 (by decide)
      push_cast [Nat.cast_sub h_le]
      rfl
    have hy_sum : y1 + y2 = (1 : ℚ) / ((2 ^ (2 * r + 3) - 1 : ℕ) : ℚ) + (1 : ℚ) / ((2 ^ (2 * r + 4) - 1 : ℕ) : ℚ) := by
      rw [hy1, hy2]
    have h_val_y : 1 ≤ padicValRat 2 (y1 + y2) := by
      rw [hy_sum]
      have ha_le : 1 ≤ 2 ^ (2 * r + 3) := Nat.one_le_pow _ 2 (by decide)
      have hb_le : 1 ≤ 2 ^ (2 * r + 4) := Nat.one_le_pow _ 2 (by decide)
      have ha_odd : (2 ^ (2 * r + 3) - 1) % 2 = 1 := by
        have h_pow : 2 ^ (2 * r + 3) = 2 * 2 ^ (2 * r + 2) := by ring
        have h_even : 2 ∣ 2 ^ (2 * r + 3) := by
          rw [h_pow]
          exact dvd_mul_right 2 _
        have h_mod : 2 ^ (2 * r + 3) % 2 = 0 := Nat.mod_eq_zero_of_dvd h_even
        omega
      have hb_odd : (2 ^ (2 * r + 4) - 1) % 2 = 1 := by
        have h_pow : 2 ^ (2 * r + 4) = 2 * 2 ^ (2 * r + 3) := by ring
        have h_even : 2 ∣ 2 ^ (2 * r + 4) := by
          rw [h_pow]
          exact dvd_mul_right 2 _
        have h_mod : 2 ^ (2 * r + 4) % 2 = 0 := Nat.mod_eq_zero_of_dvd h_even
        omega
      have ha0 : 2 ^ (2 * r + 3) - 1 ≠ 0 := by omega
      have hb0 : 2 ^ (2 * r + 4) - 1 ≠ 0 := by omega
      exact padicValRat_two_recip_add_recip_even _ _ ha_odd hb_odd ha0 hb0

    -- now apply padicValRat.min_le_padicValRat_add
    have hx_pos : 0 < x := by
      apply Finset.sum_pos
      · intro j hj
        have h_pos_nat : 0 < 2 ^ (j + 1) - 1 := by
          have h_le : 2 ≤ 2 ^ (j + 1) := by
            have h_le := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 1 ≤ j + 1 by omega)
            rw [pow_one] at h_le
            exact h_le
          omega
        have h_le : 1 ≤ 2 ^ (j + 1) := Nat.one_le_pow (j + 1) 2 (by decide)
        have : (2 : ℚ) ^ (j + 1) - 1 = ((2 ^ (j + 1) - 1 : ℕ) : ℚ) := by
          push_cast [Nat.cast_sub h_le]
          rfl
        rw [this]
        exact div_pos (by norm_num) (by exact_mod_cast h_pos_nat)
      · rw [nonempty_range_iff]
        omega
    have hy1_pos : 0 < y1 := by
      rw [hy1]
      have h_pos_nat : 0 < 2 ^ (2 * r + 3) - 1 := by
        have : 2 ≤ 2 ^ (2 * r + 3) := by
          have : 1 ≤ 2 * r + 3 := by omega
          have h_pow := Nat.pow_le_pow_right (show 0 < 2 by decide) this
          rw [pow_one] at h_pow
          exact h_pow
        omega
      exact div_pos (by norm_num) (by exact_mod_cast h_pos_nat)
    have hy2_pos : 0 < y2 := by
      rw [hy2]
      have h_pos_nat : 0 < 2 ^ (2 * r + 4) - 1 := by
        have : 2 ≤ 2 ^ (2 * r + 4) := by
          have : 1 ≤ 2 * r + 4 := by omega
          have h_pow := Nat.pow_le_pow_right (show 0 < 2 by decide) this
          rw [pow_one] at h_pow
          exact h_pow
        omega
      exact div_pos (by norm_num) (by exact_mod_cast h_pos_nat)
    have hsum_ne : x + (y1 + y2) ≠ 0 := by
      have : 0 < x + (y1 + y2) := add_pos hx_pos (add_pos hy1_pos hy2_pos)
      exact ne_of_gt this
    have h_add := padicValRat.min_le_padicValRat_add (p := 2) hsum_ne
    have h_min : 1 ≤ min (padicValRat 2 x) (padicValRat 2 (y1 + y2)) := le_min ih h_val_y
    exact le_trans h_min h_add

lemma padicValRat_two_S_two_pow_odd (k : ℕ) (hk : k % 2 = 1) :
  1 ≤ padicValRat 2 ((2^k).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := by
  rw [S_two_pow_eq]
  have h_eq : k + 1 = 2 * (k / 2) + 2 := by omega
  rw [h_eq]
  exact padicValRat_two_S_two_pow_odd_helper (k / 2)

lemma S_gt_one (n : ℕ) (hn : 1 < n) :
  1 < (n.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := by
  have h_subset : {1, n} ⊆ n.divisors := by
    intro x hx
    rw [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · rw [mem_divisors]
      exact ⟨one_dvd n, by omega⟩
    · rw [mem_divisors]
      exact ⟨dvd_rfl, by omega⟩
  have h_sum_le : ({1, n} : Finset ℕ).sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≤ (n.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg h_subset
    intro x hx h_not
    have h_sig : 0 < sigma 1 x := by
      have h_nz : x ≠ 0 := by
        intro h_zero
        subst h_zero
        have := Nat.dvd_of_mem_divisors hx
        omega
      exact sigma_pos 1 x (by positivity)
    have h_sig_q : 0 < (↑((sigma 1) x) : ℚ) := Nat.cast_pos.mpr h_sig
    exact le_of_lt (div_pos zero_lt_one h_sig_q)
  have h_pair : ({1, n} : Finset ℕ).sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) =
    (1 : ℚ) / (↑((sigma 1) 1) : ℚ) + (1 : ℚ) / (↑((sigma 1) n) : ℚ) := by
    have h_ne : 1 ≠ n := by omega
    rw [sum_insert (by simp [h_ne]), sum_singleton]
  rw [h_pair] at h_sum_le
  have h_sig1 : (sigma 1) 1 = 1 := by rfl
  have h_one_term : (1 : ℚ) / (↑((sigma 1) 1) : ℚ) = 1 := by
    push_cast [h_sig1]
    norm_num
  rw [h_one_term] at h_sum_le
  have h_term_pos : 0 < (1 : ℚ) / (↑((sigma 1) n) : ℚ) := by
    have h_sig : 0 < sigma 1 n := sigma_pos 1 n (by omega)
    have h_sig_q : 0 < (↑((sigma 1) n) : ℚ) := Nat.cast_pos.mpr h_sig
    exact div_pos zero_lt_one h_sig_q
  linarith

lemma not_int_of_between_one_three_and_v2_le_zero {q : ℚ} (h1 : 1 < q) (h2 : q < 3) (hv : padicValRat 2 q ≤ 0) : q.den ≠ 1 := by
  intro h_den
  have h_eq : q = (q.num : ℚ) := by
    rw [← Rat.num_div_den q, h_den]
    simp
  rw [h_eq] at h1 h2 hv
  have h1' : 1 < q.num := by exact_mod_cast h1
  have h2' : q.num < 3 := by exact_mod_cast h2
  have h_num : q.num = 2 := by omega
  have h_eq2 : (q.num : ℚ) = ((2 : ℕ) : ℚ) := by
    rw [h_num]
    rfl
  rw [h_eq2] at hv
  rw [padicValRat.of_nat] at hv
  have h_val_nat : padicValNat 2 2 = 1 := padicValNat.self (by decide)
  rw [h_val_nat] at hv
  norm_num at hv


lemma not_int_of_between_two_three_and_v2_ne_one {q : ℚ} (h1 : 2 ≤ q) (h2 : q < 3) (hv : padicValRat 2 q ≠ 1) : q.den ≠ 1 := by
  intro h_den
  have h_eq : q = (q.num : ℚ) := by
    rw [← Rat.num_div_den q, h_den]
    simp
  rw [h_eq] at h1 h2 hv
  have h1' : 2 ≤ q.num := by exact_mod_cast h1
  have h2' : q.num < 3 := by exact_mod_cast h2
  have h_num : q.num = 2 := by omega
  have h_eq2 : (q.num : ℚ) = ((2 : ℕ) : ℚ) := by
    rw [h_num]
    rfl
  rw [h_eq2] at hv
  rw [padicValRat.of_nat] at hv
  have h_val_nat : padicValNat 2 2 = 1 := padicValNat.self (by decide)
  rw [h_val_nat] at hv
  exact hv rfl


lemma not_int_of_between_two_four_and_v2_ne_one_ne_zero {q : ℚ} (h1 : 2 ≤ q) (h2 : q < 4) (hv1 : padicValRat 2 q ≠ 1) (hv0 : padicValRat 2 q ≠ 0) : q.den ≠ 1 := by
  intro h_den
  have h_eq : q = (q.num : ℚ) := by
    rw [← Rat.num_div_den q, h_den]
    simp
  rw [h_eq] at h1 h2 hv1 hv0
  have h1' : 2 ≤ q.num := by exact_mod_cast h1
  have h2' : q.num < 4 := by exact_mod_cast h2
  interval_cases q.num
  · have h_val : padicValRat 2 ((2 : ℤ) : ℚ) = 1 := by
      change padicValRat 2 ((2 : ℕ) : ℚ) = 1
      rw [padicValRat.of_nat]
      have : padicValNat 2 2 = 1 := padicValNat.self (by decide)
      rw [this]
      rfl
    rw [h_val] at hv1
    exact hv1 rfl
  · have h_val : padicValRat 2 ((3 : ℤ) : ℚ) = 0 := by
      change padicValRat 2 ((3 : ℕ) : ℚ) = 0
      rw [padicValRat.of_nat]
      have : padicValNat 2 3 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
      rw [this]
      rfl
    rw [h_val] at hv0
    exact hv0 rfl



lemma not_int_of_between_two_six {q : ℚ} (h1 : 2 ≤ q) (h2 : q < 6)
  (hv0 : padicValRat 2 q ≠ 0) (hv1 : padicValRat 2 q ≠ 1) (hv2 : padicValRat 2 q ≠ 2) : q.den ≠ 1 := by
  intro h_den
  have h_eq : q = (q.num : ℚ) := by
    have h_nd := Rat.num_div_den q
    rw [h_den] at h_nd
    simp at h_nd
    exact h_nd.symm
  rw [h_eq] at h1 h2 hv0 hv1 hv2
  have h1' : 2 ≤ q.num := by exact_mod_cast h1
  have h2' : q.num < 6 := by exact_mod_cast h2
  have h_pos_num : 0 ≤ q.num := by omega
  have h_eq3 : q.num = (q.num.natAbs : ℤ) := (Int.natAbs_of_nonneg h_pos_num).symm
  rw [h_eq3] at hv0 hv1 hv2 h1' h2'
  have h_val : padicValRat 2 ((q.num.natAbs : ℤ) : ℚ) = padicValNat 2 q.num.natAbs := by
    change padicValRat 2 ((q.num.natAbs : ℕ) : ℚ) = padicValNat 2 q.num.natAbs
    rw [padicValRat.of_nat]
  rw [h_val] at hv0 hv1 hv2
  have h1'' : 2 ≤ q.num.natAbs := by exact_mod_cast h1'
  have h2'' : q.num.natAbs < 6 := by exact_mod_cast h2'
  interval_cases q.num.natAbs
  · have : padicValNat 2 2 = 1 := padicValNat.self (by decide)
    omega
  · have : padicValNat 2 3 = 0 := by apply padicValNat.eq_zero_of_not_dvd; decide
    omega
  · have : padicValNat 2 4 = 2 := by
      have : (4 : ℕ) = 2^2 := by rfl
      rw [this]
      exact @padicValNat.prime_pow 2 _ 2
    omega
  · have : padicValNat 2 5 = 0 := by apply padicValNat.eq_zero_of_not_dvd; decide
    omega



lemma not_int_of_between_two_three {q : ℚ} (h1 : 2 < q) (h2 : q < 3) : q.den ≠ 1 := by
  intro h_den
  have h_eq : q = (q.num : ℚ) := by
    rw [← Rat.num_div_den q, h_den]
    simp
  rw [h_eq] at h1 h2
  have h1' : 2 < q.num := by exact_mod_cast h1
  have h2' : q.num < 3 := by exact_mod_cast h2
  omega

lemma h_val_8 : padicValRat 2 ((2^3 : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = 1 := by
  have h_S2k_eq : ((2^3 : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = 54 / 35 := by
    change ((8 : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = 54 / 35
    have h_divs : (8 : ℕ).divisors = {1, 2, 4, 8} := by decide
    rw [h_divs]
    -- divs insert-singleton sum
    rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton]
    have h_sig1 : (sigma 1) 1 = 1 := rfl
    have h_sig2 : (sigma 1) 2 = 3 := rfl
    have h_sig4 : (sigma 1) 4 = 7 := rfl
    have h_sig8 : (sigma 1) 8 = 15 := rfl
    rw [h_sig1, h_sig2, h_sig4, h_sig8]
    norm_num
  rw [h_S2k_eq]
  have h_div : (54 / 35 : ℚ) = ((54 : ℕ) : ℚ) / ((35 : ℕ) : ℚ) := by norm_num
  rw [h_div, padicValRat.div (by positivity) (by positivity)]
  rw [padicValRat.of_nat, padicValRat.of_nat]
  have h_54 : padicValNat 2 54 = 1 := by
    have : (54 : ℕ) = 2 * 27 := by decide
    rw [this]
    have : padicValNat 2 (2 * 27) = padicValNat 2 2 + padicValNat 2 27 := padicValNat.mul (by decide) (by decide)
    rw [this]
    have h_2 : padicValNat 2 2 = 1 := padicValNat.self (by decide)
    have h_27 : padicValNat 2 27 = 0 := by
      apply padicValNat.eq_zero_of_not_dvd
      decide
    rw [h_2, h_27]
  have h_35 : padicValNat 2 35 = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    decide
  rw [h_54, h_35]
  rfl

lemma S_thirty_two_eq : ((2^5 : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = 15536 / 9765 := by
  change ((32 : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = 15536 / 9765
  have h_divs : (32 : ℕ).divisors = {1, 2, 4, 8, 16, 32} := by decide
  rw [h_divs]
  have h_not1 : 1 ∉ ({2, 4, 8, 16, 32} : Finset ℕ) := by decide
  rw [Finset.sum_insert h_not1]
  have h_not2 : 2 ∉ ({4, 8, 16, 32} : Finset ℕ) := by decide
  rw [Finset.sum_insert h_not2]
  have h_not4 : 4 ∉ ({8, 16, 32} : Finset ℕ) := by decide
  rw [Finset.sum_insert h_not4]
  have h_not8 : 8 ∉ ({16, 32} : Finset ℕ) := by decide
  rw [Finset.sum_insert h_not8]
  have h_not16 : 16 ∉ ({32} : Finset ℕ) := by decide
  rw [Finset.sum_insert h_not16, Finset.sum_singleton]
  have h1 : (sigma 1) 1 = 1 := rfl
  have h2 : (sigma 1) 2 = 3 := rfl
  have h4 : (sigma 1) 4 = 7 := rfl
  have h8 : (sigma 1) 8 = 15 := rfl
  have h16 : (sigma 1) 16 = 31 := rfl
  have h32 : (sigma 1) 32 = 63 := rfl
  rw [h1, h2, h4, h8, h16, h32]
  norm_num

lemma S_thirty_two_val : padicValRat 2 ((2^5 : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = 4 := by
  rw [S_thirty_two_eq]
  have h_div : (15536 / 9765 : ℚ) = ((15536 : ℕ) : ℚ) / ((9765 : ℕ) : ℚ) := by norm_num
  rw [h_div]
  rw [padicValRat.div (by positivity) (by positivity)]
  rw [padicValRat.of_nat, padicValRat.of_nat]
  have h_num : padicValNat 2 15536 = 4 := by
    have : (15536 : ℕ) = 2^4 * 971 := by decide
    rw [this]
    rw [padicValNat.mul (by decide) (by decide)]
    have h_pow : padicValNat 2 (2^4) = 4 := by
      exact @padicValNat.prime_pow 2 _ 4
    have h_odd : padicValNat 2 971 = 0 := by
      apply padicValNat.eq_zero_of_not_dvd
      decide
    rw [h_pow, h_odd]
  have h_den : padicValNat 2 9765 = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    decide
  rw [h_num, h_den]
  rfl

lemma S_one_twenty_eight_eq : ((2^7 : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = 33790906 / 21082635 := by
  change ((128 : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = 33790906 / 21082635
  have h_divs : (128 : ℕ).divisors = {1, 2, 4, 8, 16, 32, 64, 128} := by decide
  rw [h_divs]
  have h_not1 : 1 ∉ ({2, 4, 8, 16, 32, 64, 128} : Finset ℕ) := by decide
  rw [Finset.sum_insert h_not1]
  have h_not2 : 2 ∉ ({4, 8, 16, 32, 64, 128} : Finset ℕ) := by decide
  rw [Finset.sum_insert h_not2]
  have h_not4 : 4 ∉ ({8, 16, 32, 64, 128} : Finset ℕ) := by decide
  rw [Finset.sum_insert h_not4]
  have h_not8 : 8 ∉ ({16, 32, 64, 128} : Finset ℕ) := by decide
  rw [Finset.sum_insert h_not8]
  have h_not16 : 16 ∉ ({32, 64, 128} : Finset ℕ) := by decide
  rw [Finset.sum_insert h_not16]
  have h_not32 : 32 ∉ ({64, 128} : Finset ℕ) := by decide
  rw [Finset.sum_insert h_not32]
  have h_not64 : 64 ∉ ({128} : Finset ℕ) := by decide
  rw [Finset.sum_insert h_not64, Finset.sum_singleton]
  have h1 : (sigma 1) 1 = 1 := rfl
  have h2 : (sigma 1) 2 = 3 := rfl
  have h4 : (sigma 1) 4 = 7 := rfl
  have h8 : (sigma 1) 8 = 15 := rfl
  have h16 : (sigma 1) 16 = 31 := rfl
  have h32 : (sigma 1) 32 = 63 := rfl
  have h64 : (sigma 1) 64 = 127 := rfl
  have h128 : (sigma 1) 128 = 255 := rfl
  rw [h1, h2, h4, h8, h16, h32, h64, h128]
  norm_num

theorem oeis_265709_conjecture_0.disproof :
  ¬ ∃ (n : ℕ), 1 < n ∧
  ((n.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)).den = 1) := by
  rintro ⟨n, hn, h_den⟩
  have h_or := pow_two_or_odd_prime_dvd n hn
  rcases h_or with ⟨k, rfl⟩ | ⟨p, hp, hdvd, hp2⟩
  · have hk : 1 ≤ k := by
      by_contra! h_lt
      interval_cases k
      · norm_num at hn
    exact S_two_pow_not_int k hk h_den
  · by_cases h_pow : ∃ a, n = p^a
    · rcases h_pow with ⟨a, rfl⟩
      have ha : 1 ≤ a := by
        by_contra! h_lt
        interval_cases a
        · norm_num at hn
      exact S_prime_power_not_int p hp hp2 a ha h_den
    · by_cases hn_odd : n % 2 = 1
      · have hval := padicValRat_two_S_odd_neg n hn hn_odd
        exact not_integer_of_padicVal_neg Nat.prime_two hval h_den
      · have hn_even : n % 2 = 0 := by omega
        obtain ⟨k, m, hn_eq, hm_odd, hm_gt_one, h_coprime⟩ := n_split_of_odd_prime_dvd hp hp2 hdvd hn
        have hk : k ≠ 0 := by
          intro hk0
          subst hk0
          rw [pow_zero, one_mul] at hn_eq
          rw [hn_eq] at hn_even
          omega
        by_cases hk_even : k % 2 = 0
        · have h_2k_gt : 1 < 2^k := by
            have hk_pos : 1 ≤ k := Nat.pos_of_ne_zero hk
            have : 2^1 ≤ 2^k := Nat.pow_le_pow_right (by decide) hk_pos
            omega
          have h_S_eq : (((2^k * m).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) =
            ((2^k).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) *
            (m.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := by
            rw [← sum_f_eq_sum_recip (2^k * m) (by rwa [← hn_eq])]
            rw [← sum_f_eq_sum_recip (2^k) h_2k_gt]
            rw [← sum_f_eq_sum_recip m hm_gt_one]
            rw [← f_mul_zeta_apply (2^k * m)]
            rw [← f_mul_zeta_apply (2^k)]
            rw [← f_mul_zeta_apply m]
            exact S_mul_of_coprime h_coprime
          have h_val_n : padicValRat 2 ((2^k * m).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) < 0 := by
            rw [h_S_eq]
            rw [padicValRat.mul]
            · have h_val_2k : padicValRat 2 ((2^k).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = 0 :=
                padicValRat_two_S_two_pow_even k hk_even
              have h_val_m := padicValRat_two_S_odd_neg m hm_gt_one hm_odd
              omega
            · have hk_pos : 1 ≤ k := Nat.pos_of_ne_zero hk
              have h_S_2k_gt := S_two_pow_gt_one k hk_pos
              rw [← S_two_pow_eq] at h_S_2k_gt
              exact ne_of_gt (by linarith)
            · have hm_pos : 1 ≤ m := by omega
              have h_pos_m := S_pos m hm_pos
              exact ne_of_gt h_pos_m
          rw [hn_eq] at h_den
          exact not_integer_of_padicVal_neg Nat.prime_two h_val_n h_den
        · have hk_odd : k % 2 = 1 := by omega
          by_cases hk1 : k = 1
          · subst hk1
            by_cases hm_3 : ∃ a, m = 3^a
            · rcases hm_3 with ⟨a, rfl⟩
              have h_n_eq : n = 2 * 3^a := by
                rw [hn_eq]
                ring
              have h_lt : ((2 * 3^a : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) < 2 := S_two_mul_three_pow_lt_two a
              have h_gt : 1 < ((2 * 3^a : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := by
                apply S_gt_one
                have : 1 ≤ 3^a := Nat.one_le_pow a 3 (by decide)
                omega
              have h_not_int : ((2 * 3^a : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)).den ≠ 1 :=
                den_neq_one_of_between h_gt h_lt
              rw [← h_n_eq] at h_not_int
              exact h_not_int h_den
            by_cases hm_pow : ∃ (p : ℕ) (hp : p.Prime) (a : ℕ), m = p^a
            · rcases hm_pow with ⟨p, hp, a, rfl⟩
              have hp2 : p ≠ 2 := by
                intro hp2
                subst hp2
                have hm_even : (2^a) % 2 = 0 := by
                  have ha : 1 ≤ a := by
                    by_contra! ha0
                    interval_cases a
                    norm_num at hm_gt_one
                  have : 2 ∣ 2^a := dvd_pow_self 2 (by omega)
                  exact Nat.mod_eq_zero_of_dvd this
                omega
              have hp3 : p ≠ 3 := by
                intro hp3
                subst hp3
                exact hm_3 ⟨a, rfl⟩
              have hp5 : 5 ≤ p := by
                by_contra! h_lt
                have hp_ge2 : p ≥ 2 := hp.two_le
                interval_cases p
                · exact hp2 rfl
                · exact hp3 rfl
                · have : ¬ Nat.Prime 4 := by decide
                  exact this hp
              have hp_odd : p % 2 = 1 := by
                by_contra! h_even
                have hp_even : p % 2 = 0 := by omega
                have h_div : 2 ∣ p := Nat.dvd_of_mod_eq_zero hp_even
                have hp_eq_2_symm : 2 = p := hp.eq_one_or_self_of_dvd 2 h_div |>.resolve_left (by decide)
                have hp_eq_2 : p = 2 := hp_eq_2_symm.symm
                exact hp2 hp_eq_2
              have h_n_eq : n = 2 * p^a := by
                rw [hn_eq]
                ring
              have h_2_pa_gt : 1 < 2 * p^a := by
                have : 1 ≤ p^a := Nat.one_le_pow a p hp.pos
                omega
              have h_cop : Nat.Coprime 2 (p^a) := by
                have : Fact p.Prime := ⟨hp⟩
                have hp_odd' : Odd p := Nat.odd_iff.mpr hp_odd
                have h_cop_2 : Nat.Coprime 2 p := Nat.coprime_two_left.mpr hp_odd'
                exact h_cop_2.pow_right a
              have h_S_eq_2 : (((2 * p^a : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) =
                ((2 : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) *
                ((p^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := by
                rw [← sum_f_eq_sum_recip (2 * p^a) h_2_pa_gt]
                rw [← sum_f_eq_sum_recip 2 (by decide)]
                have h_pa_gt : 1 < p^a := by
                  have : p^1 ≤ p^a := Nat.pow_le_pow_right hp.pos (by
                    by_contra! ha0
                    interval_cases a
                    norm_num at hm_gt_one)
                  rw [pow_one] at this
                  omega
                rw [← sum_f_eq_sum_recip (p^a) h_pa_gt]
                rw [← f_mul_zeta_apply (2 * p^a)]
                rw [← f_mul_zeta_apply 2]
                rw [← f_mul_zeta_apply (p^a)]
                exact S_mul_of_coprime h_cop
              have h_S2 : ((2 : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = 4 / 3 := by
                have h_divs : (2 : ℕ).divisors = {1, 2} := by decide
                rw [h_divs, sum_insert (by decide), sum_singleton]
                have h_sig1 : (sigma 1) 1 = 1 := rfl
                have h_sig2 : (sigma 1) 2 = 3 := rfl
                rw [h_sig1, h_sig2]
                norm_num
              have h_Spa : ((p^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) < 3 / 2 := by
                rw [S_prime_power_eq hp]
                exact S_prime_power_lt_one_and_half hp hp5 a
              have h_lt : ((2 * p^a : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) < 2 := by
                rw [h_S_eq_2, h_S2]
                have h_Spa_pos : 0 < ((p^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := by
                  rw [S_prime_power_eq hp]
                  exact S_prime_power_pos hp a
                nlinarith
              have h_gt : 1 < ((2 * p^a : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := S_gt_one (2 * p^a) h_2_pa_gt
              have h_not_int : ((2 * p^a : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)).den ≠ 1 :=
                den_neq_one_of_between h_gt h_lt
              rw [← h_n_eq] at h_not_int
              exact h_not_int h_den
            · have h_ne : m ≠ 1 := by omega
              have ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd h_ne
              let a := padicValNat p m
              have hp_fact : Fact p.Prime := ⟨hp⟩
              have ha : 1 ≤ a := one_le_padicValNat_of_dvd (by omega) hdvd
              have hm_nz : m ≠ 0 := by omega
              let m' := m / p^a
              have hdvd_pa : p^a ∣ m := pow_padicValNat_dvd
              have hm_eq' : m = p^a * m' := (Nat.mul_div_cancel' hdvd_pa).symm
              have h_coprime_pm' : Nat.Coprime (p^a) m' := by
                have h_cop_pm' : Nat.Coprime p m' := by
                  rw [hp.coprime_iff_not_dvd]
                  intro hp_dvd_m'
                  rcases hp_dvd_m' with ⟨w, hw⟩
                  have h_div : p^(a + 1) ∣ m := by
                    rw [hm_eq', hw]
                    use w
                    ring
                  have h_not := pow_succ_padicValNat_not_dvd (p := p) hm_nz
                  exact h_not h_div
                exact h_cop_pm'.pow_left a
              have hm'_gt_one : 1 < m' := by
                by_contra! h_le
                interval_cases m'
                · rw [mul_zero] at hm_eq'
                  omega
                · rw [mul_one] at hm_eq'
                  have : m = p^a := hm_eq'
                  exact hm_pow ⟨p, hp, a, this⟩
              have h_pa_gt_one : 1 < p^a := by
                have hp_pos : 2 ≤ p := hp.two_le
                have : p^1 ≤ p^a := Nat.pow_le_pow_right (by omega) ha
                rw [pow_one] at this
                omega
              have h_pa_odd : (p^a) % 2 = 1 := by
                have : (p^a * m') % 2 = 1 := by rwa [← hm_eq']
                rw [Nat.mul_mod] at this
                by_contra! h_even
                have h_zero : p^a % 2 = 0 := by omega
                rw [h_zero, zero_mul, Nat.zero_mod] at this
                omega
              have hm'_odd : m' % 2 = 1 := by
                have : (p^a * m') % 2 = 1 := by rwa [← hm_eq']
                rw [Nat.mul_mod] at this
                by_contra! h_even
                have h_zero : m' % 2 = 0 := by omega
                rw [h_zero, mul_zero, Nat.zero_mod] at this
                omega
              have h_S_m_eq : ((m.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) =
                ((p^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) *
                (m'.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ) ) := by
                rw [← sum_f_eq_sum_recip m hm_gt_one]
                rw [← sum_f_eq_sum_recip (p^a) h_pa_gt_one]
                rw [← sum_f_eq_sum_recip m' hm'_gt_one]
                rw [← f_mul_zeta_apply m]
                rw [← f_mul_zeta_apply (p^a)]
                rw [← f_mul_zeta_apply m']
                rw [hm_eq']
                exact S_mul_of_coprime h_coprime_pm'
              have hval_m : padicValRat 2 ((m.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) ≤ -2 := by
                rw [h_S_m_eq]
                rw [padicValRat.mul]
                · have hval_pa := padicValRat_two_S_odd_neg (p^a) h_pa_gt_one h_pa_odd
                  have hval_m' := padicValRat_two_S_odd_neg m' hm'_gt_one hm'_odd
                  omega
                · have : 0 < (p^a).divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := S_pos (p^a) (by omega)
                  exact ne_of_gt this
                · have : 0 < m'.divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := S_pos m' (by omega)
                  exact ne_of_gt this
              have h_n_eq : n = 2 * m := by
                rw [hn_eq]
                ring
              have h_2_m_gt : 1 < 2 * m := by omega
              have h_S_eq_2 : (((2 * m : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) =
                ((2 : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) *
                (m.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := by
                rw [← sum_f_eq_sum_recip (2 * m) h_2_m_gt]
                rw [← sum_f_eq_sum_recip 2 (by decide)]
                rw [← sum_f_eq_sum_recip m hm_gt_one]
                rw [← f_mul_zeta_apply (2 * m)]
                rw [← f_mul_zeta_apply 2]
                rw [← f_mul_zeta_apply m]
                exact S_mul_of_coprime h_coprime
              have h_S2 : ((2 : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = 4 / 3 := by
                have h_divs : (2 : ℕ).divisors = {1, 2} := by decide
                rw [h_divs, sum_insert (by decide), sum_singleton]
                have h_sig1 : (sigma 1) 1 = 1 := rfl
                have h_sig2 : (sigma 1) 2 = 3 := rfl
                rw [h_sig1, h_sig2]
                norm_num
              have h_S2_nz : ((2 : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≠ 0 := by
                rw [h_S2]
                norm_num
              have h_Sm_nz : m.divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≠ 0 := by
                have : 0 < m.divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := S_pos m (by omega)
                exact ne_of_gt this
              have hval_2_m : padicValRat 2 (((2 * m : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) ≤ 0 := by
                rw [h_S_eq_2]
                rw [padicValRat.mul h_S2_nz h_Sm_nz]
                rw [h_S2]
                have h_val_4_3 : padicValRat 2 (4 / 3 : ℚ) = 2 := by
                  have h_div : (4 / 3 : ℚ) = ((4 : ℕ) : ℚ) / ((3 : ℕ) : ℚ) := by norm_num
                  rw [h_div]
                  rw [padicValRat.div (by positivity) (by positivity)]
                  rw [padicValRat.of_nat, padicValRat.of_nat]
                  have h_four : padicValNat 2 4 = 2 := by
                    have : (4 : ℕ) = 2^2 := by rfl
                    rw [this]
                    exact @padicValNat.prime_pow 2 _ 2
                  have h_three : padicValNat 2 3 = 0 := by
                    apply padicValNat.eq_zero_of_not_dvd
                    decide
                  rw [h_four, h_three]
                  omega
                omega
              by_cases hval_neg : padicValRat 2 (((2 * m : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) < 0
              · have h_not_int : ((2 * m : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)).den ≠ 1 :=
                  not_integer_of_padicVal_neg Nat.prime_two hval_neg
                rw [← h_n_eq] at h_not_int
                exact h_not_int h_den
              · have h_Spa_lt : ((p^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) < 3 / 2 := by
                  by_cases hp3 : p = 3
                  · subst hp3
                    have hp3_prime : Nat.Prime 3 := by decide
                    rw [S_prime_power_eq hp3_prime]
                    exact S_three_pow_lt_three_halves a
                  · have hp5 : 5 ≤ p := by
                      by_contra! h_lt
                      have hp_ge2 : p ≥ 2 := hp.two_le
                      have hp2 : p ≠ 2 := by
                        intro hp2
                        subst hp2
                        have h_div : 2 ∣ m := by
                          have : 2^a ∣ m := pow_padicValNat_dvd
                          have ha_nz : a ≠ 0 := by omega
                          exact dvd_trans (dvd_pow_self 2 ha_nz) this
                        have : m % 2 = 0 := Nat.mod_eq_zero_of_dvd h_div
                        omega
                      interval_cases p
                      · exact hp2 rfl
                      · exact hp3 rfl
                      · have : ¬ Nat.Prime 4 := by decide
                        exact this hp
                    rw [S_prime_power_eq hp]
                    exact S_prime_power_lt_one_and_half hp hp5 a
                have hm'_pow : ∃ (q : ℕ) (hq : q.Prime) (b : ℕ), m' = q^b := by
                  by_contra! h_not_pow
                  have hm'_ne : m' ≠ 1 := by omega
                  have ⟨q, hq, hdvd_q⟩ := Nat.exists_prime_and_dvd hm'_ne
                  let b := padicValNat q m'
                  have hq_fact : Fact q.Prime := ⟨hq⟩
                  have hb : 1 ≤ b := one_le_padicValNat_of_dvd (by omega) hdvd_q
                  have hm'_nz : m' ≠ 0 := by omega
                  have hdvd_qb : q^b ∣ m' := pow_padicValNat_dvd
                  rcases hdvd_qb with ⟨m'', hm'_eq⟩
                  have h_coprime_qm'' : Nat.Coprime (q^b) m'' := by
                    have h_cop_qm'' : Nat.Coprime q m'' := by
                      rw [hq.coprime_iff_not_dvd]
                      intro hq_dvd_m''
                      rcases hq_dvd_m'' with ⟨w, hw⟩
                      have h_div : q^(b + 1) ∣ m' := by
                        rw [hm'_eq, hw]
                        use w
                        ring
                      have h_not := pow_succ_padicValNat_not_dvd (p := q) hm'_nz
                      exact h_not h_div
                    exact h_cop_qm''.pow_left b
                  have hm''_gt_one : 1 < m'' := by
                    by_contra! h_le
                    have h_or : m'' = 0 ∨ m'' = 1 := by omega
                    rcases h_or with rfl | rfl
                    · rw [mul_zero] at hm'_eq
                      omega
                    · rw [mul_one] at hm'_eq
                      have : m' = q^b := hm'_eq
                      exact h_not_pow q hq b this
                  have h_qb_gt_one : 1 < q^b := by
                    have hq_pos : 2 ≤ q := hq.two_le
                    have : q^1 ≤ q^b := Nat.pow_le_pow_right (by omega) hb
                    rw [pow_one] at this
                    omega
                  have h_qb_odd : (q^b) % 2 = 1 := by
                    have : (q^b * m'') % 2 = 1 := by rwa [← hm'_eq]
                    rw [Nat.mul_mod] at this
                    by_contra! h_even
                    have h_zero : q^b % 2 = 0 := by omega
                    rw [h_zero, zero_mul, Nat.zero_mod] at this
                    omega
                  have hm''_odd : m'' % 2 = 1 := by
                    have : (q^b * m'') % 2 = 1 := by rwa [← hm'_eq]
                    rw [Nat.mul_mod] at this
                    by_contra! h_even
                    have h_zero : m'' % 2 = 0 := by omega
                    rw [h_zero, mul_zero, Nat.zero_mod] at this
                    omega
                  have h_S_m'_eq : ((m'.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) =
                    ((q^b).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) *
                    (m''.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := by
                    rw [← sum_f_eq_sum_recip m' hm'_gt_one]
                    rw [← sum_f_eq_sum_recip (q^b) h_qb_gt_one]
                    rw [← sum_f_eq_sum_recip m'' hm''_gt_one]
                    rw [← f_mul_zeta_apply m']
                    rw [← f_mul_zeta_apply (q^b)]
                    rw [← f_mul_zeta_apply m'']
                    rw [hm'_eq]
                    exact S_mul_of_coprime h_coprime_qm''
                  have h_Sqb_nz : (q^b).divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≠ 0 := by
                    have : 0 < (q^b).divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := S_pos (q^b) (by omega)
                    exact ne_of_gt this
                  have h_Sm''_nz : m''.divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≠ 0 := by
                    have : 0 < m''.divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := S_pos m'' (by omega)
                    exact ne_of_gt this
                  have hval_qb := padicValRat_two_S_odd_neg (q^b) h_qb_gt_one h_qb_odd
                  have hval_m'' := padicValRat_two_S_odd_neg m'' hm''_gt_one hm''_odd
                  have hval_qb_le : padicValRat 2 ((q^b).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≤ -1 := by omega
                  have hval_m''_le' : padicValRat 2 (m''.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≤ -1 := by omega
                  have hval_m'_le : padicValRat 2 ((m'.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) ≤ -2 := by
                    rw [h_S_m'_eq]
                    rw [padicValRat.mul h_Sqb_nz h_Sm''_nz]
                    omega
                  have h_Spa_nz : (p^a).divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≠ 0 := by
                    have : 0 < (p^a).divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := S_pos (p^a) (by omega)
                    exact ne_of_gt this
                  have h_Sm'_nz : m'.divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≠ 0 := by
                    have : 0 < m'.divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := S_pos m' (by omega)
                    exact ne_of_gt this
                  have hval_pa := padicValRat_two_S_odd_neg (p^a) h_pa_gt_one h_pa_odd
                  have hval_m' := padicValRat_two_S_odd_neg m' hm'_gt_one hm'_odd
                  have hval_pa_le : padicValRat 2 ((p^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≤ -1 := by omega
                  have hval_m'_le' : padicValRat 2 (m'.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≤ -1 := by omega
                  have hval_m_le : padicValRat 2 ((m.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) ≤ -3 := by
                    rw [h_S_m_eq]
                    rw [padicValRat.mul h_Spa_nz h_Sm'_nz]
                    omega
                  have hval_2_m_lt : padicValRat 2 (((2 * m : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) < 0 := by
                    rw [h_S_eq_2, padicValRat.mul h_S2_nz h_Sm_nz]
                    rw [h_S2]
                    have h_val_4_3 : padicValRat 2 (4 / 3 : ℚ) = 2 := by
                      have h_div : (4 / 3 : ℚ) = ((4 : ℕ) : ℚ) / ((3 : ℕ) : ℚ) := by norm_num
                      rw [h_div]
                      rw [padicValRat.div (by positivity) (by positivity)]
                      rw [padicValRat.of_nat, padicValRat.of_nat]
                      have h_four : padicValNat 2 4 = 2 := by
                        have : (4 : ℕ) = 2^2 := by rfl
                        rw [this]
                        exact @padicValNat.prime_pow 2 _ 2
                      have h_three : padicValNat 2 3 = 0 := by
                        apply padicValNat.eq_zero_of_not_dvd
                        decide
                      rw [h_four, h_three]
                      omega
                    omega
                  exact hval_neg hval_2_m_lt
                obtain ⟨q, hq, b, hm'_eq''⟩ := hm'_pow
                have hb : 1 ≤ b := by
                  by_contra! hb0
                  have : b = 0 := by omega
                  subst this
                  rw [pow_zero] at hm'_eq''
                  omega
                have h_Spa'_lt : ((q^b).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) < 3 / 2 := by
                  by_cases hq3 : q = 3
                  · subst hq3
                    have hq3_prime : Nat.Prime 3 := by decide
                    rw [S_prime_power_eq hq3_prime]
                    exact S_three_pow_lt_three_halves b
                  · have hq5 : 5 ≤ q := by
                      by_contra! h_lt
                      have hq_ge2 : q ≥ 2 := hq.two_le
                      have hq2 : q ≠ 2 := by
                        intro hq2
                        have h_div_q : q ∣ m' := by
                          rw [hm'_eq'']
                          exact dvd_pow_self q (by omega)
                        subst hq2
                        have h_div : 2 ∣ m' := h_div_q
                        have : m' % 2 = 0 := Nat.mod_eq_zero_of_dvd h_div
                        omega
                      interval_cases q
                      · exact hq2 rfl
                      · exact hq3 rfl
                      · have : ¬ Nat.Prime 4 := by decide
                        exact this hq
                    rw [S_prime_power_eq hq]
                    exact S_prime_power_lt_one_and_half hq hq5 b
                have h_Sm_lt : ((m.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) < 9 / 4 := by
                  rw [h_S_m_eq, hm'_eq'']
                  have h_pa_pos : 0 < (p^a).divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := S_pos (p^a) (by omega)
                  have h_qb_pos : 0 < (q^b).divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := S_pos (q^b) (by omega)
                  nlinarith
                have h_S2m_lt : (((2 * m : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) < 3 := by
                  rw [h_S_eq_2, h_S2]
                  nlinarith
                have h_S2m_gt : 1 < (((2 * m : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) := S_gt_one (2 * m) h_2_m_gt
                have h_not_int : ((2 * m : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)).den ≠ 1 :=
                  not_int_of_between_one_three_and_v2_le_zero h_S2m_gt h_S2m_lt hval_2_m
                rw [← h_n_eq] at h_not_int
                exact h_not_int h_den
          · have hk_ge3 : 3 ≤ k := by omega
            by_cases hm_pow : ∃ (p : ℕ) (hp : p.Prime) (a : ℕ), m = p^a
            · rcases hm_pow with ⟨p, hp, a, rfl⟩
              have hp2 : p ≠ 2 := by
                intro hp2
                subst hp2
                have hm_even : (2^a) % 2 = 0 := by
                  have ha : 1 ≤ a := by
                    by_contra! ha0
                    interval_cases a
                    norm_num at hm_gt_one
                  have : 2 ∣ 2^a := dvd_pow_self 2 (by omega)
                  exact Nat.mod_eq_zero_of_dvd this
                omega
              have hp_odd_prop : p % 2 = 1 := by
                by_contra! h_even
                have hp_even : p % 2 = 0 := by omega
                have h_div : 2 ∣ p := Nat.dvd_of_mod_eq_zero hp_even
                have hp_eq_2_symm : 2 = p := hp.eq_one_or_self_of_dvd 2 h_div |>.resolve_left (by decide)
                have hp_eq_2 : p = 2 := hp_eq_2_symm.symm
                exact hp2 hp_eq_2
              have hp_odd' : Odd p := Nat.odd_iff.mpr hp_odd_prop
              have h_cop_2 : Nat.Coprime 2 p := Nat.coprime_two_left.mpr hp_odd'
              have h_cop_2_pa : Nat.Coprime 2 (p^a) := h_cop_2.pow_right a
              have h_cop : Nat.Coprime (2^k) (p^a) := h_cop_2_pa.pow_left k
              have h_n_eq : n = 2^k * p^a := by
                rw [hn_eq]
              have h_2k_pa_gt : 1 < 2^k * p^a := by
                have : 1 ≤ p^a := Nat.one_le_pow a p hp.pos
                have h2k_gt : 1 < 2^k := by
                  have : 2^3 ≤ 2^k := Nat.pow_le_pow_right (by decide) hk_ge3
                  omega
                nlinarith
              have h_S_eq_2 : (((2^k * p^a : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) =
                ((2^k).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) *
                ((p^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := by
                rw [← sum_f_eq_sum_recip (2^k * p^a) h_2k_pa_gt]
                have h2k_gt_1 : 1 < 2^k := by
                  have : 2^3 ≤ 2^k := Nat.pow_le_pow_right (by decide) hk_ge3
                  omega
                rw [← sum_f_eq_sum_recip (2^k) h2k_gt_1]
                have h_pa_gt : 1 < p^a := by
                  have : p^1 ≤ p^a := Nat.pow_le_pow_right hp.pos (by
                    by_contra! ha0
                    interval_cases a
                    norm_num at hm_gt_one)
                  rw [pow_one] at this
                  omega
                rw [← sum_f_eq_sum_recip (p^a) h_pa_gt]
                rw [← f_mul_zeta_apply (2^k * p^a)]
                rw [← f_mul_zeta_apply (2^k)]
                rw [← f_mul_zeta_apply (p^a)]
                exact S_mul_of_coprime h_cop
              have h_S2k_lt : ((2^k).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) < 5 / 3 := S_two_pow_lt_five_thirds k
              have h_Spa_lt : ((p^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) < 3 / 2 := by
                by_cases hp3 : p = 3
                · subst hp3
                  have hp3_prime : Nat.Prime 3 := by decide
                  rw [S_prime_power_eq hp3_prime]
                  exact S_three_pow_lt_three_halves a
                · have hp5 : 5 ≤ p := by
                    by_contra! h_lt
                    have hp_ge2 : p ≥ 2 := hp.two_le
                    interval_cases p
                    · exact hp2 rfl
                    · exact hp3 rfl
                    · have : ¬ Nat.Prime 4 := by decide
                      exact this hp
                  rw [S_prime_power_eq hp]
                  exact S_prime_power_lt_one_and_half hp hp5 a
              have h_S2k_pa_lt : (((2^k * p^a : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) < 3 := by
                rw [h_S_eq_2]
                have h_2k_pos : 0 < ((2^k).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := S_pos (2^k) (by have : 2^3 ≤ 2^k := Nat.pow_le_pow_right (by decide) hk_ge3; omega)
                have h_pa_pos : 0 < ((p^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := S_pos (p^a) (Nat.one_le_pow a p hp.pos)
                nlinarith
              by_cases h_lt2 : (((2^k * p^a : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) < 2
              · have h_gt : 1 < (((2^k * p^a : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) := S_gt_one (2^k * p^a) h_2k_pa_gt
                have h_not_int : ((2^k * p^a : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)).den ≠ 1 :=
                  den_neq_one_of_between h_gt h_lt2
                rw [← h_n_eq] at h_not_int
                exact h_not_int h_den
              · by_cases hk3 : k = 3
                · subst hk3
                  have h_val_ne_one : padicValRat 2 (((2^3 * p^a : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) ≠ 1 := by
                    rw [h_S_eq_2]
                    have h_S2k_nz : (2^3).divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≠ 0 := by
                      have : 0 < (2^3).divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := S_pos (2^3) (by decide)
                      exact ne_of_gt this
                    have h_Spa_nz : (p^a).divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≠ 0 := by
                      have : 0 < (p^a).divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := S_pos (p^a) (Nat.one_le_pow a p hp.pos)
                      exact ne_of_gt this
                    rw [padicValRat.mul h_S2k_nz h_Spa_nz]
                    rw [h_val_8]
                    have h_val_pa : padicValRat 2 ((p^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) < 0 := by
                      have : Fact p.Prime := ⟨hp⟩
                      exact padicValRat_two_S_prime_power_neg hp2 a (by
                        by_contra! ha0
                        interval_cases a
                        norm_num at hm_gt_one)
                    have h_val_pa_le : padicValRat 2 ((p^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≤ -1 := by omega
                    intro h_one
                    omega
                  have h_not_int : ((2^3 * p^a : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)).den ≠ 1 := by
                    have h_ge : 2 ≤ (((2^3 * p^a : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) := by linarith
                    exact not_int_of_between_two_three_and_v2_ne_one h_ge h_S2k_pa_lt h_val_ne_one
                  rw [← h_n_eq] at h_not_int
                  exact h_not_int h_den
                · -- k ≥ 5 case
                  have hk5 : 5 ≤ k := by omega
                  by_cases hp3 : p = 3
                  · subst hp3
                    by_cases ha2 : a = 1
                    · subst ha2
                      have hk7 : 7 ≤ k := by
                        by_contra! hk7_lt
                        have hk5_eq : k = 5 := by omega
                        subst hk5_eq
                        have h_S32_3 : (((2^5 * 3^1 : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) < 2 := by
                          rw [h_S_eq_2]
                          have h_S32 : ((2^5 : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = 15536 / 9765 := by
                            change ((32 : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = 15536 / 9765
                            have h_divs : (32 : ℕ).divisors = {1, 2, 4, 8, 16, 32} := by decide
                            rw [h_divs]
                            have h_not1 : 1 ∉ ({2, 4, 8, 16, 32} : Finset ℕ) := by decide
                            rw [Finset.sum_insert h_not1]
                            have h_not2 : 2 ∉ ({4, 8, 16, 32} : Finset ℕ) := by decide
                            rw [Finset.sum_insert h_not2]
                            have h_not4 : 4 ∉ ({8, 16, 32} : Finset ℕ) := by decide
                            rw [Finset.sum_insert h_not4]
                            have h_not8 : 8 ∉ ({16, 32} : Finset ℕ) := by decide
                            rw [Finset.sum_insert h_not8]
                            have h_not16 : 16 ∉ ({32} : Finset ℕ) := by decide
                            rw [Finset.sum_insert h_not16, Finset.sum_singleton]
                            have h1 : (sigma 1) 1 = 1 := rfl
                            have h2 : (sigma 1) 2 = 3 := rfl
                            have h4 : (sigma 1) 4 = 7 := rfl
                            have h8 : (sigma 1) 8 = 15 := rfl
                            have h16 : (sigma 1) 16 = 31 := rfl
                            have h32 : (sigma 1) 32 = 63 := rfl
                            rw [h1, h2, h4, h8, h16, h32]
                            norm_num
                          have h_S3 : ((3^1 : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = 5 / 4 := by
                            change ((3 : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = 5 / 4
                            have h_divs : (3 : ℕ).divisors = {1, 3} := by decide
                            rw [h_divs]
                            have h_not : 1 ∉ ({3} : Finset ℕ) := by decide
                            rw [Finset.sum_insert h_not, Finset.sum_singleton]
                            have h1 : (sigma 1) 1 = 1 := rfl
                            have h3 : (sigma 1) 3 = 4 := rfl
                            rw [h1, h3]
                            norm_num
                          rw [h_S32, h_S3]
                          norm_num
                        exact h_lt2 h_S32_3
                      have h_S128_ge : ((2^7 : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≤ ((2^k).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := by
                        have hdvd : 2^7 ∣ 2^k := by
                          have : k = 7 + (k - 7) := by omega
                          rw [this, pow_add]
                          exact dvd_mul_right (2^7) (2^(k-7))
                        exact S_le_S_of_dvd (by positivity) (by decide) hdvd
                      have h_S128 : ((2^7 : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = 33790906 / 21082635 := by
                        change ((128 : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = 33790906 / 21082635
                        have h_divs : (128 : ℕ).divisors = {1, 2, 4, 8, 16, 32, 64, 128} := by decide
                        rw [h_divs]
                        have h_not1 : 1 ∉ ({2, 4, 8, 16, 32, 64, 128} : Finset ℕ) := by decide
                        rw [Finset.sum_insert h_not1]
                        have h_not2 : 2 ∉ ({4, 8, 16, 32, 64, 128} : Finset ℕ) := by decide
                        rw [Finset.sum_insert h_not2]
                        have h_not4 : 4 ∉ ({8, 16, 32, 64, 128} : Finset ℕ) := by decide
                        rw [Finset.sum_insert h_not4]
                        have h_not8 : 8 ∉ ({16, 32, 64, 128} : Finset ℕ) := by decide
                        rw [Finset.sum_insert h_not8]
                        have h_not16 : 16 ∉ ({32, 64, 128} : Finset ℕ) := by decide
                        rw [Finset.sum_insert h_not16]
                        have h_not32 : 32 ∉ ({64, 128} : Finset ℕ) := by decide
                        rw [Finset.sum_insert h_not32]
                        have h_not64 : 64 ∉ ({128} : Finset ℕ) := by decide
                        rw [Finset.sum_insert h_not64, Finset.sum_singleton]
                        have h1 : (sigma 1) 1 = 1 := rfl
                        have h2 : (sigma 1) 2 = 3 := rfl
                        have h4 : (sigma 1) 4 = 7 := rfl
                        have h8 : (sigma 1) 8 = 15 := rfl
                        have h16 : (sigma 1) 16 = 31 := rfl
                        have h32 : (sigma 1) 32 = 63 := rfl
                        have h64 : (sigma 1) 64 = 127 := rfl
                        have h128 : (sigma 1) 128 = 255 := rfl
                        rw [h1, h2, h4, h8, h16, h32, h64, h128]
                        norm_num
                      have h_S3 : ((3^1 : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = 5 / 4 := by
                        change ((3 : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = 5 / 4
                        have h_divs : (3 : ℕ).divisors = {1, 3} := by decide
                        rw [h_divs]
                        have h_not : 1 ∉ ({3} : Finset ℕ) := by decide
                        rw [Finset.sum_insert h_not, Finset.sum_singleton]
                        have h1 : (sigma 1) 1 = 1 := rfl
                        have h3 : (sigma 1) 3 = 4 := rfl
                        rw [h1, h3]
                        norm_num
                      have h_prod_ge : (((2^k * 3^1 : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) > 2 := by
                        rw [h_S_eq_2]
                        have h_S3_ge : 5 / 4 ≤ ((3^1).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := by
                          rw [h_S3]
                        have : (33790906 / 21082635 : ℚ) * (5 / 4 : ℚ) ≤ ((2^k).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) * ((3^1).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := by
                          rw [← h_S128]
                          apply mul_le_mul h_S128_ge h_S3_ge (by norm_num) (by linarith)
                        linarith
                      have h_eq : (((2^k * 3^1 : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) =
                        ((((2^k * 3^1 : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))).num : ℚ) := by
                        have h_nd := Rat.num_div_den (((2^k * 3^1 : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)))
                        rw [← h_n_eq] at h_nd
                        rw [h_den] at h_nd
                        rw [Nat.cast_one] at h_nd
                        rw [div_one] at h_nd
                        rw [h_n_eq] at h_nd
                        exact h_nd.symm
                      rw [h_eq] at h_prod_ge h_S2k_pa_lt
                      have h_ge' : 2 < (((2^k * 3^1 : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))).num := by exact_mod_cast h_prod_ge
                      have h_lt' : (((2^k * 3^1 : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))).num < 3 := by exact_mod_cast h_S2k_pa_lt
                      omega
                    · have ha_pos : 1 ≤ a := by
                        by_contra! ha0
                        have : a = 0 := by omega
                        subst this
                        rw [pow_zero] at hm_gt_one
                        omega
                      have ha2_gt : 2 ≤ a := by omega
                      have h_S32_ge : ((2^5 : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≤ ((2^k).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := by
                        have hdvd : 2^5 ∣ 2^k := by
                          have : k = 5 + (k - 5) := by omega
                          rw [this, pow_add]
                          exact dvd_mul_right (2^5) (2^(k-5))
                        exact S_le_S_of_dvd (by positivity) (by decide) hdvd
                      have h_S32 : ((2^5 : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = 15536 / 9765 := by
                        change ((32 : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = 15536 / 9765
                        have h_divs : (32 : ℕ).divisors = {1, 2, 4, 8, 16, 32} := by decide
                        rw [h_divs]
                        have h_not1 : 1 ∉ ({2, 4, 8, 16, 32} : Finset ℕ) := by decide
                        rw [Finset.sum_insert h_not1]
                        have h_not2 : 2 ∉ ({4, 8, 16, 32} : Finset ℕ) := by decide
                        rw [Finset.sum_insert h_not2]
                        have h_not4 : 4 ∉ ({8, 16, 32} : Finset ℕ) := by decide
                        rw [Finset.sum_insert h_not4]
                        have h_not8 : 8 ∉ ({16, 32} : Finset ℕ) := by decide
                        rw [Finset.sum_insert h_not8]
                        have h_not16 : 16 ∉ ({32} : Finset ℕ) := by decide
                        rw [Finset.sum_insert h_not16, Finset.sum_singleton]
                        have h1 : (sigma 1) 1 = 1 := rfl
                        have h2 : (sigma 1) 2 = 3 := rfl
                        have h4 : (sigma 1) 4 = 7 := rfl
                        have h8 : (sigma 1) 8 = 15 := rfl
                        have h16 : (sigma 1) 16 = 31 := rfl
                        have h32 : (sigma 1) 32 = 63 := rfl
                        rw [h1, h2, h4, h8, h16, h32]
                        norm_num
                      have h_S9_ge : ((3^2 : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≤ ((3^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := by
                        have hdvd : 3^2 ∣ 3^a := Nat.pow_dvd_pow 3 ha2_gt
                        exact S_le_S_of_dvd (by positivity) (by decide) hdvd
                      have h_S9 : ((3^2 : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = 69 / 52 := by
                        change ((9 : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = 69 / 52
                        have h_divs : (9 : ℕ).divisors = {1, 3, 9} := by decide
                        rw [h_divs]
                        have h_not1 : 1 ∉ ({3, 9} : Finset ℕ) := by decide
                        rw [Finset.sum_insert h_not1]
                        have h_not3 : 3 ∉ ({9} : Finset ℕ) := by decide
                        rw [Finset.sum_insert h_not3, Finset.sum_singleton]
                        have h1 : (sigma 1) 1 = 1 := rfl
                        have h3 : (sigma 1) 3 = 4 := rfl
                        have h9 : (sigma 1) 9 = 13 := rfl
                        rw [h1, h3, h9]
                        norm_num
                      have h_prod_ge : (((2^k * 3^a : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) > 2 := by
                        rw [h_S_eq_2]
                        have h_S9_ge' : 69 / 52 ≤ ((3^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := by
                          rw [h_S9] at h_S9_ge
                          exact h_S9_ge
                        have : (15536 / 9765 : ℚ) * (69 / 52 : ℚ) ≤ ((2^k).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) * ((3^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := by
                          rw [← h_S32]
                          apply mul_le_mul h_S32_ge h_S9_ge' (by norm_num) (by linarith)
                        linarith
                      have h_eq : (((2^k * 3^a : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) =
                        ((((2^k * 3^a : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))).num : ℚ) := by
                        have h_nd := Rat.num_div_den (((2^k * 3^a : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)))
                        rw [← h_n_eq] at h_nd
                        rw [h_den] at h_nd
                        rw [Nat.cast_one] at h_nd
                        rw [div_one] at h_nd
                        rw [h_n_eq] at h_nd
                        exact h_nd.symm
                      rw [h_eq] at h_prod_ge h_S2k_pa_lt
                      have h_ge' : 2 < (((2^k * 3^a : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))).num := by exact_mod_cast h_prod_ge
                      have h_lt' : (((2^k * 3^a : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))).num < 3 := by exact_mod_cast h_S2k_pa_lt
                      omega
                  · have hp5 : 5 ≤ p := by
                      by_contra! h_lt
                      have hp_ge2 : p ≥ 2 := hp.two_le
                      interval_cases p
                      · exact hp2 rfl
                      · exact hp3 rfl
                      · have : ¬ Nat.Prime 4 := by decide
                        exact this hp
                    have h_S2k_lt : ((2^k).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) < 13 / 8 := S_two_pow_lt_thirteen_eighths k (by omega)
                    have h_Spa_lt' : ((p^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) < 29 / 24 := by
                      rw [S_prime_power_eq hp]
                      exact S_prime_power_lt_twenty_nine_twenty_fourths hp hp5 a
                    have h_S2k_pa_lt2 : (((2^k * p^a : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) < 2 := by
                      rw [h_S_eq_2]
                      have h_2k_pos : 0 < ((2^k).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := S_pos (2^k) (by have : 1 ≤ k := Nat.pos_of_ne_zero hk; have : 2^1 ≤ 2^k := Nat.pow_le_pow_right (show 0 < 2 by decide) this; omega)
                      have h_pa_pos : 0 < ((p^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := S_pos (p^a) (by have : 1 ≤ p^a := Nat.one_le_pow a p hp.pos; omega)
                      nlinarith
                    exact h_lt2 h_S2k_pa_lt2
            · have h_ne : m ≠ 1 := by omega
              have ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd h_ne
              let a := padicValNat p m
              have hp_fact : Fact p.Prime := ⟨hp⟩
              have ha : 1 ≤ a := one_le_padicValNat_of_dvd (by omega) hdvd
              have hm_nz : m ≠ 0 := by omega
              let m' := m / p^a
              have hdvd_pa : p^a ∣ m := pow_padicValNat_dvd
              have hm_eq' : m = p^a * m' := (Nat.mul_div_cancel' hdvd_pa).symm
              have ha_nz : a ≠ 0 := by omega
              have hp2_inner : p ≠ 2 := by
                intro hp2
                subst hp2
                have : 2 ∣ m := Nat.dvd_trans (dvd_pow_self 2 ha_nz) hdvd_pa
                have : m % 2 = 0 := Nat.mod_eq_zero_of_dvd this
                omega
              have h_coprime_pm' : Nat.Coprime (p^a) m' := by
                have h_cop_pm' : Nat.Coprime p m' := by
                  rw [hp.coprime_iff_not_dvd]
                  intro hp_dvd_m'
                  rcases hp_dvd_m' with ⟨w, hw⟩
                  have h_div : p^(a + 1) ∣ m := by
                    rw [hm_eq', hw]
                    use w
                    ring
                  have h_not := pow_succ_padicValNat_not_dvd (p := p) hm_nz
                  exact h_not h_div
                exact h_cop_pm'.pow_left a
              have hm'_gt_one : 1 < m' := by
                by_contra! h_le
                interval_cases m'
                · rw [mul_zero] at hm_eq'
                  omega
                · rw [mul_one] at hm_eq'
                  have : m = p^a := hm_eq'
                  exact hm_pow ⟨p, hp, a, this⟩
              have h_pa_gt_one : 1 < p^a := by
                have hp_pos : 2 ≤ p := hp.two_le
                have : p^1 ≤ p^a := Nat.pow_le_pow_right (by omega) ha
                rw [pow_one] at this
                omega
              have h_pa_odd : (p^a) % 2 = 1 := by
                have : (p^a * m') % 2 = 1 := by rwa [← hm_eq']
                rw [Nat.mul_mod] at this
                by_contra! h_even
                have h_zero : p^a % 2 = 0 := by omega
                rw [h_zero, zero_mul, Nat.zero_mod] at this
                omega
              have hm'_odd : m' % 2 = 1 := by
                have : (p^a * m') % 2 = 1 := by rwa [← hm_eq']
                rw [Nat.mul_mod] at this
                by_contra! h_even
                have h_zero : m' % 2 = 0 := by omega
                rw [h_zero, mul_zero, Nat.zero_mod] at this
                omega
              have h_S_m_eq : ((m.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) =
                ((p^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) *
                (m'.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ) ) := by
                rw [← sum_f_eq_sum_recip m hm_gt_one]
                rw [← sum_f_eq_sum_recip (p^a) h_pa_gt_one]
                rw [← sum_f_eq_sum_recip m' hm'_gt_one]
                rw [← f_mul_zeta_apply m]
                rw [← f_mul_zeta_apply (p^a)]
                rw [← f_mul_zeta_apply m']
                rw [hm_eq']
                exact S_mul_of_coprime h_coprime_pm'
              have h_Sqb_nz : (p^a).divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≠ 0 := by
                have : 0 < (p^a).divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := S_pos (p^a) (by omega)
                exact ne_of_gt this
              have h_Sm''_nz : m'.divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≠ 0 := by
                have : 0 < m'.divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := S_pos m' (by omega)
                exact ne_of_gt this
              have hval_qb := padicValRat_two_S_odd_neg (p^a) h_pa_gt_one h_pa_odd
              have hval_m'' := padicValRat_two_S_odd_neg m' hm'_gt_one hm'_odd
              have hval_qb_le : padicValRat 2 ((p^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≤ -1 := by omega
              have hval_m''_le' : padicValRat 2 (m'.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≤ -1 := by omega
              have hval_m : padicValRat 2 ((m.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) ≤ -2 := by
                rw [h_S_m_eq]
                rw [padicValRat.mul h_Sqb_nz h_Sm''_nz]
                omega
              have h_n_eq : n = 2^k * m := hn_eq
              have h_2k_m_gt : 1 < 2^k * m := by
                have h1 : 8 ≤ 2^k := Nat.pow_le_pow_right (show 0 < 2 by decide) hk_ge3
                have h2 : 1 ≤ m := by omega
                have h_mul : 8 * 1 ≤ 2^k * m := Nat.mul_le_mul h1 h2
                omega
              have h_cop : Nat.Coprime (2^k) m := h_coprime
              have h_S_eq_2 : (((2^k * m : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) =
                ((2^k).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) *
                (m.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := by
                rw [← sum_f_eq_sum_recip (2^k * m) h_2k_m_gt]
                have h2k_gt_1 : 1 < 2^k := by
                  have : 2^3 ≤ 2^k := Nat.pow_le_pow_right (show 0 < 2 by decide) hk_ge3
                  omega
                rw [← sum_f_eq_sum_recip (2^k) h2k_gt_1]
                rw [← sum_f_eq_sum_recip m hm_gt_one]
                rw [← f_mul_zeta_apply (2^k * m)]
                rw [← f_mul_zeta_apply (2^k)]
                rw [← f_mul_zeta_apply m]
                exact S_mul_of_coprime h_cop
              by_cases hk3 : k = 3
              · subst hk3
                have h_val_8 := h_val_8
                have h_val_lt : padicValRat 2 (((2^3 * m : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) < 0 := by
                  rw [h_S_eq_2]
                  have h_S2k_nz : (2^3).divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≠ 0 := by
                    have : 0 < (2^3).divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := S_pos (2^3) (by decide)
                    exact ne_of_gt this
                  have h_Sm_nz : m.divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≠ 0 := by
                    have : 0 < m.divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := S_pos m (by omega)
                    exact ne_of_gt this
                  rw [padicValRat.mul h_S2k_nz h_Sm_nz]
                  rw [h_val_8]
                  omega
                have h_not_int : ((2^3 * m : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)).den ≠ 1 :=
                  not_integer_of_padicVal_neg Nat.prime_two h_val_lt
                rw [← h_n_eq] at h_not_int
                exact h_not_int h_den
              · -- k ≥ 5 case
                by_cases hm'_pow : ∃ (q : ℕ) (hq : q.Prime) (b : ℕ), m' = q^b
                · obtain ⟨q, hq, b, hm'_eq''⟩ := hm'_pow
                  have hb_nz : b ≠ 0 := by
                    intro hb0
                    subst hb0
                    rw [pow_zero] at hm'_eq''
                    omega
                  have hb : 1 ≤ b := by omega
                  have hp_neq_q : p ≠ q := by
                    intro hpq
                    subst hpq
                    have h_cop : Nat.Coprime (p^a) (p^b) := by
                      rw [hm'_eq''] at h_coprime_pm'
                      exact h_coprime_pm'
                    have ha_nz : a ≠ 0 := by omega
                    have h_dvd1 : p ∣ p^a := dvd_pow_self p ha_nz
                    have h_dvd2 : p ∣ p^b := dvd_pow_self p hb_nz
                    have h_gcd : Nat.gcd (p^a) (p^b) = 1 := h_cop
                    have h_dvd_gcd : p ∣ Nat.gcd (p^a) (p^b) := Nat.dvd_gcd h_dvd1 h_dvd2
                    rw [h_gcd] at h_dvd_gcd
                    have : p ≤ 1 := Nat.le_of_dvd (by decide) h_dvd_gcd
                    have : 2 ≤ p := hp.two_le
                    omega
                  have h_Spa_lt : (p^a).divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) < 3 / 2 := by
                    by_cases hp3 : p = 3
                    · subst hp3
                      have hp3_prime : Nat.Prime 3 := by decide
                      rw [S_prime_power_eq hp3_prime]
                      exact S_three_pow_lt_three_halves a
                    · have hp5 : 5 ≤ p := by
                        by_contra! hp_lt
                        have hp_ge2 : p ≥ 2 := hp.two_le
                        interval_cases p
                        · exact hp2_inner rfl
                        · exact hp3 rfl
                        · have : ¬ Nat.Prime 4 := by decide
                          exact this hp
                      rw [S_prime_power_eq hp]
                      exact S_prime_power_lt_one_and_half hp hp5 a
                  have h_Sqb_lt : (q^b).divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) < 3 / 2 := by
                    by_cases hq3 : q = 3
                    · subst hq3
                      have hq3_prime : Nat.Prime 3 := by decide
                      rw [S_prime_power_eq hq3_prime]
                      exact S_three_pow_lt_three_halves b
                    · have hq5 : 5 ≤ q := by
                        by_contra! hq_lt
                        have hq_ge2 : q ≥ 2 := hq.two_le
                        have hq2 : q ≠ 2 := by
                          intro hq2
                          subst hq2
                          have : 2 ∣ m' := by
                            rw [hm'_eq'']
                            exact dvd_pow_self 2 hb_nz
                          have : m' % 2 = 0 := Nat.mod_eq_zero_of_dvd this
                          omega
                        interval_cases q
                        · exact hq2 rfl
                        · exact hq3 rfl
                        · have : ¬ Nat.Prime 4 := by decide
                          exact this hq
                      rw [S_prime_power_eq hq]
                      exact S_prime_power_lt_one_and_half hq hq5 b
                  have h_Sm_lt : ((m.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) < 87 / 48 := by
                    rw [h_S_m_eq, hm'_eq'']
                    generalize h_Spa : (p^a).divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = S_Spa
                    generalize h_Sqb : (q^b).divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = S_Sqb
                    by_cases hp3 : p = 3
                    · subst hp3
                      have hq5 : 5 ≤ q := by
                        by_contra! hq_lt
                        have hq_ge2 : q ≥ 2 := hq.two_le
                        have hq2 : q ≠ 2 := by
                          intro hq2
                          subst hq2
                          have : 2 ∣ m' := by
                            rw [hm'_eq'']
                            exact dvd_pow_self 2 hb_nz
                          have : m' % 2 = 0 := Nat.mod_eq_zero_of_dvd this
                          omega
                        interval_cases q
                        · exact hq2 rfl
                        · exact hp_neq_q rfl
                        · have : ¬ Nat.Prime 4 := by decide
                          exact this hq
                      have h_Sqb_lt2 : S_Sqb < 29 / 24 := by
                        rw [← h_Sqb]
                        rw [S_prime_power_eq hq]
                        exact S_prime_power_lt_twenty_nine_twenty_fourths hq hq5 b
                      have h_Spa_lt2 : S_Spa < 3 / 2 := by
                        rw [← h_Spa]
                        rw [S_prime_power_eq (by decide)]
                        exact S_three_pow_lt_three_halves a
                      have h_pa_pos : 0 < S_Spa := by
                        rw [← h_Spa]
                        exact S_pos (3^a) (by omega)
                      have h_qb_pos : 0 < S_Sqb := by
                        rw [← h_Sqb]
                        exact S_pos (q^b) (by omega)
                      have h_mul : S_Spa * S_Sqb < (3 / 2) * (29 / 24) := mul_lt_mul h_Spa_lt2 h_Sqb_lt2.le h_qb_pos (by norm_num)
                      have h_calc : (3 / 2) * (29 / 24 : ℚ) = 87 / 48 := by norm_num
                      rwa [h_calc] at h_mul
                    · have hp5 : 5 ≤ p := by
                        by_contra! hp_lt
                        have hp_ge2 : p ≥ 2 := hp.two_le
                        interval_cases p
                        · exact hp2_inner rfl
                        · exact hp3 rfl
                        · have : ¬ Nat.Prime 4 := by decide
                          exact this hp
                      have h_Spa_lt2 : S_Spa < 29 / 24 := by
                        rw [← h_Spa]
                        rw [S_prime_power_eq hp]
                        exact S_prime_power_lt_twenty_nine_twenty_fourths hp hp5 a
                      have h_pa_pos : 0 < S_Spa := by
                        rw [← h_Spa]
                        exact S_pos (p^a) (by omega)
                      have h_qb_pos : 0 < S_Sqb := by
                        rw [← h_Sqb]
                        exact S_pos (q^b) (by omega)
                      have h_Sqb_lt_gen : S_Sqb < 3 / 2 := by
                        rw [← h_Sqb]
                        exact h_Sqb_lt
                      have h_mul : S_Spa * S_Sqb < (29 / 24) * (3 / 2) := mul_lt_mul h_Spa_lt2 h_Sqb_lt_gen.le h_qb_pos (by norm_num)
                      have h_calc : (29 / 24) * (3 / 2 : ℚ) = 87 / 48 := by norm_num
                      rwa [h_calc] at h_mul
                  have h_S_lt3 : (((2^k * m : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) < 3 := by
                    rw [h_S_eq_2]
                    have h_S2k_lt : ((2^k).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) < 13 / 8 :=
                      S_two_pow_lt_thirteen_eighths k (by omega)
                    have h_S2k_pos : 0 < ((2^k).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) :=
                      S_pos (2^k) (by have : 2^3 ≤ 2^k := Nat.pow_le_pow_right (show 0 < 2 by decide) hk_ge3; omega)
                    have h_Sm_pos : 0 < (m.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) :=
                      S_pos m (by omega)
                    have h_mul := mul_lt_mul h_S2k_lt h_Sm_lt.le h_Sm_pos (by norm_num)
                    have h_calc : (13 / 8 : ℚ) * (87 / 48 : ℚ) < 3 := by norm_num
                    linarith
                  by_cases hval_2k_le2 : padicValRat 2 ((2^k).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≤ 2
                  · by_cases h_lt2 : (((2^k * m : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) < 2
                    · have h_prod_gt : (((2^k * m : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) > 1 := S_gt_one (2^k * m) h_2k_m_gt
                      have h_val_le : padicValRat 2 (((2^k * m : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) ≤ 0 := by
                        rw [h_S_eq_2]
                        have h_S2k_nz : (2^k).divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≠ 0 := by
                          have : 0 < (2^k).divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := S_pos (2^k) (by have : 2^3 ≤ 2^k := Nat.pow_le_pow_right (show 0 < 2 by decide) hk_ge3; omega)
                          exact ne_of_gt this
                        have h_Sm_nz : m.divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≠ 0 := by
                          have : 0 < m.divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := S_pos m (by omega)
                          exact ne_of_gt this
                        rw [padicValRat.mul h_S2k_nz h_Sm_nz]
                        omega
                      have h_not_int : ((2^k * m : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)).den ≠ 1 :=
                        not_int_of_between_one_three_and_v2_le_zero h_prod_gt h_S_lt3 h_val_le
                      rw [← h_n_eq] at h_not_int
                      exact h_not_int h_den
                    · have h_prod_ge : (((2^k * m : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) ≥ 2 := by linarith
                      have h_val_ne_one : padicValRat 2 (((2^k * m : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) ≠ 1 := by
                        rw [h_S_eq_2]
                        have h_S2k_nz : (2^k).divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≠ 0 := by
                          have : 0 < (2^k).divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := S_pos (2^k) (by have : 2^3 ≤ 2^k := Nat.pow_le_pow_right (show 0 < 2 by decide) hk_ge3; omega)
                          exact ne_of_gt this
                        have h_Sm_nz : m.divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≠ 0 := by
                          have : 0 < m.divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := S_pos m (by omega)
                          exact ne_of_gt this
                        rw [padicValRat.mul h_S2k_nz h_Sm_nz]
                        omega
                      have h_not_int : ((2^k * m : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)).den ≠ 1 :=
                        not_int_of_between_two_three_and_v2_ne_one h_prod_ge h_S_lt3 h_val_ne_one
                      rw [← h_n_eq] at h_not_int
                      exact h_not_int h_den
                  · -- Here padicValRat 2 S(2^k) ≥ 3, which implies k ≥ 5.
                    have hk_ge5 : 5 ≤ k := by
                      have : k ≠ 3 := hk3
                      have : k ≥ 3 := hk_ge3
                      have : k % 2 = 1 := hk_odd
                      omega
                    by_cases hk5 : k = 5
                    · subst hk5
                      generalize h_S5 : (((2^5 * m : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) = S5
                      generalize h_Sm : (m.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = Sm
                      by_cases h_lt2 : S5 < 2
                      · have h_prod_gt : S5 > 1 := by
                          rw [← h_S5]
                          exact S_gt_one (2^5 * m) (by omega)
                        have h_eq : S5 = (S5.num : ℚ) := by
                          have h_nd := Rat.num_div_den S5
                          rw [← h_S5] at h_nd
                          rw [← h_n_eq] at h_nd
                          rw [h_den] at h_nd
                          rw [Nat.cast_one] at h_nd
                          rw [div_one] at h_nd
                          rw [h_n_eq] at h_nd
                          rw [h_S5] at h_nd
                          exact h_nd.symm
                        rw [h_eq] at h_prod_gt h_lt2
                        have h_ge' : 1 < S5.num := by exact_mod_cast h_prod_gt
                        have h_lt' : S5.num < 2 := by exact_mod_cast h_lt2
                        omega
                      · have h_prod_ge : S5 ≥ 2 := not_lt.mp h_lt2
                        have h_val_ne_one : padicValRat 2 S5 ≠ 1 := by
                          rw [← h_S5]
                          rw [h_S_eq_2]
                          have h_S2k_nz : (2^5).divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≠ 0 := ne_of_gt (S_pos (2^5) (by decide))
                          have h_Sm_nz : m.divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≠ 0 := by
                            have : 0 < m.divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := S_pos m (by omega)
                            exact ne_of_gt this
                          rw [padicValRat.mul h_S2k_nz h_Sm_nz]
                          have h_S32_val : padicValRat 2 ((2^5 : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = 4 := S_thirty_two_val
                          rw [h_S32_val]
                          rcases em (padicValRat 2 Sm = -3) with h_val_m_eq | h_val_m_eq
                          · rw [h_Sm]
                            have h_S5_eq_2 : S5 = 2 := by
                              have h_nd : S5 = (S5.num : ℚ) := by
                                have h_nd' := Rat.num_div_den S5
                                rw [← h_S5] at h_nd'
                                rw [← h_n_eq] at h_nd'
                                rw [h_den] at h_nd'
                                rw [Nat.cast_one] at h_nd'
                                rw [div_one] at h_nd'
                                rw [h_n_eq] at h_nd'
                                rw [h_S5] at h_nd'
                                exact h_nd'.symm
                              have h_ge : 2 ≤ S5.num := by
                                have h_S5_ge_2 : S5 ≥ 2 := h_prod_ge
                                rw [h_nd] at h_S5_ge_2
                                exact_mod_cast h_S5_ge_2
                              have h_lt : S5.num < 3 := by
                                have h_S5_lt_3 : S5 < 3 := by
                                  have h_lt' : (∑ d ∈ (2^5 * m : ℕ).divisors, (1 : ℚ) / ↑((sigma 1) d) : ℚ) < 3 := h_S_lt3
                                  rw [h_S5] at h_lt'
                                  exact h_lt'
                                rw [h_nd] at h_S5_lt_3
                                exact_mod_cast h_S5_lt_3
                              have h_eq_2 : S5.num = 2 := by omega
                              rw [h_nd, h_eq_2]
                              rfl
                            have h_Sm_val : Sm = 9765 / 7768 := by
                              have h_S_eq : S5 = 15536 / 9765 * Sm := by
                                rw [← h_S5, h_S_eq_2, h_Sm]
                                have h32 : ((2^5 : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = 15536 / 9765 := S_thirty_two_eq
                                rw [h32]
                              rw [h_S5_eq_2] at h_S_eq
                              linarith
                                                        have h_false : False := by
                              have h_Spa_ge : 1 + 1 / ((p : ℚ) + 1) ≤ ((p^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := S_prime_power_ge hp a ha
                              have h_Sqb_ge : 1 + 1 / ((q : ℚ) + 1) ≤ ((q^b).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := S_prime_power_ge hq b hb
                              have hp_pos : 1 + 1 / ((p : ℚ) + 1) > 0 := by positivity
                              have hq_pos : 1 + 1 / ((q : ℚ) + 1) > 0 := by positivity
                              have h_Sm_eq : Sm = ((p^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) * ((q^b).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := by
                                rw [← h_Sm, h_S_m_eq, hm'_eq'']
                              by_cases hp3 : p = 3
                              · subst hp3
                                have h_q_ge5 : q ≥ 5 := by
                                  have hq3 : q ≠ 3 := hp_neq_q.symm
                                  have hq4 : q ≠ 4 := by
                                    intro hq4
                                    subst hq4
                                    have : ¬ Nat.Prime 4 := by decide
                                    exact this hq
                                  have hq2 : q ≠ 2 := by
                                    intro hq2_eq
                                    subst hq2_eq
                                    have : 2 ∣ m := by
                                      rw [hm_eq', hm'_eq'']
                                      exact dvd_mul_of_dvd_right (dvd_pow_self 2 hb_nz) (3^a)
                                    have : m % 2 = 0 := Nat.mod_eq_zero_of_dvd this
                                    omega
                                  have hq_ge2 : q ≥ 2 := hq.two_le
                                  omega
                                by_cases ha2 : 2 ≤ a
                                · have h_Spa_ge' : ((3^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≥ 69 / 52 := S_three_power_ge_two a ha2
                                  have h_Sqb_ge' : ((q^b).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≥ 1 := by
                                    have : 1 + 1 / ((q : ℚ) + 1) ≤ ((q^b).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := h_Sqb_ge
                                    have : 1 / ((q : ℚ) + 1) > 0 := by positivity
                                    linarith
                                  have h_Sm_ge : Sm ≥ 69 / 52 := by
                                    rw [h_Sm_eq]
                                    have : ((3^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) * ((q^b).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≥ (69 / 52) * 1 := by
                                      apply mul_le_mul h_Spa_ge' h_Sqb_ge' (by positivity) (by positivity)
                                    linarith
                                  linarith
                                · have ha1 : a = 1 := by omega
                                  have h_S3 : ((3^1 : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = 5 / 4 := by
                                    have hd : (3^1 : ℕ).divisors = {1, 3} := by decide
                                    rw [hd]
                                    have h1 : (sigma 1) 1 = 1 := rfl
                                    have h3 : (sigma 1) 3 = 4 := rfl
                                    rw [sum_insert (by simp), sum_singleton]
                                    rw [h1, h3]
                                    norm_num
                                  have h_Sqb_eq : ((q^b).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = 1953 / 1942 := by
                                    have : Sm = (5 / 4) * ((q^b).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := by
                                      rw [h_Sm_eq, ha1, h_S3]
                                    linarith
                                  by_cases hb1 : b = 1
                                  · subst hb1
                                    have h_Sqb : ((q^1 : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = (q + 2 : ℚ) / (q + 1 : ℚ) := by
                                      have hd : (q^1 : ℕ).divisors = {1, q} := by
                                        rw [pow_one]
                                        exact hq.divisors
                                      rw [hd, sum_insert (by simp [hq.ne_one.symm]), sum_singleton]
                                      have h1 : (sigma 1) 1 = 1 := rfl
                                      have hq_sig : (sigma 1) q = q + 1 := by
                                        rw [sigma_one_apply, hq.divisors, sum_pair hq.ne_one.symm]
                                        ring
                                      rw [h1, hq_sig]
                                      have : (q : ℚ) + 1 ≠ 0 := by positivity
                                      field_simp; ring
                                    have h_eq_frac : (q + 2 : ℚ) / (q + 1 : ℚ) = 1953 / 1942 := by
                                      rw [← h_Sqb, h_Sqb_eq]
                                    have h_11q : 11 * (q : ℚ) = 1931 := by
                                      have hq_pos' : (q : ℚ) + 1 ≠ 0 := by positivity
                                      have := (div_eq_div_iff hq_pos' (by decide : (1942 : ℚ) ≠ 0)).mp h_eq_frac
                                      linarith
                                    have h_11q_nat : 11 * q = 1931 := by exact_mod_cast h_11q
                                    have h_mod : (11 * q) % 11 = 1931 % 11 := by rw [h_11q_nat]
                                    norm_num at h_mod
                                  · -- b >= 2
                                    have hq_ge177 : q ≥ 177 := by
                                      have h_Sqb_ge_val : ((q^b).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≥ 1 + 1 / ((q : ℚ) + 1) := by
                                        have : 1 + 1 / ((q : ℚ) + 1) ≤ ((q^b).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := h_Sqb_ge
                                        linarith
                                      have h_q_ge175 : (q : ℚ) ≥ 175 := by
                                        rw [h_Sqb_eq] at h_Sqb_ge_val
                                        have hq_pos' : (q : ℚ) + 1 > 0 := by positivity
                                        have h_step1 : 1 / ((q : ℚ) + 1) ≤ 11 / 1942 := by linarith
                                        have h_step2 : (1942 : ℚ) ≤ 11 * ((q : ℚ) + 1) := by
                                          exact (div_le_div_iff_of_pos_right (by decide) hq_pos').mp h_step1
                                        linarith
                                      have hq_ge175_nat : q ≥ 175 := by exact_mod_cast h_q_ge175
                                      by_contra! h_lt
                                      interval_cases q
                                      · have : ¬ Nat.Prime 175 := by decide
                                        exact this hq
                                      · have : ¬ Nat.Prime 176 := by decide
                                        exact this hq
                                    have h_Sqb_lt_frac : ((q^b).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) < 1953 / 1942 := by
                                      have h_lt_lim := S_lt_q_sub_one q hq b
                                      have h_lim_le : (q : ℚ) / ((q : ℚ) - 1) ≤ 1953 / 1942 := by
                                        have hq_pos' : (q : ℚ) - 1 > 0 := by
                                          have : (q : ℚ) ≥ 177 := by exact_mod_cast hq_ge177
                                          linarith
                                        have h_step1 : (q : ℚ) * 1942 ≤ 1953 * ((q : ℚ) - 1) := by
                                          have : (q : ℚ) ≥ 177 := by exact_mod_cast hq_ge177
                                          linarith
                                        exact (div_le_div_iff_of_pos_right hq_pos' (by decide)).mpr h_step1
                                      linarith
                                    linarith
                              · by_cases hq3 : q = 3
                                · subst hq3
                                  have h_p_ge5 : p ≥ 5 := by
                                    by_contra! h_lt
                                    have hp_ge2 : p ≥ 2 := hp.two_le
                                    interval_cases p
                                    · exact hp2_inner rfl
                                    · exact hp3 rfl
                                    · have : ¬ Nat.Prime 4 := by decide
                                      exact this hp
                                  by_cases ha2 : 2 ≤ a
                                  · have h_Sqb_ge : ((3^b).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≥ 69 / 52 := S_three_power_ge_two b ha2
                                    have h_Spa_ge' : ((p^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≥ 1 := by
                                      have : 1 + 1 / ((p : ℚ) + 1) ≤ ((p^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := h_Spa_ge
                                      have : 1 / ((p : ℚ) + 1) > 0 := by positivity
                                      linarith
                                    have h_Sm_ge : Sm ≥ 69 / 52 := by
                                      rw [h_Sm_eq]
                                      have : ((p^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) * ((3^b).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≥ 1 * (69 / 52) := by
                                        apply mul_le_mul h_Spa_ge' h_Sqb_ge (by positivity) (by positivity)
                                      linarith
                                    linarith
                                  · have hb1 : b = 1 := by omega
                                    have h_S3 : ((3^1 : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = 5 / 4 := by
                                      have hd : (3^1 : ℕ).divisors = {1, 3} := by decide
                                      rw [hd]
                                      have h1 : (sigma 1) 1 = 1 := rfl
                                      have h3 : (sigma 1) 3 = 4 := rfl
                                      rw [sum_insert (by simp), sum_singleton]
                                      rw [h1, h3]
                                      norm_num
                                    have h_Spa_eq : ((p^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = 1953 / 1942 := by
                                      have : Sm = (5 / 4) * ((p^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := by
                                        rw [h_Sm_eq, hb1, h_S3, mul_comm]
                                      linarith
                                    by_cases ha1_eq : a = 1
                                    · subst ha1_eq
                                      have h_Spa : ((p^1 : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = (p + 2 : ℚ) / (p + 1 : ℚ) := by
                                        have hd : (p^1 : ℕ).divisors = {1, p} := by
                                          rw [pow_one]
                                          exact hp.divisors
                                        rw [hd, sum_insert (by simp [hp.ne_one.symm]), sum_singleton]
                                        have h1' : (sigma 1) 1 = 1 := rfl
                                        have hp_sig : (sigma 1) p = p + 1 := by
                                          rw [sigma_one_apply, hp.divisors, sum_pair hp.ne_one.symm]
                                          ring
                                        rw [h1', hp_sig]
                                        have : (p : ℚ) + 1 ≠ 0 := by positivity
                                        field_simp; ring
                                      have h_eq_frac : (p + 2 : ℚ) / (p + 1 : ℚ) = 1953 / 1942 := by
                                        rw [← h_Spa, h_Spa_eq]
                                      have h_11p : 11 * (p : ℚ) = 1931 := by
                                        have hp_pos' : (p : ℚ) + 1 ≠ 0 := by positivity
                                        have := (div_eq_div_iff hp_pos' (by decide : (1942 : ℚ) ≠ 0)).mp h_eq_frac
                                        linarith
                                      have h_11p_nat : 11 * p = 1931 := by exact_mod_cast h_11p
                                      have h_mod : (11 * p) % 11 = 1931 % 11 := by rw [h_11p_nat]
                                      norm_num at h_mod
                                    · -- a >= 2
                                      have hp_ge177 : p ≥ 177 := by
                                        have h_Spa_ge_val : ((p^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≥ 1 + 1 / ((p : ℚ) + 1) := by
                                          have : 1 + 1 / ((p : ℚ) + 1) ≤ ((p^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := h_Spa_ge
                                          linarith
                                        have h_p_ge175 : (p : ℚ) ≥ 175 := by
                                          rw [h_Spa_eq] at h_Spa_ge_val
                                          have hp_pos' : (p : ℚ) + 1 > 0 := by positivity
                                          have h_step1 : 1 / ((p : ℚ) + 1) ≤ 11 / 1942 := by linarith
                                          have h_step2 : (1942 : ℚ) ≤ 11 * ((p : ℚ) + 1) := by
                                            exact (div_le_div_iff_of_pos_right (by decide) hp_pos').mp h_step1
                                          linarith
                                        have hp_ge175_nat : p ≥ 175 := by exact_mod_cast h_p_ge175
                                        by_contra! h_lt
                                        interval_cases p
                                        · have : ¬ Nat.Prime 175 := by decide
                                          exact this hp
                                        · have : ¬ Nat.Prime 176 := by decide
                                          exact this hp
                                      have h_Spa_lt_frac : ((p^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) < 1953 / 1942 := by
                                        have h_lt_lim := S_lt_q_sub_one p hp a
                                        have h_lim_le : (p : ℚ) / ((p : ℚ) - 1) ≤ 1953 / 1942 := by
                                          have hp_pos' : (p : ℚ) - 1 > 0 := by
                                            have : (p : ℚ) ≥ 177 := by exact_mod_cast hp_ge177
                                            linarith
                                          have h_step1 : (p : ℚ) * 1942 ≤ 1953 * ((p : ℚ) - 1) := by
                                            have : (p : ℚ) ≥ 177 := by exact_mod_cast hp_ge177
                                            linarith
                                          exact (div_le_div_iff_of_pos_right hp_pos' (by decide)).mpr h_step1
                                        linarith
                                      linarith
                                · have hq2_eq : q ≠ 2 := by
                                    intro hq2_eq_val
                                    have : 2 ∣ m := by
                                      rw [hm_eq', hm'_eq'']
                                      have h_div : 2 ∣ 2^b := dvd_pow_self 2 (by omega)
                                      rw [← hq2_eq_val] at h_div
                                      exact dvd_mul_of_dvd_right h_div (p^a)
                                    have : m % 2 = 0 := Nat.mod_eq_zero_of_dvd this
                                    omega
                                  have hp_ge5 : p ≥ 5 := by
                                    by_contra! h_lt
                                    have hp_ge2 : p ≥ 2 := hp.two_le
                                    interval_cases p
                                    · exact hp2_inner rfl
                                    · exact hp3 rfl
                                    · have : ¬ Nat.Prime 4 := by decide
                                      exact this hp
                                  have hq_ge5 : q ≥ 5 := by
                                    by_contra! h_lt
                                    have hq_ge2 : q ≥ 2 := hq.two_le
                                    interval_cases q
                                    · exact hq2_eq rfl
                                    · exact hq3 rfl
                                    · have : ¬ Nat.Prime 4 := by decide
                                      exact this hq
                                  have hp_ne_q : p ≠ q := hp_neq_q
                                  by_cases hp5 : p = 5
                                  · subst hp5
                                    have hq_ge7 : q ≥ 7 := by
                                      have : q ≠ 5 := hp_ne_q.symm
                                      omega
                                    have h_Spa_ge2 : ((5^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≥ 7 / 6 := by
                                      have hp_prime : (5 : ℕ).Prime := by decide
                                      have := S_prime_power_ge hp_prime a ha
                                      linarith
                                    have h_Sqb_ge' : ((q^b).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≥ 9 / 8 := by
                                      have : 1 + 1 / ((q : ℚ) + 1) ≤ ((q^b).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := h_Sqb_ge
                                      have h_denom : (q : ℚ) + 1 ≥ 8 := by exact_mod_cast (by omega : q + 1 ≥ 8)
                                      have h_inv : 1 / ((q : ℚ) + 1) ≤ 1 / 8 := by
                                        apply div_le_div_of_nonneg_left (by norm_num) (by linarith) h_denom
                                      linarith
                                    have h_Sm_ge_2116 : Sm ≥ 21 / 16 := by
                                      rw [h_Sm_eq]
                                      have : ((5^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) * ((q^b).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≥ (7 / 6) * (9 / 8) := by
                                        apply mul_le_mul h_Spa_ge2 h_Sqb_ge' (by positivity) (by positivity)
                                      have h_calc : (7 / 6 : ℚ) * (9 / 8) = 21 / 16 := by ring
                                      linarith
                                    linarith
                                  · by_cases hq5 : q = 5
                                    · subst hq5
                                      have h_p_ge7 : p ≥ 7 := by
                                        have : p ≠ 5 := hp5
                                        omega
                                      have h_Sqb_ge2 : ((5^b).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≥ 7 / 6 := by
                                        have hq_prime : (5 : ℕ).Prime := by decide
                                        have := S_prime_power_ge hq_prime b (by omega)
                                        linarith
                                      have h_Spa_ge' : ((p^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≥ 9 / 8 := by
                                        have : 1 + 1 / ((p : ℚ) + 1) ≤ ((p^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := h_Spa_ge
                                        have h_denom : (p : ℚ) + 1 ≥ 8 := by exact_mod_cast (by omega : p + 1 ≥ 8)
                                        have h_inv : 1 / ((p : ℚ) + 1) ≤ 1 / 8 := by
                                          apply div_le_div_of_nonneg_left (by norm_num) (by linarith) h_denom
                                        linarith
                                      have h_Sm_ge_2116 : Sm ≥ 21 / 16 := by
                                        rw [h_Sm_eq]
                                        have : ((p^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) * ((5^b).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≥ (9 / 8) * (7 / 6) := by
                                          apply mul_le_mul h_Spa_ge' h_Sqb_ge2 (by positivity) (by positivity)
                                        have h_calc : (9 / 8 : ℚ) * (7 / 6) = 21 / 16 := by ring
                                        linarith
                                      linarith
                                    · -- both p >= 7 and q >= 7
                                      have h_p_ge7 : p ≥ 7 := by
                                        have : p ≠ 5 := hp5
                                        omega
                                      have h_q_ge7 : q ≥ 7 := by
                                        have : q ≠ 5 := hq5
                                        omega
                                      have h_Spa_ge' : ((p^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≥ 9 / 8 := by
                                        have : 1 + 1 / ((p : ℚ) + 1) ≤ ((p^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := h_Spa_ge
                                        have h_denom : (p : ℚ) + 1 ≥ 8 := by exact_mod_cast (by omega : p + 1 ≥ 8)
                                        have h_inv : 1 / ((p : ℚ) + 1) ≤ 1 / 8 := by
                                          apply div_le_div_of_nonneg_left (by norm_num) (by linarith) h_denom
                                        linarith
                                      have h_Sqb_ge' : ((q^b).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≥ 9 / 8 := by
                                        have : 1 + 1 / ((q : ℚ) + 1) ≤ ((q^b).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := h_Sqb_ge
                                        have h_denom : (q : ℚ) + 1 ≥ 8 := by exact_mod_cast (by omega : q + 1 ≥ 8)
                                        have h_inv : 1 / ((q : ℚ) + 1) ≤ 1 / 8 := by
                                          apply div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
                                        linarith
                                      have h_Sm_ge_8164 : Sm ≥ 81 / 64 := by
                                        rw [h_Sm_eq]
                                        have : ((p^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) * ((q^b).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≥ (9 / 8) * (9 / 8) := by
                                          apply mul_le_mul h_Spa_ge' h_Sqb_ge' (by positivity) (by positivity)
                                        have h_calc : (9 / 8 : ℚ) * (9 / 8) = 81 / 64 := by ring
                                        linarith
                                      linarith
                            exfalso; exact h_false
                          · -- if S_m has valuation ≠ -3
                            have h_val_ne_one : padicValRat 2 (((2^5 * m : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) ≠ 1 := by
                              rw [h_S_eq_2]
                              have h_S32_nz : (2^5).divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≠ 0 := by
                                rw [S_thirty_two_eq]
                                norm_num
                              have h_Sm_nz : m.divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≠ 0 := by
                                rw [h_Sm]
                                have : 0 < Sm := by
                                  rw [← h_Sm]
                                  exact S_pos m (by omega)
                                exact ne_of_gt this
                              rw [padicValRat.mul h_S32_nz h_Sm_nz]
                              rw [h_S32_val]
                              rw [h_Sm]
                              omega
                            have h_prod_ge' : (∑ d ∈ (2^5 * m : ℕ).divisors, (1 : ℚ) / ↑((sigma 1) d) : ℚ) ≥ 2 := by
                              rw [← h_S5] at h_prod_ge
                              exact h_prod_ge
                            have h_not_int : ((2^5 * m : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)).den ≠ 1 :=
                              not_int_of_between_two_three_and_v2_ne_one h_prod_ge' h_S_lt3 h_val_ne_one
                            rw [← h_n_eq] at h_not_int
                            exfalso; exact h_not_int h_den
                    · -- k ≥ 7
                      have hk7 : 7 ≤ k := by omega
                      have h_S2k_ge : ((2^k).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≥ 33790906 / 21082635 := by
                        have hdvd : 2^7 ∣ 2^k := by
                          have : k = 7 + (k - 7) := by omega
                          rw [this, pow_add]
                          exact dvd_mul_right (2^7) (2^(k-7))
                        have h_S2k_ge' := S_le_S_of_dvd (ne_of_gt (by positivity)) (by decide) hdvd
                        have h_S128 : ((2^7 : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = 33790906 / 21082635 := S_one_twenty_eight_eq
                        rwa [h_S128] at h_S2k_ge'
                      have h_Sm_ge : (m.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≥ 1 := S_ge_one m (by omega)
                      by_cases hval_2k_le2 : padicValRat 2 ((2^k).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≤ 2
                      · have h_val_le : padicValRat 2 (((2^k * m : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) ≤ 0 := by
                          rw [h_S_eq_2]
                          have h_S2k_nz : (2^k).divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≠ 0 := by
                            have : 0 < (2^k).divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := S_pos (2^k) (Nat.one_le_pow k 2 (by decide))
                            exact ne_of_gt this
                          have h_Sm_nz : m.divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≠ 0 := by
                            have : 0 < m.divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := S_pos m (by omega)
                            exact ne_of_gt this
                          rw [padicValRat.mul h_S2k_nz h_Sm_nz]
                          omega
                        have h_prod_gt : (((2^k * m : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) > 1 := by
                          rw [h_S_eq_2]
                          have h_mul : ((2^k).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) * (m.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≥ (33790906 / 21082635) * 1 := by
                            apply mul_le_mul h_S2k_ge h_Sm_ge (by linarith) (by positivity)
                          have : (33790906 / 21082635 : ℚ) * 1 > 1 := by norm_num
                          linarith
                        have h_not_int : ((2^k * m : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)).den ≠ 1 :=
                          not_int_of_between_one_three_and_v2_le_zero h_prod_gt h_S_lt3 h_val_le
                        rw [← h_n_eq] at h_not_int
                        exfalso; exact h_not_int h_den
                      · have h_not_int : ((2^k * m : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)).den ≠ 1 := by
                          intro h_int
                          have h_eq : ((2^k * m : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = 2 := by
                            have h_gt : ((2^k * m : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) > 1 := by
                              rw [h_S_eq_2]
                              have h_mul : ((2^k).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) * (m.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≥ (33790906 / 21082635) * 1 := by
                                apply mul_le_mul h_S2k_ge h_Sm_ge (by linarith) (by positivity)
                              have : (33790906 / 21082635 : ℚ) * 1 > 1 := by norm_num
                              linarith
                            generalize h_S : ((2^k * m : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = S_prod at *
                            have h_nd : S_prod = (S_prod.num : ℚ) := by
                              have h_den_val : S_prod.den = 1 := h_int
                              nth_rw 1 [← Rat.num_div_den S_prod]
                              rw [h_den_val, Nat.cast_one, div_one]
                            have h_ge : 2 ≤ S_prod.num := by
                              rw [h_nd] at h_gt
                              exact_mod_cast h_gt
                            have h_lt : S_prod.num < 3 := by
                              have h_lt' : S_prod < 3 := h_S_lt3
                              rw [h_nd] at h_lt'
                              exact_mod_cast h_lt'
                            have h_eq2 : S_prod.num = 2 := by omega
                            rw [h_nd, h_eq2]
                            rfl
                          have h_Sm_le : (m.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) < 5 / 4 := by
                            rw [h_S_eq_2] at h_eq
                            have h_S2k_pos : ((2^k).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) > 0 := by
                              have : 0 < (2^k).divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := S_pos (2^k) (Nat.one_le_pow k 2 (by decide))
                              exact_mod_cast this
                            have h_Sm_eq_div : (m.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = 2 / ((2^k).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := by
                              have : ((2^k).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) * (m.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = 2 := h_eq
                              rw [mul_comm] at this
                              rw [← eq_div_iff (by linarith)] at this
                              exact this
                            rw [h_Sm_eq_div]
                            have h_calc : 2 / ((2^k).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≤ 2 / (33790906 / 21082635) := by
                              apply div_le_div_of_nonneg_left (by norm_num) (by linarith) h_S2k_ge
                            have h_calc2 : 2 / (33790906 / 21082635 : ℚ) < 5 / 4 := by norm_num
                            linarith
                          have h_Sm_ge_54 : (m.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≥ 5 / 4 := by
                            have h_Spa_ge : 1 + 1 / ((p : ℚ) + 1) ≤ ((p^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := S_prime_power_ge hp a ha
                            have h_Sqb_ge : 1 + 1 / ((q : ℚ) + 1) ≤ ((q^b).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := S_prime_power_ge hq b hb
                            have h_Sm_eq : (m.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = ((p^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) * ((q^b).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := by
                              rw [h_S_m_eq, hm'_eq'']
                            by_cases hp3 : p = 3
                            · subst hp3
                              have hp3_prime : Nat.Prime 3 := by decide
                              have h_Spa_ge2 : ((3^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≥ 5 / 4 := by
                                have h_ge := S_prime_power_ge hp3_prime a ha
                                linarith
                              have h_Sqb_ge' : ((q^b).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≥ 1 := by
                                have : 1 + 1 / ((q : ℚ) + 1) ≤ ((q^b).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := h_Sqb_ge
                                have : 1 / ((q : ℚ) + 1) > 0 := by positivity
                                linarith
                              rw [h_Sm_eq]
                              have : ((3^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) * ((q^b).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≥ (5 / 4) * 1 := by
                                apply mul_le_mul h_Spa_ge2 h_Sqb_ge' (by positivity) (by positivity)
                              linarith
                            · by_cases hq3 : q = 3
                              · subst hq3
                                have hp3_prime : Nat.Prime 3 := by decide
                                have h_Sqb_ge2 : ((3^b).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≥ 5 / 4 := by
                                  have h_ge := S_prime_power_ge hp3_prime b hb
                                  linarith
                                have h_Spa_ge' : ((p^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≥ 1 := by
                                  have : 1 + 1 / ((p : ℚ) + 1) ≤ ((p^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := h_Spa_ge
                                  have : 1 / ((p : ℚ) + 1) > 0 := by positivity
                                  linarith
                                rw [h_Sm_eq]
                                have : ((p^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) * ((3^b).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≥ 1 * (5 / 4) := by
                                  apply mul_le_mul h_Spa_ge' h_Sqb_ge2 (by positivity) (by positivity)
                                linarith
                              · have hp5 : p ≥ 5 := by
                                  by_contra! h_lt
                                  have hp_ge2 : p ≥ 2 := hp.two_le
                                  interval_cases p
                                  · exact hp2_inner rfl
                                  · exact hp3 rfl
                                  · have : ¬ Nat.Prime 4 := by decide
                                    exact this hp
                                have hq2 : q ≠ 2 := by
                                    intro hq2_eq
                                    subst hq2_eq
                                    have : 2 ∣ m := by
                                      rw [hm_eq', hm'_eq'']
                                      exact dvd_mul_of_dvd_right (dvd_pow_self 2 hb_nz) (p^a)
                                    have : m % 2 = 0 := Nat.mod_eq_zero_of_dvd this
                                    omega
                                have hq5 : q ≥ 5 := by
                                  by_contra! h_lt
                                  have hq_ge2 : q ≥ 2 := hq.two_le
                                  interval_cases q
                                  · exact hq2 rfl
                                  · exact hq3 rfl
                                  · have : ¬ Nat.Prime 4 := by decide
                                    exact this hq
                                have h_pq_dist : p ≠ q := hp_neq_q
                                have h_max_ge7 : p ≥ 7 ∨ q ≥ 7 := by
                                  by_contra! h_both_lt
                                  have hp6 : p ≠ 6 := by
                                    intro hp6
                                    subst hp6
                                    have : ¬ Nat.Prime 6 := by decide
                                    exact this hp
                                  have hq6 : q ≠ 6 := by
                                    intro hq6
                                    subst hq6
                                    have : ¬ Nat.Prime 6 := by decide
                                    exact this hq
                                  have : p = 5 ∧ q = 5 := by omega
                                  have : p = q := by omega
                                  exact h_pq_dist this
                                rcases h_max_ge7 with hp7 | hq7
                                · have hp7' : (p : ℚ) ≥ 7 := by exact_mod_cast hp7
                                  have hp_denom : (p : ℚ) + 1 ≥ 8 := by linarith
                                  have hq_denom : (q : ℚ) + 1 ≥ 6 := by linarith
                                  have h_Spa_ge' : ((p^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≥ 9 / 8 := by
                                    have : 1 + 1 / ((p : ℚ) + 1) ≤ ((p^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := h_Spa_ge
                                    have h_inv : 1 / ((p : ℚ) + 1) ≥ 1 / 8 := by
                                      apply one_div_le_one_div_of_le (by positivity) hp_denom
                                    linarith
                                  have h_Sqb_ge' : ((q^b).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≥ 7 / 6 := by
                                    have : 1 + 1 / ((q : ℚ) + 1) ≤ ((q^b).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := h_Sqb_ge
                                    have h_inv : 1 / ((q : ℚ) + 1) ≥ 1 / 6 := by
                                      apply one_div_le_one_div_of_le (by positivity) hq_denom
                                    linarith
                                  have h_Sm_ge_2116 : (m.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≥ 21 / 16 := by
                                    rw [h_Sm_eq]
                                    have : ((p^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) * ((q^b).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≥ (9 / 8) * (7 / 6) := by
                                      apply mul_le_mul h_Spa_ge' h_Sqb_ge' (by positivity) (by positivity)
                                    have h_calc : (9 / 8 : ℚ) * (7 / 6) = 21 / 16 := by norm_num
                                    linarith
                                  linarith
                                · have hq7' : (q : ℚ) ≥ 7 := by exact_mod_cast hq7
                                  have hp_denom : (p : ℚ) + 1 ≥ 6 := by linarith
                                  have hq_denom : (q : ℚ) + 1 ≥ 8 := by linarith
                                  have h_Spa_ge' : ((p^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≥ 7 / 6 := by
                                    have : 1 + 1 / ((p : ℚ) + 1) ≤ ((p^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := h_Spa_ge
                                    have h_inv : 1 / ((p : ℚ) + 1) ≥ 1 / 6 := by
                                      apply one_div_le_one_div_of_le (by positivity) hp_denom
                                    linarith
                                  have h_Sqb_ge' : ((q^b).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≥ 9 / 8 := by
                                    have : 1 + 1 / ((q : ℚ) + 1) ≤ ((q^b).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := h_Sqb_ge
                                    have h_inv : 1 / ((q : ℚ) + 1) ≥ 1 / 8 := by
                                      apply one_div_le_one_div_of_le (by positivity) hq_denom
                                    linarith
                                  have h_Sm_ge_2116 : (m.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≥ 21 / 16 := by
                                    rw [h_Sm_eq]
                                    have : ((p^a).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) * ((q^b).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≥ (7 / 6) * (9 / 8) := by
                                      apply mul_le_mul h_Spa_ge' h_Sqb_ge' (by positivity) (by positivity)
                                    have h_calc : (7 / 6 : ℚ) * (9 / 8) = 21 / 16 := by norm_num
                                    linarith
                                  linarith
                          linarith
                        rw [← h_n_eq] at h_not_int
                        exfalso; exact h_not_int h_den                      
                ·
                  have hm'_ne : m' ≠ 1 := by omega
                  have h_S_lt3 : (((2^k * m : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) < 3 := by
                    rw [h_eq]
                    norm_num
                  have ⟨q, hq, hdvd_q⟩ := Nat.exists_prime_and_dvd hm'_ne
                  let b := padicValNat q m'
                  have hq_fact : Fact q.Prime := ⟨hq⟩
                  have hb : 1 ≤ b := one_le_padicValNat_of_dvd (by omega) hdvd_q
                  have hm'_nz : m' ≠ 0 := by omega
                  have hdvd_qb : q^b ∣ m' := pow_padicValNat_dvd
                  rcases hdvd_qb with ⟨m'', hm'_eq⟩
                  have h_coprime_qm'' : Nat.Coprime (q^b) m'' := by
                    have h_cop_qm'' : Nat.Coprime q m'' := by
                      rw [hq.coprime_iff_not_dvd]
                      intro hq_dvd_m''
                      rcases hq_dvd_m'' with ⟨w, hw⟩
                      have h_div : q^(b + 1) ∣ m' := by
                        rw [hm'_eq, hw]
                        use w
                        ring
                      have h_not := pow_succ_padicValNat_not_dvd (p := q) hm'_nz
                      exact h_not h_div
                    exact h_cop_qm''.pow_left b
                  have hm''_gt_one : 1 < m'' := by
                    by_contra! h_le
                    have h_or : m'' = 0 ∨ m'' = 1 := by omega
                    rcases h_or with rfl | rfl
                    · rw [mul_zero] at hm'_eq
                      omega
                    · rw [mul_one] at hm'_eq
                      have : m' = q^b := hm'_eq
                      exact hm'_pow ⟨q, hq, b, this⟩
                  have h_qb_gt_one : 1 < q^b := by
                    have hq_pos : 2 ≤ q := hq.two_le
                    have : q^1 ≤ q^b := Nat.pow_le_pow_right (by omega) hb
                    rw [pow_one] at this
                    omega
                  have h_qb_odd : (q^b) % 2 = 1 := by
                    have : (q^b * m'') % 2 = 1 := by rwa [← hm'_eq]
                    rw [Nat.mul_mod] at this
                    by_contra! h_even
                    have h_zero : q^b % 2 = 0 := by omega
                    rw [h_zero, zero_mul, Nat.zero_mod] at this
                    omega
                  have hm''_odd : m'' % 2 = 1 := by
                    have : (q^b * m'') % 2 = 1 := by rwa [← hm'_eq]
                    rw [Nat.mul_mod] at this
                    by_contra! h_even
                    have h_zero : m'' % 2 = 0 := by omega
                    rw [h_zero, mul_zero, Nat.zero_mod] at this
                    omega
                  have h_S_m'_eq : ((m'.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) =
                    ((q^b).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) *
                    (m''.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := by
                    rw [← sum_f_eq_sum_recip m' hm'_gt_one]
                    rw [← sum_f_eq_sum_recip (q^b) h_qb_gt_one]
                    rw [← sum_f_eq_sum_recip m'' hm''_gt_one]
                    rw [← f_mul_zeta_apply m']
                    rw [← f_mul_zeta_apply (q^b)]
                    rw [← f_mul_zeta_apply m'']
                    rw [hm'_eq]
                    exact S_mul_of_coprime h_coprime_qm''
                  have h_Sqb_nz_inner : (q^b).divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≠ 0 := by
                    have : 0 < (q^b).divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := S_pos (q^b) (by omega)
                    exact ne_of_gt this
                  have h_Sm''_nz_inner : m''.divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≠ 0 := by
                    have : 0 < m''.divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := S_pos m'' (by omega)
                    exact ne_of_gt this
                  have hval_qb := padicValRat_two_S_odd_neg (q^b) (by have : q^1 ≤ q^b := Nat.pow_le_pow_right hq.pos hb; rw [pow_one] at this; omega) h_qb_odd
                  have hval_m'' := padicValRat_two_S_odd_neg m'' hm''_gt_one hm''_odd
                  have hval_qb_le : padicValRat 2 ((q^b).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≤ -1 := by omega
                  have hval_m''_le' : padicValRat 2 (m''.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≤ -1 := by omega
                  have hval_m'_le : padicValRat 2 ((m'.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) ≤ -2 := by
                    rw [h_S_m'_eq]
                    rw [padicValRat.mul h_Sqb_nz_inner h_Sm''_nz_inner]
                    omega
                  have hval_m_le3 : padicValRat 2 ((m.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) ≤ -3 := by
                    rw [h_S_m_eq]
                    rw [padicValRat.mul h_Sqb_nz h_Sm''_nz]
                    omega
                  by_cases hval_2k_le2 : padicValRat 2 ((2^k).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≤ 2
                  · have h_val_lt : padicValRat 2 (((2^k * m : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) < 0 := by
                      rw [h_S_eq_2]
                      have h_S2k_nz : (2^k).divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≠ 0 := by
                        have : 0 < (2^k).divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := S_pos (2^k) (by have : 2^3 ≤ 2^k := Nat.pow_le_pow_right (show 0 < 2 by decide) hk_ge3; omega)
                        exact ne_of_gt this
                      have h_Sm_nz : m.divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≠ 0 := by
                        have : 0 < m.divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := S_pos m (by omega)
                        exact ne_of_gt this
                      rw [padicValRat.mul h_S2k_nz h_Sm_nz]
                      omega
                    have h_not_int : ((2^k * m : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)).den ≠ 1 :=
                      not_integer_of_padicVal_neg Nat.prime_two h_val_lt
                    rw [← h_n_eq] at h_not_int
                    exact h_not_int h_den
                  · -- Here padicValRat 2 S(2^k) ≥ 3.
                    by_cases hval_2k_le3 : padicValRat 2 ((2^k).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≤ 3
                    · -- hval_2k_le3 is true
                      by_cases h_lt2 : (((2^k * m : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) < 2
                      · have h_prod_gt : (((2^k * m : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) > 1 := S_gt_one (2^k * m) h_2k_m_gt
                        have h_val_le : padicValRat 2 (((2^k * m : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) ≤ 0 := by
                          rw [h_S_eq_2]
                          have h_S2k_nz : (2^k).divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≠ 0 := by
                            have : 0 < (2^k).divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := S_pos (2^k) (by have : 2^3 ≤ 2^k := Nat.pow_le_pow_right (show 0 < 2 by decide) hk_ge3; omega)
                            exact ne_of_gt this
                          have h_Sm_nz : m.divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≠ 0 := by
                            have : 0 < m.divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := S_pos m (by omega)
                            exact ne_of_gt this
                          rw [padicValRat.mul h_S2k_nz h_Sm_nz]
                          omega
                        have h_not_int : ((2^k * m : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)).den ≠ 1 :=
                          not_int_of_between_one_three_and_v2_le_zero h_prod_gt h_S_lt3 h_val_le
                        rw [← h_n_eq] at h_not_int
                        exfalso; exact h_not_int h_den
                      · have h_prod_ge : (((2^k * m : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) ≥ 2 := by linarith
                        have h_val_ne_one : padicValRat 2 (((2^k * m : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) ≠ 1 := by
                          rw [h_S_eq_2]
                          have h_S2k_nz : (2^k).divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≠ 0 := by
                            have : 0 < (2^k).divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := S_pos (2^k) (by have : 2^3 ≤ 2^k := Nat.pow_le_pow_right (show 0 < 2 by decide) hk_ge3; omega)
                            exact ne_of_gt this
                          have h_Sm_nz : m.divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≠ 0 := by
                            have : 0 < m.divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := S_pos m (by omega)
                            exact ne_of_gt this
                          rw [padicValRat.mul h_S2k_nz h_Sm_nz]
                          omega
                        have h_not_int : ((2^k * m : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)).den ≠ 1 :=
                          not_int_of_between_two_three_and_v2_ne_one h_prod_ge h_S_lt3 h_val_ne_one
                        rw [← h_n_eq] at h_not_int
                        exfalso; exact h_not_int h_den
                    · -- hval_2k_le3 is false, so padicVal_2 S(2^k) ≥ 4
                      by_cases h_lt2 : (((2^k * m : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) < 2
                      · have h_prod_gt : (((2^k * m : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) > 1 := S_gt_one (2^k * m) h_2k_m_gt
                        have h_not_int : ((2^k * m : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)).den ≠ 1 :=
                          den_neq_one_of_between h_prod_gt h_lt2
                        rw [← h_n_eq] at h_not_int
                        exfalso; exact h_not_int h_den
                      · have h_prod_ge : (((2^k * m : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) ≥ 2 := by linarith
                        have h_val_ne_one : padicValRat 2 (((2^k * m : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) ≠ 1 := by
                          rw [h_S_eq_2]
                          have h_S2k_nz : (2^k).divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≠ 0 := by
                            have : 0 < (2^k).divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := S_pos (2^k) (Nat.one_le_pow k 2 (by decide))
                            exact ne_of_gt this
                          have h_Sm_nz : m.divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) ≠ 0 := by
                            have : 0 < m.divisors.sum (fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := S_pos m (by omega)
                            exact ne_of_gt this
                          rw [padicValRat.mul h_S2k_nz h_Sm_nz]
                          omega
                        have h_not_int : ((2^k * m : ℕ).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)).den ≠ 1 :=
                          not_int_of_between_two_three_and_v2_ne_one h_prod_ge h_S_lt3 h_val_ne_one
                        rw [← h_n_eq] at h_not_int
                        exfalso; exact h_not_int h_den

#print axioms oeis_265709_conjecture_0.disproof


