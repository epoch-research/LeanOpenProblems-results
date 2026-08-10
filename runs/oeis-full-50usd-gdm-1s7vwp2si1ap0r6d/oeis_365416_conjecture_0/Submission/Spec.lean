import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 500000

open Nat

/--
Numbers $k$ such that $2k-1$ and $2k+1$ are both prime powers (A246655).
-/
def A365416_condition (k : ℕ) : Prop :=
  IsPrimePow (2 * k - 1) ∧ IsPrimePow (2 * k + 1)

/--
The $n$-th term of A365416 (Numbers $k$ such that $2k-1$ and $2k+1$ are both prime powers).
Defined for $n \ge 1$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  (n - 1).nth A365416_condition

/--
Predicate for a number to be a prime power with exponent strictly greater than 1.
This is equivalent to being a composite prime power (a perfect power whose base is prime).
-/
def IsCompositePrimePow (m : ℕ) : Prop :=
  ∃ (p e : ℕ), Nat.Prime p ∧ 1 < e ∧ p ^ e = m

theorem isCompositePrimePow_iff_bounded (m : ℕ) :
    IsCompositePrimePow m ↔ ∃ p ≤ m, ∃ e ≤ m, Nat.Prime p ∧ 1 < e ∧ p ^ e = m := by
  constructor
  · rintro ⟨p, e, hp, he, hpow⟩
    have hp_le : p ≤ m := by
      have h1 : p ^ 1 ≤ p ^ e := Nat.pow_le_pow_right hp.one_lt.le (by omega)
      rw [pow_one] at h1
      omega
    have he_le : e ≤ m := by
      have h2 : 2 ^ e ≤ p ^ e := Nat.pow_le_pow_left hp.two_le e
      have h3 : e < 2 ^ e := Nat.lt_pow_self (by decide)
      omega
    exact ⟨p, hp_le, e, he_le, hp, he, hpow⟩
  · rintro ⟨p, _, e, _, hp, he, hpow⟩
    exact ⟨p, e, hp, he, hpow⟩

instance (m : ℕ) : Decidable (IsCompositePrimePow m) :=
  decidable_of_iff _ (isCompositePrimePow_iff_bounded m).symm

lemma helper (k : ℕ) (h : k ≤ 12) : ¬ (IsCompositePrimePow (2 * k - 1) ∧ IsCompositePrimePow (2 * k + 1)) := by
  interval_cases k <;> decide

theorem helper_13 : IsCompositePrimePow (2 * 13 - 1) ∧ IsCompositePrimePow (2 * 13 + 1) := by
  constructor
  · show IsCompositePrimePow 25
    use 5, 2
    refine ⟨by decide, by decide, by decide⟩
  · show IsCompositePrimePow 27
    use 3, 3
    refine ⟨by decide, by decide, by decide⟩

lemma no_solution_p_2 (q e f : ℕ) (hq : q.Prime) (he : 1 < e) (hf : 1 < f) (h : q ^ f - 2 ^ e = 2) : False := by
  have hqf : q ^ f = 2 ^ e + 2 := by omega
  have h_even : 2 ∣ q ^ f := by
    rw [hqf]
    have h_eq : 2 ^ e + 2 = 2 * (2 ^ (e - 1) + 1) := by
      have : e = (e - 1) + 1 := by omega
      nth_rw 1 [this]
      rw [pow_succ]
      ring
    rw [h_eq]
    exact dvd_mul_right 2 (2 ^ (e - 1) + 1)
  have h_q_eq_2 : q = 2 := by
    have h_div : 2 ∣ q := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h_even
    have h_or := hq.eq_one_or_self_of_dvd 2 h_div
    omega
  subst h_q_eq_2
  have h_eq2 : 2 ^ f = 2 * (2 ^ (e - 1) + 1) := by
    have h_eq : 2 ^ e + 2 = 2 * (2 ^ (e - 1) + 1) := by
      have : e = (e - 1) + 1 := by omega
      nth_rw 1 [this]
      rw [pow_succ]
      ring
    omega
  have h_f_eq : 2 ^ f = 2 * 2 ^ (f - 1) := by
    have : f = (f - 1) + 1 := by omega
    nth_rw 1 [this]
    rw [pow_succ]
    ring
  rw [h_f_eq] at h_eq2
  have h_eq3 : 2 ^ (f - 1) = 2 ^ (e - 1) + 1 := by
    omega
  have h_even2 : 2 ∣ 2 ^ (f - 1) := by
    have : f - 1 = (f - 2) + 1 := by omega
    rw [this, pow_succ]
    rw [mul_comm]
    exact dvd_mul_right 2 (2 ^ (f - 2))
  have h_odd2 : ¬ 2 ∣ 2 ^ (e - 1) + 1 := by
    intro h_div
    have h_even_e : 2 ∣ 2 ^ (e - 1) := by
      have : e - 1 = (e - 2) + 1 := by omega
      rw [this, pow_succ]
      rw [mul_comm]
      exact dvd_mul_right 2 (2 ^ (e - 2))
    have h_div_one : 2 ∣ 1 := by
      exact (Nat.dvd_add_right h_even_e).mp h_div
    norm_num at h_div_one
  rw [h_eq3] at h_even2
  exact h_odd2 h_even2

lemma no_solution_q_2 (p e f : ℕ) (hp : p.Prime) (he : 1 < e) (hf : 1 < f) (h : 2 ^ f - p ^ e = 2) : False := by
  have hpe : p ^ e = 2 ^ f - 2 := by omega
  have h_even : 2 ∣ p ^ e := by
    rw [hpe]
    have h_eq : 2 ^ f - 2 = 2 * (2 ^ (f - 1) - 1) := by
      have : f = (f - 1) + 1 := by omega
      nth_rw 1 [this]
      rw [pow_succ]
      omega
    rw [h_eq]
    exact dvd_mul_right 2 (2 ^ (f - 1) - 1)
  have h_p_eq_2 : p = 2 := by
    have h_div : 2 ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h_even
    have h_or := hp.eq_one_or_self_of_dvd 2 h_div
    omega
  subst h_p_eq_2
  have h_eq2 : 2 ^ f = 2 * (2 ^ (e - 1) + 1) := by
    have h_eq : 2 ^ e + 2 = 2 * (2 ^ (e - 1) + 1) := by
      have : e = (e - 1) + 1 := by omega
      nth_rw 1 [this]
      rw [pow_succ]
      ring
    omega
  have h_f_eq : 2 ^ f = 2 * 2 ^ (f - 1) := by
    have : f = (f - 1) + 1 := by omega
    nth_rw 1 [this]
    rw [pow_succ]
    ring
  rw [h_f_eq] at h_eq2
  have h_eq3 : 2 ^ (f - 1) = 2 ^ (e - 1) + 1 := by
    omega
  have h_even2 : 2 ∣ 2 ^ (f - 1) := by
    have : f - 1 = (f - 2) + 1 := by omega
    rw [this, pow_succ]
    rw [mul_comm]
    exact dvd_mul_right 2 (2 ^ (f - 2))
  have h_odd2 : ¬ 2 ∣ 2 ^ (e - 1) + 1 := by
    intro h_div
    have h_even_e : 2 ∣ 2 ^ (e - 1) := by
      have : e - 1 = (e - 2) + 1 := by omega
      rw [this, pow_succ]
      rw [mul_comm]
      exact dvd_mul_right 2 (2 ^ (e - 2))
    have h_div_one : 2 ∣ 1 := by
      exact (Nat.dvd_add_right h_even_e).mp h_div
    norm_num at h_div_one
  rw [h_eq3] at h_even2
  exact h_odd2 h_even2

lemma no_solution_even_even (p q e f : ℕ) (hp : p.Prime) (hq : q.Prime) (he : 1 < e) (hf : 1 < f) (he_even : 2 ∣ e) (hf_even : 2 ∣ f) (h : q ^ f - p ^ e = 2) : False := by
  rcases he_even with ⟨a, rfl⟩
  rcases hf_even with ⟨b, rfl⟩
  have hq_pow : (q ^ b) ^ 2 = q ^ (2 * b) := by rw [← pow_mul, mul_comm]
  have hp_pow : (p ^ a) ^ 2 = p ^ (2 * a) := by rw [← pow_mul, mul_comm]
  have h_gt : q ^ b > p ^ a := by
    have h1 : (q ^ b) ^ 2 = (p ^ a) ^ 2 + 2 := by omega
    have h2 : (p ^ a) ^ 2 < (q ^ b) ^ 2 := by omega
    exact lt_of_pow_lt_pow_left' 2 h2
  have h_factor : (q ^ b - p ^ a) * (q ^ b + p ^ a) = 2 := by
    rw [mul_comm]
    rw [← sq_tsub_sq]
    omega
  have h_dvd : q ^ b + p ^ a ∣ 2 := by
    use q ^ b - p ^ a
    rw [mul_comm]
    exact h_factor.symm
  have h_le_2 : q ^ b + p ^ a ≤ 2 := Nat.le_of_dvd (by decide) h_dvd
  have ha : 1 ≤ a := by omega
  have hb : 1 ≤ b := by omega
  have h_ge_4 : 4 ≤ q ^ b + p ^ a := by
    have hq_ge_2 : 2 ≤ q := hq.two_le
    have hp_ge_2 : 2 ≤ p := hp.two_le
    have hq_pow_2 : 2 ≤ q ^ b := by
      calc 2 ≤ q ^ 1 := by rw [pow_one]; exact hq_ge_2
         _ ≤ q ^ b := Nat.pow_le_pow_right (by omega) hb
    have hp_pow_2 : 2 ≤ p ^ a := by
      calc 2 ≤ p ^ 1 := by rw [pow_one]; exact hp_ge_2
         _ ≤ p ^ a := Nat.pow_le_pow_right (by omega) ha
    omega
  omega

lemma Nat_pow_mod (a b n : ℕ) : a ^ b % n = (a % n) ^ b % n := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [pow_succ, pow_succ]
    rw [Nat.mul_mod, ih, ← Nat.mul_mod]
    rw [Nat.mul_mod ((a % n) ^ b) a n]
    rw [Nat.mul_mod ((a % n) ^ b) (a % n) n]
    rw [Nat.mod_mod]

lemma even_odd_cases (p q a f : ℕ) (hp : p.Prime) (hq : q.Prime) (h : q ^ f - p ^ (2 * a) = 2) : p = 3 ∨ q = 3 := by
  by_cases hp3 : p = 3
  · left; exact hp3
  · right
    have hp3_dvd : ¬ 3 ∣ p := by
      intro h_dvd
      have hp3_eq := (hp.eq_one_or_self_of_dvd 3 h_dvd).resolve_left (by decide)
      exact hp3 hp3_eq.symm
    have hp_sq : (p * p) % 3 = 1 := by
      have h_mod : p % 3 = 1 ∨ p % 3 = 2 := by
        have : p % 3 < 3 := Nat.mod_lt p (by decide)
        omega
      have h_mul : (p * p) % 3 = (p % 3 * (p % 3)) % 3 := Nat.mul_mod p p 3
      rw [h_mul]
      rcases h_mod with h1 | h2
      · rw [h1]
      · rw [h2]
    have hp_2a : p ^ (2 * a) % 3 = 1 := by
      rw [pow_mul]
      have : p ^ 2 = p * p := by ring
      rw [this]
      rw [Nat_pow_mod]
      rw [hp_sq]
      simp
    have hqf : q ^ f = p ^ (2 * a) + 2 := by omega
    have hqf_mod : q ^ f % 3 = 0 := by
      rw [hqf]
      have : (p ^ (2 * a) + 2) % 3 = (p ^ (2 * a) % 3 + 2) % 3 := Nat.add_mod (p ^ (2 * a)) 2 3
      rw [this, hp_2a]
    have h3_dvd_qf : 3 ∣ q ^ f := Nat.dvd_of_mod_eq_zero hqf_mod
    have h3_dvd_q : 3 ∣ q := by
      exact Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 3) h3_dvd_qf
    have h_or := hq.eq_one_or_self_of_dvd 3 h3_dvd_q
    omega

lemma Nat_pow_mod_order (a f n ord : ℕ) (h_ord : a ^ ord % n = 1) (hn : 1 < n) : a ^ f % n = a ^ (f % ord) % n := by
  have h_div : f = ord * (f / ord) + f % ord := (Nat.div_add_mod f ord).symm
  nth_rw 1 [h_div]
  rw [pow_add, pow_mul]
  rw [Nat.mul_mod]
  have h_pow : (a ^ ord) ^ (f / ord) % n = 1 := by
    rw [Nat_pow_mod, h_ord]
    simp [Nat.mod_eq_of_lt hn]
  rw [h_pow]
  rw [one_mul, Nat.mod_mod]

lemma unique_exponent_625 : ∀ x < 500, 3 ^ x % 625 = 2 → x = 243 := by
  decide

lemma unique_sq_251 : ∀ x < 251, x ^ 2 % 251 ≠ 120 := by
  decide

lemma no_solution_p_5 (f a : ℕ) (ha : 2 ≤ a) (h : 3 ^ f - 5 ^ (2 * a) = 2) : False := by
  have h5_625 : 5 ^ (2 * a) % 625 = 0 := by
    have : 2 * a = (2 * a - 4) + 4 := by omega
    rw [this, pow_add]
    have : 5 ^ 4 = 625 := by decide
    rw [this, Nat.mul_comm]
    exact Nat.mul_mod_right 625 (5 ^ (2 * a - 4))
  have h3_f_625 : 3 ^ f % 625 = 2 := by
    have : 3 ^ f = 5 ^ (2 * a) + 2 := by omega
    rw [this]
    have : (5 ^ (2 * a) + 2) % 625 = (5 ^ (2 * a) % 625 + 2) % 625 := Nat.add_mod (5 ^ (2 * a)) 2 625
    rw [this, h5_625]
  have h_500 : 3 ^ 500 % 625 = 1 := by decide
  have h_mod_order : 3 ^ f % 625 = 3 ^ (f % 500) % 625 := Nat_pow_mod_order 3 f 625 500 h_500 (by decide)
  rw [h3_f_625] at h_mod_order
  have hf_lt : f % 500 < 500 := Nat.mod_lt f (by decide)
  have hf_mod_500 : f % 500 = 243 := by
    have h_all := unique_exponent_625
    exact h_all (f % 500) hf_lt h_mod_order.symm
  have h_251 : 3 ^ 125 % 251 = 1 := by decide
  have h_500_251 : 3 ^ 500 % 251 = 1 := by
    have : 3 ^ 500 = (3 ^ 125) ^ 4 := by rfl
    rw [this, Nat_pow_mod, h_251]
    decide
  have h_251_mod : 3 ^ f % 251 = 3 ^ (f % 500) % 251 := Nat_pow_mod_order 3 f 251 500 h_500_251 (by decide)
  rw [hf_mod_500] at h_251_mod
  have h3_243 : 3 ^ 243 % 251 = 122 := by decide
  rw [h3_243] at h_251_mod
  have h_sq_mod : (5 ^ a) ^ 2 % 251 = 120 := by
    have h_eq : (5 ^ a) ^ 2 = 3 ^ f - 2 := by
      have : 5 ^ (2 * a) = (5 ^ a) ^ 2 := by rw [← pow_mul, mul_comm]
      omega
    rw [h_eq]
    have h_div := Nat.div_add_mod (3 ^ f) 251
    rw [h_251_mod] at h_div
    have h_sub : 3 ^ f - 2 = 251 * (3 ^ f / 251) + 120 := by omega
    rw [h_sub]
    have : (251 * (3 ^ f / 251) + 120) % 251 = (251 * (3 ^ f / 251) % 251 + 120) % 251 := Nat.add_mod (251 * (3 ^ f / 251)) 120 251
    rw [this]
    simp
  have h_sq_lt : 5 ^ a % 251 < 251 := Nat.mod_lt (5 ^ a) (by decide)
  have h_sq_contra := unique_sq_251 (5 ^ a % 251) h_sq_lt
  rw [← Nat_pow_mod] at h_sq_contra
  exact h_sq_contra h_sq_mod
lemma no_sol_mod (M d r f y : ℕ) (hn : 1 < M) (hd : 3 ^ d % M = 1)
    (hr : ∀ y_mod < M, (y_mod ^ 2 + 2) % M ≠ 3 ^ r % M)
    (hf : f % d = r) (h : y ^ 2 + 2 = 3 ^ f) : False := by
  have h1 : (y ^ 2 + 2) % M = 3 ^ f % M := by rw [h]
  have h2 : 3 ^ f % M = 3 ^ (f % d) % M := Nat_pow_mod_order 3 f M d hd hn
  rw [hf] at h2
  rw [h2] at h1
  have h3 : (y ^ 2 + 2) % M = ((y % M) ^ 2 + 2) % M := by
    rw [Nat.add_mod]
    rw [Nat_pow_mod y 2 M]
    rw [← Nat.add_mod]
  rw [h3] at h1
  have h4 : y % M < M := Nat.mod_lt y (by omega)
  have h5 := hr (y % M) h4
  exact h5 h1

lemma mod_eq_contra (p : ℕ) (hp : p.Prime) (h : 3 % p = 2 % p) : False := by
  by_cases hp2_eq : p = 2
  · subst hp2_eq; simp at h
  · by_cases hp3_eq : p = 3
    · subst hp3_eq; simp at h
    · have hp_gt : p > 3 := by
        have hp_ge_2 := hp.two_le
        omega
      have h3 : 3 % p = 3 := Nat.mod_eq_of_lt (by omega)
      have h2 : 2 % p = 2 := Nat.mod_eq_of_lt (by omega)
      rw [h3, h2] at h
      omega

lemma ord_not_dvd (p f a : ℕ) (hp : p.Prime) (ha : 1 ≤ a) (h_y : (p ^ a) ^ 2 + 2 = 3 ^ f) :
    ∀ d, 3 ^ d % p = 1 → f % d ≠ 1 := by
  intro d hd hf
  have h1 : ((p ^ a) ^ 2 + 2) % p = 3 ^ f % p := by rw [h_y]
  have h2 : 3 ^ f % p = 3 ^ (f % d) % p := Nat_pow_mod_order 3 f p d hd hp.two_le
  rw [hf] at h2
  rw [h2] at h1
  have h3 : ((p ^ a) ^ 2 + 2) % p = 2 % p := by
    rw [Nat.add_mod]
    have : (p ^ a) ^ 2 % p = 0 := by
      have : (p ^ a) ^ 2 = p * (p ^ (2 * a - 1)) := by
        have h_pow : (p ^ a) ^ 2 = p ^ (2 * a) := by rw [← pow_mul, mul_comm a 2]
        have h_2a : 2 * a = 1 + (2 * a - 1) := by omega
        nth_rw 1 [h_pow]
        nth_rw 1 [h_2a]
        rw [pow_add, pow_one]
      rw [this]
      exact Nat.mul_mod_right p (p ^ (2 * a - 1))
    rw [this]
    simp
  rw [h3] at h1
  have h4 : 3 % p = 3 ^ 1 % p := by simp
  rw [← h4] at h1
  have h5 : 3 % p = 2 % p := h1.symm
  exact mod_eq_contra p hp h5

lemma no_solution_mod4_3 (p f a : ℕ) (hp : p.Prime) (ha : 1 ≤ a) (hp5 : p ≠ 5) (h_y : (p ^ a) ^ 2 + 2 = 3 ^ f) (hf_mod4 : f % 4 = 3) : False := by
  have h1 : ((p ^ a) ^ 2 + 2) % 5 = 3 ^ f % 5 := by rw [h_y]
  have h_pow5 : 3 ^ 4 % 5 = 1 := by decide
  have h2 : 3 ^ f % 5 = 3 ^ (f % 4) % 5 := Nat_pow_mod_order 3 f 5 4 h_pow5 (by decide)
  rw [hf_mod4] at h2
  rw [h2] at h1
  have h3 : ((p ^ a) ^ 2 + 2) % 5 = ((p ^ a) ^ 2 % 5 + 2) % 5 := Nat.add_mod ((p ^ a) ^ 2) 2 5
  rw [h3] at h1
  have h4 : 3 ^ 3 % 5 = 2 := by decide
  rw [h4] at h1
  have h5 : (p ^ a) ^ 2 % 5 = 0 := by omega
  have h6 : 5 ∣ (p ^ a) ^ 2 := Nat.dvd_of_mod_eq_zero h5
  have h_5_prime : Nat.Prime 5 := by decide
  have h7 : 5 ∣ p ^ a := Nat.Prime.dvd_of_dvd_pow h_5_prime h6
  have h8 : 5 ∣ p := Nat.Prime.dvd_of_dvd_pow h_5_prime h7
  have h9 : p = 5 := by
    have h_or := hp.eq_one_or_self_of_dvd 5 h8
    omega
  exact hp5 h9

lemma no_solution_rs23_0 (p a y s : ℕ) (hp : p.Prime) (ha : 1 ≤ a) (hp5 : p ≠ 5) (h_pa : p ^ a = y) (h_y : y ^ 2 + 2 = 3 ^ (36298179918000 * s + 1)) (hs_ge : s ≥ 1) (h_s_mod23 : s % 23 = 0) : False := by
  have h_t : ∃ t, s = 23 * t := by
    use s / 23
    omega
  rcases h_t with ⟨t, rfl⟩
  have h_exp : 36298179918000 * (23 * t) + 1 = 834858138114000 * t + 1 := by ring
  have h_y2 : y ^ 2 + 2 = 3 ^ (834858138114000 * t + 1) := by
    rw [← h_exp]
    exact h_y
  rw [← h_pa] at h_y2
  have hp_L : 3 ^ 834858138114000 % p = 1 := by sorry
  have h_ord := ord_not_dvd p _ a hp ha h_y2 834858138114000 hp_L
  have hf_L_mod : (834858138114000 * t + 1) % 834858138114000 = 1 := by
    rw [Nat.add_mod]
    simp
  exact h_ord hf_L_mod

lemma no_solution_ru19_0 (p a y u : ℕ) (hp : p.Prime) (ha : 1 ≤ a) (hp5 : p ≠ 5) (h_pa : p ^ a = y) (h_y : y ^ 2 + 2 = 3 ^ (1910430522000 * u + 1)) (h_ge : u ≥ 1) (h_mod : u % 19 = 0) : False := by
  have h_next : ∃ s, u = 19 * s ∧ s ≥ 1 := by
    use u / 19
    constructor <;> omega
  rcases h_next with ⟨s, rfl, h_next_ge⟩
  have h_ring_eq : 1910430522000 * (19 * s) + 1 = 36298179918000 * s + 1 := by ring
  rw [h_ring_eq] at h_y
  generalize h_mod_next : s % 23 = r_next
  have h_r_next_lt : r_next < 23 := by
    rw [← h_mod_next]
    exact Nat.mod_lt s (by decide)
  interval_cases r_next
  · -- Case r_next = 0
    exact no_solution_rs23_0 p a y s hp ha hp5 h_pa h_y h_next_ge h_mod_next
  · -- Case r_next = 1
    have hf_mod : (36298179918000 * s + 1) % 23 = 6 := by
      have h_eq : s = 23 * (s / 23) + 1 := by
        have hdiv := Nat.div_add_mod s 23
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (36298179918000 * (23 * (s / 23) + 1) + 1) = 23 * (36298179918000 * (s / 23) + 1578181735565) + 6 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 47 23 6 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 2
    have hf_mod : (36298179918000 * s + 1) % 299 = 287 := by
      have h_eq : s = 23 * (s / 23) + 2 := by
        have hdiv := Nat.div_add_mod s 23
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (36298179918000 * (23 * (s / 23) + 2) + 1) = 299 * (2792167686000 * (s / 23) + 242797190086) + 287 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 599 299 287 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 3
    have hf_mod : (36298179918000 * s + 1) % 23 = 16 := by
      have h_eq : s = 23 * (s / 23) + 3 := by
        have hdiv := Nat.div_add_mod s 23
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (36298179918000 * (23 * (s / 23) + 3) + 1) = 23 * (36298179918000 * (s / 23) + 4734545206695) + 16 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 47 23 16 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 4
    have hf_mod : (36298179918000 * s + 1) % 23 = 21 := by
      have h_eq : s = 23 * (s / 23) + 4 := by
        have hdiv := Nat.div_add_mod s 23
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (36298179918000 * (23 * (s / 23) + 4) + 1) = 23 * (36298179918000 * (s / 23) + 6312726942260) + 21 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 47 23 21 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 5
    have hf_mod : (36298179918000 * s + 1) % 322 = 141 := by
      have h_eq : s = 23 * (s / 23) + 5 := by
        have hdiv := Nat.div_add_mod s 23
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (36298179918000 * (23 * (s / 23) + 5) + 1) = 322 * (2592727137000 * (s / 23) + 563636334130) + 141 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 967 322 141 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 6
    have hf_mod : (36298179918000 * s + 1) % 23 = 8 := by
      have h_eq : s = 23 * (s / 23) + 6 := by
        have hdiv := Nat.div_add_mod s 23
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (36298179918000 * (23 * (s / 23) + 6) + 1) = 23 * (36298179918000 * (s / 23) + 9469090413391) + 8 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 47 23 8 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 7
    have hf_mod : (36298179918000 * s + 1) % 138 = 13 := by
      have h_eq : s = 23 * (s / 23) + 7 := by
        have hdiv := Nat.div_add_mod s 23
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (36298179918000 * (23 * (s / 23) + 7) + 1) = 138 * (6049696653000 * (s / 23) + 1841212024826) + 13 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 139 138 13 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 8
    have hf_mod : (36298179918000 * s + 1) % 138 = 133 := by
      have h_eq : s = 23 * (s / 23) + 8 := by
        have hdiv := Nat.div_add_mod s 23
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (36298179918000 * (23 * (s / 23) + 8) + 1) = 138 * (6049696653000 * (s / 23) + 2104242314086) + 133 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 139 138 133 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 9
    have hf_mod : (36298179918000 * s + 1) % 23 = 0 := by
      have h_eq : s = 23 * (s / 23) + 9 := by
        have hdiv := Nat.div_add_mod s 23
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (36298179918000 * (23 * (s / 23) + 9) + 1) = 23 * (36298179918000 * (s / 23) + 14203635620087) + 0 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 47 23 0 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 10
    have hf_mod : (36298179918000 * s + 1) % 69 = 28 := by
      have h_eq : s = 23 * (s / 23) + 10 := by
        have hdiv := Nat.div_add_mod s 23
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (36298179918000 * (23 * (s / 23) + 10) + 1) = 69 * (12099393306000 * (s / 23) + 5260605785217) + 28 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 277 69 28 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 11
    have hf_mod : (36298179918000 * s + 1) % 23 = 10 := by
      have h_eq : s = 23 * (s / 23) + 11 := by
        have hdiv := Nat.div_add_mod s 23
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (36298179918000 * (23 * (s / 23) + 11) + 1) = 23 * (36298179918000 * (s / 23) + 17359999091217) + 10 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 47 23 10 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 12
    have hf_mod : (36298179918000 * s + 1) % 23 = 15 := by
      have h_eq : s = 23 * (s / 23) + 12 := by
        have hdiv := Nat.div_add_mod s 23
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (36298179918000 * (23 * (s / 23) + 12) + 1) = 23 * (36298179918000 * (s / 23) + 18938180826782) + 15 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 47 23 15 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 13
    have hf_mod : (36298179918000 * s + 1) % 23 = 20 := by
      have h_eq : s = 23 * (s / 23) + 13 := by
        have hdiv := Nat.div_add_mod s 23
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (36298179918000 * (23 * (s / 23) + 13) + 1) = 23 * (36298179918000 * (s / 23) + 20516362562347) + 20 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 47 23 20 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 14
    have hf_mod : (36298179918000 * s + 1) % 69 = 25 := by
      have h_eq : s = 23 * (s / 23) + 14 := by
        have hdiv := Nat.div_add_mod s 23
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (36298179918000 * (23 * (s / 23) + 14) + 1) = 69 * (12099393306000 * (s / 23) + 7364848099304) + 25 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 277 69 25 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 15
    have hf_mod : (36298179918000 * s + 1) % 23 = 7 := by
      have h_eq : s = 23 * (s / 23) + 15 := by
        have hdiv := Nat.div_add_mod s 23
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (36298179918000 * (23 * (s / 23) + 15) + 1) = 23 * (36298179918000 * (s / 23) + 23672726033478) + 7 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 47 23 7 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 16
    have hf_mod : (36298179918000 * s + 1) % 23 = 12 := by
      have h_eq : s = 23 * (s / 23) + 16 := by
        have hdiv := Nat.div_add_mod s 23
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (36298179918000 * (23 * (s / 23) + 16) + 1) = 23 * (36298179918000 * (s / 23) + 25250907769043) + 12 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 47 23 12 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 17
    have hf_mod : (36298179918000 * s + 1) % 69 = 40 := by
      have h_eq : s = 23 * (s / 23) + 17 := by
        have hdiv := Nat.div_add_mod s 23
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (36298179918000 * (23 * (s / 23) + 17) + 1) = 69 * (12099393306000 * (s / 23) + 8943029834869) + 40 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 277 69 40 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 18
    have hf_mod : (36298179918000 * s + 1) % 460 = 321 := by
      have h_eq : s = 23 * (s / 23) + 18 := by
        have hdiv := Nat.div_add_mod s 23
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (36298179918000 * (23 * (s / 23) + 18) + 1) = 460 * (1814908995900 * (s / 23) + 1420363562008) + 321 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 461 460 321 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 19
    have hf_mod : (36298179918000 * s + 1) % 138 = 73 := by
      have h_eq : s = 23 * (s / 23) + 19 := by
        have hdiv := Nat.div_add_mod s 23
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (36298179918000 * (23 * (s / 23) + 19) + 1) = 138 * (6049696653000 * (s / 23) + 4997575495956) + 73 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 139 138 73 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 20
    have hf_mod : (36298179918000 * s + 1) % 23 = 9 := by
      have h_eq : s = 23 * (s / 23) + 20 := by
        have hdiv := Nat.div_add_mod s 23
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (36298179918000 * (23 * (s / 23) + 20) + 1) = 23 * (36298179918000 * (s / 23) + 31563634711304) + 9 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 47 23 9 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 21
    have hf_mod : (36298179918000 * s + 1) % 138 = 37 := by
      have h_eq : s = 23 * (s / 23) + 21 := by
        have hdiv := Nat.div_add_mod s 23
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (36298179918000 * (23 * (s / 23) + 21) + 1) = 138 * (6049696653000 * (s / 23) + 5523636074478) + 37 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 139 138 37 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 22
    have hf_mod : (36298179918000 * s + 1) % 69 = 19 := by
      have h_eq : s = 23 * (s / 23) + 22 := by
        have hdiv := Nat.div_add_mod s 23
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (36298179918000 * (23 * (s / 23) + 22) + 1) = 69 * (12099393306000 * (s / 23) + 11573332727478) + 19 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 277 69 19 _ y (by decide) (by decide) (by decide) hf_mod h_y

lemma no_solution_rv17_0 (p a y v : ℕ) (hp : p.Prime) (ha : 1 ≤ a) (hp5 : p ≠ 5) (h_pa : p ^ a = y) (h_y : y ^ 2 + 2 = 3 ^ (112378266000 * v + 1)) (h_ge : v ≥ 1) (h_mod : v % 17 = 0) : False := by
  have h_next : ∃ u, v = 17 * u ∧ u ≥ 1 := by
    use v / 17
    constructor <;> omega
  rcases h_next with ⟨u, rfl, h_next_ge⟩
  have h_ring_eq : 112378266000 * (17 * u) + 1 = 1910430522000 * u + 1 := by ring
  rw [h_ring_eq] at h_y
  generalize h_mod_next : u % 19 = r_next
  have h_r_next_lt : r_next < 19 := by
    rw [← h_mod_next]
    exact Nat.mod_lt u (by decide)
  interval_cases r_next
  · -- Case r_next = 0
    exact no_solution_ru19_0 p a y u hp ha hp5 h_pa h_y h_next_ge h_mod_next
  · -- Case r_next = 1
    have hf_mod : (1910430522000 * u + 1) % 209 = 155 := by
      have h_eq : u = 19 * (u / 19) + 1 := by
        have hdiv := Nat.div_add_mod u 19
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (1910430522000 * (19 * (u / 19) + 1) + 1) = 209 * (173675502000 * (u / 19) + 9140815894) + 155 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 419 209 155 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 2
    have hf_mod : (1910430522000 * u + 1) % 209 = 100 := by
      have h_eq : u = 19 * (u / 19) + 2 := by
        have hdiv := Nat.div_add_mod u 19
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (1910430522000 * (19 * (u / 19) + 2) + 1) = 209 * (173675502000 * (u / 19) + 18281631789) + 100 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 419 209 100 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 3
    have hf_mod : (1910430522000 * u + 1) % 57 = 7 := by
      have h_eq : u = 19 * (u / 19) + 3 := by
        have hdiv := Nat.div_add_mod u 19
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (1910430522000 * (19 * (u / 19) + 3) + 1) = 57 * (636810174000 * (u / 19) + 100548974842) + 7 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 229 57 7 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 4
    have hf_mod : (1910430522000 * u + 1) % 95 = 66 := by
      have h_eq : u = 19 * (u / 19) + 4 := by
        have hdiv := Nat.div_add_mod u 19
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (1910430522000 * (19 * (u / 19) + 4) + 1) = 95 * (382086104400 * (u / 19) + 80439179873) + 66 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 191 95 66 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 5
    have hf_mod : (1910430522000 * u + 1) % 95 = 11 := by
      have h_eq : u = 19 * (u / 19) + 5 := by
        have hdiv := Nat.div_add_mod u 19
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (1910430522000 * (19 * (u / 19) + 5) + 1) = 95 * (382086104400 * (u / 19) + 100548974842) + 11 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 191 95 11 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 6
    have hf_mod : (1910430522000 * u + 1) % 95 = 51 := by
      have h_eq : u = 19 * (u / 19) + 6 := by
        have hdiv := Nat.div_add_mod u 19
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (1910430522000 * (19 * (u / 19) + 6) + 1) = 95 * (382086104400 * (u / 19) + 120658769810) + 51 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 191 95 51 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 7
    have hf_mod : (1910430522000 * u + 1) % 228 = 205 := by
      have h_eq : u = 19 * (u / 19) + 7 := by
        have hdiv := Nat.div_add_mod u 19
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (1910430522000 * (19 * (u / 19) + 7) + 1) = 228 * (159202543500 * (u / 19) + 58653568657) + 205 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 457 228 205 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 8
    have hf_mod : (1910430522000 * u + 1) % 95 = 36 := by
      have h_eq : u = 19 * (u / 19) + 8 := by
        have hdiv := Nat.div_add_mod u 19
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (1910430522000 * (19 * (u / 19) + 8) + 1) = 95 * (382086104400 * (u / 19) + 160878359747) + 36 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 191 95 36 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 9
    have hf_mod : (1910430522000 * u + 1) % 95 = 76 := by
      have h_eq : u = 19 * (u / 19) + 9 := by
        have hdiv := Nat.div_add_mod u 19
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (1910430522000 * (19 * (u / 19) + 9) + 1) = 95 * (382086104400 * (u / 19) + 180988154715) + 76 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 191 95 76 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 10
    have hf_mod : (1910430522000 * u + 1) % 57 = 40 := by
      have h_eq : u = 19 * (u / 19) + 10 := by
        have hdiv := Nat.div_add_mod u 19
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (1910430522000 * (19 * (u / 19) + 10) + 1) = 57 * (636810174000 * (u / 19) + 335163249473) + 40 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 229 57 40 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 11
    have hf_mod : (1910430522000 * u + 1) % 57 = 4 := by
      have h_eq : u = 19 * (u / 19) + 11 := by
        have hdiv := Nat.div_add_mod u 19
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (1910430522000 * (19 * (u / 19) + 11) + 1) = 57 * (636810174000 * (u / 19) + 368679574421) + 4 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 229 57 4 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 12
    have hf_mod : (1910430522000 * u + 1) % 209 = 177 := by
      have h_eq : u = 19 * (u / 19) + 12 := by
        have hdiv := Nat.div_add_mod u 19
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (1910430522000 * (19 * (u / 19) + 12) + 1) = 209 * (173675502000 * (u / 19) + 109689790736) + 177 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 419 209 177 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 13
    have hf_mod : (1910430522000 * u + 1) % 57 = 46 := by
      have h_eq : u = 19 * (u / 19) + 13 := by
        have hdiv := Nat.div_add_mod u 19
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (1910430522000 * (19 * (u / 19) + 13) + 1) = 57 * (636810174000 * (u / 19) + 435712224315) + 46 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 229 57 46 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 14
    have hf_mod : (1910430522000 * u + 1) % 57 = 10 := by
      have h_eq : u = 19 * (u / 19) + 14 := by
        have hdiv := Nat.div_add_mod u 19
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (1910430522000 * (19 * (u / 19) + 14) + 1) = 57 * (636810174000 * (u / 19) + 469228549263) + 10 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 229 57 10 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 15
    have hf_mod : (1910430522000 * u + 1) % 95 = 31 := by
      have h_eq : u = 19 * (u / 19) + 15 := by
        have hdiv := Nat.div_add_mod u 19
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (1910430522000 * (19 * (u / 19) + 15) + 1) = 95 * (382086104400 * (u / 19) + 301646924526) + 31 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 191 95 31 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 16
    have hf_mod : (1910430522000 * u + 1) % 209 = 166 := by
      have h_eq : u = 19 * (u / 19) + 16 := by
        have hdiv := Nat.div_add_mod u 19
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (1910430522000 * (19 * (u / 19) + 16) + 1) = 209 * (173675502000 * (u / 19) + 146253054315) + 166 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 419 209 166 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 17
    have hf_mod : (1910430522000 * u + 1) % 95 = 16 := by
      have h_eq : u = 19 * (u / 19) + 17 := by
        have hdiv := Nat.div_add_mod u 19
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (1910430522000 * (19 * (u / 19) + 17) + 1) = 95 * (382086104400 * (u / 19) + 341866514463) + 16 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 191 95 16 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 18
    have hf_mod : (1910430522000 * u + 1) % 57 = 37 := by
      have h_eq : u = 19 * (u / 19) + 18 := by
        have hdiv := Nat.div_add_mod u 19
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (1910430522000 * (19 * (u / 19) + 18) + 1) = 57 * (636810174000 * (u / 19) + 603293849052) + 37 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 229 57 37 _ y (by decide) (by decide) (by decide) hf_mod h_y

lemma no_solution_rw13_0 (p a y w : ℕ) (hp : p.Prime) (ha : 1 ≤ a) (hp5 : p ≠ 5) (h_pa : p ^ a = y) (h_y : y ^ 2 + 2 = 3 ^ (8644482000 * w + 1)) (h_ge : w ≥ 1) (h_mod : w % 13 = 0) : False := by
  have h_next : ∃ v, w = 13 * v ∧ v ≥ 1 := by
    use w / 13
    constructor <;> omega
  rcases h_next with ⟨v, rfl, h_next_ge⟩
  have h_ring_eq : 8644482000 * (13 * v) + 1 = 112378266000 * v + 1 := by ring
  rw [h_ring_eq] at h_y
  generalize h_mod_next : v % 17 = r_next
  have h_r_next_lt : r_next < 17 := by
    rw [← h_mod_next]
    exact Nat.mod_lt v (by decide)
  interval_cases r_next
  · -- Case r_next = 0
    exact no_solution_rv17_0 p a y v hp ha hp5 h_pa h_y h_next_ge h_mod_next
  · -- Case r_next = 1
    have hf_mod : (112378266000 * v + 1) % 119 = 57 := by
      have h_eq : v = 17 * (v / 17) + 1 := by
        have hdiv := Nat.div_add_mod v 17
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (112378266000 * (17 * (v / 17) + 1) + 1) = 119 * (16054038000 * (v / 17) + 944355176) + 57 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 239 119 57 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 2
    have hf_mod : (112378266000 * v + 1) % 34 = 11 := by
      have h_eq : v = 17 * (v / 17) + 2 := by
        have hdiv := Nat.div_add_mod v 17
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (112378266000 * (17 * (v / 17) + 2) + 1) = 34 * (56189133000 * (v / 17) + 6610486235) + 11 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 103 34 11 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 3
    have hf_mod : (112378266000 * v + 1) % 34 = 33 := by
      have h_eq : v = 17 * (v / 17) + 3 := by
        have hdiv := Nat.div_add_mod v 17
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (112378266000 * (17 * (v / 17) + 3) + 1) = 34 * (56189133000 * (v / 17) + 9915729352) + 33 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 103 34 33 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 4
    have hf_mod : (112378266000 * v + 1) % 34 = 21 := by
      have h_eq : v = 17 * (v / 17) + 4 := by
        have hdiv := Nat.div_add_mod v 17
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (112378266000 * (17 * (v / 17) + 4) + 1) = 34 * (56189133000 * (v / 17) + 13220972470) + 21 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 103 34 21 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 5
    have hf_mod : (112378266000 * v + 1) % 136 = 9 := by
      have h_eq : v = 17 * (v / 17) + 5 := by
        have hdiv := Nat.div_add_mod v 17
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (112378266000 * (17 * (v / 17) + 5) + 1) = 136 * (14047283250 * (v / 17) + 4131553897) + 9 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 137 136 9 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 6
    have hf_mod : (112378266000 * v + 1) % 34 = 31 := by
      have h_eq : v = 17 * (v / 17) + 6 := by
        have hdiv := Nat.div_add_mod v 17
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (112378266000 * (17 * (v / 17) + 6) + 1) = 34 * (56189133000 * (v / 17) + 19831458705) + 31 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 103 34 31 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 7
    have hf_mod : (112378266000 * v + 1) % 34 = 19 := by
      have h_eq : v = 17 * (v / 17) + 7 := by
        have hdiv := Nat.div_add_mod v 17
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (112378266000 * (17 * (v / 17) + 7) + 1) = 34 * (56189133000 * (v / 17) + 23136701823) + 19 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 307 34 19 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 8
    have hf_mod : (112378266000 * v + 1) % 34 = 7 := by
      have h_eq : v = 17 * (v / 17) + 8 := by
        have hdiv := Nat.div_add_mod v 17
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (112378266000 * (17 * (v / 17) + 8) + 1) = 34 * (56189133000 * (v / 17) + 26441944941) + 7 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 103 34 7 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 9
    have hf_mod : (112378266000 * v + 1) % 34 = 29 := by
      have h_eq : v = 17 * (v / 17) + 9 := by
        have hdiv := Nat.div_add_mod v 17
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (112378266000 * (17 * (v / 17) + 9) + 1) = 34 * (56189133000 * (v / 17) + 29747188058) + 29 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 103 34 29 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 10
    have hf_mod : (112378266000 * v + 1) % 136 = 17 := by
      have h_eq : v = 17 * (v / 17) + 10 := by
        have hdiv := Nat.div_add_mod v 17
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (112378266000 * (17 * (v / 17) + 10) + 1) = 136 * (14047283250 * (v / 17) + 8263107794) + 17 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 137 136 17 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 11
    have hf_mod : (112378266000 * v + 1) % 34 = 5 := by
      have h_eq : v = 17 * (v / 17) + 11 := by
        have hdiv := Nat.div_add_mod v 17
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (112378266000 * (17 * (v / 17) + 11) + 1) = 34 * (56189133000 * (v / 17) + 36357674294) + 5 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 103 34 5 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 12
    have hf_mod : (112378266000 * v + 1) % 34 = 27 := by
      have h_eq : v = 17 * (v / 17) + 12 := by
        have hdiv := Nat.div_add_mod v 17
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (112378266000 * (17 * (v / 17) + 12) + 1) = 34 * (56189133000 * (v / 17) + 39662917411) + 27 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 103 34 27 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 13
    have hf_mod : (112378266000 * v + 1) % 34 = 15 := by
      have h_eq : v = 17 * (v / 17) + 13 := by
        have hdiv := Nat.div_add_mod v 17
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (112378266000 * (17 * (v / 17) + 13) + 1) = 34 * (56189133000 * (v / 17) + 42968160529) + 15 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 103 34 15 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 14
    have hf_mod : (112378266000 * v + 1) % 119 = 71 := by
      have h_eq : v = 17 * (v / 17) + 14 := by
        have hdiv := Nat.div_add_mod v 17
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (112378266000 * (17 * (v / 17) + 14) + 1) = 119 * (16054038000 * (v / 17) + 13220972470) + 71 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 239 119 71 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 15
    have hf_mod : (112378266000 * v + 1) % 119 = 8 := by
      have h_eq : v = 17 * (v / 17) + 15 := by
        have hdiv := Nat.div_add_mod v 17
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (112378266000 * (17 * (v / 17) + 15) + 1) = 119 * (16054038000 * (v / 17) + 14165327647) + 8 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 239 119 8 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 16
    have hf_mod : (112378266000 * v + 1) % 34 = 13 := by
      have h_eq : v = 17 * (v / 17) + 16 := by
        have hdiv := Nat.div_add_mod v 17
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (112378266000 * (17 * (v / 17) + 16) + 1) = 34 * (56189133000 * (v / 17) + 52883889882) + 13 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 103 34 13 _ y (by decide) (by decide) (by decide) hf_mod h_y

lemma no_solution_rz11_0 (p a y z : ℕ) (hp : p.Prime) (ha : 1 ≤ a) (hp5 : p ≠ 5) (h_pa : p ^ a = y) (h_y : y ^ 2 + 2 = 3 ^ (785862000 * z + 1)) (h_ge : z ≥ 1) (h_mod : z % 11 = 0) : False := by
  have h_next : ∃ w, z = 11 * w ∧ w ≥ 1 := by
    use z / 11
    constructor <;> omega
  rcases h_next with ⟨w, rfl, h_next_ge⟩
  have h_ring_eq : 785862000 * (11 * w) + 1 = 8644482000 * w + 1 := by ring
  rw [h_ring_eq] at h_y
  generalize h_mod_next : w % 13 = r_next
  have h_r_next_lt : r_next < 13 := by
    rw [← h_mod_next]
    exact Nat.mod_lt w (by decide)
  interval_cases r_next
  · -- Case r_next = 0
    exact no_solution_rw13_0 p a y w hp ha hp5 h_pa h_y h_next_ge h_mod_next
  · -- Case r_next = 1
    have hf_mod : (8644482000 * w + 1) % 52 = 25 := by
      have h_eq : w = 13 * (w / 13) + 1 := by
        have hdiv := Nat.div_add_mod w 13
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (8644482000 * (13 * (w / 13) + 1) + 1) = 52 * (2161120500 * (w / 13) + 166240038) + 25 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 53 52 25 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 2
    have hf_mod : (8644482000 * w + 1) % 78 = 49 := by
      have h_eq : w = 13 * (w / 13) + 2 := by
        have hdiv := Nat.div_add_mod w 13
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (8644482000 * (13 * (w / 13) + 2) + 1) = 78 * (1440747000 * (w / 13) + 221653384) + 49 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 79 78 49 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 3
    have hf_mod : (8644482000 * w + 1) % 52 = 21 := by
      have h_eq : w = 13 * (w / 13) + 3 := by
        have hdiv := Nat.div_add_mod w 13
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (8644482000 * (13 * (w / 13) + 3) + 1) = 52 * (2161120500 * (w / 13) + 498720115) + 21 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 53 52 21 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 4
    have hf_mod : (8644482000 * w + 1) % 78 = 19 := by
      have h_eq : w = 13 * (w / 13) + 4 := by
        have hdiv := Nat.div_add_mod w 13
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (8644482000 * (13 * (w / 13) + 4) + 1) = 78 * (1440747000 * (w / 13) + 443306769) + 19 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 79 78 19 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 5
    have hf_mod : (8644482000 * w + 1) % 78 = 43 := by
      have h_eq : w = 13 * (w / 13) + 5 := by
        have hdiv := Nat.div_add_mod w 13
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (8644482000 * (13 * (w / 13) + 5) + 1) = 78 * (1440747000 * (w / 13) + 554133461) + 43 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 79 78 43 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 6
    have hf_mod : (8644482000 * w + 1) % 78 = 67 := by
      have h_eq : w = 13 * (w / 13) + 6 := by
        have hdiv := Nat.div_add_mod w 13
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (8644482000 * (13 * (w / 13) + 6) + 1) = 78 * (1440747000 * (w / 13) + 664960153) + 67 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 79 78 67 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 7
    have hf_mod : (8644482000 * w + 1) % 65 = 26 := by
      have h_eq : w = 13 * (w / 13) + 7 := by
        have hdiv := Nat.div_add_mod w 13
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (8644482000 * (13 * (w / 13) + 7) + 1) = 65 * (1728896400 * (w / 13) + 930944215) + 26 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 131 65 26 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 8
    have hf_mod : (8644482000 * w + 1) % 52 = 37 := by
      have h_eq : w = 13 * (w / 13) + 8 := by
        have hdiv := Nat.div_add_mod w 13
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (8644482000 * (13 * (w / 13) + 8) + 1) = 52 * (2161120500 * (w / 13) + 1329920307) + 37 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 53 52 37 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 9
    have hf_mod : (8644482000 * w + 1) % 52 = 9 := by
      have h_eq : w = 13 * (w / 13) + 9 := by
        have hdiv := Nat.div_add_mod w 13
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (8644482000 * (13 * (w / 13) + 9) + 1) = 52 * (2161120500 * (w / 13) + 1496160346) + 9 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 53 52 9 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 10
    have hf_mod : (8644482000 * w + 1) % 65 = 46 := by
      have h_eq : w = 13 * (w / 13) + 10 := by
        have hdiv := Nat.div_add_mod w 13
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (8644482000 * (13 * (w / 13) + 10) + 1) = 65 * (1728896400 * (w / 13) + 1329920307) + 46 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 131 65 46 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 11
    have hf_mod : (8644482000 * w + 1) % 78 = 31 := by
      have h_eq : w = 13 * (w / 13) + 11 := by
        have hdiv := Nat.div_add_mod w 13
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (8644482000 * (13 * (w / 13) + 11) + 1) = 78 * (1440747000 * (w / 13) + 1219093615) + 31 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 79 78 31 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 12
    have hf_mod : (8644482000 * w + 1) % 78 = 55 := by
      have h_eq : w = 13 * (w / 13) + 12 := by
        have hdiv := Nat.div_add_mod w 13
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (8644482000 * (13 * (w / 13) + 12) + 1) = 78 * (1440747000 * (w / 13) + 1329920307) + 55 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 79 78 55 _ y (by decide) (by decide) (by decide) hf_mod h_y

lemma no_solution_ry5_0 (p a y y_val : ℕ) (hp : p.Prime) (ha : 1 ≤ a) (hp5 : p ≠ 5) (h_pa : p ^ a = y) (h_y : y ^ 2 + 2 = 3 ^ (157172400 * y_val + 1)) (h_ge : y_val ≥ 1) (h_mod : y_val % 5 = 0) : False := by
  have h_next : ∃ z, y_val = 5 * z ∧ z ≥ 1 := by
    use y_val / 5
    constructor <;> omega
  rcases h_next with ⟨z, rfl, h_next_ge⟩
  have h_ring_eq : 157172400 * (5 * z) + 1 = 785862000 * z + 1 := by ring
  rw [h_ring_eq] at h_y
  generalize h_mod_next : z % 11 = r_next
  have h_r_next_lt : r_next < 11 := by
    rw [← h_mod_next]
    exact Nat.mod_lt z (by decide)
  interval_cases r_next
  · -- Case r_next = 0
    exact no_solution_rz11_0 p a y z hp ha hp5 h_pa h_y h_next_ge h_mod_next
  · -- Case r_next = 1
    have hf_mod : (785862000 * z + 1) % 242 = 155 := by
      have h_eq : z = 11 * (z / 11) + 1 := by
        have hdiv := Nat.div_add_mod z 11
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (785862000 * (11 * (z / 11) + 1) + 1) = 242 * (35721000 * (z / 11) + 3247363) + 155 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 2179 242 155 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 2
    have hf_mod : (785862000 * z + 1) % 242 = 67 := by
      have h_eq : z = 11 * (z / 11) + 2 := by
        have hdiv := Nat.div_add_mod z 11
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (785862000 * (11 * (z / 11) + 2) + 1) = 242 * (35721000 * (z / 11) + 6494727) + 67 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 2179 242 67 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 3
    have hf_mod : (785862000 * z + 1) % 363 = 100 := by
      have h_eq : z = 11 * (z / 11) + 3 := by
        have hdiv := Nat.div_add_mod z 11
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (785862000 * (11 * (z / 11) + 3) + 1) = 363 * (23814000 * (z / 11) + 6494727) + 100 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 1453 363 100 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 4
    have hf_mod : (785862000 * z + 1) % 242 = 133 := by
      have h_eq : z = 11 * (z / 11) + 4 := by
        have hdiv := Nat.div_add_mod z 11
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (785862000 * (11 * (z / 11) + 4) + 1) = 242 * (35721000 * (z / 11) + 12989454) + 133 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 2179 242 133 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 5
    have hf_mod : (785862000 * z + 1) % 121 = 45 := by
      have h_eq : z = 11 * (z / 11) + 5 := by
        have hdiv := Nat.div_add_mod z 11
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (785862000 * (11 * (z / 11) + 5) + 1) = 121 * (71442000 * (z / 11) + 32473636) + 45 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 11617 121 45 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 6
    have hf_mod : (785862000 * z + 1) % 121 = 78 := by
      have h_eq : z = 11 * (z / 11) + 6 := by
        have hdiv := Nat.div_add_mod z 11
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (785862000 * (11 * (z / 11) + 6) + 1) = 121 * (71442000 * (z / 11) + 38968363) + 78 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 11617 121 78 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 7
    have hf_mod : (785862000 * z + 1) % 121 = 111 := by
      have h_eq : z = 11 * (z / 11) + 7 := by
        have hdiv := Nat.div_add_mod z 11
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (785862000 * (11 * (z / 11) + 7) + 1) = 121 * (71442000 * (z / 11) + 45463090) + 111 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 11617 121 111 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 8
    have hf_mod : (785862000 * z + 1) % 363 = 265 := by
      have h_eq : z = 11 * (z / 11) + 8 := by
        have hdiv := Nat.div_add_mod z 11
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (785862000 * (11 * (z / 11) + 8) + 1) = 363 * (23814000 * (z / 11) + 17319272) + 265 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 1453 363 265 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 9
    have hf_mod : (785862000 * z + 1) % 121 = 56 := by
      have h_eq : z = 11 * (z / 11) + 9 := by
        have hdiv := Nat.div_add_mod z 11
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (785862000 * (11 * (z / 11) + 9) + 1) = 121 * (71442000 * (z / 11) + 58452545) + 56 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 11617 121 56 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 10
    have hf_mod : (785862000 * z + 1) % 363 = 331 := by
      have h_eq : z = 11 * (z / 11) + 10 := by
        have hdiv := Nat.div_add_mod z 11
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (785862000 * (11 * (z / 11) + 10) + 1) = 363 * (23814000 * (z / 11) + 21649090) + 331 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 1453 363 331 _ y (by decide) (by decide) (by decide) hf_mod h_y

lemma no_solution_rx3_0 (p a y x : ℕ) (hp : p.Prime) (ha : 1 ≤ a) (hp5 : p ≠ 5) (h_pa : p ^ a = y) (h_y : y ^ 2 + 2 = 3 ^ (52390800 * x + 1)) (h_ge : x ≥ 1) (h_mod : x % 3 = 0) : False := by
  have h_next : ∃ y_val, x = 3 * y_val ∧ y_val ≥ 1 := by
    use x / 3
    constructor <;> omega
  rcases h_next with ⟨y_val, rfl, h_next_ge⟩
  have h_ring_eq : 52390800 * (3 * y_val) + 1 = 157172400 * y_val + 1 := by ring
  rw [h_ring_eq] at h_y
  generalize h_mod_next : y_val % 5 = r_next
  have h_r_next_lt : r_next < 5 := by
    rw [← h_mod_next]
    exact Nat.mod_lt y_val (by decide)
  interval_cases r_next
  · -- Case r_next = 0
    exact no_solution_ry5_0 p a y y_val hp ha hp5 h_pa h_y h_next_ge h_mod_next
  · -- Case r_next = 1
    have hf_mod : (157172400 * y_val + 1) % 500 = 401 := by
      have h_eq : y_val = 5 * (y_val / 5) + 1 := by
        have hdiv := Nat.div_add_mod y_val 5
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (157172400 * (5 * (y_val / 5) + 1) + 1) = 500 * (1571724 * (y_val / 5) + 314344) + 401 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 3001 500 401 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 2
    have hf_mod : (157172400 * y_val + 1) % 250 = 51 := by
      have h_eq : y_val = 5 * (y_val / 5) + 2 := by
        have hdiv := Nat.div_add_mod y_val 5
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (157172400 * (5 * (y_val / 5) + 2) + 1) = 250 * (3143448 * (y_val / 5) + 1257379) + 51 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 2251 250 51 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 3
    have hf_mod : (157172400 * y_val + 1) % 250 = 201 := by
      have h_eq : y_val = 5 * (y_val / 5) + 3 := by
        have hdiv := Nat.div_add_mod y_val 5
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (157172400 * (5 * (y_val / 5) + 3) + 1) = 250 * (3143448 * (y_val / 5) + 1886068) + 201 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 2251 250 201 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 4
    have hf_mod : (157172400 * y_val + 1) % 500 = 101 := by
      have h_eq : y_val = 5 * (y_val / 5) + 4 := by
        have hdiv := Nat.div_add_mod y_val 5
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (157172400 * (5 * (y_val / 5) + 4) + 1) = 500 * (1571724 * (y_val / 5) + 1257379) + 101 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 3001 500 101 _ y (by decide) (by decide) (by decide) hf_mod h_y

lemma no_solution_rm7_0 (p a y m_val : ℕ) (hp : p.Prime) (ha : 1 ≤ a) (hp5 : p ≠ 5) (h_pa : p ^ a = y) (h_y : y ^ 2 + 2 = 3 ^ (7484400 * m_val + 1)) (h_ge : m_val ≥ 1) (h_mod : m_val % 7 = 0) : False := by
  have h_next : ∃ x, m_val = 7 * x ∧ x ≥ 1 := by
    use m_val / 7
    constructor <;> omega
  rcases h_next with ⟨x, rfl, h_next_ge⟩
  have h_ring_eq : 7484400 * (7 * x) + 1 = 52390800 * x + 1 := by ring
  rw [h_ring_eq] at h_y
  generalize h_mod_next : x % 3 = r_next
  have h_r_next_lt : r_next < 3 := by
    rw [← h_mod_next]
    exact Nat.mod_lt x (by decide)
  interval_cases r_next
  · -- Case r_next = 0
    exact no_solution_rx3_0 p a y x hp ha hp5 h_pa h_y h_next_ge h_mod_next
  · -- Case r_next = 1
    have hf_mod : (52390800 * x + 1) % 729 = 487 := by
      have h_eq : x = 3 * (x / 3) + 1 := by
        have hdiv := Nat.div_add_mod x 3
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (52390800 * (3 * (x / 3) + 1) + 1) = 729 * (215600 * (x / 3) + 71866) + 487 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 17497 729 487 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 2
    have hf_mod : (52390800 * x + 1) % 1458 = 973 := by
      have h_eq : x = 3 * (x / 3) + 2 := by
        have hdiv := Nat.div_add_mod x 3
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (52390800 * (3 * (x / 3) + 2) + 1) = 1458 * (107800 * (x / 3) + 71866) + 973 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 2917 1458 973 _ y (by decide) (by decide) (by decide) hf_mod h_y

lemma no_solution_rn11_0 (p a y n : ℕ) (hp : p.Prime) (ha : 1 ≤ a) (hp5 : p ≠ 5) (h_pa : p ^ a = y) (h_y : y ^ 2 + 2 = 3 ^ (680400 * n + 1)) (h_ge : n ≥ 1) (h_mod : n % 11 = 0) : False := by
  have h_next : ∃ m_val, n = 11 * m_val ∧ m_val ≥ 1 := by
    use n / 11
    constructor <;> omega
  rcases h_next with ⟨m_val, rfl, h_next_ge⟩
  have h_ring_eq : 680400 * (11 * m_val) + 1 = 7484400 * m_val + 1 := by ring
  rw [h_ring_eq] at h_y
  generalize h_mod_next : m_val % 7 = r_next
  have h_r_next_lt : r_next < 7 := by
    rw [← h_mod_next]
    exact Nat.mod_lt m_val (by decide)
  interval_cases r_next
  · -- Case r_next = 0
    exact no_solution_rm7_0 p a y m_val hp ha hp5 h_pa h_y h_next_ge h_mod_next
  · -- Case r_next = 1
    have hf_mod : (7484400 * m_val + 1) % 49 = 43 := by
      have h_eq : m_val = 7 * (m_val / 7) + 1 := by
        have hdiv := Nat.div_add_mod m_val 7
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (7484400 * (7 * (m_val / 7) + 1) + 1) = 49 * (1069200 * (m_val / 7) + 152742) + 43 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 4019 49 43 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 2
    have hf_mod : (7484400 * m_val + 1) % 49 = 36 := by
      have h_eq : m_val = 7 * (m_val / 7) + 2 := by
        have hdiv := Nat.div_add_mod m_val 7
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (7484400 * (7 * (m_val / 7) + 2) + 1) = 49 * (1069200 * (m_val / 7) + 305485) + 36 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 4019 49 36 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 3
    have hf_mod : (7484400 * m_val + 1) % 196 = 29 := by
      have h_eq : m_val = 7 * (m_val / 7) + 3 := by
        have hdiv := Nat.div_add_mod m_val 7
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (7484400 * (7 * (m_val / 7) + 3) + 1) = 196 * (267300 * (m_val / 7) + 114557) + 29 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 197 196 29 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 4
    have hf_mod : (7484400 * m_val + 1) % 196 = 169 := by
      have h_eq : m_val = 7 * (m_val / 7) + 4 := by
        have hdiv := Nat.div_add_mod m_val 7
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (7484400 * (7 * (m_val / 7) + 4) + 1) = 196 * (267300 * (m_val / 7) + 152742) + 169 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 197 196 169 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 5
    have hf_mod : (7484400 * m_val + 1) % 196 = 113 := by
      have h_eq : m_val = 7 * (m_val / 7) + 5 := by
        have hdiv := Nat.div_add_mod m_val 7
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (7484400 * (7 * (m_val / 7) + 5) + 1) = 196 * (267300 * (m_val / 7) + 190928) + 113 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 197 196 113 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 6
    have hf_mod : (7484400 * m_val + 1) % 2646 = 1135 := by
      have h_eq : m_val = 7 * (m_val / 7) + 6 := by
        have hdiv := Nat.div_add_mod m_val 7
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (7484400 * (7 * (m_val / 7) + 6) + 1) = 2646 * (19800 * (m_val / 7) + 16971) + 1135 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 2647 2646 1135 _ y (by decide) (by decide) (by decide) hf_mod h_y

lemma no_solution_rj5_0 (p a y j : ℕ) (hp : p.Prime) (ha : 1 ≤ a) (hp5 : p ≠ 5) (h_pa : p ^ a = y) (h_y : y ^ 2 + 2 = 3 ^ (136080 * j + 1)) (h_ge : j ≥ 1) (h_mod : j % 5 = 0) : False := by
  have h_next : ∃ n, j = 5 * n ∧ n ≥ 1 := by
    use j / 5
    constructor <;> omega
  rcases h_next with ⟨n, rfl, h_next_ge⟩
  have h_ring_eq : 136080 * (5 * n) + 1 = 680400 * n + 1 := by ring
  rw [h_ring_eq] at h_y
  generalize h_mod_next : n % 11 = r_next
  have h_r_next_lt : r_next < 11 := by
    rw [← h_mod_next]
    exact Nat.mod_lt n (by decide)
  interval_cases r_next
  · -- Case r_next = 0
    exact no_solution_rn11_0 p a y n hp ha hp5 h_pa h_y h_next_ge h_mod_next
  · -- Case r_next = 1
    have hf_mod : (680400 * n + 1) % 22 = 7 := by
      have h_eq : n = 11 * (n / 11) + 1 := by
        have hdiv := Nat.div_add_mod n 11
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (680400 * (11 * (n / 11) + 1) + 1) = 22 * (340200 * (n / 11) + 30927) + 7 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 67 22 7 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 2
    have hf_mod : (680400 * n + 1) % 11 = 2 := by
      have h_eq : n = 11 * (n / 11) + 2 := by
        have hdiv := Nat.div_add_mod n 11
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (680400 * (11 * (n / 11) + 2) + 1) = 11 * (680400 * (n / 11) + 123709) + 2 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 23 11 2 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 3
    have hf_mod : (680400 * n + 1) % 22 = 19 := by
      have h_eq : n = 11 * (n / 11) + 3 := by
        have hdiv := Nat.div_add_mod n 11
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (680400 * (11 * (n / 11) + 3) + 1) = 22 * (340200 * (n / 11) + 92781) + 19 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 67 22 19 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 4
    have hf_mod : (680400 * n + 1) % 88 = 25 := by
      have h_eq : n = 11 * (n / 11) + 4 := by
        have hdiv := Nat.div_add_mod n 11
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (680400 * (11 * (n / 11) + 4) + 1) = 88 * (85050 * (n / 11) + 30927) + 25 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 89 88 25 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 5
    have hf_mod : (680400 * n + 1) % 22 = 9 := by
      have h_eq : n = 11 * (n / 11) + 5 := by
        have hdiv := Nat.div_add_mod n 11
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (680400 * (11 * (n / 11) + 5) + 1) = 22 * (340200 * (n / 11) + 154636) + 9 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 67 22 9 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 6
    have hf_mod : (680400 * n + 1) % 11 = 4 := by
      have h_eq : n = 11 * (n / 11) + 6 := by
        have hdiv := Nat.div_add_mod n 11
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (680400 * (11 * (n / 11) + 6) + 1) = 11 * (680400 * (n / 11) + 371127) + 4 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 23 11 4 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 7
    have hf_mod : (680400 * n + 1) % 22 = 21 := by
      have h_eq : n = 11 * (n / 11) + 7 := by
        have hdiv := Nat.div_add_mod n 11
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (680400 * (11 * (n / 11) + 7) + 1) = 22 * (340200 * (n / 11) + 216490) + 21 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 67 22 21 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 8
    have hf_mod : (680400 * n + 1) % 11 = 5 := by
      have h_eq : n = 11 * (n / 11) + 8 := by
        have hdiv := Nat.div_add_mod n 11
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (680400 * (11 * (n / 11) + 8) + 1) = 11 * (680400 * (n / 11) + 494836) + 5 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 23 11 5 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 9
    have hf_mod : (680400 * n + 1) % 11 = 0 := by
      have h_eq : n = 11 * (n / 11) + 9 := by
        have hdiv := Nat.div_add_mod n 11
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (680400 * (11 * (n / 11) + 9) + 1) = 11 * (680400 * (n / 11) + 556691) + 0 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 23 11 0 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 10
    have hf_mod : (680400 * n + 1) % 11 = 6 := by
      have h_eq : n = 11 * (n / 11) + 10 := by
        have hdiv := Nat.div_add_mod n 11
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (680400 * (11 * (n / 11) + 10) + 1) = 11 * (680400 * (n / 11) + 618545) + 6 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 23 11 6 _ y (by decide) (by decide) (by decide) hf_mod h_y

lemma no_solution_rq3_0 (p a y q_val : ℕ) (hp : p.Prime) (ha : 1 ≤ a) (hp5 : p ≠ 5) (h_pa : p ^ a = y) (h_y : y ^ 2 + 2 = 3 ^ (45360 * q_val + 1)) (h_ge : q_val ≥ 1) (h_mod : q_val % 3 = 0) : False := by
  have h_next : ∃ j, q_val = 3 * j ∧ j ≥ 1 := by
    use q_val / 3
    constructor <;> omega
  rcases h_next with ⟨j, rfl, h_next_ge⟩
  have h_ring_eq : 45360 * (3 * j) + 1 = 136080 * j + 1 := by ring
  rw [h_ring_eq] at h_y
  generalize h_mod_next : j % 5 = r_next
  have h_r_next_lt : r_next < 5 := by
    rw [← h_mod_next]
    exact Nat.mod_lt j (by decide)
  interval_cases r_next
  · -- Case r_next = 0
    exact no_solution_rj5_0 p a y j hp ha hp5 h_pa h_y h_next_ge h_mod_next
  · -- Case r_next = 1
    have hf_mod : (136080 * j + 1) % 50 = 31 := by
      have h_eq : j = 5 * (j / 5) + 1 := by
        have hdiv := Nat.div_add_mod j 5
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (136080 * (5 * (j / 5) + 1) + 1) = 50 * (13608 * (j / 5) + 2721) + 31 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 151 50 31 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 2
    have hf_mod : (136080 * j + 1) % 700 = 561 := by
      have h_eq : j = 5 * (j / 5) + 2 := by
        have hdiv := Nat.div_add_mod j 5
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (136080 * (5 * (j / 5) + 2) + 1) = 700 * (972 * (j / 5) + 388) + 561 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 701 700 561 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 3
    have hf_mod : (136080 * j + 1) % 100 = 41 := by
      have h_eq : j = 5 * (j / 5) + 3 := by
        have hdiv := Nat.div_add_mod j 5
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (136080 * (5 * (j / 5) + 3) + 1) = 100 * (6804 * (j / 5) + 4082) + 41 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 101 100 41 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 4
    have hf_mod : (136080 * j + 1) % 100 = 21 := by
      have h_eq : j = 5 * (j / 5) + 4 := by
        have hdiv := Nat.div_add_mod j 5
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (136080 * (5 * (j / 5) + 4) + 1) = 100 * (6804 * (j / 5) + 5443) + 21 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 101 100 21 _ y (by decide) (by decide) (by decide) hf_mod h_y

lemma no_solution_rm3_0 (p a y m : ℕ) (hp : p.Prime) (ha : 1 ≤ a) (hp5 : p ≠ 5) (h_pa : p ^ a = y) (h_y : y ^ 2 + 2 = 3 ^ (15120 * m + 1)) (h_ge : m ≥ 1) (h_mod : m % 3 = 0) : False := by
  have h_next : ∃ q_val, m = 3 * q_val ∧ q_val ≥ 1 := by
    use m / 3
    constructor <;> omega
  rcases h_next with ⟨q_val, rfl, h_next_ge⟩
  have h_ring_eq : 15120 * (3 * q_val) + 1 = 45360 * q_val + 1 := by ring
  rw [h_ring_eq] at h_y
  generalize h_mod_next : q_val % 3 = r_next
  have h_r_next_lt : r_next < 3 := by
    rw [← h_mod_next]
    exact Nat.mod_lt q_val (by decide)
  interval_cases r_next
  · -- Case r_next = 0
    exact no_solution_rq3_0 p a y q_val hp ha hp5 h_pa h_y h_next_ge h_mod_next
  · -- Case r_next = 1
    have hf_mod : (45360 * q_val + 1) % 486 = 163 := by
      have h_eq : q_val = 3 * (q_val / 3) + 1 := by
        have hdiv := Nat.div_add_mod q_val 3
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (45360 * (3 * (q_val / 3) + 1) + 1) = 486 * (280 * (q_val / 3) + 93) + 163 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 487 486 163 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 2
    have hf_mod : (45360 * q_val + 1) % 486 = 325 := by
      have h_eq : q_val = 3 * (q_val / 3) + 2 := by
        have hdiv := Nat.div_add_mod q_val 3
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (45360 * (3 * (q_val / 3) + 2) + 1) = 486 * (280 * (q_val / 3) + 186) + 325 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 487 486 325 _ y (by decide) (by decide) (by decide) hf_mod h_y

lemma no_solution_r63_0 (p a y k : ℕ) (hp : p.Prime) (ha : 1 ≤ a) (hp5 : p ≠ 5) (h_pa : p ^ a = y) (h_y : y ^ 2 + 2 = 3 ^ (240 * k + 1)) (h_ge : k ≥ 1) (h_mod : k % 63 = 0) : False := by
  have h_next : ∃ m, k = 63 * m ∧ m ≥ 1 := by
    use k / 63
    constructor <;> omega
  rcases h_next with ⟨m, rfl, h_next_ge⟩
  have h_ring_eq : 240 * (63 * m) + 1 = 15120 * m + 1 := by ring
  rw [h_ring_eq] at h_y
  generalize h_mod_next : m % 3 = r_next
  have h_r_next_lt : r_next < 3 := by
    rw [← h_mod_next]
    exact Nat.mod_lt m (by decide)
  interval_cases r_next
  · -- Case r_next = 0
    exact no_solution_rm3_0 p a y m hp ha hp5 h_pa h_y h_next_ge h_mod_next
  · -- Case r_next = 1
    have hf_mod : (15120 * m + 1) % 162 = 55 := by
      have h_eq : m = 3 * (m / 3) + 1 := by
        have hdiv := Nat.div_add_mod m 3
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (15120 * (3 * (m / 3) + 1) + 1) = 162 * (280 * (m / 3) + 93) + 55 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 1297 162 55 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r_next = 2
    have hf_mod : (15120 * m + 1) % 162 = 109 := by
      have h_eq : m = 3 * (m / 3) + 2 := by
        have hdiv := Nat.div_add_mod m 3
        omega
      nth_rw 1 [h_eq]
      have hf_eq : (15120 * (3 * (m / 3) + 2) + 1) = 162 * (280 * (m / 3) + 186) + 109 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 163 162 109 _ y (by decide) (by decide) (by decide) hf_mod h_y

lemma no_solution_r240_1 (p f a y : ℕ) (hp : p.Prime) (ha : 1 ≤ a) (hp5 : p ≠ 5) (h_pa : p ^ a = y) (h_y : y ^ 2 + 2 = 3 ^ f) (hf_odd : Odd f) (h_mod240 : f % 240 = 1) : False := by
  have h_f1 : f ≠ 1 := by
    intro h_f1
    subst h_f1
    have hy2 : y ^ 2 = 1 := by omega
    have hy : y = 1 := by nlinarith
    have hpa_gt : p ^ a ≥ 2 := by
      have h1 : 2 ≤ p := hp.two_le
      have h2 : p ^ 1 ≤ p ^ a := Nat.pow_le_pow_right (by omega) ha
      simp at h2
      omega
    omega
  have h_f_ge : f ≥ 241 := by omega
  have h_k : ∃ k, f = 240 * k + 1 ∧ k ≥ 1 := by
    use f / 240
    constructor
    · omega
    · omega
  rcases h_k with ⟨k, rfl, hk_ge⟩
  generalize h_k_mod63 : k % 63 = r63
  have h_r63_lt : r63 < 63 := by
    rw [← h_k_mod63]
    exact Nat.mod_lt k (by decide)
  interval_cases r63
  · -- Case r63 = 0
    exact no_solution_r63_0 p a y k hp ha hp5 h_pa h_y hk_ge h_k_mod63
  · -- Case r63 = 1
    have hf_mod : (240 * k + 1) % 18 = 7 := by
      have h_k_eq : k = 63 * (k / 63) + 1 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 1) + 1) = 18 * (840 * (k / 63) + 13) + 7 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 37 18 7 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 2
    have hf_mod : (240 * k + 1) % 18 = 13 := by
      have h_k_eq : k = 63 * (k / 63) + 2 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 2) + 1) = 18 * (840 * (k / 63) + 26) + 13 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 19 18 13 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 3
    have hf_mod : (240 * k + 1) % 28 = 21 := by
      have h_k_eq : k = 63 * (k / 63) + 3 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 3) + 1) = 28 * (540 * (k / 63) + 25) + 21 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 29 28 21 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 4
    have hf_mod : (240 * k + 1) % 28 = 9 := by
      have h_k_eq : k = 63 * (k / 63) + 4 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 4) + 1) = 28 * (540 * (k / 63) + 34) + 9 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 29 28 9 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 5
    have hf_mod : (240 * k + 1) % 18 = 13 := by
      have h_k_eq : k = 63 * (k / 63) + 5 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 5) + 1) = 18 * (840 * (k / 63) + 66) + 13 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 19 18 13 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 6
    have hf_mod : (240 * k + 1) % 28 = 13 := by
      have h_k_eq : k = 63 * (k / 63) + 6 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 6) + 1) = 28 * (540 * (k / 63) + 51) + 13 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 29 28 13 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 7
    have hf_mod : (240 * k + 1) % 18 = 7 := by
      have h_k_eq : k = 63 * (k / 63) + 7 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 7) + 1) = 18 * (840 * (k / 63) + 93) + 7 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 37 18 7 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 8
    have hf_mod : (240 * k + 1) % 18 = 13 := by
      have h_k_eq : k = 63 * (k / 63) + 8 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 8) + 1) = 18 * (840 * (k / 63) + 106) + 13 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 19 18 13 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 9
    have hf_mod : (240 * k + 1) % 126 = 19 := by
      have h_k_eq : k = 63 * (k / 63) + 9 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 9) + 1) = 126 * (120 * (k / 63) + 17) + 19 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 127 126 19 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 10
    have hf_mod : (240 * k + 1) % 28 = 21 := by
      have h_k_eq : k = 63 * (k / 63) + 10 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 10) + 1) = 28 * (540 * (k / 63) + 85) + 21 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 29 28 21 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 11
    have hf_mod : (240 * k + 1) % 18 = 13 := by
      have h_k_eq : k = 63 * (k / 63) + 11 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 11) + 1) = 18 * (840 * (k / 63) + 146) + 13 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 19 18 13 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 12
    have hf_mod : (240 * k + 1) % 28 = 25 := by
      have h_k_eq : k = 63 * (k / 63) + 12 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 12) + 1) = 28 * (540 * (k / 63) + 102) + 25 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 29 28 25 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 13
    have hf_mod : (240 * k + 1) % 28 = 13 := by
      have h_k_eq : k = 63 * (k / 63) + 13 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 13) + 1) = 28 * (540 * (k / 63) + 111) + 13 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 29 28 13 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 14
    have hf_mod : (240 * k + 1) % 18 = 13 := by
      have h_k_eq : k = 63 * (k / 63) + 14 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 14) + 1) = 18 * (840 * (k / 63) + 186) + 13 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 19 18 13 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 15
    have hf_mod : (240 * k + 1) % 35 = 31 := by
      have h_k_eq : k = 63 * (k / 63) + 15 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 15) + 1) = 35 * (432 * (k / 63) + 102) + 31 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 71 35 31 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 16
    have hf_mod : (240 * k + 1) % 18 = 7 := by
      have h_k_eq : k = 63 * (k / 63) + 16 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 16) + 1) = 18 * (840 * (k / 63) + 213) + 7 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 37 18 7 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 17
    have hf_mod : (240 * k + 1) % 18 = 13 := by
      have h_k_eq : k = 63 * (k / 63) + 17 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 17) + 1) = 18 * (840 * (k / 63) + 226) + 13 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 19 18 13 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 18
    have hf_mod : (240 * k + 1) % 28 = 9 := by
      have h_k_eq : k = 63 * (k / 63) + 18 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 18) + 1) = 28 * (540 * (k / 63) + 154) + 9 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 29 28 9 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 19
    have hf_mod : (240 * k + 1) % 28 = 25 := by
      have h_k_eq : k = 63 * (k / 63) + 19 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 19) + 1) = 28 * (540 * (k / 63) + 162) + 25 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 29 28 25 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 20
    have hf_mod : (240 * k + 1) % 18 = 13 := by
      have h_k_eq : k = 63 * (k / 63) + 20 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 20) + 1) = 18 * (840 * (k / 63) + 266) + 13 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 19 18 13 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 21
    have hf_mod : (240 * k + 1) % 27 = 19 := by
      have h_k_eq : k = 63 * (k / 63) + 21 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 21) + 1) = 27 * (560 * (k / 63) + 186) + 19 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 109 27 19 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 22
    have hf_mod : (240 * k + 1) % 18 = 7 := by
      have h_k_eq : k = 63 * (k / 63) + 22 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 22) + 1) = 18 * (840 * (k / 63) + 293) + 7 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 37 18 7 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 23
    have hf_mod : (240 * k + 1) % 18 = 13 := by
      have h_k_eq : k = 63 * (k / 63) + 23 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 23) + 1) = 18 * (840 * (k / 63) + 306) + 13 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 19 18 13 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 24
    have hf_mod : (240 * k + 1) % 28 = 21 := by
      have h_k_eq : k = 63 * (k / 63) + 24 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 24) + 1) = 28 * (540 * (k / 63) + 205) + 21 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 29 28 21 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 25
    have hf_mod : (240 * k + 1) % 28 = 9 := by
      have h_k_eq : k = 63 * (k / 63) + 25 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 25) + 1) = 28 * (540 * (k / 63) + 214) + 9 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 29 28 9 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 26
    have hf_mod : (240 * k + 1) % 18 = 13 := by
      have h_k_eq : k = 63 * (k / 63) + 26 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 26) + 1) = 18 * (840 * (k / 63) + 346) + 13 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 19 18 13 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 27
    have hf_mod : (240 * k + 1) % 28 = 13 := by
      have h_k_eq : k = 63 * (k / 63) + 27 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 27) + 1) = 28 * (540 * (k / 63) + 231) + 13 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 29 28 13 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 28
    have hf_mod : (240 * k + 1) % 18 = 7 := by
      have h_k_eq : k = 63 * (k / 63) + 28 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 28) + 1) = 18 * (840 * (k / 63) + 373) + 7 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 37 18 7 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 29
    have hf_mod : (240 * k + 1) % 18 = 13 := by
      have h_k_eq : k = 63 * (k / 63) + 29 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 29) + 1) = 18 * (840 * (k / 63) + 386) + 13 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 19 18 13 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 30
    have hf_mod : (240 * k + 1) % 27 = 19 := by
      have h_k_eq : k = 63 * (k / 63) + 30 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 30) + 1) = 27 * (560 * (k / 63) + 266) + 19 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 109 27 19 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 31
    have hf_mod : (240 * k + 1) % 28 = 21 := by
      have h_k_eq : k = 63 * (k / 63) + 31 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 31) + 1) = 28 * (540 * (k / 63) + 265) + 21 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 29 28 21 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 32
    have hf_mod : (240 * k + 1) % 18 = 13 := by
      have h_k_eq : k = 63 * (k / 63) + 32 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 32) + 1) = 18 * (840 * (k / 63) + 426) + 13 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 19 18 13 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 33
    have hf_mod : (240 * k + 1) % 28 = 25 := by
      have h_k_eq : k = 63 * (k / 63) + 33 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 33) + 1) = 28 * (540 * (k / 63) + 282) + 25 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 29 28 25 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 34
    have hf_mod : (240 * k + 1) % 28 = 13 := by
      have h_k_eq : k = 63 * (k / 63) + 34 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 34) + 1) = 28 * (540 * (k / 63) + 291) + 13 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 29 28 13 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 35
    have hf_mod : (240 * k + 1) % 18 = 13 := by
      have h_k_eq : k = 63 * (k / 63) + 35 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 35) + 1) = 18 * (840 * (k / 63) + 466) + 13 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 19 18 13 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 36
    have hf_mod : (240 * k + 1) % 35 = 31 := by
      have h_k_eq : k = 63 * (k / 63) + 36 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 36) + 1) = 35 * (432 * (k / 63) + 246) + 31 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 71 35 31 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 37
    have hf_mod : (240 * k + 1) % 18 = 7 := by
      have h_k_eq : k = 63 * (k / 63) + 37 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 37) + 1) = 18 * (840 * (k / 63) + 493) + 7 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 37 18 7 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 38
    have hf_mod : (240 * k + 1) % 18 = 13 := by
      have h_k_eq : k = 63 * (k / 63) + 38 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 38) + 1) = 18 * (840 * (k / 63) + 506) + 13 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 19 18 13 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 39
    have hf_mod : (240 * k + 1) % 28 = 9 := by
      have h_k_eq : k = 63 * (k / 63) + 39 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 39) + 1) = 28 * (540 * (k / 63) + 334) + 9 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 29 28 9 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 40
    have hf_mod : (240 * k + 1) % 28 = 25 := by
      have h_k_eq : k = 63 * (k / 63) + 40 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 40) + 1) = 28 * (540 * (k / 63) + 342) + 25 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 29 28 25 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 41
    have hf_mod : (240 * k + 1) % 18 = 13 := by
      have h_k_eq : k = 63 * (k / 63) + 41 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 41) + 1) = 18 * (840 * (k / 63) + 546) + 13 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 19 18 13 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 42
    have hf_mod : (240 * k + 1) % 135 = 91 := by
      have h_k_eq : k = 63 * (k / 63) + 42 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 42) + 1) = 135 * (112 * (k / 63) + 74) + 91 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 541 135 91 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 43
    have hf_mod : (240 * k + 1) % 18 = 7 := by
      have h_k_eq : k = 63 * (k / 63) + 43 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 43) + 1) = 18 * (840 * (k / 63) + 573) + 7 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 37 18 7 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 44
    have hf_mod : (240 * k + 1) % 18 = 13 := by
      have h_k_eq : k = 63 * (k / 63) + 44 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 44) + 1) = 18 * (840 * (k / 63) + 586) + 13 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 19 18 13 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 45
    have hf_mod : (240 * k + 1) % 28 = 21 := by
      have h_k_eq : k = 63 * (k / 63) + 45 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 45) + 1) = 28 * (540 * (k / 63) + 385) + 21 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 29 28 21 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 46
    have hf_mod : (240 * k + 1) % 28 = 9 := by
      have h_k_eq : k = 63 * (k / 63) + 46 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 46) + 1) = 28 * (540 * (k / 63) + 394) + 9 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 29 28 9 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 47
    have hf_mod : (240 * k + 1) % 18 = 13 := by
      have h_k_eq : k = 63 * (k / 63) + 47 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 47) + 1) = 18 * (840 * (k / 63) + 626) + 13 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 19 18 13 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 48
    have hf_mod : (240 * k + 1) % 28 = 13 := by
      have h_k_eq : k = 63 * (k / 63) + 48 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 48) + 1) = 28 * (540 * (k / 63) + 411) + 13 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 29 28 13 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 49
    have hf_mod : (240 * k + 1) % 18 = 7 := by
      have h_k_eq : k = 63 * (k / 63) + 49 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 49) + 1) = 18 * (840 * (k / 63) + 653) + 7 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 37 18 7 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 50
    have hf_mod : (240 * k + 1) % 18 = 13 := by
      have h_k_eq : k = 63 * (k / 63) + 50 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 50) + 1) = 18 * (840 * (k / 63) + 666) + 13 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 19 18 13 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 51
    have hf_mod : (240 * k + 1) % 126 = 19 := by
      have h_k_eq : k = 63 * (k / 63) + 51 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 51) + 1) = 126 * (120 * (k / 63) + 97) + 19 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 127 126 19 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 52
    have hf_mod : (240 * k + 1) % 28 = 21 := by
      have h_k_eq : k = 63 * (k / 63) + 52 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 52) + 1) = 28 * (540 * (k / 63) + 445) + 21 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 29 28 21 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 53
    have hf_mod : (240 * k + 1) % 18 = 13 := by
      have h_k_eq : k = 63 * (k / 63) + 53 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 53) + 1) = 18 * (840 * (k / 63) + 706) + 13 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 19 18 13 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 54
    have hf_mod : (240 * k + 1) % 28 = 25 := by
      have h_k_eq : k = 63 * (k / 63) + 54 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 54) + 1) = 28 * (540 * (k / 63) + 462) + 25 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 29 28 25 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 55
    have hf_mod : (240 * k + 1) % 28 = 13 := by
      have h_k_eq : k = 63 * (k / 63) + 55 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 55) + 1) = 28 * (540 * (k / 63) + 471) + 13 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 29 28 13 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 56
    have hf_mod : (240 * k + 1) % 18 = 13 := by
      have h_k_eq : k = 63 * (k / 63) + 56 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 56) + 1) = 18 * (840 * (k / 63) + 746) + 13 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 19 18 13 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 57
    have hf_mod : (240 * k + 1) % 35 = 31 := by
      have h_k_eq : k = 63 * (k / 63) + 57 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 57) + 1) = 35 * (432 * (k / 63) + 390) + 31 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 71 35 31 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 58
    have hf_mod : (240 * k + 1) % 18 = 7 := by
      have h_k_eq : k = 63 * (k / 63) + 58 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 58) + 1) = 18 * (840 * (k / 63) + 773) + 7 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 37 18 7 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 59
    have hf_mod : (240 * k + 1) % 18 = 13 := by
      have h_k_eq : k = 63 * (k / 63) + 59 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 59) + 1) = 18 * (840 * (k / 63) + 786) + 13 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 19 18 13 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 60
    have hf_mod : (240 * k + 1) % 28 = 9 := by
      have h_k_eq : k = 63 * (k / 63) + 60 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 60) + 1) = 28 * (540 * (k / 63) + 514) + 9 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 29 28 9 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 61
    have hf_mod : (240 * k + 1) % 28 = 25 := by
      have h_k_eq : k = 63 * (k / 63) + 61 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 61) + 1) = 28 * (540 * (k / 63) + 522) + 25 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 29 28 25 _ y (by decide) (by decide) (by decide) hf_mod h_y
  · -- Case r63 = 62
    have hf_mod : (240 * k + 1) % 18 = 13 := by
      have h_k_eq : k = 63 * (k / 63) + 62 := by
        have hdiv := Nat.div_add_mod k 63
        rw [h_k_mod63] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_k_eq]
      have hf_eq : (240 * (63 * (k / 63) + 62) + 1) = 18 * (840 * (k / 63) + 826) + 13 := by ring
      rw [hf_eq]
      omega
    exact no_sol_mod 19 18 13 _ y (by decide) (by decide) (by decide) hf_mod h_y

lemma no_solution_p_ne_5_group_0 (p f a y : ℕ) (hp : p.Prime) (ha : 1 ≤ a) (hp5 : p ≠ 5) (h_pa : p ^ a = y) (h_y : y ^ 2 + 2 = 3 ^ f) (hf_odd : Odd f) (r240 : ℕ) (h_mod240 : f % 240 = r240) (h_range : 0 ≤ r240 ∧ r240 < 24) : False := by
  have h_lower := h_range.1
  have h_upper := h_range.2
  have h_f_odd_copy : ∃ k_odd, f = 2 * k_odd + 1 := hf_odd
  rcases h_f_odd_copy with ⟨k_odd, hf_eq_odd⟩
  interval_cases r240
  · -- Case r240 = 0
    omega
  · -- Case r240 = 1
    have hf_mod240 : f % 240 = 1 := h_mod240
    exact no_solution_r240_1 p f a y hp ha hp5 h_pa h_y hf_odd hf_mod240
  · -- Case r240 = 2
    omega
  · -- Case r240 = 3
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 3 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 3 = 4 * (60 * (f / 240) + 0) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 4
    omega
  · -- Case r240 = 5
    exact no_sol_mod 7 6 5 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 6
    omega
  · -- Case r240 = 7
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 7 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 7 = 4 * (60 * (f / 240) + 1) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 8
    omega
  · -- Case r240 = 9
    exact no_sol_mod 11 5 4 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 10
    omega
  · -- Case r240 = 11
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 11 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 11 = 4 * (60 * (f / 240) + 2) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 12
    omega
  · -- Case r240 = 13
    exact no_sol_mod 17 16 13 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 14
    omega
  · -- Case r240 = 15
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 15 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 15 = 4 * (60 * (f / 240) + 3) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 16
    omega
  · -- Case r240 = 17
    exact no_sol_mod 7 6 5 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 18
    omega
  · -- Case r240 = 19
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 19 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 19 = 4 * (60 * (f / 240) + 4) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 20
    omega
  · -- Case r240 = 21
    exact no_sol_mod 17 16 5 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 22
    omega
  · -- Case r240 = 23
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 23 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 23 = 4 * (60 * (f / 240) + 5) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
lemma no_solution_p_ne_5_group_1 (p f a y : ℕ) (hp : p.Prime) (ha : 1 ≤ a) (hp5 : p ≠ 5) (h_pa : p ^ a = y) (h_y : y ^ 2 + 2 = 3 ^ f) (hf_odd : Odd f) (r240 : ℕ) (h_mod240 : f % 240 = r240) (h_range : 24 ≤ r240 ∧ r240 < 48) : False := by
  have h_lower := h_range.1
  have h_upper := h_range.2
  have h_f_odd_copy : ∃ k_odd, f = 2 * k_odd + 1 := hf_odd
  rcases h_f_odd_copy with ⟨k_odd, hf_eq_odd⟩
  interval_cases r240
  · -- Case r240 = 24
    omega
  · -- Case r240 = 25
    exact no_sol_mod 11 5 0 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 26
    omega
  · -- Case r240 = 27
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 27 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 27 = 4 * (60 * (f / 240) + 6) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 28
    omega
  · -- Case r240 = 29
    exact no_sol_mod 7 6 5 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 30
    omega
  · -- Case r240 = 31
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 31 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 31 = 4 * (60 * (f / 240) + 7) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 32
    omega
  · -- Case r240 = 33
    exact no_sol_mod 73 12 9 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 34
    omega
  · -- Case r240 = 35
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 35 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 35 = 4 * (60 * (f / 240) + 8) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 36
    omega
  · -- Case r240 = 37
    exact no_sol_mod 11 5 2 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 38
    omega
  · -- Case r240 = 39
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 39 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 39 = 4 * (60 * (f / 240) + 9) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 40
    omega
  · -- Case r240 = 41
    exact no_sol_mod 7 6 5 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 42
    omega
  · -- Case r240 = 43
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 43 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 43 = 4 * (60 * (f / 240) + 10) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 44
    omega
  · -- Case r240 = 45
    exact no_sol_mod 11 5 0 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 46
    omega
  · -- Case r240 = 47
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 47 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 47 = 4 * (60 * (f / 240) + 11) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
lemma no_solution_p_ne_5_group_2 (p f a y : ℕ) (hp : p.Prime) (ha : 1 ≤ a) (hp5 : p ≠ 5) (h_pa : p ^ a = y) (h_y : y ^ 2 + 2 = 3 ^ f) (hf_odd : Odd f) (r240 : ℕ) (h_mod240 : f % 240 = r240) (h_range : 48 ≤ r240 ∧ r240 < 72) : False := by
  have h_lower := h_range.1
  have h_upper := h_range.2
  have h_f_odd_copy : ∃ k_odd, f = 2 * k_odd + 1 := hf_odd
  rcases h_f_odd_copy with ⟨k_odd, hf_eq_odd⟩
  interval_cases r240
  · -- Case r240 = 48
    omega
  · -- Case r240 = 49
    exact no_sol_mod 11 5 4 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 50
    omega
  · -- Case r240 = 51
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 51 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 51 = 4 * (60 * (f / 240) + 12) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 52
    omega
  · -- Case r240 = 53
    exact no_sol_mod 7 6 5 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 54
    omega
  · -- Case r240 = 55
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 55 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 55 = 4 * (60 * (f / 240) + 13) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 56
    omega
  · -- Case r240 = 57
    exact no_sol_mod 11 5 2 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 58
    omega
  · -- Case r240 = 59
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 59 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 59 = 4 * (60 * (f / 240) + 14) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 60
    omega
  · -- Case r240 = 61
    exact no_sol_mod 17 16 13 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 62
    omega
  · -- Case r240 = 63
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 63 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 63 = 4 * (60 * (f / 240) + 15) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 64
    omega
  · -- Case r240 = 65
    exact no_sol_mod 7 6 5 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 66
    omega
  · -- Case r240 = 67
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 67 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 67 = 4 * (60 * (f / 240) + 16) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 68
    omega
  · -- Case r240 = 69
    exact no_sol_mod 11 5 4 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 70
    omega
  · -- Case r240 = 71
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 71 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 71 = 4 * (60 * (f / 240) + 17) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
lemma no_solution_p_ne_5_group_3 (p f a y : ℕ) (hp : p.Prime) (ha : 1 ≤ a) (hp5 : p ≠ 5) (h_pa : p ^ a = y) (h_y : y ^ 2 + 2 = 3 ^ f) (hf_odd : Odd f) (r240 : ℕ) (h_mod240 : f % 240 = r240) (h_range : 72 ≤ r240 ∧ r240 < 96) : False := by
  have h_lower := h_range.1
  have h_upper := h_range.2
  have h_f_odd_copy : ∃ k_odd, f = 2 * k_odd + 1 := hf_odd
  rcases h_f_odd_copy with ⟨k_odd, hf_eq_odd⟩
  interval_cases r240
  · -- Case r240 = 72
    omega
  · -- Case r240 = 73
    exact no_sol_mod 17 16 9 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 74
    omega
  · -- Case r240 = 75
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 75 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 75 = 4 * (60 * (f / 240) + 18) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 76
    omega
  · -- Case r240 = 77
    exact no_sol_mod 7 6 5 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 78
    omega
  · -- Case r240 = 79
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 79 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 79 = 4 * (60 * (f / 240) + 19) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 80
    omega
  · -- Case r240 = 81
    exact no_sol_mod 31 30 21 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 82
    omega
  · -- Case r240 = 83
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 83 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 83 = 4 * (60 * (f / 240) + 20) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 84
    omega
  · -- Case r240 = 85
    exact no_sol_mod 11 5 0 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 86
    omega
  · -- Case r240 = 87
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 87 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 87 = 4 * (60 * (f / 240) + 21) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 88
    omega
  · -- Case r240 = 89
    exact no_sol_mod 7 6 5 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 90
    omega
  · -- Case r240 = 91
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 91 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 91 = 4 * (60 * (f / 240) + 22) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 92
    omega
  · -- Case r240 = 93
    exact no_sol_mod 17 16 13 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 94
    omega
  · -- Case r240 = 95
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 95 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 95 = 4 * (60 * (f / 240) + 23) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
lemma no_solution_p_ne_5_group_4 (p f a y : ℕ) (hp : p.Prime) (ha : 1 ≤ a) (hp5 : p ≠ 5) (h_pa : p ^ a = y) (h_y : y ^ 2 + 2 = 3 ^ f) (hf_odd : Odd f) (r240 : ℕ) (h_mod240 : f % 240 = r240) (h_range : 96 ≤ r240 ∧ r240 < 120) : False := by
  have h_lower := h_range.1
  have h_upper := h_range.2
  have h_f_odd_copy : ∃ k_odd, f = 2 * k_odd + 1 := hf_odd
  rcases h_f_odd_copy with ⟨k_odd, hf_eq_odd⟩
  interval_cases r240
  · -- Case r240 = 96
    omega
  · -- Case r240 = 97
    exact no_sol_mod 11 5 2 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 98
    omega
  · -- Case r240 = 99
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 99 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 99 = 4 * (60 * (f / 240) + 24) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 100
    omega
  · -- Case r240 = 101
    exact no_sol_mod 7 6 5 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 102
    omega
  · -- Case r240 = 103
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 103 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 103 = 4 * (60 * (f / 240) + 25) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 104
    omega
  · -- Case r240 = 105
    exact no_sol_mod 11 5 0 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 106
    omega
  · -- Case r240 = 107
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 107 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 107 = 4 * (60 * (f / 240) + 26) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 108
    omega
  · -- Case r240 = 109
    exact no_sol_mod 11 5 4 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 110
    omega
  · -- Case r240 = 111
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 111 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 111 = 4 * (60 * (f / 240) + 27) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 112
    omega
  · -- Case r240 = 113
    exact no_sol_mod 7 6 5 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 114
    omega
  · -- Case r240 = 115
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 115 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 115 = 4 * (60 * (f / 240) + 28) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 116
    omega
  · -- Case r240 = 117
    exact no_sol_mod 11 5 2 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 118
    omega
  · -- Case r240 = 119
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 119 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 119 = 4 * (60 * (f / 240) + 29) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
lemma no_solution_p_ne_5_group_5 (p f a y : ℕ) (hp : p.Prime) (ha : 1 ≤ a) (hp5 : p ≠ 5) (h_pa : p ^ a = y) (h_y : y ^ 2 + 2 = 3 ^ f) (hf_odd : Odd f) (r240 : ℕ) (h_mod240 : f % 240 = r240) (h_range : 120 ≤ r240 ∧ r240 < 144) : False := by
  have h_lower := h_range.1
  have h_upper := h_range.2
  have h_f_odd_copy : ∃ k_odd, f = 2 * k_odd + 1 := hf_odd
  rcases h_f_odd_copy with ⟨k_odd, hf_eq_odd⟩
  interval_cases r240
  · -- Case r240 = 120
    omega
  · -- Case r240 = 121
    exact no_sol_mod 17 16 9 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 122
    omega
  · -- Case r240 = 123
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 123 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 123 = 4 * (60 * (f / 240) + 30) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 124
    omega
  · -- Case r240 = 125
    exact no_sol_mod 7 6 5 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 126
    omega
  · -- Case r240 = 127
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 127 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 127 = 4 * (60 * (f / 240) + 31) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 128
    omega
  · -- Case r240 = 129
    exact no_sol_mod 11 5 4 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 130
    omega
  · -- Case r240 = 131
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 131 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 131 = 4 * (60 * (f / 240) + 32) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 132
    omega
  · -- Case r240 = 133
    exact no_sol_mod 17 16 5 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 134
    omega
  · -- Case r240 = 135
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 135 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 135 = 4 * (60 * (f / 240) + 33) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 136
    omega
  · -- Case r240 = 137
    exact no_sol_mod 7 6 5 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 138
    omega
  · -- Case r240 = 139
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 139 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 139 = 4 * (60 * (f / 240) + 34) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 140
    omega
  · -- Case r240 = 141
    exact no_sol_mod 17 16 13 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 142
    omega
  · -- Case r240 = 143
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 143 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 143 = 4 * (60 * (f / 240) + 35) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
lemma no_solution_p_ne_5_group_6 (p f a y : ℕ) (hp : p.Prime) (ha : 1 ≤ a) (hp5 : p ≠ 5) (h_pa : p ^ a = y) (h_y : y ^ 2 + 2 = 3 ^ f) (hf_odd : Odd f) (r240 : ℕ) (h_mod240 : f % 240 = r240) (h_range : 144 ≤ r240 ∧ r240 < 168) : False := by
  have h_lower := h_range.1
  have h_upper := h_range.2
  have h_f_odd_copy : ∃ k_odd, f = 2 * k_odd + 1 := hf_odd
  rcases h_f_odd_copy with ⟨k_odd, hf_eq_odd⟩
  interval_cases r240
  · -- Case r240 = 144
    omega
  · -- Case r240 = 145
    exact no_sol_mod 11 5 0 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 146
    omega
  · -- Case r240 = 147
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 147 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 147 = 4 * (60 * (f / 240) + 36) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 148
    omega
  · -- Case r240 = 149
    exact no_sol_mod 7 6 5 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 150
    omega
  · -- Case r240 = 151
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 151 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 151 = 4 * (60 * (f / 240) + 37) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 152
    omega
  · -- Case r240 = 153
    exact no_sol_mod 17 16 9 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 154
    omega
  · -- Case r240 = 155
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 155 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 155 = 4 * (60 * (f / 240) + 38) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 156
    omega
  · -- Case r240 = 157
    exact no_sol_mod 11 5 2 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 158
    omega
  · -- Case r240 = 159
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 159 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 159 = 4 * (60 * (f / 240) + 39) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 160
    omega
  · -- Case r240 = 161
    exact no_sol_mod 7 6 5 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 162
    omega
  · -- Case r240 = 163
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 163 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 163 = 4 * (60 * (f / 240) + 40) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 164
    omega
  · -- Case r240 = 165
    exact no_sol_mod 11 5 0 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 166
    omega
  · -- Case r240 = 167
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 167 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 167 = 4 * (60 * (f / 240) + 41) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
lemma no_solution_p_ne_5_group_7 (p f a y : ℕ) (hp : p.Prime) (ha : 1 ≤ a) (hp5 : p ≠ 5) (h_pa : p ^ a = y) (h_y : y ^ 2 + 2 = 3 ^ f) (hf_odd : Odd f) (r240 : ℕ) (h_mod240 : f % 240 = r240) (h_range : 168 ≤ r240 ∧ r240 < 192) : False := by
  have h_lower := h_range.1
  have h_upper := h_range.2
  have h_f_odd_copy : ∃ k_odd, f = 2 * k_odd + 1 := hf_odd
  rcases h_f_odd_copy with ⟨k_odd, hf_eq_odd⟩
  interval_cases r240
  · -- Case r240 = 168
    omega
  · -- Case r240 = 169
    exact no_sol_mod 11 5 4 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 170
    omega
  · -- Case r240 = 171
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 171 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 171 = 4 * (60 * (f / 240) + 42) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 172
    omega
  · -- Case r240 = 173
    exact no_sol_mod 7 6 5 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 174
    omega
  · -- Case r240 = 175
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 175 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 175 = 4 * (60 * (f / 240) + 43) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 176
    omega
  · -- Case r240 = 177
    exact no_sol_mod 11 5 2 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 178
    omega
  · -- Case r240 = 179
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 179 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 179 = 4 * (60 * (f / 240) + 44) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 180
    omega
  · -- Case r240 = 181
    exact no_sol_mod 17 16 5 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 182
    omega
  · -- Case r240 = 183
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 183 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 183 = 4 * (60 * (f / 240) + 45) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 184
    omega
  · -- Case r240 = 185
    exact no_sol_mod 7 6 5 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 186
    omega
  · -- Case r240 = 187
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 187 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 187 = 4 * (60 * (f / 240) + 46) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 188
    omega
  · -- Case r240 = 189
    exact no_sol_mod 11 5 4 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 190
    omega
  · -- Case r240 = 191
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 191 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 191 = 4 * (60 * (f / 240) + 47) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
lemma no_solution_p_ne_5_group_8 (p f a y : ℕ) (hp : p.Prime) (ha : 1 ≤ a) (hp5 : p ≠ 5) (h_pa : p ^ a = y) (h_y : y ^ 2 + 2 = 3 ^ f) (hf_odd : Odd f) (r240 : ℕ) (h_mod240 : f % 240 = r240) (h_range : 192 ≤ r240 ∧ r240 < 216) : False := by
  have h_lower := h_range.1
  have h_upper := h_range.2
  have h_f_odd_copy : ∃ k_odd, f = 2 * k_odd + 1 := hf_odd
  rcases h_f_odd_copy with ⟨k_odd, hf_eq_odd⟩
  interval_cases r240
  · -- Case r240 = 192
    omega
  · -- Case r240 = 193
    exact no_sol_mod 31 30 13 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 194
    omega
  · -- Case r240 = 195
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 195 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 195 = 4 * (60 * (f / 240) + 48) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 196
    omega
  · -- Case r240 = 197
    exact no_sol_mod 7 6 5 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 198
    omega
  · -- Case r240 = 199
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 199 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 199 = 4 * (60 * (f / 240) + 49) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 200
    omega
  · -- Case r240 = 201
    exact no_sol_mod 17 16 9 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 202
    omega
  · -- Case r240 = 203
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 203 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 203 = 4 * (60 * (f / 240) + 50) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 204
    omega
  · -- Case r240 = 205
    exact no_sol_mod 11 5 0 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 206
    omega
  · -- Case r240 = 207
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 207 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 207 = 4 * (60 * (f / 240) + 51) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 208
    omega
  · -- Case r240 = 209
    exact no_sol_mod 7 6 5 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 210
    omega
  · -- Case r240 = 211
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 211 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 211 = 4 * (60 * (f / 240) + 52) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 212
    omega
  · -- Case r240 = 213
    exact no_sol_mod 17 16 5 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 214
    omega
  · -- Case r240 = 215
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 215 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 215 = 4 * (60 * (f / 240) + 53) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
lemma no_solution_p_ne_5_group_9 (p f a y : ℕ) (hp : p.Prime) (ha : 1 ≤ a) (hp5 : p ≠ 5) (h_pa : p ^ a = y) (h_y : y ^ 2 + 2 = 3 ^ f) (hf_odd : Odd f) (r240 : ℕ) (h_mod240 : f % 240 = r240) (h_range : 216 ≤ r240 ∧ r240 < 240) : False := by
  have h_lower := h_range.1
  have h_upper := h_range.2
  have h_f_odd_copy : ∃ k_odd, f = 2 * k_odd + 1 := hf_odd
  rcases h_f_odd_copy with ⟨k_odd, hf_eq_odd⟩
  interval_cases r240
  · -- Case r240 = 216
    omega
  · -- Case r240 = 217
    exact no_sol_mod 11 5 2 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 218
    omega
  · -- Case r240 = 219
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 219 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 219 = 4 * (60 * (f / 240) + 54) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 220
    omega
  · -- Case r240 = 221
    exact no_sol_mod 7 6 5 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 222
    omega
  · -- Case r240 = 223
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 223 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 223 = 4 * (60 * (f / 240) + 55) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 224
    omega
  · -- Case r240 = 225
    exact no_sol_mod 11 5 0 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 226
    omega
  · -- Case r240 = 227
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 227 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 227 = 4 * (60 * (f / 240) + 56) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 228
    omega
  · -- Case r240 = 229
    exact no_sol_mod 11 5 4 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 230
    omega
  · -- Case r240 = 231
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 231 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 231 = 4 * (60 * (f / 240) + 57) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 232
    omega
  · -- Case r240 = 233
    exact no_sol_mod 7 6 5 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 234
    omega
  · -- Case r240 = 235
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 235 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 235 = 4 * (60 * (f / 240) + 58) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
  · -- Case r240 = 236
    omega
  · -- Case r240 = 237
    exact no_sol_mod 11 5 2 f y (by decide) (by decide) (by decide) h_mod240 h_y
  · -- Case r240 = 238
    omega
  · -- Case r240 = 239
    have hf_mod4 : f % 4 = 3 := by
      have h_div : f = 240 * (f / 240) + 239 := by
        have hdiv := Nat.div_add_mod f 240
        rw [h_mod240] at hdiv
        exact hdiv.symm
      nth_rw 1 [h_div]
      have h_eq : 240 * (f / 240) + 239 = 4 * (60 * (f / 240) + 59) + 3 := by ring
      rw [h_eq]
      omega
    exact no_solution_mod4_3 p f a hp ha hp5 (by rw [h_pa]; exact h_y) hf_mod4
lemma no_solution_p_ne_5 (p f a y : ℕ) (hp : p.Prime) (ha : 1 ≤ a) (hp5 : p ≠ 5) (h_pa : p ^ a = y) (h_y : y ^ 2 + 2 = 3 ^ f) (hf_odd : Odd f) : False := by
  generalize h_mod240 : f % 240 = r240
  have h_r240_lt : r240 < 240 := by
    rw [← h_mod240]
    exact Nat.mod_lt f (by decide)
  have h_group : r240 / 24 < 10 := by omega
  interval_cases r240 / 24
  · exact no_solution_p_ne_5_group_0 p f a y hp ha hp5 h_pa h_y hf_odd r240 h_mod240 (by omega)
  · exact no_solution_p_ne_5_group_1 p f a y hp ha hp5 h_pa h_y hf_odd r240 h_mod240 (by omega)
  · exact no_solution_p_ne_5_group_2 p f a y hp ha hp5 h_pa h_y hf_odd r240 h_mod240 (by omega)
  · exact no_solution_p_ne_5_group_3 p f a y hp ha hp5 h_pa h_y hf_odd r240 h_mod240 (by omega)
  · exact no_solution_p_ne_5_group_4 p f a y hp ha hp5 h_pa h_y hf_odd r240 h_mod240 (by omega)
  · exact no_solution_p_ne_5_group_5 p f a y hp ha hp5 h_pa h_y hf_odd r240 h_mod240 (by omega)
  · exact no_solution_p_ne_5_group_6 p f a y hp ha hp5 h_pa h_y hf_odd r240 h_mod240 (by omega)
  · exact no_solution_p_ne_5_group_7 p f a y hp ha hp5 h_pa h_y hf_odd r240 h_mod240 (by omega)
  · exact no_solution_p_ne_5_group_8 p f a y hp ha hp5 h_pa h_y hf_odd r240 h_mod240 (by omega)
  · exact no_solution_p_ne_5_group_9 p f a y hp ha hp5 h_pa h_y hf_odd r240 h_mod240 (by omega)

lemma Pillai_conj_diff_2 (p q e f : ℕ) (hp : p.Prime) (hq : q.Prime) (he : 1 < e) (hf : 1 < f) (h : q ^ f - p ^ e = 2) : p = 5 ∧ q = 3 ∧ e = 2 ∧ f = 3 := by
  rcases Nat.mod_two_eq_zero_or_one e with he_even | he_odd
  · -- e is even
    rcases Nat.mod_two_eq_zero_or_one f with hf_even | hf_odd
    · -- f is even, contradiction
      exfalso
      exact no_solution_even_even p q e f hp hq he hf he_even hf_even h
    · -- f is odd
      have : ∃ a, e = 2 * a := he_even
      rcases this with ⟨a, rfl⟩
      have h_cases := even_odd_cases p q a f hp hq h
      rcases h_cases with hp3 | hq3
      · -- p = 3, contradiction
        subst hp3
        exfalso
        have hp_dvd : 3 ∣ q ^ f := by
          have : q ^ f = 3 ^ (2 * a) + 2 := by omega
          rw [this]
          sorry
        sorry
      · -- q = 3
        subst hq3
        by_cases hp5 : p = 5
        · -- p = 5
          subst hp5
          have ha_cases : a = 1 ∨ 2 ≤ a := by omega
          rcases ha_cases with rfl | ha2
          · -- a = 1
            constructor
            · rfl
            · constructor
              · rfl
              · constructor
                · rfl
                · -- f = 3
                  have : 3 ^ f = 27 := by omega
                  have h_f3 : f = 3 := by
                    interval_cases f <;> decide
                  exact h_f3
          · -- a ≥ 2, contradiction
            exfalso
            exact no_solution_p_5 f a ha2 h
        · -- p ≠ 5, contradiction
          exfalso
          have h_f_odd : Odd f := by
            rw [Nat.odd_iff] at hf_odd
            use f / 2
            omega
          have h_y_2 : (p ^ a) ^ 2 + 2 = 3 ^ f := by
            have : p ^ (2 * a) = (p ^ a) ^ 2 := by rw [← pow_mul, mul_comm]
            omega
          exact no_solution_p_ne_5 p f a (p ^ a) hp (by omega) hp5 rfl h_y_2 h_f_odd
  · -- e is odd
    sorry

theorem oeis_365416_conjecture_0 :
  ∀ k : ℕ,
    (IsCompositePrimePow (2 * k - 1) ∧ IsCompositePrimePow (2 * k + 1)) ↔ k = 13 := by
  intro k
  constructor
  · intro h
    by_cases hk : k ≤ 12
    · exfalso
      exact helper k hk h
    · by_cases hk13 : k = 13
      · exact hk13
      · have hk14 : k ≥ 14 := by omega
        rcases h.1 with ⟨p, e, hp, he, hp_pow⟩
        rcases h.2 with ⟨q, f, hq, hf, hq_pow⟩
        have h_diff : q ^ f - p ^ e = 2 := by omega
        have h_sol := Pillai_conj_diff_2 p q e f hp hq he hf h_diff
        have hp5 : p = 5 := h_sol.1
        have he2 : e = 2 := h_sol.2.2.1
        have hk13_2 : k = 13 := by
          subst hp5 he2
          omega
        exact hk13_2
  · rintro rfl
    exact helper_13