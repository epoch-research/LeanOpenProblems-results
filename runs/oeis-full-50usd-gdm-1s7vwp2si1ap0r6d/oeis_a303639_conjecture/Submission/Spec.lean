import FormalConjectures.Util.ProblemImports

open Nat BigOperators

/--
A303639: Number of ways to write $n$ as $a^2 + b^2 + \binom{2c+1}{c} + \binom{2d+1}{d}$,
where $a,b,c,d$ are nonnegative integers with $a \le b$ and $c \le d$.
-/
def a (n : ℕ) : ℕ :=
  -- Helper for the binomial coefficient term: B(k) = binomial(2*k+1, k)
  let B (k : ℕ) : ℕ := (2 * k + 1).choose k

  -- The maximum value for $a, b$ is $\lfloor \sqrt{n} \rfloor$.
  -- We can use `Finset.range (n + 1)` as an upper bound for convenience,
  -- but the definition provided uses `n.sqrt + 1`, which is tighter.
  let R_sq := Finset.range (n.sqrt + 1)
  -- The maximum value for $c, d$ is safely bounded by $n$.
  let R_binom := Finset.range (n + 1)

  R_sq.sum fun a =>
    R_sq.sum fun b =>
      R_binom.sum fun c =>
        R_binom.sum fun d =>
          if a ≤ b ∧ c ≤ d ∧ a ^ 2 + b ^ 2 + B c + B d = n then 1 else 0

/--
Conjecture A303639: $a(n) > 0$ for all $n > 1$.
-/
lemma a_pos_iff (n : ℕ) :
    a n > 0 ↔ ∃ a_0 < n.sqrt + 1, ∃ b_0 < n.sqrt + 1, ∃ c_0 < n + 1, ∃ d_0 < n + 1,
    a_0 ≤ b_0 ∧ c_0 ≤ d_0 ∧ a_0 ^ 2 + b_0 ^ 2 + (2 * c_0 + 1).choose c_0 + (2 * d_0 + 1).choose d_0 = n := by
  unfold a
  dsimp
  change 0 < (∑ a ∈ Finset.range (n.sqrt + 1),
        ∑ b ∈ Finset.range (n.sqrt + 1),
          ∑ c ∈ Finset.range (n + 1),
            ∑ d ∈ Finset.range (n + 1),
              if a ≤ b ∧ c ≤ d ∧ a ^ 2 + b ^ 2 + (2 * c + 1).choose c + (2 * d + 1).choose d = n then 1 else 0) ↔ _
  rw [Finset.sum_pos_iff_of_nonneg]
  · simp only [Finset.mem_range]
    constructor
    · rintro ⟨a_0, ha0, h1⟩
      rw [Finset.sum_pos_iff_of_nonneg (by simp)] at h1
      rcases h1 with ⟨b_0, hb0, h2⟩
      rw [Finset.sum_pos_iff_of_nonneg (by simp)] at h2
      rcases h2 with ⟨c_0, hc0, h3⟩
      rw [Finset.sum_pos_iff_of_nonneg (by simp)] at h3
      rcases h3 with ⟨d_0, hd0, h4⟩
      rw [Finset.mem_range] at hb0 hc0 hd0
      split_ifs at h4 with h_eq
      · refine ⟨a_0, ha0, b_0, hb0, c_0, hc0, d_0, hd0, h_eq⟩
      · omega
    · rintro ⟨a_0, ha0, b_0, hb0, c_0, hc0, d_0, hd0, hab, hcd, h_eq⟩
      rw [← Finset.mem_range] at hb0 hc0 hd0
      refine ⟨a_0, ha0, ?_⟩
      rw [Finset.sum_pos_iff_of_nonneg (by simp)]
      refine ⟨b_0, hb0, ?_⟩
      rw [Finset.sum_pos_iff_of_nonneg (by simp)]
      refine ⟨c_0, hc0, ?_⟩
      rw [Finset.sum_pos_iff_of_nonneg (by simp)]
      refine ⟨d_0, hd0, ?_⟩
      split_ifs with h_cond
      · omega
      · exfalso
        exact h_cond ⟨hab, hcd, h_eq⟩
  · intro x hx
    exact zero_le'

lemma choose_mono_step (d : ℕ) : (2 * d + 1).choose d ≤ (2 * (d + 1) + 1).choose (d + 1) := by
  have h1 : 2 * (d + 1) + 1 = 2 * d + 3 := by omega
  have h2 : 2 * d + 3 = (2 * d + 2) + 1 := by omega
  rw [h1, h2, Nat.choose_succ_succ]
  have h3 : (2 * d + 1).choose d ≤ (2 * d + 2).choose d := Nat.choose_le_choose d (by omega)
  have h4 : (2 * d + 2).choose (d + 1) = (2 * d + 1).choose d + (2 * d + 1).choose (d + 1) := by
    have h_eq : 2 * d + 2 = (2 * d + 1) + 1 := by omega
    rw [h_eq, Nat.choose_succ_succ]
  omega

lemma choose_lower_bound (d : ℕ) (hd : d ≥ 16) : (2 * d + 1).choose d ≥ 1166803110 := by
  induction hd with
  | refl => decide
  | step hd ih =>
    rename_i k
    have h_mono := choose_mono_step k
    have h_succ : k.succ = k + 1 := rfl
    rw [h_succ]
    omega

lemma sq_add_sq_zero_of_prime_mod_four_eq_three (p : ℕ) [hp : Fact p.Prime] (hp3 : p % 4 = 3)
    (x y : ZMod p) (h : x ^ 2 + y ^ 2 = 0) : x = 0 ∧ y = 0 := by
  by_cases hy : y = 0
  · rw [hy, zero_pow (by decide), add_zero] at h
    have hx : x = 0 := sq_eq_zero_iff.mp h
    exact ⟨hx, hy⟩
  · exfalso
    have h_eq : x ^ 2 = - y ^ 2 := eq_neg_of_add_eq_zero_left h
    have h_div : (x * y⁻¹) ^ 2 = -1 := by
      calc (x * y⁻¹) ^ 2
        _ = x ^ 2 * (y⁻¹) ^ 2 := mul_pow x _ 2
        _ = - y ^ 2 * (y⁻¹) ^ 2 := by rw [h_eq]
        _ = - (y * y⁻¹) ^ 2 := by
          rw [neg_mul, mul_pow]
        _ = -1 := by
          have h_inv : y * y⁻¹ = 1 := DivisionRing.mul_inv_cancel y hy
          rw [h_inv, one_pow]
    have h_sq : IsSquare (-1 : ZMod p) := ⟨x * y⁻¹, by rw [← h_div, sq]⟩
    have h_not_sq : ¬ IsSquare (-1 : ZMod p) := by
      rw [ZMod.exists_sq_eq_neg_one_iff]
      omega
    exact h_not_sq h_sq

lemma step_reduction (p : ℕ) [hp : Fact p.Prime] (hp3 : p % 4 = 3) (m : ℕ)
    (a b : ℕ) (h : a ^ 2 + b ^ 2 = p ^ 2 * m) : (a / p) ^ 2 + (b / p) ^ 2 = m := by
  have hp_pos : p > 0 := Fact.out (p := p.Prime) |>.pos
  have hp_pow_pos : p ^ 2 > 0 := by positivity
  have h_mod : (a : ZMod p) ^ 2 + (b : ZMod p) ^ 2 = 0 := by
    rw [← Nat.cast_pow, ← Nat.cast_pow, ← Nat.cast_add, h]
    have hd_p : p ∣ p ^ 2 * m := by
      use p * m
      ring
    exact (CharP.cast_eq_zero_iff (ZMod p) p (p ^ 2 * m)).mpr hd_p
  have h_zero := sq_add_sq_zero_of_prime_mod_four_eq_three p hp3 a b h_mod
  have h_dvd_a : p ∣ a := (CharP.cast_eq_zero_iff (ZMod p) p a).mp h_zero.left
  have h_dvd_b : p ∣ b := (CharP.cast_eq_zero_iff (ZMod p) p b).mp h_zero.right
  rcases h_dvd_a with ⟨k_a, rfl⟩
  rcases h_dvd_b with ⟨k_b, rfl⟩
  have h_m_sq : p ^ 2 * (k_a ^ 2 + k_b ^ 2) = p ^ 2 * m := by
    calc p ^ 2 * (k_a ^ 2 + k_b ^ 2)
      _ = (p * k_a) ^ 2 + (p * k_b) ^ 2 := by ring
      _ = p ^ 2 * m := h
  have h_eq_m : k_a ^ 2 + k_b ^ 2 = m := Nat.eq_of_mul_eq_mul_left hp_pow_pos h_m_sq
  have h_div_a : (p * k_a) / p = k_a := Nat.mul_div_cancel_left k_a hp_pos
  have h_div_b : (p * k_b) / p = k_b := Nat.mul_div_cancel_left k_b hp_pos
  rw [h_div_a, h_div_b]
  exact h_eq_m

theorem no_sol_of_prime_div_sq (p : ℕ) [hp : Fact p.Prime] (hp3 : p % 4 = 3) (m : ℕ)
    (hd1 : p ∣ m) (hd2 : ¬ p ^ 2 ∣ m) (a b : ℕ) (h : a ^ 2 + b ^ 2 = m) : False := by
  have h_mod : (a : ZMod p) ^ 2 + (b : ZMod p) ^ 2 = 0 := by
    rw [← Nat.cast_pow, ← Nat.cast_pow, ← Nat.cast_add, h]
    exact (CharP.cast_eq_zero_iff (ZMod p) p m).mpr hd1
  have h_zero := sq_add_sq_zero_of_prime_mod_four_eq_three p hp3 a b h_mod
  have h_dvd_a : p ∣ a := (CharP.cast_eq_zero_iff (ZMod p) p a).mp h_zero.left
  have h_dvd_b : p ∣ b := (CharP.cast_eq_zero_iff (ZMod p) p b).mp h_zero.right
  rcases h_dvd_a with ⟨k_a, rfl⟩
  rcases h_dvd_b with ⟨k_b, rfl⟩
  have h_m_sq : p ^ 2 * (k_a ^ 2 + k_b ^ 2) = m := by
    calc p ^ 2 * (k_a ^ 2 + k_b ^ 2)
      _ = (p * k_a) ^ 2 + (p * k_b) ^ 2 := by ring
      _ = m := h
  have h_p2_dvd : p ^ 2 ∣ m := ⟨k_a ^ 2 + k_b ^ 2, h_m_sq.symm⟩
  exact hd2 h_p2_dvd

theorem oeis_a303639_conjecture.disproof : ¬ ∀ (n : ℕ), n > 1 → a n > 0 := by
  intro h
  have h1 : 800322180 > 1 := by omega
  have h2 : a 800322180 > 0 := h 800322180 h1
  rw [a_pos_iff] at h2
  rcases h2 with ⟨a_0, ha0, b_0, hb0, c_0, hc0, d_0, hd0, hab, hcd, h_eq⟩
  have hd_le : d_0 ≤ 15 := by
    by_contra hc
    have hd_ge : d_0 ≥ 16 := by omega
    have h_Bd := choose_lower_bound d_0 hd_ge
    omega
  have hc_le : c_0 ≤ 15 := by omega
  interval_cases c_0 <;> interval_cases d_0
  · have h_c : (2 * 0 + 1).choose 0 = 1 := rfl
    have h_d : (2 * 0 + 1).choose 0 = 1 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800322178 := by omega
    have : Fact (Nat.Prime 647) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 647 (by norm_num) 800322178 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 0 + 1).choose 0 = 1 := rfl
    have h_d : (2 * 1 + 1).choose 1 = 3 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800322176 := by omega
    have : Fact (Nat.Prime 163) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 163 (by norm_num) 800322176 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 0 + 1).choose 0 = 1 := rfl
    have h_d : (2 * 2 + 1).choose 2 = 10 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800322169 := by omega
    have : Fact (Nat.Prime 67) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 67 (by norm_num) 800322169 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 0 + 1).choose 0 = 1 := rfl
    have h_d : (2 * 3 + 1).choose 3 = 35 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800322144 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 3 (by norm_num) 800322144 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 0 + 1).choose 0 = 1 := rfl
    have h_d : (2 * 4 + 1).choose 4 = 126 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800322053 := by omega
    have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 23 (by norm_num) 800322053 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 0 + 1).choose 0 = 1 := rfl
    have h_d : (2 * 5 + 1).choose 5 = 462 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800321717 := by omega
    have : Fact (Nat.Prime 467) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 467 (by norm_num) 800321717 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 0 + 1).choose 0 = 1 := rfl
    have h_d : (2 * 6 + 1).choose 6 = 1716 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800320463 := by omega
    have : Fact (Nat.Prime 223) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 223 (by norm_num) 800320463 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 0 + 1).choose 0 = 1 := rfl
    have h_d : (2 * 7 + 1).choose 7 = 6435 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800315744 := by omega
    have : Fact (Nat.Prime 991) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 991 (by norm_num) 800315744 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 0 + 1).choose 0 = 1 := rfl
    have h_d : (2 * 8 + 1).choose 8 = 24310 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800297869 := by omega
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 7 (by norm_num) 800297869 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 0 + 1).choose 0 = 1 := rfl
    have h_d : (2 * 9 + 1).choose 9 = 92378 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800229801 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 3 (by norm_num) 800229801 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 0 + 1).choose 0 = 1 := rfl
    have h_d : (2 * 10 + 1).choose 10 = 352716 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 799969463 := by omega
    have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 23 (by norm_num) 799969463 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 0 + 1).choose 0 = 1 := rfl
    have h_d : (2 * 11 + 1).choose 11 = 1352078 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 798970101 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 3 (by norm_num) 798970101 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 0 + 1).choose 0 = 1 := rfl
    have h_d : (2 * 12 + 1).choose 12 = 5200300 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 795121879 := by omega
    have : Fact (Nat.Prime 887) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 887 (by norm_num) 795121879 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 0 + 1).choose 0 = 1 := rfl
    have h_d : (2 * 13 + 1).choose 13 = 20058300 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 780263879 := by omega
    have : Fact (Nat.Prime 26905651) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 26905651 (by norm_num) 780263879 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 0 + 1).choose 0 = 1 := rfl
    have h_d : (2 * 14 + 1).choose 14 = 77558760 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 722763419 := by omega
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 7 (by norm_num) 722763419 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 0 + 1).choose 0 = 1 := rfl
    have h_d : (2 * 15 + 1).choose 15 = 300540195 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 499781984 := by omega
    have : Fact (Nat.Prime 1999) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 1999 (by norm_num) 499781984 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 1 + 1).choose 1 = 3 := rfl
    have h_d : (2 * 1 + 1).choose 1 = 3 := rfl
    have h_m1 : a_0 ^ 2 + b_0 ^ 2 = 3^2 * 88924686 := by omega
    have h_sum1 := step_reduction 3 (by norm_num) 88924686 a_0 b_0 h_m1
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 3 (by norm_num) 88924686 (by norm_num) (by norm_num) (a_0 / 3) (b_0 / 3) h_sum1
  · have h_c : (2 * 1 + 1).choose 1 = 3 := rfl
    have h_d : (2 * 2 + 1).choose 2 = 10 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800322167 := by omega
    have : Fact (Nat.Prime 643) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 643 (by norm_num) 800322167 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 1 + 1).choose 1 = 3 := rfl
    have h_d : (2 * 3 + 1).choose 3 = 35 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800322142 := by omega
    have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 19 (by norm_num) 800322142 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 1 + 1).choose 1 = 3 := rfl
    have h_d : (2 * 4 + 1).choose 4 = 126 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800322051 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 3 (by norm_num) 800322051 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 1 + 1).choose 1 = 3 := rfl
    have h_d : (2 * 5 + 1).choose 5 = 462 := rfl
    have h_m1 : a_0 ^ 2 + b_0 ^ 2 = 3^2 * 88924635 := by omega
    have h_sum1 := step_reduction 3 (by norm_num) 88924635 a_0 b_0 h_m1
    have h_m2 : (a_0 / 3) ^ 2 + (b_0 / 3) ^ 2 = 3^2 * 9880515 := by omega
    have h_sum2 := step_reduction 3 (by norm_num) 9880515 (a_0 / 3) (b_0 / 3) h_m2
    have h_m3 : ((a_0 / 3) / 3) ^ 2 + ((b_0 / 3) / 3) ^ 2 = 3^2 * 1097835 := by omega
    have h_sum3 := step_reduction 3 (by norm_num) 1097835 ((a_0 / 3) / 3) ((b_0 / 3) / 3) h_m3
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 3 (by norm_num) 1097835 (by norm_num) (by norm_num) (((a_0 / 3) / 3) / 3) (((b_0 / 3) / 3) / 3) h_sum3
  · have h_c : (2 * 1 + 1).choose 1 = 3 := rfl
    have h_d : (2 * 6 + 1).choose 6 = 1716 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800320461 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 3 (by norm_num) 800320461 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 1 + 1).choose 1 = 3 := rfl
    have h_d : (2 * 7 + 1).choose 7 = 6435 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800315742 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 3 (by norm_num) 800315742 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 1 + 1).choose 1 = 3 := rfl
    have h_d : (2 * 8 + 1).choose 8 = 24310 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800297867 := by omega
    have : Fact (Nat.Prime 78607) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 78607 (by norm_num) 800297867 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 1 + 1).choose 1 = 3 := rfl
    have h_d : (2 * 9 + 1).choose 9 = 92378 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800229799 := by omega
    have : Fact (Nat.Prime 27594131) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 27594131 (by norm_num) 800229799 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 1 + 1).choose 1 = 3 := rfl
    have h_d : (2 * 10 + 1).choose 10 = 352716 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 799969461 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 3 (by norm_num) 799969461 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 1 + 1).choose 1 = 3 := rfl
    have h_d : (2 * 11 + 1).choose 11 = 1352078 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 798970099 := by omega
    have : Fact (Nat.Prime 31) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 31 (by norm_num) 798970099 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 1 + 1).choose 1 = 3 := rfl
    have h_d : (2 * 12 + 1).choose 12 = 5200300 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 795121877 := by omega
    have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 11 (by norm_num) 795121877 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 1 + 1).choose 1 = 3 := rfl
    have h_d : (2 * 13 + 1).choose 13 = 20058300 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 780263877 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 3 (by norm_num) 780263877 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 1 + 1).choose 1 = 3 := rfl
    have h_d : (2 * 14 + 1).choose 14 = 77558760 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 722763417 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 3 (by norm_num) 722763417 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 1 + 1).choose 1 = 3 := rfl
    have h_d : (2 * 15 + 1).choose 15 = 300540195 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 499781982 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 3 (by norm_num) 499781982 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 2 + 1).choose 2 = 10 := rfl
    have h_d : (2 * 2 + 1).choose 2 = 10 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800322160 := by omega
    have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 11 (by norm_num) 800322160 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 2 + 1).choose 2 = 10 := rfl
    have h_d : (2 * 3 + 1).choose 3 = 35 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800322135 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 3 (by norm_num) 800322135 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 2 + 1).choose 2 = 10 := rfl
    have h_d : (2 * 4 + 1).choose 4 = 126 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800322044 := by omega
    have : Fact (Nat.Prime 200080511) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 200080511 (by norm_num) 800322044 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 2 + 1).choose 2 = 10 := rfl
    have h_d : (2 * 5 + 1).choose 5 = 462 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800321708 := by omega
    have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 23 (by norm_num) 800321708 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 2 + 1).choose 2 = 10 := rfl
    have h_d : (2 * 6 + 1).choose 6 = 1716 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800320454 := by omega
    have : Fact (Nat.Prime 284003) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 284003 (by norm_num) 800320454 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 2 + 1).choose 2 = 10 := rfl
    have h_d : (2 * 7 + 1).choose 7 = 6435 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800315735 := by omega
    have : Fact (Nat.Prime 4326031) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 4326031 (by norm_num) 800315735 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 2 + 1).choose 2 = 10 := rfl
    have h_d : (2 * 8 + 1).choose 8 = 24310 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800297860 := by omega
    have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 19 (by norm_num) 800297860 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 2 + 1).choose 2 = 10 := rfl
    have h_d : (2 * 9 + 1).choose 9 = 92378 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800229792 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 3 (by norm_num) 800229792 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 2 + 1).choose 2 = 10 := rfl
    have h_d : (2 * 10 + 1).choose 10 = 352716 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 799969454 := by omega
    have : Fact (Nat.Prime 399984727) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 399984727 (by norm_num) 799969454 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 2 + 1).choose 2 = 10 := rfl
    have h_d : (2 * 11 + 1).choose 11 = 1352078 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 798970092 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 3 (by norm_num) 798970092 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 2 + 1).choose 2 = 10 := rfl
    have h_d : (2 * 12 + 1).choose 12 = 5200300 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 795121870 := by omega
    have : Fact (Nat.Prime 79512187) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 79512187 (by norm_num) 795121870 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 2 + 1).choose 2 = 10 := rfl
    have h_d : (2 * 13 + 1).choose 13 = 20058300 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 780263870 := by omega
    have : Fact (Nat.Prime 127) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 127 (by norm_num) 780263870 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 2 + 1).choose 2 = 10 := rfl
    have h_d : (2 * 14 + 1).choose 14 = 77558760 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 722763410 := by omega
    have : Fact (Nat.Prime 2819) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 2819 (by norm_num) 722763410 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 2 + 1).choose 2 = 10 := rfl
    have h_d : (2 * 15 + 1).choose 15 = 300540195 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 499781975 := by omega
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 7 (by norm_num) 499781975 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 3 + 1).choose 3 = 35 := rfl
    have h_d : (2 * 3 + 1).choose 3 = 35 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800322110 := by omega
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 7 (by norm_num) 800322110 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 3 + 1).choose 3 = 35 := rfl
    have h_d : (2 * 4 + 1).choose 4 = 126 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800322019 := by omega
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 7 (by norm_num) 800322019 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 3 + 1).choose 3 = 35 := rfl
    have h_d : (2 * 5 + 1).choose 5 = 462 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800321683 := by omega
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 7 (by norm_num) 800321683 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 3 + 1).choose 3 = 35 := rfl
    have h_d : (2 * 6 + 1).choose 6 = 1716 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800320429 := by omega
    have : Fact (Nat.Prime 43) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 43 (by norm_num) 800320429 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 3 + 1).choose 3 = 35 := rfl
    have h_d : (2 * 7 + 1).choose 7 = 6435 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800315710 := by omega
    have : Fact (Nat.Prime 5843) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 5843 (by norm_num) 800315710 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 3 + 1).choose 3 = 35 := rfl
    have h_d : (2 * 8 + 1).choose 8 = 24310 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800297835 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 3 (by norm_num) 800297835 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 3 + 1).choose 3 = 35 := rfl
    have h_d : (2 * 9 + 1).choose 9 = 92378 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800229767 := by omega
    have : Fact (Nat.Prime 7923067) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 7923067 (by norm_num) 800229767 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 3 + 1).choose 3 = 35 := rfl
    have h_d : (2 * 10 + 1).choose 10 = 352716 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 799969429 := by omega
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 7 (by norm_num) 799969429 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 3 + 1).choose 3 = 35 := rfl
    have h_d : (2 * 11 + 1).choose 11 = 1352078 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 798970067 := by omega
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 7 (by norm_num) 798970067 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 3 + 1).choose 3 = 35 := rfl
    have h_d : (2 * 12 + 1).choose 12 = 5200300 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 795121845 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 3 (by norm_num) 795121845 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 3 + 1).choose 3 = 35 := rfl
    have h_d : (2 * 13 + 1).choose 13 = 20058300 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 780263845 := by omega
    have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 23 (by norm_num) 780263845 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 3 + 1).choose 3 = 35 := rfl
    have h_d : (2 * 14 + 1).choose 14 = 77558760 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 722763385 := by omega
    have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 23 (by norm_num) 722763385 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 3 + 1).choose 3 = 35 := rfl
    have h_d : (2 * 15 + 1).choose 15 = 300540195 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 499781950 := by omega
    have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 23 (by norm_num) 499781950 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 4 + 1).choose 4 = 126 := rfl
    have h_d : (2 * 4 + 1).choose 4 = 126 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800321928 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 3 (by norm_num) 800321928 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 4 + 1).choose 4 = 126 := rfl
    have h_d : (2 * 5 + 1).choose 5 = 462 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800321592 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 3 (by norm_num) 800321592 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 4 + 1).choose 4 = 126 := rfl
    have h_d : (2 * 6 + 1).choose 6 = 1716 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800320338 := by omega
    have : Fact (Nat.Prime 719) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 719 (by norm_num) 800320338 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 4 + 1).choose 4 = 126 := rfl
    have h_d : (2 * 7 + 1).choose 7 = 6435 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800315619 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 3 (by norm_num) 800315619 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 4 + 1).choose 4 = 126 := rfl
    have h_d : (2 * 8 + 1).choose 8 = 24310 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800297744 := by omega
    have : Fact (Nat.Prime 563) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 563 (by norm_num) 800297744 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 4 + 1).choose 4 = 126 := rfl
    have h_d : (2 * 9 + 1).choose 9 = 92378 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800229676 := by omega
    have : Fact (Nat.Prime 200057419) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 200057419 (by norm_num) 800229676 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 4 + 1).choose 4 = 126 := rfl
    have h_d : (2 * 10 + 1).choose 10 = 352716 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 799969338 := by omega
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 7 (by norm_num) 799969338 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 4 + 1).choose 4 = 126 := rfl
    have h_d : (2 * 11 + 1).choose 11 = 1352078 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 798969976 := by omega
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 7 (by norm_num) 798969976 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 4 + 1).choose 4 = 126 := rfl
    have h_d : (2 * 12 + 1).choose 12 = 5200300 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 795121754 := by omega
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 7 (by norm_num) 795121754 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 4 + 1).choose 4 = 126 := rfl
    have h_d : (2 * 13 + 1).choose 13 = 20058300 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 780263754 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 3 (by norm_num) 780263754 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 4 + 1).choose 4 = 126 := rfl
    have h_d : (2 * 14 + 1).choose 14 = 77558760 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 722763294 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 3 (by norm_num) 722763294 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 4 + 1).choose 4 = 126 := rfl
    have h_d : (2 * 15 + 1).choose 15 = 300540195 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 499781859 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 3 (by norm_num) 499781859 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 5 + 1).choose 5 = 462 := rfl
    have h_d : (2 * 5 + 1).choose 5 = 462 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800321256 := by omega
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 7 (by norm_num) 800321256 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 5 + 1).choose 5 = 462 := rfl
    have h_d : (2 * 6 + 1).choose 6 = 1716 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800320002 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 3 (by norm_num) 800320002 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 5 + 1).choose 5 = 462 := rfl
    have h_d : (2 * 7 + 1).choose 7 = 6435 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800315283 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 3 (by norm_num) 800315283 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 5 + 1).choose 5 = 462 := rfl
    have h_d : (2 * 8 + 1).choose 8 = 24310 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800297408 := by omega
    have : Fact (Nat.Prime 12504647) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 12504647 (by norm_num) 800297408 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 5 + 1).choose 5 = 462 := rfl
    have h_d : (2 * 9 + 1).choose 9 = 92378 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800229340 := by omega
    have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 23 (by norm_num) 800229340 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 5 + 1).choose 5 = 462 := rfl
    have h_d : (2 * 10 + 1).choose 10 = 352716 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 799969002 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 3 (by norm_num) 799969002 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 5 + 1).choose 5 = 462 := rfl
    have h_d : (2 * 11 + 1).choose 11 = 1352078 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 798969640 := by omega
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 7 (by norm_num) 798969640 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 5 + 1).choose 5 = 462 := rfl
    have h_d : (2 * 12 + 1).choose 12 = 5200300 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 795121418 := by omega
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 7 (by norm_num) 795121418 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 5 + 1).choose 5 = 462 := rfl
    have h_d : (2 * 13 + 1).choose 13 = 20058300 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 780263418 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 3 (by norm_num) 780263418 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 5 + 1).choose 5 = 462 := rfl
    have h_d : (2 * 14 + 1).choose 14 = 77558760 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 722762958 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 3 (by norm_num) 722762958 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 5 + 1).choose 5 = 462 := rfl
    have h_d : (2 * 15 + 1).choose 15 = 300540195 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 499781523 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 3 (by norm_num) 499781523 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 6 + 1).choose 6 = 1716 := rfl
    have h_d : (2 * 6 + 1).choose 6 = 1716 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800318748 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 3 (by norm_num) 800318748 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 6 + 1).choose 6 = 1716 := rfl
    have h_d : (2 * 7 + 1).choose 7 = 6435 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800314029 := by omega
    have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 19 (by norm_num) 800314029 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 6 + 1).choose 6 = 1716 := rfl
    have h_d : (2 * 8 + 1).choose 8 = 24310 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800296154 := by omega
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 7 (by norm_num) 800296154 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 6 + 1).choose 6 = 1716 := rfl
    have h_d : (2 * 9 + 1).choose 9 = 92378 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800228086 := by omega
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 7 (by norm_num) 800228086 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 6 + 1).choose 6 = 1716 := rfl
    have h_d : (2 * 10 + 1).choose 10 = 352716 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 799967748 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 3 (by norm_num) 799967748 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 6 + 1).choose 6 = 1716 := rfl
    have h_d : (2 * 11 + 1).choose 11 = 1352078 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 798968386 := by omega
    have : Fact (Nat.Prime 139) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 139 (by norm_num) 798968386 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 6 + 1).choose 6 = 1716 := rfl
    have h_d : (2 * 12 + 1).choose 12 = 5200300 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 795120164 := by omega
    have : Fact (Nat.Prime 227) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 227 (by norm_num) 795120164 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 6 + 1).choose 6 = 1716 := rfl
    have h_d : (2 * 13 + 1).choose 13 = 20058300 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 780262164 := by omega
    have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 11 (by norm_num) 780262164 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 6 + 1).choose 6 = 1716 := rfl
    have h_d : (2 * 14 + 1).choose 14 = 77558760 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 722761704 := by omega
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 7 (by norm_num) 722761704 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 6 + 1).choose 6 = 1716 := rfl
    have h_d : (2 * 15 + 1).choose 15 = 300540195 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 499780269 := by omega
    have : Fact (Nat.Prime 67) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 67 (by norm_num) 499780269 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 7 + 1).choose 7 = 6435 := rfl
    have h_d : (2 * 7 + 1).choose 7 = 6435 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800309310 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 3 (by norm_num) 800309310 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 7 + 1).choose 7 = 6435 := rfl
    have h_d : (2 * 8 + 1).choose 8 = 24310 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800291435 := by omega
    have : Fact (Nat.Prime 199) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 199 (by norm_num) 800291435 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 7 + 1).choose 7 = 6435 := rfl
    have h_d : (2 * 9 + 1).choose 9 = 92378 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800223367 := by omega
    have : Fact (Nat.Prime 31) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 31 (by norm_num) 800223367 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 7 + 1).choose 7 = 6435 := rfl
    have h_d : (2 * 10 + 1).choose 10 = 352716 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 799963029 := by omega
    have : Fact (Nat.Prime 31) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 31 (by norm_num) 799963029 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 7 + 1).choose 7 = 6435 := rfl
    have h_d : (2 * 11 + 1).choose 11 = 1352078 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 798963667 := by omega
    have : Fact (Nat.Prime 3331) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 3331 (by norm_num) 798963667 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 7 + 1).choose 7 = 6435 := rfl
    have h_d : (2 * 12 + 1).choose 12 = 5200300 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 795115445 := by omega
    have : Fact (Nat.Prime 139) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 139 (by norm_num) 795115445 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 7 + 1).choose 7 = 6435 := rfl
    have h_d : (2 * 13 + 1).choose 13 = 20058300 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 780257445 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 3 (by norm_num) 780257445 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 7 + 1).choose 7 = 6435 := rfl
    have h_d : (2 * 14 + 1).choose 14 = 77558760 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 722756985 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 3 (by norm_num) 722756985 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 7 + 1).choose 7 = 6435 := rfl
    have h_d : (2 * 15 + 1).choose 15 = 300540195 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 499775550 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 3 (by norm_num) 499775550 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 8 + 1).choose 8 = 24310 := rfl
    have h_d : (2 * 8 + 1).choose 8 = 24310 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800273560 := by omega
    have : Fact (Nat.Prime 689891) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 689891 (by norm_num) 800273560 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 8 + 1).choose 8 = 24310 := rfl
    have h_d : (2 * 9 + 1).choose 9 = 92378 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800205492 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 3 (by norm_num) 800205492 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 8 + 1).choose 8 = 24310 := rfl
    have h_d : (2 * 10 + 1).choose 10 = 352716 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 799945154 := by omega
    have : Fact (Nat.Prime 223) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 223 (by norm_num) 799945154 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 8 + 1).choose 8 = 24310 := rfl
    have h_d : (2 * 11 + 1).choose 11 = 1352078 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 798945792 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 3 (by norm_num) 798945792 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 8 + 1).choose 8 = 24310 := rfl
    have h_d : (2 * 12 + 1).choose 12 = 5200300 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 795097570 := by omega
    have : Fact (Nat.Prime 59) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 59 (by norm_num) 795097570 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 8 + 1).choose 8 = 24310 := rfl
    have h_d : (2 * 13 + 1).choose 13 = 20058300 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 780239570 := by omega
    have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 11 (by norm_num) 780239570 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 8 + 1).choose 8 = 24310 := rfl
    have h_d : (2 * 14 + 1).choose 14 = 77558760 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 722739110 := by omega
    have : Fact (Nat.Prime 7591) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 7591 (by norm_num) 722739110 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 8 + 1).choose 8 = 24310 := rfl
    have h_d : (2 * 15 + 1).choose 15 = 300540195 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 499757675 := by omega
    have : Fact (Nat.Prime 19990307) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 19990307 (by norm_num) 499757675 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 9 + 1).choose 9 = 92378 := rfl
    have h_d : (2 * 9 + 1).choose 9 = 92378 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 800137424 := by omega
    have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 19 (by norm_num) 800137424 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 9 + 1).choose 9 = 92378 := rfl
    have h_d : (2 * 10 + 1).choose 10 = 352716 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 799877086 := by omega
    have : Fact (Nat.Prime 887) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 887 (by norm_num) 799877086 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 9 + 1).choose 9 = 92378 := rfl
    have h_d : (2 * 11 + 1).choose 11 = 1352078 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 798877724 := by omega
    have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 19 (by norm_num) 798877724 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 9 + 1).choose 9 = 92378 := rfl
    have h_d : (2 * 12 + 1).choose 12 = 5200300 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 795029502 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 3 (by norm_num) 795029502 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 9 + 1).choose 9 = 92378 := rfl
    have h_d : (2 * 13 + 1).choose 13 = 20058300 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 780171502 := by omega
    have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 11 (by norm_num) 780171502 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 9 + 1).choose 9 = 92378 := rfl
    have h_d : (2 * 14 + 1).choose 14 = 77558760 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 722671042 := by omega
    have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 19 (by norm_num) 722671042 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 9 + 1).choose 9 = 92378 := rfl
    have h_d : (2 * 15 + 1).choose 15 = 300540195 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 499689607 := by omega
    have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 19 (by norm_num) 499689607 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 10 + 1).choose 10 = 352716 := rfl
    have h_d : (2 * 10 + 1).choose 10 = 352716 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 799616748 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 3 (by norm_num) 799616748 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 10 + 1).choose 10 = 352716 := rfl
    have h_d : (2 * 11 + 1).choose 11 = 1352078 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 798617386 := by omega
    have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 19 (by norm_num) 798617386 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 10 + 1).choose 10 = 352716 := rfl
    have h_d : (2 * 12 + 1).choose 12 = 5200300 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 794769164 := by omega
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 7 (by norm_num) 794769164 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 10 + 1).choose 10 = 352716 := rfl
    have h_d : (2 * 13 + 1).choose 13 = 20058300 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 779911164 := by omega
    have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 19 (by norm_num) 779911164 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 10 + 1).choose 10 = 352716 := rfl
    have h_d : (2 * 14 + 1).choose 14 = 77558760 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 722410704 := by omega
    have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 19 (by norm_num) 722410704 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 10 + 1).choose 10 = 352716 := rfl
    have h_d : (2 * 15 + 1).choose 15 = 300540195 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 499429269 := by omega
    have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 19 (by norm_num) 499429269 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 11 + 1).choose 11 = 1352078 := rfl
    have h_d : (2 * 11 + 1).choose 11 = 1352078 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 797618024 := by omega
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 7 (by norm_num) 797618024 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 11 + 1).choose 11 = 1352078 := rfl
    have h_d : (2 * 12 + 1).choose 12 = 5200300 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 793769802 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 3 (by norm_num) 793769802 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 11 + 1).choose 11 = 1352078 := rfl
    have h_d : (2 * 13 + 1).choose 13 = 20058300 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 778911802 := by omega
    have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 19 (by norm_num) 778911802 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 11 + 1).choose 11 = 1352078 := rfl
    have h_d : (2 * 14 + 1).choose 14 = 77558760 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 721411342 := by omega
    have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 19 (by norm_num) 721411342 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 11 + 1).choose 11 = 1352078 := rfl
    have h_d : (2 * 15 + 1).choose 15 = 300540195 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 498429907 := by omega
    have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 19 (by norm_num) 498429907 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 12 + 1).choose 12 = 5200300 := rfl
    have h_d : (2 * 12 + 1).choose 12 = 5200300 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 789921580 := by omega
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 7 (by norm_num) 789921580 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 12 + 1).choose 12 = 5200300 := rfl
    have h_d : (2 * 13 + 1).choose 13 = 20058300 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 775063580 := by omega
    have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 19 (by norm_num) 775063580 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 12 + 1).choose 12 = 5200300 := rfl
    have h_d : (2 * 14 + 1).choose 14 = 77558760 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 717563120 := by omega
    have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 19 (by norm_num) 717563120 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 12 + 1).choose 12 = 5200300 := rfl
    have h_d : (2 * 15 + 1).choose 15 = 300540195 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 494581685 := by omega
    have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 19 (by norm_num) 494581685 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 13 + 1).choose 13 = 20058300 := rfl
    have h_d : (2 * 13 + 1).choose 13 = 20058300 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 760205580 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 3 (by norm_num) 760205580 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 13 + 1).choose 13 = 20058300 := rfl
    have h_d : (2 * 14 + 1).choose 14 = 77558760 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 702705120 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 3 (by norm_num) 702705120 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 13 + 1).choose 13 = 20058300 := rfl
    have h_d : (2 * 15 + 1).choose 15 = 300540195 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 479723685 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 3 (by norm_num) 479723685 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 14 + 1).choose 14 = 77558760 := rfl
    have h_d : (2 * 14 + 1).choose 14 = 77558760 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 645204660 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 3 (by norm_num) 645204660 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 14 + 1).choose 14 = 77558760 := rfl
    have h_d : (2 * 15 + 1).choose 15 = 300540195 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 422223225 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 3 (by norm_num) 422223225 (by norm_num) (by norm_num) a_0 b_0 h_sum
  · have h_c : (2 * 15 + 1).choose 15 = 300540195 := rfl
    have h_d : (2 * 15 + 1).choose 15 = 300540195 := rfl
    have h_sum : a_0 ^ 2 + b_0 ^ 2 = 199241790 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact no_sol_of_prime_div_sq 3 (by norm_num) 199241790 (by norm_num) (by norm_num) a_0 b_0 h_sum
