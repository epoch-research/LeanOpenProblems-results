import FormalConjectures.Util.ProblemImports

open Nat

-- Let's put the definitions we need
def a (n : ℕ) : ℕ :=
  (8 * n).factorial * n.factorial / ((4 * n).factorial * (3 * n).factorial * (2 * n).factorial)

theorem ratio_inequality (r P : ℕ) (hP : 0 < P) (hr : r < P) :
    4 * r / P + 3 * r / P + 2 * r / P ≤ 8 * r / P := sorry

theorem n_div_P_relation (n P : ℕ) (hP : 0 < P) :
    4 * n / P = 4 * (n / P) + (4 * (n % P)) / P := sorry

theorem div_add_div_eq (n P : ℕ) (hP : 0 < P) :
    4 * n / P + 3 * n / P + 2 * n / P ≤ 8 * n / P + n / P := sorry

theorem a_mul_Y_eq_X (n : ℕ) :
    (a n : ℤ) * ((4 * n).factorial * (3 * n).factorial * (2 * n).factorial : ℕ) =
    ((8 * n).factorial * n.factorial : ℕ) := sorry

theorem div_eq_of_lt_of_le {a b c : ℕ} (hb : 0 < b) (h1 : b * c ≤ a) (h2 : a < b * (c + 1)) : a / b = c := by
  have h1' : c * b ≤ a := by rwa [mul_comm] at h1
  have h2' : a < (c + 1) * b := by rwa [mul_comm] at h2
  have h3 : c ≤ a / b := (Nat.le_div_iff_mul_le hb).mpr h1'
  have h4 : a / b < c + 1 := (Nat.div_lt_iff_lt_mul hb).mpr h2'
  omega

theorem rem_div_sum_le (rem r P k : ℕ) (hP : 0 < P) (h_gt : 8 * r + 3 < P)
    (h_rem : 8 * rem = k * P + 2 * r + 1) (hk_cases : k = 1 ∨ k = 3 ∨ k = 5 ∨ k = 7) :
    4 * rem / P + 3 * rem / P + 2 * rem / P + 1 ≤ k := by
  rcases hk_cases with rfl | rfl | rfl | rfl
  · -- Case k = 1
    have hd4 : 4 * rem / P = 0 := by
      apply div_eq_of_lt_of_le hP
      · omega
      · have h : 8 * (4 * rem) < 8 * (P * 1) := by
          calc 8 * (4 * rem) = 4 * (8 * rem) := by ring
          _ = 4 * (1 * P + 2 * r + 1) := by rw [h_rem]
          _ = 4 * P + 8 * r + 4 := by ring
          _ < 8 * P := by omega
          _ = 8 * (P * 1) := by ring
        omega
    have hd3 : 3 * rem / P = 0 := by
      apply div_eq_of_lt_of_le hP
      · omega
      · have h : 8 * (3 * rem) < 8 * (P * 1) := by
          calc 8 * (3 * rem) = 3 * (8 * rem) := by ring
          _ = 3 * (1 * P + 2 * r + 1) := by rw [h_rem]
          _ = 3 * P + 6 * r + 3 := by ring
          _ < 8 * P := by omega
          _ = 8 * (P * 1) := by ring
        omega
    have hd2 : 2 * rem / P = 0 := by
      apply div_eq_of_lt_of_le hP
      · omega
      · have h : 8 * (2 * rem) < 8 * (P * 1) := by
          calc 8 * (2 * rem) = 2 * (8 * rem) := by ring
          _ = 2 * (1 * P + 2 * r + 1) := by rw [h_rem]
          _ = 2 * P + 4 * r + 2 := by ring
          _ < 8 * P := by omega
          _ = 8 * (P * 1) := by ring
        omega
    rw [hd4, hd3, hd2]
  · -- Case k = 3
    have hd4 : 4 * rem / P = 1 := by
      apply div_eq_of_lt_of_le hP
      · have h : 8 * (P * 1) ≤ 8 * (4 * rem) := by
          calc 8 * (P * 1) = 8 * P := by ring
          _ ≤ 12 * P + 8 * r + 4 := by omega
          _ = 4 * (3 * P + 2 * r + 1) := by ring
          _ = 4 * (8 * rem) := by rw [← h_rem]
          _ = 8 * (4 * rem) := by ring
        omega
      · have h : 8 * (4 * rem) < 8 * (P * 2) := by
          calc 8 * (4 * rem) = 4 * (8 * rem) := by ring
          _ = 4 * (3 * P + 2 * r + 1) := by rw [h_rem]
          _ = 12 * P + 8 * r + 4 := by ring
          _ < 16 * P := by omega
          _ = 8 * (P * 2) := by ring
        omega
    have hd3 : 3 * rem / P = 1 := by
      apply div_eq_of_lt_of_le hP
      · have h : 8 * (P * 1) ≤ 8 * (3 * rem) := by
          calc 8 * (P * 1) = 8 * P := by ring
          _ ≤ 9 * P + 6 * r + 3 := by omega
          _ = 3 * (3 * P + 2 * r + 1) := by ring
          _ = 3 * (8 * rem) := by rw [← h_rem]
          _ = 8 * (3 * rem) := by ring
        omega
      · have h : 8 * (3 * rem) < 8 * (P * 2) := by
          calc 8 * (3 * rem) = 3 * (8 * rem) := by ring
          _ = 3 * (3 * P + 2 * r + 1) := by rw [h_rem]
          _ = 9 * P + 6 * r + 3 := by ring
          _ < 16 * P := by omega
          _ = 8 * (P * 2) := by ring
        omega
    have hd2 : 2 * rem / P = 0 := by
      apply div_eq_of_lt_of_le hP
      · omega
      · have h : 8 * (2 * rem) < 8 * (P * 1) := by
          calc 8 * (2 * rem) = 2 * (8 * rem) := by ring
          _ = 2 * (3 * P + 2 * r + 1) := by rw [h_rem]
          _ = 6 * P + 4 * r + 2 := by ring
          _ < 8 * P := by omega
          _ = 8 * (P * 1) := by ring
        omega
    rw [hd4, hd3, hd2]
  · -- Case k = 5
    have hd4 : 4 * rem / P = 2 := by
      apply div_eq_of_lt_of_le hP
      · have h : 8 * (P * 2) ≤ 8 * (4 * rem) := by
          calc 8 * (P * 2) = 16 * P := by ring
          _ ≤ 20 * P + 8 * r + 4 := by omega
          _ = 4 * (5 * P + 2 * r + 1) := by ring
          _ = 4 * (8 * rem) := by rw [← h_rem]
          _ = 8 * (4 * rem) := by ring
        omega
      · have h : 8 * (4 * rem) < 8 * (P * 3) := by
          calc 8 * (4 * rem) = 4 * (8 * rem) := by ring
          _ = 4 * (5 * P + 2 * r + 1) := by rw [h_rem]
          _ = 20 * P + 8 * r + 4 := by ring
          _ < 24 * P := by omega
          _ = 8 * (P * 3) := by ring
        omega
    have hd3 : 3 * rem / P = 1 := by
      apply div_eq_of_lt_of_le hP
      · have h : 8 * (P * 1) ≤ 8 * (3 * rem) := by
          calc 8 * (P * 1) = 8 * P := by ring
          _ ≤ 15 * P + 6 * r + 3 := by omega
          _ = 3 * (5 * P + 2 * r + 1) := by ring
          _ = 3 * (8 * rem) := by rw [← h_rem]
          _ = 8 * (3 * rem) := by ring
        omega
      · have h : 8 * (3 * rem) < 8 * (P * 2) := by
          calc 8 * (3 * rem) = 3 * (8 * rem) := by ring
          _ = 3 * (5 * P + 2 * r + 1) := by rw [h_rem]
          _ = 15 * P + 6 * r + 3 := by ring
          _ < 16 * P := by omega
          _ = 8 * (P * 2) := by ring
        omega
    have hd2 : 2 * rem / P = 1 := by
      apply div_eq_of_lt_of_le hP
      · have h : 8 * (P * 1) ≤ 8 * (2 * rem) := by
          calc 8 * (P * 1) = 8 * P := by ring
          _ ≤ 10 * P + 4 * r + 2 := by omega
          _ = 2 * (5 * P + 2 * r + 1) := by ring
          _ = 2 * (8 * rem) := by rw [← h_rem]
          _ = 8 * (2 * rem) := by ring
        omega
      · have h : 8 * (2 * rem) < 8 * (P * 2) := by
          calc 8 * (2 * rem) = 2 * (8 * rem) := by ring
          _ = 2 * (5 * P + 2 * r + 1) := by rw [h_rem]
          _ = 10 * P + 4 * r + 2 := by ring
          _ < 16 * P := by omega
          _ = 8 * (P * 2) := by ring
        omega
    rw [hd4, hd3, hd2]
  · -- Case k = 7
    have hd4 : 4 * rem / P = 3 := by
      apply div_eq_of_lt_of_le hP
      · have h : 8 * (P * 3) ≤ 8 * (4 * rem) := by
          calc 8 * (P * 3) = 24 * P := by ring
          _ ≤ 28 * P + 8 * r + 4 := by omega
          _ = 4 * (7 * P + 2 * r + 1) := by ring
          _ = 4 * (8 * rem) := by rw [← h_rem]
          _ = 8 * (4 * rem) := by ring
        omega
      · have h : 8 * (4 * rem) < 8 * (P * 4) := by
          calc 8 * (4 * rem) = 4 * (8 * rem) := by ring
          _ = 4 * (7 * P + 2 * r + 1) := by rw [h_rem]
          _ = 28 * P + 8 * r + 4 := by ring
          _ < 32 * P := by omega
          _ = 8 * (P * 4) := by ring
        omega
    have hd3 : 3 * rem / P = 2 := by
      apply div_eq_of_lt_of_le hP
      · have h : 8 * (P * 2) ≤ 8 * (3 * rem) := by
          calc 8 * (P * 2) = 16 * P := by ring
          _ ≤ 21 * P + 6 * r + 3 := by omega
          _ = 3 * (7 * P + 2 * r + 1) := by ring
          _ = 3 * (8 * rem) := by rw [← h_rem]
          _ = 8 * (3 * rem) := by ring
        omega
      · have h : 8 * (3 * rem) < 8 * (P * 3) := by
          calc 8 * (3 * rem) = 3 * (8 * rem) := by ring
          _ = 3 * (7 * P + 2 * r + 1) := by rw [h_rem]
          _ = 21 * P + 6 * r + 3 := by ring
          _ < 24 * P := by omega
          _ = 8 * (P * 3) := by ring
        omega
    have hd2 : 2 * rem / P = 1 := by
      apply div_eq_of_lt_of_le hP
      · have h : 8 * (P * 1) ≤ 8 * (2 * rem) := by
          calc 8 * (P * 1) = 8 * P := by ring
          _ ≤ 14 * P + 4 * r + 2 := by omega
          _ = 2 * (7 * P + 2 * r + 1) := by ring
          _ = 2 * (8 * rem) := by rw [← h_rem]
          _ = 8 * (2 * rem) := by ring
        omega
      · have h : 8 * (2 * rem) < 8 * (P * 2) := by
          calc 8 * (2 * rem) = 2 * (8 * rem) := by ring
          _ = 2 * (7 * P + 2 * r + 1) := by rw [h_rem]
          _ = 14 * P + 4 * r + 2 := by ring
          _ < 16 * P := by omega
          _ = 8 * (P * 2) := by ring
        omega
    rw [hd4, hd3, hd2]

theorem omega_test (n r m P q rem : ℕ) (hP : 0 < P) (h_rem : rem < P)
    (h_eq1 : n = q * P + rem) (h_eq2 : 8 * n = (2 * m + 1) * P + 2 * r + 1) (h_gt : 8 * r + 3 < P) :
    4 * n / P + 3 * n / P + 2 * n / P + 1 ≤ 8 * n / P + n / P := by
  have hd8 : 8 * n / P = 2 * m + 1 := by
    rw [h_eq2]
    have : (2 * m + 1) * P + 2 * r + 1 = (2 * r + 1) + P * (2 * m + 1) := by ring
    rw [this]
    rw [Nat.add_mul_div_left (2 * r + 1) (2 * m + 1) hP]
    have : (2 * r + 1) / P = 0 := Nat.div_eq_of_lt (by omega)
    omega
  have hdn : n / P = q := by
    rw [h_eq1]
    have : q * P + rem = rem + P * q := by ring
    rw [this]
    rw [Nat.add_mul_div_left rem q hP]
    have : rem / P = 0 := Nat.div_eq_of_lt h_rem
    omega
  have h_le_q : 8 * q ≤ 2 * m + 1 := by
    have h_div_le : 8 * (n / P) ≤ (8 * n) / P := by
      rw [Nat.le_div_iff_mul_le hP]
      calc 8 * (n / P) * P = 8 * (n / P * P) := by ring
      _ ≤ 8 * n := Nat.mul_le_mul_left 8 (Nat.div_mul_le_self n P)
    rw [hd8] at h_div_le
    rw [hdn] at h_div_le
    exact h_div_le
  have h_rem_eq : 8 * rem = (2 * m + 1 - 8 * q) * P + 2 * r + 1 := by
    have h1 : 8 * n = 8 * q * P + 8 * rem := by
      rw [h_eq1]
      ring
    rw [h1] at h_eq2
    have h2 : (2 * m + 1) * P = (8 * q + (2 * m + 1 - 8 * q)) * P := by
      congr 1
      omega
    rw [h2] at h_eq2
    have h3 : (8 * q + (2 * m + 1 - 8 * q)) * P + 2 * r + 1 = 8 * q * P + (2 * m + 1 - 8 * q) * P + 2 * r + 1 := by ring
    rw [h3] at h_eq2
    omega
  have hd4 : 4 * n / P = 4 * q + 4 * rem / P := by
    rw [h_eq1]
    have : 4 * (q * P + rem) = 4 * rem + P * (4 * q) := by ring
    rw [this]
    rw [Nat.add_mul_div_left (4 * rem) (4 * q) hP]
    omega
  have hd3 : 3 * n / P = 3 * q + 3 * rem / P := by
    rw [h_eq1]
    have : 3 * (q * P + rem) = 3 * rem + P * (3 * q) := by ring
    rw [this]
    rw [Nat.add_mul_div_left (3 * rem) (3 * q) hP]
    omega
  have hd2 : 2 * n / P = 2 * q + 2 * rem / P := by
    rw [h_eq1]
    have : 2 * (q * P + rem) = 2 * rem + P * (2 * q) := by ring
    rw [this]
    rw [Nat.add_mul_div_left (2 * rem) (2 * q) hP]
    omega
  rw [hd8, hdn, hd4, hd3, hd2]
  let k := 2 * m + 1 - 8 * q
  have hk_cases : k = 1 ∨ k = 3 ∨ k = 5 ∨ k = 7 := by
    have h_lt : k * P < 8 * P := by
      calc k * P ≤ k * P + 2 * r + 1 := by omega
      _ = 8 * rem := by rw [h_rem_eq]
      _ < 8 * P := by omega
    have hk_lt : k < 8 := by
      by_contra h_ge
      push_neg at h_ge
      have : 8 * P ≤ k * P := Nat.mul_le_mul_right P h_ge
      omega
    have : k % 2 = 1 := by omega
    omega
  have h_rem_le := rem_div_sum_le rem r P k hP h_gt h_rem_eq hk_cases
  omega

lemma p_pow_gt_of_gt_padicValNat_factorial {p X : ℕ} [hp : Fact p.Prime] {k : ℕ} (hk : k = padicValNat p X.factorial) {i : ℕ} (hi : i > k) : p ^ i > X := by
  by_contra h_le
  push_neg at h_le
  have h_pos : p ^ i > 0 := Nat.pos_of_ne_zero (pow_ne_zero i hp.out.ne_zero)
  have h_dvd := Nat.dvd_factorial h_pos h_le
  have h_ne : X.factorial ≠ 0 := Nat.factorial_ne_zero X
  rw [padicValNat_dvd_iff_le h_ne] at h_dvd
  rw [← hk] at h_dvd
  omega

theorem term_by_term (n r p i v k : ℕ) [hp : Fact p.Prime] (hv : v = padicValNat p (8 * n - (2 * r + 1)))
    (hk : k = padicValNat p (8 * r + 3).factorial) (hi_pos : i ≥ 1) (hn_ge : 8 * n ≥ 2 * r + 1) :
    let Iv := if i ≤ v then 1 else 0
    let Ik := if i ≤ k then 1 else 0
    4 * n / p^i + 3 * n / p^i + 2 * n / p^i + Iv ≤ 8 * n / p^i + n / p^i + Ik := by
  intro Iv Ik
  have h_pow_pos : p^i > 0 := Nat.pos_of_ne_zero (pow_ne_zero i hp.out.ne_zero)
  have h_div := div_add_div_eq n (p^i) h_pow_pos
  by_cases h_v : i ≤ v
  · by_cases h_k : i ≤ k
    · have h_Iv : Iv = 1 := by simp [Iv, h_v]
      have h_Ik : Ik = 1 := by simp [Ik, h_k]
      rw [h_Iv, h_Ik]
      omega
    · have h_Iv : Iv = 1 := by simp [Iv, h_v]
      have h_Ik : Ik = 0 := by simp [Ik, h_k]
      rw [h_Iv, h_Ik]
      simp only [add_zero]
      have h_ne : 8 * n - (2 * r + 1) ≠ 0 := by omega
      have h_v_rew : i ≤ padicValNat p (8 * n - (2 * r + 1)) := hv ▸ h_v
      have h_dvd : p^i ∣ 8 * n - (2 * r + 1) := by
        rw [padicValNat_dvd_iff_le h_ne]
        exact h_v_rew
      have h_gt : p^i > 8 * r + 3 := by
        have hi_gt : i > k := by omega
        exact p_pow_gt_of_gt_padicValNat_factorial hk hi_gt
      let rem := n % (p^i)
      let q := n / (p^i)
      have h_eq1 : n = q * (p^i) + rem := by
        have : n = (p^i) * q + rem := (Nat.div_add_mod n (p^i)).symm
        rw [this, mul_comm (p^i) q]
      have h_rem : rem < p^i := Nat.mod_lt n h_pow_pos
      rcases h_dvd with ⟨c, hc⟩
      have hc2 : 8 * n = c * p^i + 2 * r + 1 := by
        have : 8 * n - (2 * r + 1) = c * p^i := by
          rw [hc, mul_comm]
        omega
      have h_P_odd : (p^i) % 2 = 1 := by
        have h_mod : (p^i) % 2 = 0 ∨ (p^i) % 2 = 1 := by omega
        rcases h_mod with h0 | h1
        · rcases Nat.dvd_of_mod_eq_zero h0 with ⟨k_odd, hk⟩
          have : 2 * (k_odd * c) = 8 * n - (2 * r + 1) := by
            calc 2 * (k_odd * c) = (2 * k_odd) * c := by ring
            _ = (p^i) * c := by rw [← hk]
            _ = 8 * n - (2 * r + 1) := hc.symm
          omega
        · exact h1
      have h_c_odd : c % 2 = 1 := by
        have h_mod : c % 2 = 0 ∨ c % 2 = 1 := by omega
        rcases h_mod with h0 | h1
        · rcases Nat.dvd_of_mod_eq_zero h0 with ⟨k_odd, hk⟩
          have : 2 * (p^i * k_odd) = 8 * n - (2 * r + 1) := by
            calc 2 * (p^i * k_odd) = (p^i) * (2 * k_odd) := by ring
            _ = (p^i) * c := by rw [← hk]
            _ = 8 * n - (2 * r + 1) := hc.symm
          omega
        · exact h1
      let m := c / 2
      have h_c_eq : c = 2 * m + 1 := by omega
      have hc3 : 8 * n = (2 * m + 1) * p^i + 2 * r + 1 := by
        rw [← h_c_eq]
        exact hc2
      exact omega_test n r m (p^i) q rem h_pow_pos h_rem h_eq1 hc3 h_gt
  · have h_Iv : Iv = 0 := by simp [Iv, h_v]
    rw [h_Iv]
    simp only [add_zero]
    by_cases h_k : i ≤ k
    · have h_Ik : Ik = 1 := by simp [Ik, h_k]
      rw [h_Ik]
      omega
    · have h_Ik : Ik = 0 := by simp [Ik, h_k]
      rw [h_Ik]
      simp only [add_zero]
      omega

lemma sum_indicator_eq_self_base (v : ℕ) :
    (Finset.Ico 1 (v + 1)).sum (fun i => if i ≤ v then 1 else 0) = v := by
  induction v with
  | zero => simp
  | succ v ih =>
    rw [Finset.sum_Ico_succ_top (by omega)]
    have : (if v + 1 ≤ v + 1 then 1 else 0) = 1 := by simp
    rw [this]
    have h_eq : (Finset.Ico 1 (v + 1)).sum (fun i => if i ≤ v + 1 then 1 else 0) =
                (Finset.Ico 1 (v + 1)).sum (fun i => if i ≤ v then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mem_Ico] at hx
      have h1 : x ≤ v + 1 := by omega
      have h2 : x ≤ v := by omega
      rw [if_pos h1, if_pos h2]
    rw [h_eq, ih]

lemma sum_indicator_eq_self (v b : ℕ) (h : v < b) :
    (Finset.Ico 1 b).sum (fun i => if i ≤ v then 1 else 0) = v := by
  induction b with
  | zero => omega
  | succ b ih =>
    by_cases hb : v < b
    · rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ b)]
      have : (if b ≤ v then 1 else 0) = 0 := by simp [hb]
      rw [this, add_zero]
      exact ih hb
    · have : b = v := by omega
      subst this
      exact sum_indicator_eq_self_base b

theorem claim1_case1 (r n : ℕ) (h_lt : 8 * n < 2 * r + 1) :
    ((8 * n : ℤ) - (2 * r + 1 : ℤ)) ∣ (a n : ℤ) * (8 * r + 3).factorial := by
  have h1 : 0 < 2 * r + 1 - 8 * n := by omega
  have h2 : 2 * r + 1 - 8 * n ≤ 8 * r + 3 := by omega
  have h_dvd := Nat.dvd_factorial h1 h2
  have h_dvd_int : ((2 * r + 1 - 8 * n : ℕ) : ℤ) ∣ ((8 * r + 3).factorial : ℤ) := by exact_mod_cast h_dvd
  have h_eq : ((8 * n : ℤ) - (2 * r + 1 : ℤ)) = - ((2 * r + 1 - 8 * n : ℕ) : ℤ) := by omega
  rw [h_eq]
  have h_neg_dvd : -((2 * r + 1 - 8 * n : ℕ) : ℤ) ∣ ((8 * r + 3).factorial : ℤ) := by
    exact neg_dvd.mpr h_dvd_int
  exact dvd_mul_of_dvd_right h_neg_dvd _

theorem claim1_case2 (r n : ℕ) (h_ge : 8 * n ≥ 2 * r + 1) :
    ((8 * n : ℤ) - (2 * r + 1 : ℤ)) ∣ (a n : ℤ) * (8 * r + 3).factorial := by
  let d_nat := 8 * n - (2 * r + 1)
  let H_nat := (8 * r + 3).factorial
  let Y := (4 * n).factorial * (3 * n).factorial * (2 * n).factorial
  let X := (8 * n).factorial * n.factorial
  have h_dvd : d_nat * Y ∣ X * H_nat := by
    have h_ne1 : d_nat * Y ≠ 0 := by
      have : d_nat ≠ 0 := by omega
      have : Y ≠ 0 := by positivity
      positivity
    have h_ne2 : X * H_nat ≠ 0 := by
      have : X ≠ 0 := by positivity
      have : H_nat ≠ 0 := by positivity
      positivity
    rw [← Nat.factorization_le_iff_dvd h_ne1 h_ne2]
    rw [Finsupp.le_def]
    intro p
    by_cases pp : p.Prime
    · have : Fact p.Prime := ⟨pp⟩
      rw [Nat.factorization_def _ pp, Nat.factorization_def _ pp]
      have h1 : padicValNat p (d_nat * Y) = padicValNat p d_nat + padicValNat p Y := padicValNat.mul (by omega) (by positivity)
      have h2 : padicValNat p (X * H_nat) = padicValNat p X + padicValNat p H_nat := padicValNat.mul (by positivity) (by positivity)
      rw [h1, h2]
      let b := 8 * n + 8 * r + 4
      have hb4 : log p (4 * n) < b := by
        have := Nat.log_le_self p (4 * n)
        omega
      have hb3 : log p (3 * n) < b := by
        have := Nat.log_le_self p (3 * n)
        omega
      have hb2 : log p (2 * n) < b := by
        have := Nat.log_le_self p (2 * n)
        omega
      have hb8 : log p (8 * n) < b := by
        have := Nat.log_le_self p (8 * n)
        omega
      have hbn : log p n < b := by
        have := Nat.log_le_self p n
        omega
      have h_v_lt : padicValNat p d_nat < b := by
        have h_pow_le : p ^ (padicValNat p d_nat) ≤ d_nat := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
        have h_v_lt_pow : padicValNat p d_nat < p ^ (padicValNat p d_nat) := Nat.lt_pow_self pp.one_lt
        omega
      have h_k_lt : padicValNat p H_nat < b := by
        have h_k_le : padicValNat p H_nat ≤ 8 * r + 3 := padicValNat_factorial_le p (8 * r + 3)
        omega
      have hY_val : padicValNat p Y = padicValNat p (4 * n).factorial + padicValNat p (3 * n).factorial + padicValNat p (2 * n).factorial := by
        change padicValNat p ((4 * n).factorial * (3 * n).factorial * (2 * n).factorial) = _
        have h1_mul : padicValNat p ((4 * n).factorial * (3 * n).factorial * (2 * n).factorial) =
                  padicValNat p ((4 * n).factorial * (3 * n).factorial) + padicValNat p (2 * n).factorial := by
          exact padicValNat.mul (by positivity) (by positivity)
        have h2_mul : padicValNat p ((4 * n).factorial * (3 * n).factorial) =
                  padicValNat p (4 * n).factorial + padicValNat p (3 * n).factorial := by
          exact padicValNat.mul (by positivity) (by positivity)
        rw [h1_mul, h2_mul]
      have hX_val : padicValNat p X = padicValNat p (8 * n).factorial + padicValNat p n.factorial := by
        exact padicValNat.mul (by positivity) (by positivity)
      rw [hY_val, hX_val]
      rw [padicValNat_factorial hb4, padicValNat_factorial hb3, padicValNat_factorial hb2, padicValNat_factorial hb8, padicValNat_factorial hbn]
      rw [← sum_indicator_eq_self (padicValNat p d_nat) b h_v_lt, ← sum_indicator_eq_self (padicValNat p H_nat) b h_k_lt]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i hi
      rw [Finset.mem_Ico] at hi
      have hi_pos : i ≥ 1 := by omega
      have h_term := term_by_term n r p i (padicValNat p d_nat) (padicValNat p H_nat) rfl rfl hi_pos h_ge
      omega
    · rw [Nat.factorization_eq_zero_of_not_prime _ pp, Nat.factorization_eq_zero_of_not_prime _ pp]
  have h_eq : (X * H_nat : ℤ) = (a n : ℤ) * H_nat * Y := by
    calc (X * H_nat : ℤ) = (X : ℤ) * (H_nat : ℤ) := by push_cast; rfl
    _ = ((a n : ℤ) * Y) * (H_nat : ℤ) := by rw [← a_mul_Y_eq_X n]
    _ = (a n : ℤ) * H_nat * Y := by ring
  have h_dvd_int : ((d_nat * Y : ℕ) : ℤ) ∣ ((X * H_nat : ℕ) : ℤ) := by exact_mod_cast h_dvd
  have h_dvd_int_rew : ((d_nat : ℤ) * (Y : ℤ)) ∣ ((X : ℤ) * (H_nat : ℤ)) := by exact_mod_cast h_dvd_int
  rw [h_eq] at h_dvd_int_rew
  have hY_pos : (Y : ℤ) ≠ 0 := by positivity
  rw [mul_dvd_mul_iff_right hY_pos] at h_dvd_int_rew
  have h_final := h_dvd_int_rew
  have h_eq_d : ((8 * n : ℤ) - (2 * r + 1 : ℤ)) = (d_nat : ℤ) := by omega
  rw [h_eq_d]
  exact h_final

theorem claim1 (r : ℕ) : ∃ H : ℤ, H > 0 ∧ ∀ n : ℕ,
    ((8 * n : ℤ) - (2 * r + 1 : ℤ)) ∣ (a n : ℤ) * H := by
  use (8 * r + 3).factorial
  refine ⟨by positivity, fun n => ?_⟩
  have h_cases : 8 * n < 2 * r + 1 ∨ 8 * n ≥ 2 * r + 1 := by omega
  rcases h_cases with h_lt | h_ge
  · exact claim1_case1 r n h_lt
  · exact claim1_case2 r n h_ge
