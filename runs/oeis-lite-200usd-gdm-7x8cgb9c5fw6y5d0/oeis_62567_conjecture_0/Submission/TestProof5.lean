import FormalConjectures.Util.ProblemImports

open Nat Classical

def reverse_nat (k : ℕ) : ℕ :=
  ofDigits 10 (digits 10 k).reverse

noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let P (k : ℕ) : Prop := k > 0 ∧ n ∣ reverse_nat (k * n)
    if h_ex : ∃ k, P k then
      have HP : DecidablePred P := by infer_instance
      let k_min : ℕ := Nat.find h_ex
      k_min * n
    else
      0

def weighted_sum_helper (idx : ℕ) : List ℕ → ℕ
  | [] => 0
  | x :: xs => idx * x + weighted_sum_helper (idx + 1) xs

def weighted_sum (L : List ℕ) : ℕ :=
  weighted_sum_helper 0 L

theorem weighted_sum_helper_shift (idx : ℕ) (L : List ℕ) :
    weighted_sum_helper (idx + 1) L = weighted_sum_helper idx L + L.sum := by
  induction L generalizing idx with
  | nil => rfl
  | cons x xs ih =>
    simp [weighted_sum_helper, List.sum_cons]
    rw [ih (idx + 1)]
    have h_dist : (idx + 1) * x = idx * x + x := by ring
    rw [h_dist]
    omega

theorem ofDigits_cong (L : List ℕ) :
    ofDigits 10 L ≡ L.sum + 9 * weighted_sum L [MOD 81] := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    dsimp [ofDigits, List.sum, weighted_sum]
    have h_mul : x + 10 * ofDigits 10 xs ≡ x + 10 * (xs.sum + 9 * weighted_sum_helper 0 xs) [MOD 81] := by
      have h1 := ModEq.mul_left 10 ih
      have h2 := ModEq.add_left x h1
      exact h2
    have h_rhs : weighted_sum_helper 0 (x :: xs) = weighted_sum_helper 0 xs + xs.sum := by
      simp [weighted_sum_helper]
      exact weighted_sum_helper_shift 0 xs
    rw [h_rhs]
    have h_eq : x + 10 * (xs.sum + 9 * weighted_sum_helper 0 xs) ≡ x + xs.sum + 9 * (weighted_sum_helper 0 xs + xs.sum) [MOD 81] := by
      unfold ModEq
      omega
    exact h_mul.trans h_eq

theorem weighted_sum_helper_add (idx : ℕ) (L1 L2 : List ℕ) :
    weighted_sum_helper idx (L1 ++ L2) = weighted_sum_helper idx L1 + weighted_sum_helper (idx + L1.length) L2 := by
  induction L1 generalizing idx with
  | nil => simp [weighted_sum_helper]
  | cons y ys ih =>
    simp [weighted_sum_helper]
    rw [ih (idx + 1)]
    omega

theorem weighted_sum_add (L1 L2 : List ℕ) :
    weighted_sum (L1 ++ L2) = weighted_sum L1 + weighted_sum L2 + L1.length * L2.sum := by
  unfold weighted_sum
  rw [weighted_sum_helper_add 0 L1 L2]
  have h_shift : ∀ idx, weighted_sum_helper idx L2 = weighted_sum_helper 0 L2 + idx * L2.sum := by
    intro idx
    induction idx with
    | zero => simp
    | succ idx ih =>
      rw [weighted_sum_helper_shift idx L2]
      rw [ih]
      ring
  have h_add : 0 + L1.length = L1.length := by omega
  rw [h_add, h_shift L1.length]
  ring

theorem weighted_sum_reverse (L : List ℕ) :
    weighted_sum L.reverse + weighted_sum L = (L.length - 1) * L.sum := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    simp [List.reverse_cons]
    rw [weighted_sum_add xs.reverse [x]]
    simp only [weighted_sum] at *
    simp [weighted_sum_helper, List.sum_cons]
    cases h_len : xs.length with
    | zero =>
      have h_xs : xs = [] := by
        cases xs
        · rfl
        · contradiction
      subst h_xs
      simp [weighted_sum_helper]
    | succ n =>
      have h_sub : xs.length - 1 = n := by omega
      have ih' : weighted_sum_helper 0 xs.reverse + weighted_sum_helper 0 xs = n * xs.sum := by
        rw [h_sub] at ih
        exact ih
      have h_shift1 : weighted_sum_helper 1 xs = weighted_sum_helper 0 xs + xs.sum := by
        exact weighted_sum_helper_shift 0 xs
      have h_group : weighted_sum_helper 0 xs.reverse + (n + 1) * x + weighted_sum_helper 1 xs = (weighted_sum_helper 0 xs.reverse + weighted_sum_helper 0 xs) + (n + 1) * x + xs.sum := by
        rw [h_shift1]
        ring
      rw [h_group, ih']
      ring

theorem list_all_nines (L : List ℕ) (h_len : L.length = 9) (h_sum : L.sum = 81) (h_lt : ∀ x ∈ L, x < 10) :
    L = [9, 9, 9, 9, 9, 9, 9, 9, 9] := by
  match L with
  | [d1, d2, d3, d4, d5, d6, d7, d8, d9] =>
    have h_d1 : d1 < 10 := h_lt d1 (by simp)
    have h_d2 : d2 < 10 := h_lt d2 (by simp)
    have h_d3 : d3 < 10 := h_lt d3 (by simp)
    have h_d4 : d4 < 10 := h_lt d4 (by simp)
    have h_d5 : d5 < 10 := h_lt d5 (by simp)
    have h_d6 : d6 < 10 := h_lt d6 (by simp)
    have h_d7 : d7 < 10 := h_lt d7 (by simp)
    have h_d8 : d8 < 10 := h_lt d8 (by simp)
    have h_d9 : d9 < 10 := h_lt d9 (by simp)
    have h_sum' : d1 + d2 + d3 + d4 + d5 + d6 + d7 + d8 + d9 = 81 := by
      simp [List.sum] at h_sum
      omega
    have h_eq1 : d1 = 9 := by omega
    have h_eq2 : d2 = 9 := by omega
    have h_eq3 : d3 = 9 := by omega
    have h_eq4 : d4 = 9 := by omega
    have h_eq5 : d5 = 9 := by omega
    have h_eq6 : d6 = 9 := by omega
    have h_eq7 : d7 = 9 := by omega
    have h_eq8 : d8 = 9 := by omega
    have h_eq9 : d9 = 9 := by omega
    subst h_eq1 h_eq2 h_eq3 h_eq4 h_eq5 h_eq6 h_eq7 h_eq8 h_eq9
    rfl

theorem ofDigits_eq_zero_of_sum_eq_zero (L : List ℕ) (h : L.sum = 0) : ofDigits 10 L = 0 := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    simp [List.sum] at h
    have h_x : x = 0 := by omega
    have h_xs : xs.sum = 0 := by omega
    simp [ofDigits, h_x, ih h_xs]

theorem a_81_eq : a 81 = 999999999 := by
  dsimp [a]
  split_ifs with h0
  · have h_le : Nat.find h0 ≤ 12345679 := by
      apply Nat.find_min'
      refine ⟨by decide, ?_⟩
      unfold reverse_nat
      simp; decide
    have h_ge : Nat.find h0 ≥ 12345679 := by
      by_contra hc
      push_neg at hc
      let k := Nat.find h0
      have hk : k > 0 ∧ 81 ∣ reverse_nat (k * 81) := Nat.find_spec h0
      let M := k * 81
      have h_m_pos : M > 0 := by omega
      have h_m_lt : M < 999999999 := by omega
      let L := digits 10 M
      have h_of_digits : ofDigits 10 L = M := ofDigits_digits 10 M
      have h_reverse : reverse_nat M = ofDigits 10 L.reverse := rfl
      have h_lt10 : M < 10^9 := by omega
      have h_digits_len : L.length ≤ 9 := by
        rwa [digits_length_le_iff (by decide)]
      have h_m_cong : M ≡ L.sum + 9 * weighted_sum L [MOD 81] := by
        rw [← h_of_digits]
        exact ofDigits_cong L
      have h_r_cong : reverse_nat M ≡ L.sum + 9 * weighted_sum L.reverse [MOD 81] := by
        rw [h_reverse]
        have h_sum_rev : L.reverse.sum = L.sum := by simp
        have h_cong_rev := ofDigits_cong L.reverse
        rw [h_sum_rev] at h_cong_rev
        exact h_cong_rev
      have h_m_div : 81 ∣ M := by use k
      have h_m_zero : M ≡ 0 [MOD 81] := h_m_div
      have h_r_div : 81 ∣ reverse_nat M := hk.2
      have h_r_zero : reverse_nat M ≡ 0 [MOD 81] := h_r_div
      have h_m_zero2 : L.sum + 9 * weighted_sum L ≡ 0 [MOD 81] := h_m_cong.symm.trans h_m_zero
      have h_r_zero2 : L.sum + 9 * weighted_sum L.reverse ≡ 0 [MOD 81] := h_r_cong.symm.trans h_r_zero
      have h_add_zero : (L.sum + 9 * weighted_sum L) + (L.sum + 9 * weighted_sum L.reverse) ≡ 0 + 0 [MOD 81] := by
        exact ModEq.add h_m_zero2 h_r_zero2
      have h_rearr : (L.sum + 9 * weighted_sum L) + (L.sum + 9 * weighted_sum L.reverse) = 2 * L.sum + 9 * (weighted_sum L.reverse + weighted_sum L) := by ring
      rw [h_rearr] at h_add_zero
      rw [weighted_sum_reverse L] at h_add_zero
      have h_factor : 2 * L.sum + 9 * ((L.length - 1) * L.sum) = L.sum * (2 + 9 * (L.length - 1)) := by ring
      rw [h_factor] at h_add_zero
      have h_len_pos : L.length > 0 := by
        rw [length_pos_iff]
        apply digits_ne_nil_iff_ne_zero (by decide) |>.mpr
        omega
      have h_sum_div_81 : 81 ∣ L.sum := by
        unfold ModEq at h_add_zero
        have h_dvd : 81 ∣ L.sum * (2 + 9 * (L.length - 1)) := by
          rw [← dvd_iff_mod_eq_zero] at h_add_zero
          exact h_add_zero
        interval_cases L.length
        · have h_coprime : Coprime 81 2 := by decide
          exact Coprime.dvd_of_dvd_mul_right h_coprime h_dvd
        · have h_coprime : Coprime 81 11 := by decide
          exact Coprime.dvd_of_dvd_mul_right h_coprime h_dvd
        · have h_coprime : Coprime 81 20 := by decide
          exact Coprime.dvd_of_dvd_mul_right h_coprime h_dvd
        · have h_coprime : Coprime 81 29 := by decide
          exact Coprime.dvd_of_dvd_mul_right h_coprime h_dvd
        · have h_coprime : Coprime 81 38 := by decide
          exact Coprime.dvd_of_dvd_mul_right h_coprime h_dvd
        · have h_coprime : Coprime 81 47 := by decide
          exact Coprime.dvd_of_dvd_mul_right h_coprime h_dvd
        · have h_coprime : Coprime 81 56 := by decide
          exact Coprime.dvd_of_dvd_mul_right h_coprime h_dvd
        · have h_coprime : Coprime 81 65 := by decide
          exact Coprime.dvd_of_dvd_mul_right h_coprime h_dvd
        · have h_coprime : Coprime 81 74 := by decide
          exact Coprime.dvd_of_dvd_mul_right h_coprime h_dvd
      have h_digits_lt10 : ∀ x ∈ L, x < 10 := fun x hx ↦ digits_lt_base (by decide) hx
      have h_sum_le : L.sum ≤ 9 * L.length := by
        have h_le_nine : ∀ x ∈ L, x ≤ 9 := fun x hx ↦ by
          have := h_digits_lt10 x hx
          omega
        have h_sum_le_card := List.sum_le_card_nsmul L 9 h_le_nine
        omega
      have h_sum_le_81 : L.sum ≤ 81 := by omega
      have h_sum_pos : L.sum > 0 := by
        by_contra h_zero
        have h_sum_eq0 : L.sum = 0 := by omega
        have h_m_eq0 : M = 0 := by
          rw [← h_of_digits]
          exact ofDigits_eq_zero_of_sum_eq_zero L h_sum_eq0
        omega
      have h_sum_eq_81 : L.sum = 81 := by
        rcases h_sum_div_81 with ⟨c, hc⟩
        have : c > 0 := by
          by_contra hc_zero
          have : c = 0 := by omega
          subst this
          omega
        have : c = 1 := by omega
        subst this
        omega
      have h_len_eq_9 : L.length = 9 := by omega
      have h_L_eq : L = [9, 9, 9, 9, 9, 9, 9, 9, 9] := list_all_nines L h_len_eq_9 h_sum_eq_81 h_digits_lt10
      have h_m_eq_999 : M = 999999999 := by
        rw [← h_of_digits, h_L_eq]
        rfl
      omega
    omega
  · contradiction
