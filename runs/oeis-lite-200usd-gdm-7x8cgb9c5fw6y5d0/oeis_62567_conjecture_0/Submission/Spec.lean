import FormalConjectures.Util.ProblemImports

set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000

open Nat Classical

/-- The number whose digits in base 10 are $n$'s digits reversed. -/
def reverse_nat (k : ℕ) : ℕ :=
  ofDigits 10 (digits 10 k).reverse

/--
A062567: First multiple of $n$ whose reverse is also divisible by $n$, or 0 if no such multiple exists.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    -- P(k) is the predicate for the multiplier k: k > 0 and n divides the reverse of (k*n).
    let P (k : ℕ) : Prop := k > 0 ∧ n ∣ reverse_nat (k * n)

    -- We check if a solution exists (using classical reasoning, since P is decidable).
    if h_ex : ∃ k, P k then
      -- Nat.find requires a DecidablePred instance, which holds for this property on ℕ.
      have HP : DecidablePred P := by infer_instance
      -- k_min is the smallest multiplier k >= 1.
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
    have h_add : idx + 1 + ys.length = idx + (ys.length + 1) := by omega
    rw [h_add]
    ring

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
        · rename_i y ys
          simp [List.length] at h_len
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
    simp [ofDigits]
    have h_sum_zero : x = 0 ∧ xs.sum = 0 := by
      rw [List.sum_cons] at h
      omega
    exact ⟨h_sum_zero.1, ih h_sum_zero.2⟩

theorem omega_helper (S : ℕ) (h_mod : S % 81 = 0) (h_le : S ≤ 81) (h_pos : S > 0) : S = 81 := by omega

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
      have h_m_div : 81 ∣ M := by
        use k
        ring
      have h_m_zero : M ≡ 0 [MOD 81] := modEq_zero_iff_dvd.mpr h_m_div
      have h_r_div : 81 ∣ reverse_nat M := hk.2
      have h_r_zero : reverse_nat M ≡ 0 [MOD 81] := modEq_zero_iff_dvd.mpr h_r_div
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
        have h_ne : L ≠ [] := digits_ne_nil_iff_ne_zero.mpr (by omega)
        rcases L with _ | ⟨y, ys⟩
        · contradiction
        · simp
      have h_sum_div_81 : 81 ∣ L.sum := by
        unfold ModEq at h_add_zero
        have h_dvd : 81 ∣ L.sum * (2 + 9 * (L.length - 1)) := modEq_zero_iff_dvd.mp h_add_zero
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
        rw [nsmul_eq_mul] at h_sum_le_card
        norm_cast at h_sum_le_card
        have h_comm : L.length * 9 = 9 * L.length := Nat.mul_comm L.length 9
        rw [h_comm] at h_sum_le_card
        exact h_sum_le_card
      have h_mul_le : 9 * L.length ≤ 81 := by omega
      have h_sum_le_81 : L.sum ≤ 81 := Nat.le_trans h_sum_le h_mul_le
      have h_sum_pos : L.sum > 0 := by
        by_contra h_zero
        have h_sum_eq0 : L.sum = 0 := by omega
        have h_m_eq0 : M = 0 := by
          rw [← h_of_digits]
          exact ofDigits_eq_zero_of_sum_eq_zero L h_sum_eq0
        omega
      have h_sum_eq_81 : L.sum = 81 := by
        have h_mod : L.sum % 81 = 0 := dvd_iff_mod_eq_zero.mp h_sum_div_81
        exact omega_helper L.sum h_mod h_sum_le_81 h_sum_pos
      have h_len_eq_9 : L.length = 9 := by omega
      have h_L_eq : L = [9, 9, 9, 9, 9, 9, 9, 9, 9] := list_all_nines L h_len_eq_9 h_sum_eq_81 h_digits_lt10
      have h_m_eq_999 : M = 999999999 := by
        rw [← h_of_digits, h_L_eq]
        rfl
      omega
    omega
  · have h_ex : ∃ k, (k > 0 ∧ 81 ∣ reverse_nat (k * 81)) := by
      use 12345679
      refine ⟨by decide, ?_⟩
      unfold reverse_nat
      simp; decide
    contradiction

theorem a_nine : a 9 = 9 := by
  dsimp [a]
  split_ifs with h0
  · have h_find : Nat.find h0 = 1 := by
      rw [Nat.find_eq_iff]
      refine ⟨?_, fun m hm ↦ ?_⟩
      · refine ⟨by decide, ?_⟩
        unfold reverse_nat
        simp
      · interval_cases m
        rintro ⟨h_pos, -⟩
        contradiction
    rw [h_find, one_mul]
  · have h_ex : ∃ k, (k > 0 ∧ 9 ∣ reverse_nat (k * 9)) := by
      use 1
      refine ⟨by decide, ?_⟩
      unfold reverse_nat
      simp
    contradiction

theorem a_twentyseven : a 27 = 999 := by
  dsimp [a]
  split_ifs with h0
  · have h_find : Nat.find h0 = 37 := by
      rw [Nat.find_eq_iff]
      refine ⟨?_, fun m hm ↦ ?_⟩
      · refine ⟨by decide, ?_⟩
        unfold reverse_nat
        simp; decide
      · interval_cases m
        · rintro ⟨h_pos, -⟩
          contradiction
        all_goals
          rintro ⟨-, h_dvd⟩
          revert h_dvd
          unfold reverse_nat
          simp; decide
    rw [h_find]
  · have h_ex : ∃ k, (k > 0 ∧ 27 ∣ reverse_nat (k * 27)) := by
      use 37
      refine ⟨by decide, ?_⟩
      unfold reverse_nat
      simp; decide
    contradiction

theorem a_243_ne : a 243 ≠ 10^27 - 1 := by
  dsimp [a]
  split_ifs with h0
  · have h_le : Nat.find h0 ≤ 20164609 := by
      apply Nat.find_min'
      refine ⟨by decide, ?_⟩
      unfold reverse_nat
      simp; decide
    have h_val : Nat.find h0 * 243 ≤ 4899999987 := by
      omega
    omega
  · decide

theorem a_729_ne : a 729 ≠ 10^81 - 1 := by
  dsimp [a]
  split_ifs with h0
  · have h_le : Nat.find h0 ≤ 27297668 := by
      apply Nat.find_min'
      refine ⟨by decide, ?_⟩
      unfold reverse_nat
      simp; decide
    have h_val : Nat.find h0 * 729 ≤ 19899999972 := by
      omega
    omega
  · decide

theorem a_mono (n m : ℕ) (hnm : n ∣ m) (hn_pos : n > 0) (hm_pos : m > 0)
    (h_ex_m : ∃ k, k > 0 ∧ m ∣ reverse_nat (k * m)) : a n ≤ a m := by
  have h_n_ne : n ≠ 0 := by omega
  have h_m_ne : m ≠ 0 := by omega
  dsimp [a]
  rw [if_neg h_n_ne, if_neg h_m_ne]
  rw [dif_pos h_ex_m]
  split_ifs with h_ex_n
  · have h_m_spec := Nat.find_spec h_ex_m
    let k_m := Nat.find h_ex_m
    let M := k_m * m
    have h_div_n : n ∣ M := dvd_trans hnm (by use k_m; ring)
    have h_rev_n : n ∣ reverse_nat M := dvd_trans hnm h_m_spec.2
    rcases h_div_n with ⟨k_n, hk_n⟩
    have hk_n' : k_n * n = M := by
      rw [hk_n]
      ring
    have h_pos_kn : k_n > 0 := by
      have : M > 0 := by
        have : k_m > 0 := h_m_spec.1
        have : m > 0 := hm_pos
        exact Nat.mul_pos ‹k_m > 0› ‹m > 0›
      rw [← hk_n'] at this
      exact Nat.pos_of_mul_pos_right this
    have h_spec_n : k_n > 0 ∧ n ∣ reverse_nat (k_n * n) := by
      refine ⟨h_pos_kn, ?_⟩
      rw [hk_n']
      exact h_rev_n
    have h_find_le : Nat.find h_ex_n ≤ k_n := Nat.find_min' h_ex_n h_spec_n
    have h_le_mul : Nat.find h_ex_n * n ≤ k_n * n := Nat.mul_le_mul_right n h_find_le
    rw [hk_n'] at h_le_mul
    exact h_le_mul
  · have h_ex_n_true : ∃ k, k > 0 ∧ n ∣ reverse_nat (k * n) := by
      have h_m_spec := Nat.find_spec h_ex_m
      let k_m := Nat.find h_ex_m
      let M := k_m * m
      have h_div_n : n ∣ M := dvd_trans hnm (by use k_m; ring)
      rcases h_div_n with ⟨k_n, hk_n⟩
      have hk_n' : k_n * n = M := by rw [hk_n]; ring
      have h_pos_kn : k_n > 0 := by
        have : M > 0 := Nat.mul_pos h_m_spec.1 hm_pos
        rw [← hk_n'] at this
        exact Nat.pos_of_mul_pos_right this
      use k_n
      refine ⟨h_pos_kn, ?_⟩
      rw [hk_n']
      exact dvd_trans hnm h_m_spec.2
    contradiction

theorem digits_append_zeroes_append_digits_10 {k m n : ℕ} (hm : 0 < m) :
    digits 10 n ++ List.replicate k 0 ++ digits 10 m =
    digits 10 (n + 10 ^ ((digits 10 n).length + k) * m) := by
  exact digits_append_zeroes_append_digits (by decide) hm

theorem list_reverse_repeat (A : List ℕ) (k : ℕ) :
    (A ++ List.replicate k 0 ++ A ++ List.replicate k 0 ++ A).reverse =
    A.reverse ++ List.replicate k 0 ++ A.reverse ++ List.replicate k 0 ++ A.reverse := by
  simp

theorem ofDigits_append_replicate_zero (b : ℕ) (L : List ℕ) (k : ℕ) :
    ofDigits b (L ++ List.replicate k 0) = ofDigits b L := by
  rw [ofDigits_append]
  rw [Nat.ofDigits_replicate_zero]
  ring

lemma ten_pow_algebra (N : ℕ) (hN : 10^N ≥ 1) :
    (10^N - 1) * (1 + 10^N + 10^(2*N)) = 10^(3*N) - 1 := by
  have h1 : 3 * N = N + 2 * N := by ring
  rw [h1, Nat.pow_add]
  have h2 : 2 * N = N + N := by ring
  rw [h2, Nat.pow_add]
  let X := 10^N
  change (X - 1) * (1 + X + X * X) = X * (X * X) - 1
  have h_add : (X - 1) * (1 + X + X * X) + (1 + X + X * X) = X * (X * X) - 1 + (1 + X + X * X) := by
    have h_left : (X - 1) * (1 + X + X * X) + (1 + X + X * X) = X * (1 + X + X * X) := by
      rw [← Nat.add_one_mul]
      have : X - 1 + 1 = X := Nat.sub_add_cancel hN
      rw [this]
    rw [h_left]
    have h_sub_add : X * (X * X) - 1 + (1 + X + X * X) = X * (X * X) + X + X * X := by
      have : 1 + X + X * X = 1 + (X + X * X) := by omega
      rw [this, ← Nat.add_assoc]
      have hX3 : X * (X * X) ≥ 1 := by
        have : 1 ≤ X := hN
        have hsq : 1 ≤ X * X := one_le_mul this this
        exact one_le_mul this hsq
      rw [Nat.sub_add_cancel hX3]
      omega
    rw [h_sub_add]
    ring
  omega

lemma three_dvd_ten_pow_add (M : ℕ) : 3 ∣ 1 + 10^M + 10^(2*M) := by
  have h1 : 10 ≡ 1 [MOD 3] := by decide
  have h2 : 10^M ≡ 1^M [MOD 3] := ModEq.pow M h1
  have h3 : 1^M = 1 := by simp
  rw [h3] at h2
  have h4 : 10^(2*M) ≡ 1 [MOD 3] := by
    have h_pow := ModEq.pow (2*M) h1
    simp at h_pow
    exact h_pow
  have h_add : 1 + 10^M + 10^(2*M) ≡ 1 + 1 + 1 [MOD 3] := by
    apply ModEq.add
    · apply ModEq.add
      · rfl
      · exact h2
    · exact h4
  have h_zero : 1 + 10^M + 10^(2*M) ≡ 0 [MOD 3] := h_add.trans (by decide)
  exact modEq_zero_iff_dvd.mp h_zero

theorem reverse_nat_repeat (M N : ℕ) (hM_pos : M > 0) (hM : M < 10^N) :
    let k := N - (digits 10 M).length
    digits 10 (M + M * 10^N + M * 10^(2*N)) =
    digits 10 M ++ List.replicate k 0 ++ digits 10 M ++ List.replicate k 0 ++ digits 10 M := by
  intro k
  have h_len : (digits 10 M).length ≤ N := by
    exact (digits_length_le_iff (by decide) M).mpr hM
  have h_eq : (digits 10 M).length + k = N := by
    dsimp [k]
    omega
  let Y := M + M * 10^N
  have h_Y_eq : Y = M + 10^((digits 10 M).length + k) * M := by
    rw [h_eq]
    ring
  have h1 := digits_append_zeroes_append_digits_10 hM_pos (k := k) (n := M) (m := M)
  rw [← h_Y_eq] at h1
  have h2 := digits_append_zeroes_append_digits_10 hM_pos (k := k) (n := Y) (m := M)
  have h_len_Y : (digits 10 Y).length = N + (digits 10 M).length := by
    rw [← h1]
    simp
    omega
  have h_pow : (digits 10 Y).length + k = 2 * N := by
    omega
  rw [h_pow] at h2
  have h_assoc : Y + 10^(2*N) * M = M + M * 10^N + M * 10^(2*N) := by
    ring
  rw [h_assoc] at h2
  rw [← h2]
  rw [← h1]

theorem reverse_nat_repeat_mul (M N : ℕ) (hM_pos : M > 0) (hM : M < 10^N) :
    reverse_nat (M * (1 + 10^N + 10^(2*N))) = reverse_nat M * (1 + 10^N + 10^(2*N)) := by
  let k := N - (digits 10 M).length
  have h_len : (digits 10 M).length ≤ N := by
    exact (digits_length_le_iff (by decide) M).mpr hM
  have h_eq : (digits 10 M).length + k = N := by
    dsimp [k]
    omega
  have h_X : M * (1 + 10^N + 10^(2*N)) = M + M * 10^N + M * 10^(2*N) := by ring
  unfold reverse_nat
  rw [h_X]
  have h_digits := reverse_nat_repeat M N hM_pos hM
  dsimp [k] at h_digits
  rw [h_digits]
  have h_rev := list_reverse_repeat (digits 10 M) k
  rw [h_rev]
  let L1 := (digits 10 M).reverse ++ List.replicate k 0
  have h_L1_len : L1.length = N := by
    dsimp [L1]
    rw [List.length_append, List.length_reverse, List.length_replicate]
    exact h_eq
  have h_append3 : (digits 10 M).reverse ++ List.replicate k 0 ++ (digits 10 M).reverse ++ List.replicate k 0 ++ (digits 10 M).reverse = L1 ++ L1 ++ (digits 10 M).reverse := by
    dsimp [L1]
    simp
  rw [h_append3]
  rw [ofDigits_append, ofDigits_append]
  rw [h_L1_len]
  have h_L1_val : ofDigits 10 L1 = ofDigits 10 (digits 10 M).reverse := by
    dsimp [L1]
    exact ofDigits_append_replicate_zero 10 (digits 10 M).reverse k
  rw [h_L1_val]
  have h_L2_len : (L1 ++ L1).length = N * 2 := by
    rw [List.length_append, h_L1_len]
    ring
  rw [h_L2_len]
  have h_ring : 2 * N = N * 2 := by ring
  rw [h_ring]
  ring

lemma a_ne_target_of_exists_candidate (m T : ℕ) (hm_pos : m > 0) (h_ex : ∃ C, C > 0 ∧ m ∣ C ∧ m ∣ reverse_nat C ∧ C < T) :
    a m ≠ T := by
  intro h_eq
  rcases h_ex with ⟨C, hC_pos, h_div, h_rev, h_lt⟩
  have hm_ne : m ≠ 0 := by omega
  dsimp [a] at h_eq
  rw [if_neg hm_ne] at h_eq
  have h_prop : ∃ k, k > 0 ∧ m ∣ reverse_nat (k * m) := by
    rcases h_div with ⟨k, hk⟩
    use k
    have hk_pos : k > 0 := by
      by_contra hk0
      have : k = 0 := by omega
      subst this
      simp [hk] at hC_pos
    refine ⟨hk_pos, ?_⟩
    have hk_eq : k * m = C := by
      rw [Nat.mul_comm, ← hk]
    rw [hk_eq]
    exact h_rev
  rw [dif_pos h_prop] at h_eq
  rcases h_div with ⟨k, hk⟩
  have hk_pos : k > 0 := by
    by_contra hk0
    have : k = 0 := by omega
    subst this
    simp [hk] at hC_pos
  have h_spec_k : k > 0 ∧ m ∣ reverse_nat (k * m) := by
    refine ⟨hk_pos, ?_⟩
    have hk_eq : k * m = C := by
      rw [Nat.mul_comm, ← hk]
    rw [hk_eq]
    exact h_rev
  have h_le : Nat.find h_prop ≤ k := Nat.find_min' h_prop h_spec_k
  have h_le_mul : Nat.find h_prop * m ≤ k * m := Nat.mul_le_mul_right m h_le
  have hk_eq : k * m = C := by
    rw [Nat.mul_comm, ← hk]
  rw [hk_eq] at h_le_mul
  omega

def W : ℕ → ℕ
  | 0 => 4899999987
  | d + 1 => W d * (1 + 10^(10 * 3^d) + 10^(20 * 3^d))

def W_rev_val : ℕ → ℕ
  | 0 => 7899999984
  | d + 1 => W_rev_val d * (1 + 10^(10 * 3^d) + 10^(20 * 3^d))

lemma W_pos (d : ℕ) : W d > 0 := by
  induction d with
  | zero =>
    unfold W
    decide
  | succ d ih =>
    unfold W
    have h_term : 1 + 10 ^ (10 * 3 ^ d) + 10 ^ (20 * 3 ^ d) > 0 := by
      have : 1 + 10 ^ (10 * 3 ^ d) + 10 ^ (20 * 3 ^ d) = succ (10 ^ (10 * 3 ^ d) + 10 ^ (20 * 3 ^ d)) := by omega
      rw [this]
      exact Nat.succ_pos _
    exact Nat.mul_pos ih h_term

lemma ten_pow_ge_one (N : ℕ) : 10^N ≥ 1 := by
  have : 10 ≥ 1 := by decide
  exact Nat.one_le_pow N 10 this

lemma W_lt (d : ℕ) : W d < 10 ^ (10 * 3^d) := by
  induction d with
  | zero =>
    unfold W
    decide
  | succ d ih =>
    unfold W
    let N := 10 * 3^d
    have h_ih : W d < 10^N := ih
    have h_le : W d ≤ 10^N - 1 := by omega
    have h_mul_le : W d * (1 + 10^N + 10^(2*N)) ≤ (10^N - 1) * (1 + 10^N + 10^(2*N)) := Nat.mul_le_mul_right (1 + 10^N + 10^(2*N)) h_le
    have h_alg := ten_pow_algebra N (ten_pow_ge_one N)
    rw [h_alg] at h_mul_le
    have h_ring : 3 * N = 10 * 3^(d + 1) := by ring
    have h_lt_term : 10^(3 * N) - 1 < 10^(3 * N) := by
      have := ten_pow_ge_one (3 * N)
      omega
    have h_final : W d * (1 + 10^N + 10^(2*N)) < 10^(3 * N) := Nat.lt_of_le_of_lt h_mul_le h_lt_term
    rw [h_ring] at h_final
    have h_ring2 : W d * (1 + 10^N + 10^(2*N)) = W d * (1 + 10^(10 * 3^d) + 10^(20 * 3^d)) := by
      dsimp [N]
      ring
    rw [h_ring2] at h_final
    exact h_final

lemma W_div (d : ℕ) : 3^(d + 5) ∣ W d := by
  induction d with
  | zero =>
    unfold W
    decide
  | succ d ih =>
    unfold W
    have h_three := three_dvd_ten_pow_add (10 * 3^d)
    have h_mul := Nat.mul_dvd_mul ih h_three
    have h_ring_L : 3^(d + 5) * 3 = 3^(d + 6) := by ring
    rw [← h_ring_L]
    have h_ring_R : W d * (1 + 10^(10 * 3^d) + 10^(20 * 3^d)) = W d * (1 + 10^(10 * 3^d) + 10^(2 * (10 * 3^d))) := by ring
    rw [h_ring_R]
    exact h_mul

lemma W_rev (d : ℕ) : reverse_nat (W d) = W_rev_val d := by
  induction d with
  | zero =>
    unfold W W_rev_val reverse_nat
    simp
    decide
  | succ d ih =>
    let N := 10 * 3^d
    have h_pos := W_pos d
    have h_lt := W_lt d
    change W d < 10^N at h_lt
    have h_repeat := reverse_nat_repeat_mul (W d) N h_pos h_lt
    have h_unfold : W (d + 1) = W d * (1 + 10^N + 10^(2*N)) := by
      change W d * (1 + 10 ^ (10 * 3 ^ d) + 10 ^ (20 * 3 ^ d)) = W d * (1 + 10 ^ N + 10 ^ (2 * N))
      dsimp [N]
      ring
    unfold W_rev_val
    rw [h_unfold, h_repeat, ih]
    dsimp [N]
    ring

lemma W_rev_div (d : ℕ) : 3^(d + 5) ∣ reverse_nat (W d) := by
  rw [W_rev d]
  induction d with
  | zero =>
    unfold W_rev_val
    decide
  | succ d ih =>
    unfold W_rev_val
    have h_three := three_dvd_ten_pow_add (10 * 3^d)
    have h_mul := Nat.mul_dvd_mul ih h_three
    have h_ring_L : 3^(d + 5) * 3 = 3^(d + 6) := by ring
    rw [← h_ring_L]
    have h_ring_R : W_rev_val d * (1 + 10^(10 * 3^d) + 10^(20 * 3^d)) = W_rev_val d * (1 + 10^(10 * 3^d) + 10^(2 * (10 * 3^d))) := by ring
    rw [h_ring_R]
    exact h_mul

theorem a_ge_seven_ne (n : ℕ) : a (3^(n+7)) ≠ 10 ^ (3 ^ (n + 5)) - 1 := by
  let m := 3^(n+7)
  let T := 10 ^ (3 ^ (n + 5)) - 1
  have hm_pos : m > 0 := Nat.one_le_pow (n+7) 3 (by decide)
  have h_ex : ∃ C, C > 0 ∧ m ∣ C ∧ m ∣ reverse_nat C ∧ C < T := by
    let d := n + 2
    use W d
    refine ⟨W_pos d, ?_, ?_, ?_⟩
    · have h_div := W_div d
      have h_ring : d + 5 = n + 7 := by ring
      rw [h_ring] at h_div
      exact h_div
    · have h_rev_div := W_rev_div d
      have h_ring : d + 5 = n + 7 := by ring
      rw [h_ring] at h_rev_div
      exact h_rev_div
    · have h_lt := W_lt d
      have h_exp_ring : 3^(n + 5) = 27 * 3^(n + 2) := by ring
      have h_lt_exp : 10 * 3^(n + 2) < 3^(n + 5) := by
        rw [h_exp_ring]
        have h3_pos : 3^(n+2) > 0 := Nat.one_le_pow (n+2) 3 (by decide)
        exact Nat.mul_lt_mul_of_pos_right (by decide) h3_pos
      have h_pow_lt : 10 ^ (10 * 3^(n + 2)) < 10 ^ (3 ^ (n + 5)) := by
        have : 1 < 10 := by decide
        exact Nat.pow_lt_pow_right this h_lt_exp
      have h_pow_le : 10 ^ (10 * 3^(n + 2)) ≤ 10 ^ (3 ^ (n + 5)) - 1 := by
        omega
      exact Nat.lt_of_lt_of_le h_lt h_pow_le
  exact a_ne_target_of_exists_candidate m T hm_pos h_ex

/--
Conjecture A062567: It seems that only for n=2,3 & 4 we have a($3^n$) = $10^{3^{n-2}} - 1$.
(Formalized for $n \ge 2$ so that $n-2$ is a natural number exponent.)
-/
theorem oeis_62567_conjecture_0 (n : ℕ) :
  2 ≤ n → (a (3^n) = 10 ^ (3 ^ (n - 2)) - 1 ↔ n = 2 ∨ n = 3 ∨ n = 4) := by
  intro hn
  rcases n with _ | _ | n
  · omega
  · omega
  · rcases n with _ | _ | _ | n
    · -- n = 2
      simp [a_nine]
    · -- n = 3
      simp [a_twentyseven]
    · -- n = 4
      have hL : a 81 = 10 ^ (3 ^ 2) - 1 := by
        have h_pow : 10 ^ (3 ^ 2) - 1 = 999999999 := by rfl
        rw [h_pow]
        exact a_81_eq
      simp [hL]
    · -- n >= 5 (i.e. n + 5)
      have h_not : ¬ (n + 5 = 2 ∨ n + 5 = 3 ∨ n + 5 = 4) := by omega
      simp only [h_not, iff_false]
      rcases n with _ | n
      · -- n = 5
        exact a_243_ne
      · rcases n with _ | n
        · -- n = 6
          exact a_729_ne
        · -- n >= 7
          exact a_ge_seven_ne n
