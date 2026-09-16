import Submission.Lemmas
import Mathlib

open Nat Finset

lemma sum_filter_not_zero (L : List ℕ) : (L.filter (· ≠ 0)).sum = L.sum := by
  induction' L with d t ih
  · rfl
  · by_cases h : d = 0
    · subst h
      have : (0 :: t).filter (· ≠ 0) = t.filter (· ≠ 0) := rfl
      rw [this, ih]
      simp
    · have : decide (d ≠ 0) = true := decide_eq_true h
      have e : (d :: t).filter (· ≠ 0) = d :: t.filter (· ≠ 0) := by
        rw [List.filter_cons, this]
        simp
      rw [e, List.sum_cons, List.sum_cons, ih]

lemma sum_le_ofDigits (L : List ℕ) : L.sum ≤ Nat.ofDigits 10 L := by
  induction' L with d t ih
  · rfl
  · simp [Nat.ofDigits]
    omega

lemma sumD_ofDigits (L : List ℕ) (h : ∀ x ∈ L, x < 10) : sumD (Nat.ofDigits 10 L) = L.sum := by
  induction' L with d t ih
  · rw [Nat.ofDigits, sumD_zero]
    rfl
  · simp [Nat.ofDigits]
    have hd : d < 10 := by
      apply h
      simp
    have ht : ∀ x ∈ t, x < 10 := by
      intro x hx
      apply h
      simp [hx]
    have eq1 : d + 10 * Nat.ofDigits 10 t = Nat.ofDigits 10 t * 10^1 + d := by ring
    rw [eq1]
    have h_lt : d < 10^1 := by omega
    rw [sumD_append (Nat.ofDigits 10 t) d 1 h_lt]
    rw [ih ht]
    have : sumD d = d := sumD_lt_10 d hd
    omega

lemma digits_lt_10 (M : ℕ) : ∀ x ∈ Nat.digits 10 M, x < 10 := by
  induction' M using Nat.strong_induction_on with M ih
  by_cases h : M = 0
  · subst h
    simp
  · intro x hx
    have h_pos := Nat.pos_of_ne_zero h
    rw [Nat.digits_def' (by decide) h_pos] at hx
    simp at hx
    cases hx with
    | inl eq =>
      subst eq
      exact Nat.mod_lt _ (by decide)
    | inr mem =>
      exact ih (M / 10) (Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)) x mem

lemma sumD_eq_digits_sum (M : ℕ) : sumD M = (Nat.digits 10 M).sum := by
  induction' M using Nat.strong_induction_on with M ih
  by_cases h : M = 0
  · subst h; simp [sumD_zero]
  · have h_pos := Nat.pos_of_ne_zero h
    rw [Nat.digits_def' (by decide) h_pos, sumD_pos _ h]
    simp
    rw [ih (M / 10) (Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide))]

lemma sumD_remove_zeros (M : ℕ) : sumD (Submission.Spec.remove_zeros M) = sumD M := by
  unfold Submission.Spec.remove_zeros
  have hd_lt := digits_lt_10 M
  have h_filter : ∀ x ∈ (Nat.digits 10 M).filter (· ≠ 0), x < 10 := by
    intro x hx
    have : x ∈ Nat.digits 10 M := List.mem_of_mem_filter hx
    exact hd_lt x this
  rw [sumD_ofDigits _ h_filter]
  rw [sum_filter_not_zero]
  rw [sumD_eq_digits_sum M]

lemma V_list_pos (l : List ℕ) (k pos : ℕ) (h : l.sum > 0) : V_list l k pos > 0 := by
  induction' l with d t ih generalizing pos
  · simp at h
  · simp [V_list]
    by_cases h0 : d = 0
    · subst h0
      simp at h
      have := ih (pos + 1) h
      omega
    · have h_d : d > 0 := Nat.pos_of_ne_zero h0
      have h_pow : 10^(pos % k) > 0 := pow_ten_pos _
      have : d * 10^(pos % k) > 0 := Nat.mul_pos h_d h_pow
      omega

lemma V_list_zero_iff (l : List ℕ) (k pos : ℕ) : V_list l k pos = 0 ↔ l.sum = 0 := by
  constructor
  · intro h
    by_contra h_sum
    have h_pos : l.sum > 0 := by omega
    have := V_list_pos l k pos h_pos
    omega
  · intro h
    induction' l with d t ih generalizing pos
    · simp [V_list]
    · simp at h
      have hd : d = 0 := by omega
      have ht : t.sum = 0 := by omega
      subst hd
      simp [V_list]
      exact ih (pos + 1) ht

lemma sumD_le_self (x : ℕ) : sumD x ≤ x := by
  induction' x using Nat.strong_induction_on with x ih
  by_cases h : x = 0
  · subst h; simp [sumD_zero]
  · rw [sumD_pos _ h]
    have := ih (x / 10) (Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide))
    have : x % 10 + x / 10 ≤ x := by
      have e : x = 10 * (x / 10) + x % 10 := (Nat.div_add_mod x 10).symm
      have : x / 10 ≤ 10 * (x / 10) := Nat.le_mul_of_pos_left _ (by decide)
      omega
    omega

lemma sumD_eq_zero_iff (M : ℕ) : sumD M = 0 ↔ M = 0 := by
  induction' M using Nat.strong_induction_on with M ih
  constructor
  · intro h
    by_contra h_neq
    have H : sumD M = M % 10 + sumD (M / 10) := sumD_pos M h_neq
    rw [h] at H
    have H1 : M % 10 = 0 := by omega
    have H2 : sumD (M / 10) = 0 := by omega
    have h_div_lt : M / 10 < M := Nat.div_lt_self (Nat.pos_of_ne_zero h_neq) (by decide)
    have : M / 10 = 0 := (ih (M / 10) h_div_lt).mp H2
    have e : M = 10 * (M / 10) + M % 10 := (Nat.div_add_mod M 10).symm
    rw [this, H1] at e
    omega
  · intro h
    subst h
    exact sumD_zero

lemma extract_y (n : ℕ) (x : ℕ) (hx : x ∈ Submission.Spec.reachable_zeroless_factorials (n + 1)) :
  ∃ y ∈ Submission.Spec.reachable_zeroless_factorials n, x = (n + 1) * y ∨ x = Submission.Spec.remove_zeros ((n + 1) * y) := by
  unfold Submission.Spec.reachable_zeroless_factorials at hx
  have h1 : ∃ a ∈ Submission.Spec.reachable_zeroless_factorials n, x ∈ {(n + 1) * a, Submission.Spec.remove_zeros ((n + 1) * a)} := Finset.mem_biUnion.mp hx
  rcases h1 with ⟨y, hy, h_insert⟩
  use y
  constructor
  · exact hy
  · simp at h_insert
    exact h_insert

lemma reachable_ge_one_strong (n : ℕ) (x : ℕ) (hx : x ∈ Submission.Spec.reachable_zeroless_factorials n) : x ≥ 1 := by
  induction' n with n ih generalizing x
  · unfold Submission.Spec.reachable_zeroless_factorials at hx
    simp at hx
    omega
  · rcases extract_y n x hx with ⟨y, hy, h_eq⟩
    have hy1 : y ≥ 1 := ih y hy
    cases h_eq with
    | inl h =>
      subst h
      have h1 : n + 1 > 0 := by omega
      have h2 : y > 0 := by omega
      have := Nat.mul_pos h1 h2
      omega
    | inr h =>
      subst h
      have h1 : n + 1 > 0 := by omega
      have h2 : y > 0 := by omega
      have M_pos : (n + 1) * y > 0 := Nat.mul_pos h1 h2
      have h_sumD : sumD ((n + 1) * y) ≠ 0 := by
        intro h0
        have := sumD_eq_zero_iff ((n + 1) * y)
        have H := this.mp h0
        omega
      have h_sumD_rz : sumD (Submission.Spec.remove_zeros ((n + 1) * y)) ≠ 0 := by
        rw [sumD_remove_zeros]
        exact h_sumD
      by_contra h_contra
      have : Submission.Spec.remove_zeros ((n + 1) * y) = 0 := by omega
      rw [this] at h_sumD_rz
      rw [sumD_zero] at h_sumD_rz
      exact h_sumD_rz rfl

lemma ten_pow_k_ge (B : ℕ) : 10^(B + 2) ≥ 100 := by
  have e : 10^(B + 2) = 10^B * 100 := by ring
  have h_pos : 10^B > 0 := pow_ten_pos B
  nlinarith

lemma B_lt_pow (B : ℕ) : B < 10^(B+2) - 1 := by
  induction' B with B ih
  · decide
  · have e : 10^(B+1+2) = 10 * 10^(B+2) := by ring
    rw [e]
    have : 10^(B+2) ≥ 100 := ten_pow_k_ge B
    generalize 10^(B+2) = X at this ih ⊢
    omega

theorem oeis_a374265_conjecture_1_boundedness_disproof : ¬ (∃ B : ℕ, ∀ n : ℕ, Submission.Spec.a n ≤ B) := by
  intro ⟨B, hB⟩
  let k := B + 2
  let n := 10^k - 1
  have H_a := hB n
  have H_nonempty := Submission.Spec.reachable_nonempty n
  have hx_in : Submission.Spec.a n ∈ Submission.Spec.reachable_zeroless_factorials n := Finset.min'_mem _ H_nonempty
  let x := Submission.Spec.a n
  have hx_le_B : x ≤ B := H_a

  have hk_pos : k > 0 := by omega
  have hn_pos : n > 0 := by
    have : 10^k ≥ 100 := ten_pow_k_ge B
    omega
  
  have h_n_eq : n = (n - 1) + 1 := by omega
  have hx_in2 : x ∈ Submission.Spec.reachable_zeroless_factorials ((n - 1) + 1) := by
    have e : (n - 1) + 1 = n := by omega
    rw [e]
    exact hx_in
  
  rcases extract_y (n - 1) x hx_in2 with ⟨y, hy, h_eq⟩
  have hy_ge : y ≥ 1 := reachable_ge_one_strong (n - 1) y hy
  let M := n * y
  have hM_eq : M = n * y := rfl
  have hM_pos : M > 0 := by
    have : n ≥ 1 := by omega
    have : y ≥ 1 := hy_ge
    nlinarith
  have hx_M : x = M ∨ x = Submission.Spec.remove_zeros M := by
    have e : (n - 1) + 1 = n := by omega
    rw [e] at h_eq
    exact h_eq
  
  have h_sumD_x : sumD x = sumD M := by
    cases hx_M with
    | inl h => rw [h]
    | inr h => rw [h, sumD_remove_zeros]

  have hM_mod : M % (10^k - 1) = 0 := by
    rw [hM_eq]
    have : n = 10^k - 1 := rfl
    rw [this]
    exact Nat.mul_mod_right _ _

  have h_sumD_x_le : sumD M ≤ B := by
    have : sumD x ≤ x := sumD_le_self x
    omega

  let L := Nat.digits 10 M
  have hL_sum : L.sum = sumD M := (sumD_eq_digits_sum M).symm
  have hL_lt : ∀ d ∈ L, d < 10 := digits_lt_10 M

  let V := V_list L k 0
  have hV_mod : V ≡ Nat.ofDigits 10 L * 10^0 [MOD 10^k - 1] := V_list_modEq L k 0 hk_pos
  have h_ofD : Nat.ofDigits 10 L = M := Nat.ofDigits_digits 10 M
  have hV_mod2 : V ≡ M [MOD 10^k - 1] := by
    have e : Nat.ofDigits 10 L * 10^0 = M := by rw [h_ofD]; ring
    rw [e] at hV_mod
    exact hV_mod
  
  have hM_mod2 : M ≡ 0 [MOD 10^k - 1] := by
    exact hM_mod
  have hV_mod3 : V ≡ 0 [MOD 10^k - 1] := Nat.ModEq.trans hV_mod2 hM_mod2

  have hV_le : V ≤ L.sum * 10^(k - 1) := V_list_le L k 0 hk_pos hL_lt
  have hL_sum_le : L.sum ≤ B := by omega
  have hV_le_B : V ≤ B * 10^(k - 1) := by
    have : L.sum * 10^(k - 1) ≤ B * 10^(k - 1) := Nat.mul_le_mul_right _ hL_sum_le
    omega

  have hL_sum_pos : L.sum > 0 := by
    rw [hL_sum]
    have : sumD M ≠ 0 := by
      intro h
      have := (sumD_eq_zero_iff M).mp h
      omega
    omega
  have hV_pos : V > 0 := V_list_pos L k 0 hL_sum_pos

  have hV_div : (10^k - 1) ∣ V := Nat.dvd_of_mod_eq_zero hV_mod3
  rcases hV_div with ⟨C, hC⟩
  have hC_pos : C > 0 := by
    by_contra h
    have : C = 0 := by omega
    subst this
    simp at hC
    omega
  
  have hV_eq : V = C * (10^k - 1) := by rw [hC, mul_comm]
  
  have hC_lt : C < 10^k := by
    by_contra h
    have h1 : C ≥ 10^k := by omega
    have h2 : V ≥ 10^k * (10^k - 1) := by
      rw [hV_eq]
      exact Nat.mul_le_mul_right _ h1
    have e_pos : 10^(k - 1) > 0 := pow_ten_pos (k - 1)
    have hB_lt : B < 10^k - 1 := B_lt_pow B
    have : 10^k = 10 * 10^(k - 1) := by
      have : k = (k - 1) + 1 := by omega
      nth_rw 1 [this]
      ring
    nlinarith

  have h_sumD_V : sumD V ≤ L.sum := sumD_V_list L k 0
  have h_sumD_V_le_B : sumD V ≤ B := by omega

  have hV_split : V = (C - 1) * 10^k + (10^k - C) := by
    have : C * 10^k = C * 10^k := rfl
    have e1 : C * (10^k - 1) = C * 10^k - C := by
      have h := Nat.mul_sub_left_distrib C (10^k) 1
      rw [Nat.mul_one] at h
      exact h
    rw [e1] at hV_eq
    have e2 : C * 10^k - C = (C - 1) * 10^k + (10^k - C) := by
      have h1 : C * 10^k = (C - 1) * 10^k + 10^k := by
        have : C = (C - 1) + 1 := by omega
        nth_rw 1 [this]
        ring
      rw [h1]
      have : 10^k ≥ C := by omega
      omega
    rw [e2] at hV_eq
    exact hV_eq

  have h_sumD_split : sumD V = sumD (C - 1) + sumD (10^k - C) := by
    rw [hV_split]
    have : 10^k - C < 10^k := by omega
    exact sumD_append (C - 1) (10^k - C) k this

  have h_sumD_9k : sumD (C - 1) + sumD (10^k - C) = 9 * k := by
    have : 10^k - C = 10^k - 1 - (C - 1) := by omega
    rw [this]
    have : C - 1 < 10^k := by omega
    exact sumD_comp (C - 1) k this

  have h_9k_le_B : 9 * k ≤ B := by omega
  have h_cont : 9 * k > B := by
    have : k = B + 2 := rfl
    omega

  omega
