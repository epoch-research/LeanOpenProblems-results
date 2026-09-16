import Submission.Lemmas
import Submission.Spec
import Mathlib

open Nat

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

lemma sumD_remove_zeros (M : ℕ) : sumD (remove_zeros M) = sumD M := by
  unfold remove_zeros
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
