import Mathlib

open Nat

def sumD (n : ℕ) : ℕ := if n = 0 then 0 else (n % 10) + sumD (n / 10)
termination_by n

lemma sumD_zero : sumD 0 = 0 := by
  conv => lhs; unfold sumD
  simp

lemma sumD_pos (n : ℕ) (h : n ≠ 0) : sumD n = n % 10 + sumD (n / 10) := by
  conv => lhs; unfold sumD
  simp [h]

lemma sumD_lt_10 (d : ℕ) (hd : d < 10) : sumD d = d := by
  by_cases h0 : d = 0
  · rw [h0, sumD_zero]
  · rw [sumD_pos d h0]
    have : d / 10 = 0 := by omega
    have h2 : d % 10 = d := by omega
    rw [this, sumD_zero, h2]
    exact rfl

lemma pow_ten_pos (i : ℕ) : 10^i > 0 := by
  induction' i with i ih
  · decide
  · have : 10^(i+1) = 10 * 10^i := by ring
    omega

lemma sumD_pow_ten (i : ℕ) : sumD (10^i) = 1 := by
  induction' i with i ih
  · rw [pow_zero, sumD_pos 1 (by decide), sumD_zero]
  · have h1 : 10^(i+1) = 10 * 10^i := by ring
    have h2 : 10^(i+1) ≠ 0 := by
      have := pow_ten_pos (i+1)
      omega
    rw [sumD_pos _ h2]
    have Hmod : 10^(i+1) % 10 = 0 := by
      rw [h1]
      generalize 10^i = T
      omega
    have Hdiv : 10^(i+1) / 10 = 10^i := by
      rw [h1]
      generalize 10^i = T
      omega
    rw [Hmod, Hdiv, ih]

lemma sumD_add_one (X : ℕ) : sumD (X + 1) ≤ sumD X + 1 := by
  induction' X using Nat.strong_induction_on with X ih
  by_cases h : X = 0
  · subst h
    rw [sumD_pos 1 (by decide), sumD_zero]
  · let q := X / 10
    let r := X % 10
    have hX : X = 10 * q + r := (Nat.div_add_mod X 10).symm
    by_cases hr : r = 9
    · have H1 : (X + 1) % 10 = 0 := by omega
      have H2 : (X + 1) / 10 = q + 1 := by omega
      have HX : X ≠ 0 := h
      rw [sumD_pos (X+1) (by omega)]
      rw [sumD_pos X h]
      rw [H1, H2]
      have h_q_lt : q < X := by omega
      have := ih q h_q_lt
      have H3 : X % 10 = r := rfl
      have H4 : X / 10 = q := rfl
      rw [H3, H4, hr]
      omega
    · have H1 : (X + 1) % 10 = r + 1 := by omega
      have H2 : (X + 1) / 10 = q := by omega
      have HX : X ≠ 0 := h
      rw [sumD_pos (X+1) (by omega)]
      rw [sumD_pos X h]
      rw [H1, H2]
      have H3 : X % 10 = r := rfl
      have H4 : X / 10 = q := rfl
      rw [H3, H4]
      omega

lemma sumD_add_pow_ten (X i : ℕ) : sumD (X + 10^i) ≤ sumD X + 1 := by
  induction' X using Nat.strong_induction_on with X ih generalizing i
  cases i with
  | zero =>
    have : 10^0 = 1 := rfl
    rw [this]
    exact sumD_add_one X
  | succ i =>
    have h1 : 10^(i+1) = 10 * 10^i := by ring
    have hX_add : X + 10^(i+1) ≠ 0 := by
      have := pow_ten_pos (i+1)
      omega
    have Hmod : (X + 10^(i+1)) % 10 = X % 10 := by
      rw [h1]
      generalize 10^i = T
      omega
    have Hdiv : (X + 10^(i+1)) / 10 = X / 10 + 10^i := by
      rw [h1]
      generalize 10^i = T
      omega
    rw [sumD_pos _ hX_add]
    rw [Hmod, Hdiv]
    by_cases hX : X = 0
    · subst hX
      rw [sumD_zero]
      have : 0 / 10 = 0 := by decide
      rw [this, zero_add, sumD_pow_ten]
    · rw [sumD_pos X hX]
      have := ih (X / 10) (by omega) i
      omega

lemma sumD_add_mul_pow_ten (X c i : ℕ) : sumD (X + c * 10^i) ≤ sumD X + c := by
  induction' c with c ih
  · simp
  · have H : X + (c + 1) * 10^i = (X + c * 10^i) + 10^i := by ring
    rw [H]
    have h2 := sumD_add_pow_ten (X + c * 10^i) i
    omega

def V_list (l : List ℕ) (k pos : ℕ) : ℕ :=
  match l with
  | [] => 0
  | d :: t => d * 10^(pos % k) + V_list t k (pos + 1)

lemma sumD_V_list (l : List ℕ) (k pos : ℕ) : sumD (V_list l k pos) ≤ l.sum := by
  induction' l with d t ih generalizing pos
  · simp [V_list, sumD_zero]
  · simp [V_list]
    rw [add_comm]
    have := sumD_add_mul_pow_ten (V_list t k (pos + 1)) d (pos % k)
    have ih' := ih (pos + 1)
    omega

lemma V_list_le (l : List ℕ) (k pos : ℕ) (hk : k > 0) (hl : ∀ x ∈ l, x < 10) :
  V_list l k pos ≤ l.sum * 10^(k - 1) := by
  induction' l with d t ih generalizing pos
  · simp [V_list]
  · simp [V_list]
    have hd : d * 10^(pos % k) ≤ d * 10^(k - 1) := by
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_right (by decide)
      apply Nat.le_pred_of_lt (Nat.mod_lt _ hk)
    have ht : V_list t k (pos + 1) ≤ t.sum * 10^(k - 1) := ih (pos + 1) (fun x hx => hl x (List.mem_cons_of_mem _ hx))
    have H : (d + t.sum) * 10^(k - 1) = d * 10^(k - 1) + t.sum * 10^(k - 1) := by ring
    rw [H]
    omega

lemma pow_modEq (pos k : ℕ) (hk : k > 0) : 10^(pos % k) ≡ 10^pos [MOD 10^k - 1] := by
  let q := pos / k
  let r := pos % k
  have hpos : pos = k * q + r := (Nat.div_add_mod pos k).symm
  have h1 : 10^k ≡ 1 [MOD 10^k - 1] := by
    change 10^k % (10^k - 1) = 1 % (10^k - 1)
    have e1 : 10^k % (10^k - 1) = (1 + (10^k - 1)) % (10^k - 1) := by
      have h : 10^k = 1 + (10^k - 1) := by
        have := pow_ten_pos k
        omega
      nth_rw 1 [h]
    rw [e1]
    exact Nat.add_mod_right 1 (10^k - 1)
  have h2 : (10^k)^q ≡ 1^q [MOD 10^k - 1] := Nat.ModEq.pow q h1
  have h3 : (10^k)^q * 10^r ≡ 1^q * 10^r [MOD 10^k - 1] := Nat.ModEq.mul h2 rfl
  have h4 : 10^(k * q) * 10^r ≡ 10^r [MOD 10^k - 1] := by
    have e1 : (10^k)^q = 10^(k * q) := by rw [←pow_mul]
    have e2 : 1^q * 10^r = 10^r := by simp
    rw [e1] at h3
    rw [e2] at h3
    exact h3
  have h5 : 10^(k * q + r) ≡ 10^r [MOD 10^k - 1] := by
    have e3 : 10^(k * q + r) = 10^(k * q) * 10^r := by rw [pow_add]
    rw [e3]
    exact h4
  have h6 : 10^pos ≡ 10^r [MOD 10^k - 1] := by
    rw [hpos]
    exact h5
  exact h6.symm

lemma V_list_modEq (l : List ℕ) (k pos : ℕ) (hk : k > 0) :
  V_list l k pos ≡ Nat.ofDigits 10 l * 10^pos [MOD 10^k - 1] := by
  induction' l with d t ih generalizing pos
  · simp [V_list]
    rfl
  · simp [V_list, Nat.ofDigits]
    have h1 : (d + 10 * Nat.ofDigits 10 t) * 10^pos = d * 10^pos + Nat.ofDigits 10 t * 10^(pos + 1) := by
      have e : 10^(pos + 1) = 10 * 10^pos := by ring
      rw [e]
      ring
    rw [h1]
    have hp := pow_modEq pos k hk
    have hd : d * 10^(pos % k) ≡ d * 10^pos [MOD 10^k - 1] := Nat.ModEq.mul rfl hp
    have ht := ih (pos + 1)
    exact Nat.ModEq.add hd ht

lemma sumD_append (U L k : ℕ) (hL : L < 10^k) : sumD (U * 10^k + L) = sumD U + sumD L := by
  induction' k with k ih generalizing U L
  · have : L = 0 := by omega
    subst this
    simp [sumD_zero]
  · have hL10 : L % 10 < 10 := Nat.mod_lt _ (by decide)
    have eq1 : 10^(k+1) = 10 * 10^k := by ring
    have h_split : U * 10^(k+1) + L = 10 * (U * 10^k) + L := by rw [eq1]; ring
    by_cases h : U * 10^(k+1) + L = 0
    · have hU : U = 0 := by
        have h_mul : U * 10^(k+1) = 0 := by omega
        cases U with
        | zero => rfl
        | succ n =>
          have hM : 10^(k+1) > 0 := pow_ten_pos (k+1)
          generalize 10^(k+1) = M at h_mul hM
          have : (n + 1) * M ≥ 1 := by nlinarith
          omega
      have hL0 : L = 0 := by omega
      subst hU hL0
      simp [sumD_zero]
    · rw [sumD_pos _ h]
      have Hmod : (U * 10^(k+1) + L) % 10 = L % 10 := by
        rw [h_split]
        generalize U * 10^k = A
        omega
      have Hdiv : (U * 10^(k+1) + L) / 10 = U * 10^k + L / 10 := by
        rw [h_split]
        generalize U * 10^k = A
        omega
      rw [Hmod, Hdiv]
      have hL_div : L / 10 < 10^k := by
        have e : 10^(k+1) = 10^k * 10 := by ring
        rw [e] at hL
        omega
      rw [ih U (L / 10) hL_div]
      by_cases hL0 : L = 0
      · subst hL0
        have : 0 / 10 = 0 := by decide
        rw [this, sumD_zero]
        omega
      · rw [sumD_pos L hL0]
        omega

lemma sumD_comp (X k : ℕ) (hX : X < 10^k) : sumD X + sumD (10^k - 1 - X) = 9 * k := by
  induction' k with k ih generalizing X
  · have : X = 0 := by omega
    rw [this, sumD_zero]
    have : 10^0 - 1 - 0 = 0 := rfl
    rw [this, sumD_zero]
  · let d := X / 10^k
    let Y := X % 10^k
    have Hdiv : X = d * 10^k + Y := by
      have e : 10^k * d = d * 10^k := mul_comm _ _
      have H : X = 10^k * d + Y := (Nat.div_add_mod X (10^k)).symm
      rw [e] at H
      exact H
    have hY : Y < 10^k := Nat.mod_lt _ (pow_ten_pos k)
    have hd : d < 10 := by
      have e1 : X < 10 * 10^k := by
        have e : 10 * 10^k = 10^(k+1) := by ring
        rw [e]; exact hX
      have e2 : X = d * 10^k + Y := Hdiv
      have e3 : 10^k > 0 := pow_ten_pos k
      nlinarith
    clear_value d Y
    have e1 : 10^(k+1) - 1 - X = (9 - d) * 10^k + (10^k - 1 - Y) := by
      have e : 10^(k+1) = 10 * 10^k := by ring
      rw [e, Hdiv, Nat.sub_mul]
      have hdT : d * 10^k ≤ 9 * 10^k := by
        apply Nat.mul_le_mul_right
        omega
      generalize d * 10^k = D at hdT ⊢
      have e3 : 10^k > 0 := pow_ten_pos k
      generalize 10^k = T at hY e3 hdT ⊢
      omega
    rw [e1, Hdiv]
    have hT_Y : 10^k - 1 - Y < 10^k := by
      have := pow_ten_pos k
      omega
    rw [sumD_append d Y k hY]
    rw [sumD_append (9 - d) (10^k - 1 - Y) k hT_Y]
    have ih_val := ih Y hY
    have hd_sum : sumD d = d := sumD_lt_10 d hd
    have h9d_sum : sumD (9 - d) = 9 - d := sumD_lt_10 (9 - d) (by omega)
    rw [hd_sum, h9d_sum]
    omega
