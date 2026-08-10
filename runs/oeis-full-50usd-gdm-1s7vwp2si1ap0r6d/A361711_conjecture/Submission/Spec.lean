import FormalConjectures.Util.ProblemImports

open Nat Int Finset BigOperators
theorem sum_range_sq (n : ℕ) : (∑ i ∈ Finset.range n, (i : ℤ) ^ 2) * 6 = ((n : ℤ) - 1) * n * (2 * n - 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    push_cast
    rw [add_mul, ih]
    ring

theorem sum_range_id_int (n : ℕ) : (∑ i ∈ Finset.range n, (i : ℤ)) * 2 = ((n : ℤ) - 1) * n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    push_cast
    rw [add_mul, ih]
    ring

theorem choose_p_minus_one (p k : ℕ) (hp : Nat.Prime p) (hk : k < p) :
    (((p - 1).choose k : ℕ) : ZMod p) = (-1) ^ k := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  induction k with
  | zero => simp
  | succ m ih =>
    have hm : m < p - 1 := by omega
    have h_rec := Nat.choose_succ_right_eq (p - 1) m
    have h_cast : (((p - 1).choose (m + 1) * (m + 1) : ℕ) : ZMod p) = (((p - 1).choose m * (p - 1 - m) : ℕ) : ZMod p) := by
      rw [h_rec]
    push_cast at h_cast
    have h_sub : (((p - 1 - m : ℕ) : ZMod p)) = - (m + 1 : ZMod p) := by
      have h_eq_nat : p - 1 - m + (m + 1) = p := by omega
      have h_eq_cast : (((p - 1 - m + (m + 1) : ℕ) : ZMod p)) = (p : ZMod p) := by rw [h_eq_nat]
      push_cast at h_eq_cast
      have hp_eq : (p : ZMod p) = 0 := by simp
      rw [hp_eq] at h_eq_cast
      linear_combination h_eq_cast
    rw [h_sub] at h_cast
    have h_ih_cast : (((p - 1).choose m : ℕ) : ZMod p) = (-1) ^ m := ih (by omega)
    rw [h_ih_cast] at h_cast
    have h_nz : (m + 1 : ZMod p) ≠ 0 := by
      intro hc
      have hc' : (((m + 1 : ℕ) : ZMod p)) = 0 := by
        push_cast
        exact hc
      have h_dvd : p ∣ m + 1 := (ZMod.natCast_eq_zero_iff (m + 1) p).1 hc'
      have h_lt : m + 1 < p := by omega
      have h_pos : m + 1 > 0 := by omega
      have h_le := Nat.le_of_dvd h_pos h_dvd
      omega
    have h_cancel : (((p - 1).choose (m + 1) : ℕ) : ZMod p) = - (-1) ^ m := by
      exact mul_right_cancel₀ h_nz (by
        calc (((p - 1).choose (m + 1) : ℕ) : ZMod p) * (m + 1 : ZMod p) = (-1) ^ m * - (m + 1 : ZMod p) := h_cast
        _ = (- (-1) ^ m) * (m + 1 : ZMod p) := by ring
      )
    rw [h_cancel]
    ring

theorem choose_p_minus_two (p k : ℕ) (hp : Nat.Prime p) (hk : k < p - 1) :
    (((p - 2).choose k : ℕ) : ZMod p) = (-1) ^ k * (k + 1) := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  induction k with
  | zero => simp
  | succ m ih =>
    have hm : m < p - 2 := by omega
    have h_rec := Nat.choose_succ_succ' (p - 2) m
    have h_p21 : p - 2 + 1 = p - 1 := by omega
    rw [h_p21] at h_rec
    have h_rec' : (p - 2).choose (m + 1) + (p - 2).choose m = (p - 1).choose (m + 1) := by
      rw [add_comm]
      exact h_rec.symm
    have h_cast : (((p - 2).choose (m + 1) + (p - 2).choose m : ℕ) : ZMod p) = (((p - 1).choose (m + 1) : ℕ) : ZMod p) := by
      rw [h_rec']
    push_cast at h_cast
    have h_minus_one : (((p - 1).choose (m + 1) : ℕ) : ZMod p) = (-1) ^ (m + 1) := choose_p_minus_one p (m + 1) hp (by omega)
    rw [h_minus_one] at h_cast
    have h_ih_cast : (((p - 2).choose m : ℕ) : ZMod p) = (-1) ^ m * (m + 1) := ih (by omega)
    rw [h_ih_cast] at h_cast
    have h_solve : (((p - 2).choose (m + 1) : ℕ) : ZMod p) = (-1) ^ (m + 1) * (m + 1 + 1) := by
      linear_combination h_cast
    rw [h_solve]
    push_cast
    rfl

theorem choose_div_succ (p k : ℕ) (hp : Nat.Prime p) (hk : k < p - 1) :
    (p.choose (k + 1) / p) * (k + 1) = (p - 1).choose k := by
  have h_p_pos : p > 0 := hp.pos
  have h_sub : p - 1 + 1 = p := Nat.sub_add_cancel h_p_pos
  have h_rec := Nat.add_one_mul_choose_eq (p - 1) k
  rw [h_sub] at h_rec
  have hdvd : p ∣ p.choose (k + 1) := by
    apply Nat.Prime.dvd_choose_self hp
    · omega
    · omega
  have h_div_mul : (p * (p.choose (k + 1) / p)) * (k + 1) = p.choose (k + 1) * (k + 1) := by
    rw [Nat.mul_div_cancel' hdvd]
  rw [mul_assoc] at h_div_mul
  have h_eq : p * ((p.choose (k + 1) / p) * (k + 1)) = p * (p - 1).choose k := by
    rw [h_div_mul, h_rec]
  exact Nat.eq_of_mul_eq_mul_left h_p_pos h_eq

theorem neg_one_pow_mul_self {R : Type*} [CommRing R] (k : ℕ) : (-1 : R) ^ k * (-1 : R) ^ k = 1 := by
  rw [← mul_pow]
  have h : (-1 : R) * -1 = 1 := by ring
  rw [h, one_pow]

theorem term_simplify (p k : ℕ) (hp : Nat.Prime p) (hk : k < p - 2) :
    (-1 : ZMod p) ^ (k + 1) * (((p.choose (k + 1) / p : ℕ) : ZMod p) ^ 2 * ((p - 2).choose (k + 1) : ZMod p)) =
    ((k + 1 : ZMod p)⁻¹) ^ 2 * (k + 2) := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hk_lt : k < p - 1 := by omega
  have h_div := choose_div_succ p k hp hk_lt
  have h_div_cast : (((p.choose (k + 1) / p) * (k + 1) : ℕ) : ZMod p) = (((p - 1).choose k : ℕ) : ZMod p) := by
    rw [h_div]
  push_cast at h_div_cast
  have h_p1 := choose_p_minus_one p k hp (by omega)
  rw [h_p1] at h_div_cast
  have hk_nz : (k + 1 : ZMod p) ≠ 0 := by
    intro hc
    have hc' : (((k + 1 : ℕ) : ZMod p)) = 0 := by
      push_cast
      exact hc
    have h_dvd : p ∣ k + 1 := (ZMod.natCast_eq_zero_iff (k + 1) p).1 hc'
    have h_lt : k + 1 < p := by omega
    have h_pos : k + 1 > 0 := by omega
    have h_le := Nat.le_of_dvd h_pos h_dvd
    omega
  have h_div_eq : ((p.choose (k + 1) / p : ℕ) : ZMod p) = (-1)^k * (k + 1 : ZMod p)⁻¹ := by
    rw [← h_div_cast, mul_assoc, mul_inv_cancel₀ hk_nz, mul_one]
  rw [h_div_eq]
  have h_p2 := choose_p_minus_two p (k + 1) hp (by omega)
  rw [h_p2]
  have h_sq : ((-1 : ZMod p) ^ k * (k + 1 : ZMod p)⁻¹) ^ 2 = ((k + 1 : ZMod p)⁻¹) ^ 2 := by
    calc ((-1 : ZMod p) ^ k * (k + 1 : ZMod p)⁻¹) ^ 2 = ((-1 : ZMod p) ^ k) ^ 2 * ((k + 1 : ZMod p)⁻¹) ^ 2 := mul_pow _ _ _
    _ = ((-1 : ZMod p) ^ k * (-1 : ZMod p) ^ k) * ((k + 1 : ZMod p)⁻¹) ^ 2 := by ring
    _ = 1 * ((k + 1 : ZMod p)⁻¹) ^ 2 := by rw [neg_one_pow_mul_self]
    _ = ((k + 1 : ZMod p)⁻¹) ^ 2 := by ring
  rw [h_sq]
  have h_neg_one_sq : (-1 : ZMod p) ^ (k + 1) * (-1 : ZMod p) ^ (k + 1) = 1 := neg_one_pow_mul_self (k + 1)
  calc (-1 : ZMod p) ^ (k + 1) * (((k + 1 : ZMod p)⁻¹) ^ 2 * ((-1 : ZMod p) ^ (k + 1) * (↑(k + 1) + 1))) =
       ((-1 : ZMod p) ^ (k + 1) * (-1 : ZMod p) ^ (k + 1)) * (((k + 1 : ZMod p)⁻¹) ^ 2 * (↑(k + 1) + 1)) := by ring
  _ = 1 * (((k + 1 : ZMod p)⁻¹) ^ 2 * (↑(k + 1) + 1)) := by rw [h_neg_one_sq]
  _ = ((k + 1 : ZMod p)⁻¹) ^ 2 * (k + 2) := by push_cast; ring

theorem term_rewrite_inv (p k : ℕ) (hp : Nat.Prime p) (hk : k < p - 2) :
    ((k + 1 : ZMod p)⁻¹) ^ 2 * (k + 2) = (k + 1 : ZMod p)⁻¹ + ((k + 1 : ZMod p)⁻¹) ^ 2 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hk_nz : (k + 1 : ZMod p) ≠ 0 := by
    intro hc
    have hc' : (((k + 1 : ℕ) : ZMod p)) = 0 := by
      push_cast
      exact hc
    have h_dvd : p ∣ k + 1 := (ZMod.natCast_eq_zero_iff (k + 1) p).1 hc'
    have h_lt : k + 1 < p := by omega
    have h_pos : k + 1 > 0 := by omega
    have h_le := Nat.le_of_dvd h_pos h_dvd
    omega
  have h_eq : (k + 2 : ZMod p) = (k + 1 : ZMod p) + 1 := by ring
  rw [h_eq]
  calc ((k + 1 : ZMod p)⁻¹) ^ 2 * ((k + 1 : ZMod p) + 1) = ((k + 1 : ZMod p)⁻¹) ^ 2 * (k + 1 : ZMod p) + ((k + 1 : ZMod p)⁻¹) ^ 2 * 1 := mul_add _ _ _
  _ = (k + 1 : ZMod p)⁻¹ * ((k + 1 : ZMod p)⁻¹ * (k + 1)) + ((k + 1 : ZMod p)⁻¹) ^ 2 * 1 := by ring
  _ = (k + 1 : ZMod p)⁻¹ * 1 + ((k + 1 : ZMod p)⁻¹) ^ 2 * 1 := by rw [inv_mul_cancel₀ hk_nz]
  _ = (k + 1 : ZMod p)⁻¹ + ((k + 1 : ZMod p)⁻¹) ^ 2 := by ring

theorem sum_inv_eq_sum_self (p : ℕ) (hp : Nat.Prime p) (h_geq_5 : 5 ≤ p) (g : ZMod p → ZMod p) :
    ∑ k ∈ Finset.range (p - 2), g (k + 1 : ZMod p)⁻¹ = ∑ k ∈ Finset.range (p - 2), g (k + 1 : ZMod p) := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have h_p_gt : p > 2 := by omega
  have h_p2_lt_p : p - 2 < p := by omega
  let i : (k : ℕ) → k ∈ Finset.range (p - 2) → ℕ := fun k hk =>
    let v := ((k + 1 : ZMod p)⁻¹).val
    v - 1
  apply Finset.sum_bij i
  · intro k hk
    rw [Finset.mem_range] at hk
    rw [Finset.mem_range]
    dsimp [i]
    let x : ZMod p := (k + 1 : ZMod p)
    have hx_nz : x ≠ 0 := by
      intro hc
      have hc' : (((k + 1 : ℕ) : ZMod p)) = 0 := by
        push_cast
        exact hc
      have h_dvd : p ∣ k + 1 := (ZMod.natCast_eq_zero_iff (k + 1) p).1 hc'
      have h_lt : k + 1 < p := by omega
      have h_pos : k + 1 > 0 := by omega
      have h_le := Nat.le_of_dvd h_pos h_dvd
      omega
    have h_inv_nz : x⁻¹ ≠ 0 := inv_ne_zero hx_nz
    have h_val_nz : (x⁻¹).val ≠ 0 := by
      intro hc
      have hc' : (x⁻¹) = 0 := by
        rw [← ZMod.natCast_zmod_val x⁻¹, hc]
        push_cast; rfl
      exact h_inv_nz hc'
    have h_val_lt : (x⁻¹).val < p := ZMod.val_lt (x⁻¹)
    have h_val_pos : (x⁻¹).val > 0 := by omega
    have h_val_ne_p1 : (x⁻¹).val ≠ p - 1 := by
      intro hc
      have hp_eq : (p : ZMod p) = 0 := ZMod.natCast_self p
      have h_sub : (((p - 1 : ℕ) : ZMod p)) = -1 := by
        have h_eq_nat : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
        have h_eq_cast : (((p - 1 + 1 : ℕ) : ZMod p)) = (p : ZMod p) := by rw [h_eq_nat]
        push_cast at h_eq_cast
        rw [hp_eq] at h_eq_cast
        linear_combination h_eq_cast
      have hc' : x⁻¹ = -1 := by
        rw [← ZMod.natCast_zmod_val x⁻¹, hc]
        exact h_sub
      have hc'' : x = -1 := by
        have h_inv_inv : (x⁻¹)⁻¹ = (-1 : ZMod p)⁻¹ := congr_arg (·⁻¹) hc'
        rw [inv_inv] at h_inv_inv
        have h_neg_one_inv : (-1 : ZMod p)⁻¹ = -1 := by
          apply inv_eq_of_mul_eq_one_right
          ring
        rw [h_neg_one_inv] at h_inv_inv
        exact h_inv_inv
      have h_x_cast : (((k + 1 : ℕ) : ZMod p)) = x := by push_cast; rfl
      have hc''' : ((k + 1 : ℕ) : ZMod p) = ((p - 1 : ℕ) : ZMod p) := by
        rw [h_x_cast, hc'', h_sub]
      have h_eq_nat : k + 1 = p - 1 := by
        have h_val_eq := congr_arg ZMod.val hc'''
        rw [ZMod.val_cast_of_lt (show k + 1 < p by omega), ZMod.val_cast_of_lt (show p - 1 < p by omega)] at h_val_eq
        exact h_val_eq
      have h_lt_p1 : k + 1 < p - 1 := by omega
      rw [h_eq_nat] at h_lt_p1
      exact lt_irrefl (p - 1) h_lt_p1
    change (x⁻¹).val - 1 < p - 2
    omega
  · intro k1 hk1 k2 hk2 h_eq
    rw [Finset.mem_range] at hk1 hk2
    dsimp [i] at h_eq
    let x1 : ZMod p := (k1 + 1 : ZMod p)
    let x2 : ZMod p := (k2 + 1 : ZMod p)
    have hx1_nz : x1 ≠ 0 := by
      intro hc
      have hc' : (((k1 + 1 : ℕ) : ZMod p)) = 0 := by
        push_cast
        exact hc
      have h_dvd : p ∣ k1 + 1 := (ZMod.natCast_eq_zero_iff (k1 + 1) p).1 hc'
      have h_lt : k1 + 1 < p := by omega
      have h_pos : k1 + 1 > 0 := by omega
      have h_le := Nat.le_of_dvd h_pos h_dvd
      omega
    have hx2_nz : x2 ≠ 0 := by
      intro hc
      have hc' : (((k2 + 1 : ℕ) : ZMod p)) = 0 := by
        push_cast
        exact hc
      have h_dvd : p ∣ k2 + 1 := (ZMod.natCast_eq_zero_iff (k2 + 1) p).1 hc'
      have h_lt : k2 + 1 < p := by omega
      have h_pos : k2 + 1 > 0 := by omega
      have h_le := Nat.le_of_dvd h_pos h_dvd
      omega
    have h_val1_pos : (x1⁻¹).val > 0 := by
      have h_inv_nz : x1⁻¹ ≠ 0 := inv_ne_zero hx1_nz
      have hc : (x1⁻¹).val ≠ 0 := by
        intro hc
        have hc' : (x1⁻¹) = 0 := by
          rw [← ZMod.natCast_zmod_val x1⁻¹, hc]
          push_cast; rfl
        exact h_inv_nz hc'
      omega
    have h_val2_pos : (x2⁻¹).val > 0 := by
      have h_inv_nz : x2⁻¹ ≠ 0 := inv_ne_zero hx2_nz
      have hc : (x2⁻¹).val ≠ 0 := by
        intro hc
        have hc' : (x2⁻¹) = 0 := by
          rw [← ZMod.natCast_zmod_val x2⁻¹, hc]
          push_cast; rfl
        exact h_inv_nz hc'
      omega
    have h_val_eq : (x1⁻¹).val = (x2⁻¹).val := by
      have h1 : (x1⁻¹).val = ((k1 + 1 : ZMod p)⁻¹).val := rfl
      have h2 : (x2⁻¹).val = ((k2 + 1 : ZMod p)⁻¹).val := rfl
      omega
    have h_inv_eq : x1⁻¹ = x2⁻¹ := by
      rw [← ZMod.natCast_zmod_val x1⁻¹, ← ZMod.natCast_zmod_val x2⁻¹, h_val_eq]
    have h_x_eq : x1 = x2 := by
      have h_inv_inv1 : (x1⁻¹)⁻¹ = (x2⁻¹)⁻¹ := by rw [h_inv_eq]
      rw [inv_inv, inv_inv] at h_inv_inv1
      exact h_inv_inv1
    have hk1_cast : (k1 + 1 : ZMod p) = (((k1 + 1 : ℕ) : ZMod p)) := by push_cast; rfl
    have hk2_cast : (k2 + 1 : ZMod p) = (((k2 + 1 : ℕ) : ZMod p)) := by push_cast; rfl
    have h_val_k_eq : (k1 + 1 : ZMod p).val = (k2 + 1 : ZMod p).val := congr_arg ZMod.val h_x_eq
    rw [hk1_cast, hk2_cast] at h_val_k_eq
    rw [ZMod.val_cast_of_lt (show k1 + 1 < p by omega), ZMod.val_cast_of_lt (show k2 + 1 < p by omega)] at h_val_k_eq
    omega
  · intro j hj
    rw [Finset.mem_range] at hj
    let y : ZMod p := (j + 1 : ZMod p)
    let k := (y⁻¹).val - 1
    have hy_nz : y ≠ 0 := by
      intro hc
      have hc' : (((j + 1 : ℕ) : ZMod p)) = 0 := by
        push_cast
        exact hc
      have h_dvd : p ∣ j + 1 := (ZMod.natCast_eq_zero_iff (j + 1) p).1 hc'
      have h_lt : j + 1 < p := by omega
      have h_pos : j + 1 > 0 := by omega
      have h_le := Nat.le_of_dvd h_pos h_dvd
      omega
    have h_yinv_nz : y⁻¹ ≠ 0 := inv_ne_zero hy_nz
    have h_yinv_val_nz : (y⁻¹).val ≠ 0 := by
      intro hc
      have hc' : y⁻¹ = 0 := by
        rw [← ZMod.natCast_zmod_val y⁻¹, hc]
        push_cast; rfl
      exact h_yinv_nz hc'
    have h_yinv_val_lt : (y⁻¹).val < p := ZMod.val_lt y⁻¹
    have h_yinv_val_pos : (y⁻¹).val > 0 := by omega
    have h_yinv_val_ne_p1 : (y⁻¹).val ≠ p - 1 := by
      intro hc
      have hp_eq : (p : ZMod p) = 0 := ZMod.natCast_self p
      have h_sub : (((p - 1 : ℕ) : ZMod p)) = -1 := by
        have h_eq_nat : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
        have h_eq_cast : (((p - 1 + 1 : ℕ) : ZMod p)) = (p : ZMod p) := by rw [h_eq_nat]
        push_cast at h_eq_cast
        rw [hp_eq] at h_eq_cast
        linear_combination h_eq_cast
      have hc' : y⁻¹ = -1 := by
        rw [← ZMod.natCast_zmod_val y⁻¹, hc]
        exact h_sub
      have hc'' : y = -1 := by
        have h_inv_inv : (y⁻¹)⁻¹ = (-1 : ZMod p)⁻¹ := congr_arg (·⁻¹) hc'
        rw [inv_inv] at h_inv_inv
        have h_neg_one_inv : (-1 : ZMod p)⁻¹ = -1 := by
          apply inv_eq_of_mul_eq_one_right
          ring
        rw [h_neg_one_inv] at h_inv_inv
        exact h_inv_inv
      have h_y_cast : (((j + 1 : ℕ) : ZMod p)) = y := by push_cast; rfl
      have hc''' : ((j + 1 : ℕ) : ZMod p) = ((p - 1 : ℕ) : ZMod p) := by
        rw [h_y_cast, hc'', h_sub]
      have h_eq_nat : j + 1 = p - 1 := by
        have h_val_eq := congr_arg ZMod.val hc'''
        rw [ZMod.val_cast_of_lt (show j + 1 < p by omega), ZMod.val_cast_of_lt (show p - 1 < p by omega)] at h_val_eq
        exact h_val_eq
      have h_lt_p1 : j + 1 < p - 1 := by omega
      rw [h_eq_nat] at h_lt_p1
      exact lt_irrefl (p - 1) h_lt_p1
    have hk_lt : k < p - 2 := by omega
    use k
    have hk_mem : k ∈ Finset.range (p - 2) := by
      rw [Finset.mem_range]
      exact hk_lt
    use hk_mem
    dsimp [i]
    have hk_eq : k + 1 = (y⁻¹).val := by omega
    have hk_cast : (k + 1 : ZMod p) = y⁻¹ := by
      have h_eq_cast : (k + 1 : ZMod p) = (((k + 1 : ℕ) : ZMod p)) := by push_cast; rfl
      rw [h_eq_cast, hk_eq, ZMod.natCast_zmod_val]
    have h_inv : (k + 1 : ZMod p)⁻¹ = y := by
      rw [hk_cast, inv_inv]
    have h_val : ((k + 1 : ZMod p)⁻¹).val = y.val := congr_arg ZMod.val h_inv
    have h_y_cast2 : y = (((j + 1 : ℕ) : ZMod p)) := by push_cast; rfl
    have hy_val : y.val = j + 1 := by
      rw [h_y_cast2]
      exact ZMod.val_cast_of_lt (show j + 1 < p by omega)
    omega
  · intro k hk
    rw [Finset.mem_range] at hk
    dsimp [i]
    let x : ZMod p := (k + 1 : ZMod p)
    have hx_nz : x ≠ 0 := by
      intro hc
      have hc' : (((k + 1 : ℕ) : ZMod p)) = 0 := by
        push_cast
        exact hc
      have h_dvd : p ∣ k + 1 := (ZMod.natCast_eq_zero_iff (k + 1) p).1 hc'
      have h_lt : k + 1 < p := by omega
      have h_pos : k + 1 > 0 := by omega
      have h_le := Nat.le_of_dvd h_pos h_dvd
      omega
    have h_inv_nz : x⁻¹ ≠ 0 := inv_ne_zero hx_nz
    have h_val_nz : (x⁻¹).val ≠ 0 := by
      intro hc
      have hc' : (x⁻¹) = 0 := by
        rw [← ZMod.natCast_zmod_val x⁻¹, hc]
        push_cast; rfl
      exact h_inv_nz hc'
    have h_val_lt : (x⁻¹).val < p := ZMod.val_lt (x⁻¹)
    have h_val_pos : (x⁻¹).val > 0 := by omega
    have h_sub_add : (x⁻¹).val - 1 + 1 = (x⁻¹).val := Nat.sub_add_cancel h_val_pos
    have h_cast : (((x⁻¹).val - 1 + 1 : ℕ) : ZMod p) = x⁻¹ := by
      rw [h_sub_add, ZMod.natCast_zmod_val]
    push_cast at h_cast
    rw [h_cast]

theorem sum_zmod_zero (p : ℕ) (hp : Nat.Prime p) (h_geq_5 : 5 ≤ p) :
    (∑ k ∈ Finset.range (p - 2), (-1 : ZMod p) ^ (k + 1) * (((p.choose (k + 1) / p : ℕ) : ZMod p) ^ 2 * ((p - 2).choose (k + 1) : ZMod p))) = 0 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hp1_eq : (((p - 1 : ℕ) : ZMod p)) = -1 := by
    have hp_eq : (p : ZMod p) = 0 := ZMod.natCast_self p
    have h_eq_nat : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
    have h_eq_cast : (((p - 1 + 1 : ℕ) : ZMod p)) = (p : ZMod p) := by rw [h_eq_nat]
    push_cast at h_eq_cast
    rw [hp_eq] at h_eq_cast
    linear_combination h_eq_cast
  have h_sum : (∑ k ∈ Finset.range (p - 2), (-1 : ZMod p) ^ (k + 1) * (((p.choose (k + 1) / p : ℕ) : ZMod p) ^ 2 * ((p - 2).choose (k + 1) : ZMod p))) =
      ∑ k ∈ Finset.range (p - 2), ((k + 1 : ZMod p)⁻¹ + ((k + 1 : ZMod p)⁻¹) ^ 2) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    rw [term_simplify p k hp hk, term_rewrite_inv p k hp hk]
  rw [h_sum]
  rw [Finset.sum_add_distrib]
  have h_sum_inv : (∑ k ∈ Finset.range (p - 2), (k + 1 : ZMod p)⁻¹) = 1 := by
    rw [sum_inv_eq_sum_self p hp h_geq_5 (fun x => x)]
    have h_shift : (∑ k ∈ Finset.range (p - 2), (k + 1 : ZMod p)) = ∑ i ∈ Finset.range (p - 1), (i : ZMod p) := by
      have hp1 : p - 1 = p - 2 + 1 := by omega
      rw [hp1, Finset.sum_range_succ']
      push_cast
      simp
    rw [h_shift]
    have h_id := sum_range_id_int (p - 1)
    have h_cast := congr_arg (fun x : ℤ => (x : ZMod p)) h_id
    push_cast at h_cast
    rw [hp1_eq] at h_cast
    have h_rhs_eq : (-1 - 1 : ZMod p) * -1 = 2 := by ring
    rw [h_rhs_eq] at h_cast
    have h_two_nz : (2 : ZMod p) ≠ 0 := by
      intro hc
      have h_dvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 hc
      have h_le := Nat.le_of_dvd (by decide) h_dvd
      omega
    exact mul_right_cancel₀ h_two_nz (by
      calc (∑ i ∈ Finset.range (p - 1), (i : ZMod p)) * 2 = 2 := h_cast
      _ = 1 * 2 := by ring
    )
  have h_sum_inv_sq : (∑ k ∈ Finset.range (p - 2), ((k + 1 : ZMod p)⁻¹) ^ 2) = -1 := by
    rw [sum_inv_eq_sum_self p hp h_geq_5 (fun x => x ^ 2)]
    have h_shift : (∑ k ∈ Finset.range (p - 2), (k + 1 : ZMod p) ^ 2) = ∑ i ∈ Finset.range (p - 1), (i : ZMod p) ^ 2 := by
      have hp1 : p - 1 = p - 2 + 1 := by omega
      rw [hp1, Finset.sum_range_succ']
      push_cast
      simp
    rw [h_shift]
    have h_sq := sum_range_sq (p - 1)
    have h_cast := congr_arg (fun x : ℤ => (x : ZMod p)) h_sq
    push_cast at h_cast
    rw [hp1_eq] at h_cast
    have h_rhs_eq : (-1 - 1 : ZMod p) * -1 * (2 * -1 - 1) = -6 := by ring
    rw [h_rhs_eq] at h_cast
    have h_six_nz : (6 : ZMod p) ≠ 0 := by
      intro hc
      have h_dvd : p ∣ 6 := (ZMod.natCast_eq_zero_iff 6 p).1 hc
      have h_dvd_mul : p ∣ 2 * 3 := by
        have h_six : 6 = 2 * 3 := rfl
        rw [← h_six]
        exact h_dvd
      have h_or : p ∣ 2 ∨ p ∣ 3 := (Nat.Prime.dvd_mul hp).1 h_dvd_mul
      rcases h_or with hp2 | hp3
      · have : p ≤ 2 := Nat.le_of_dvd (by decide) hp2
        omega
      · have : p ≤ 3 := Nat.le_of_dvd (by decide) hp3
        omega
    exact mul_right_cancel₀ h_six_nz (by
      calc (∑ i ∈ Finset.range (p - 1), (i : ZMod p) ^ 2) * 6 = -6 := h_cast
      _ = -1 * 6 := by ring
    )
  rw [h_sum_inv, h_sum_inv_sq]
  ring

def A361711 (n : ℕ) : ℤ :=
  match n with
  | 0 => 0
  | 1 => 1
  | n_ge_2 =>
    let N := n_ge_2
    let m : ℕ := N - 2
    (Finset.range (m + 1)).sum fun k : ℕ =>
      let term_nat : ℕ := (N.choose k) * (N.choose k) * (m.choose k)
      let sign_k : ℤ := (-1 : ℤ) ^ k
      sign_k * term_nat.cast

theorem A361711_p_modeq_p_cube (p : ℕ) (hp : Nat.Prime p) (h_geq_5 : 5 ≤ p) :
    A361711 p ≡ 1 [ZMOD (p ^ 3)] := by
  rcases p with _ | _ | n
  · omega
  · omega
  unfold A361711
  split
  · -- case 0
    omega
  · -- case 1
    omega
  · -- case n_ge_2
    rw [Finset.sum_range_succ']
    dsimp
    have hn : n + 1 + 1 - 2 = n := by omega
    rw [hn]
    simp only [Nat.choose_zero_right, Nat.cast_one, mul_one]
    let p := n + 2
    have hp_eq : p = n + 1 + 1 := by rfl
    have h_term (k : ℕ) (hk : k < n) : 
        (↑(p.choose (k + 1)) * ↑(p.choose (k + 1)) * ↑(n.choose (k + 1)) : ℤ) = 
        (p : ℤ) ^ 2 * ((p.choose (k + 1) / p : ℕ) : ℤ) ^ 2 * (n.choose (k + 1) : ℤ) := by
      have hk_lt : k + 1 < p := by omega
      have hk_nz : k + 1 ≠ 0 := by omega
      have hdvd : p ∣ p.choose (k + 1) := Nat.Prime.dvd_choose_self hp hk_nz hk_lt
      have h_div : p * (p.choose (k + 1) / p) = p.choose (k + 1) := Nat.mul_div_cancel' hdvd
      have h_div_cast : (p : ℤ) * ((p.choose (k + 1) / p : ℕ) : ℤ) = (p.choose (k + 1) : ℤ) := by
        exact_mod_cast h_div
      rw [← h_div_cast]
      ring
    have h_sum_rewrite : (∑ k ∈ Finset.range n, (-1) ^ (k + 1) * (↑(p.choose (k + 1)) * ↑(p.choose (k + 1)) * ↑(n.choose (k + 1)) : ℤ)) =
        (p : ℤ) ^ 2 * ∑ k ∈ Finset.range n, (-1) ^ (k + 1) * (((p.choose (k + 1) / p : ℕ) : ℤ) ^ 2 * (n.choose (k + 1) : ℤ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      rw [h_term k hk]
      ring
    rw [h_sum_rewrite]
    have h_div_congr (S : ℤ) (hS : (p : ℤ) ∣ S) : (p : ℤ) ^ 2 * S ≡ 0 [ZMOD (p ^ 3 : ℕ)] := by
      rcases hS with ⟨Q, hQ⟩
      rw [hQ]
      have h_pow : (p : ℤ) ^ 2 * ((p : ℤ) * Q) = (p : ℤ) ^ 3 * Q := by ring
      rw [h_pow]
      have hdvd : ((p ^ 3 : ℕ) : ℤ) ∣ (p : ℤ) ^ 3 * Q := by
        simp only [Nat.cast_pow]
        exact dvd_mul_right ((p : ℤ) ^ 3) Q
      exact Dvd.dvd.modEq_zero_int hdvd
    have h_sum_dvd : (p : ℤ) ∣ (∑ k ∈ Finset.range n, (-1) ^ (k + 1) * (((p.choose (k + 1) / p : ℕ) : ℤ) ^ 2 * (n.choose (k + 1) : ℤ))) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      have hn_eq : n = p - 2 := by omega
      rw [hn_eq]
      exact sum_zmod_zero p hp h_geq_5
    have h_goal := h_div_congr (∑ k ∈ Finset.range n, (-1) ^ (k + 1) * (((p.choose (k + 1) / p : ℕ) : ℤ) ^ 2 * (n.choose (k + 1) : ℤ))) h_sum_dvd
    have h_add := Int.ModEq.add_right 1 h_goal
    exact h_add

/--
A361711 Conjecture: the supercongruence a(p^k) == a(p^(k-1)) (mod p^(3*k)) holds for all primes p >= 5 and positive integer k.
-/
theorem A361711_conjecture (p : ℕ) (hp : Nat.Prime p) (h_geq_5 : 5 ≤ p) (k : ℕ) (hk : k > 0) :
    A361711 (p ^ k) ≡ A361711 (p ^ (k - 1)) [ZMOD (p ^ (3 * k) : ℕ)] := by
  rcases k with _ | k
  · omega
  rcases k with _ | k
  · -- Case k = 1
    have hp1 : p ^ (3 * 1) = p ^ 3 := by ring
    have h_a1 : A361711 (p ^ (1 - 1)) = 1 := by
      have : 1 - 1 = 0 := rfl
      rw [this]
      rfl
    have hp1_eq : p ^ (0 + 1) = p := by ring
    have h_mod_cast : ((p ^ 3 : ℕ) : ℤ) = (p : ℤ) ^ 3 := by push_cast; rfl
    rw [hp1_eq, h_a1, h_mod_cast]
    exact A361711_p_modeq_p_cube p hp h_geq_5
  · -- Case k > 1 (k is actually k + 2)
    sorry
#print axioms A361711_p_modeq_p_cube
