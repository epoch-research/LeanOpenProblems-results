import FormalConjectures.Util.ProblemImports
import Mathlib.NumberTheory.Real.GoldenRatio

open Real Int
open scoped Classical

noncomputable def A208326 (n : ℕ) : ℕ :=
  let r : ℝ := 5
  let s : ℝ := goldenRatio
  let t : ℝ := 1 / s
  let n_r : ℝ := n
  let term1_int : ℤ := Int.floor (n_r * r / t)
  let term2_int : ℤ := Int.floor (n_r * s / t)
  let result_int : ℤ := n.cast + term1_int + term2_int
  result_int.toNat

noncomputable def A207672 (n : ℕ) : ℕ :=
  let r : ℝ := 5
  let s : ℝ := goldenRatio
  let t : ℝ := 1 / s
  let n_r : ℝ := n
  let term1_int : ℤ := Int.floor (n_r * s / r)
  let term2_int : ℤ := Int.floor (n_r * t / r)
  let result_int : ℤ := n.cast + term1_int + term2_int
  result_int.toNat

noncomputable def A207673 (n : ℕ) : ℕ :=
  let r : ℝ := 5
  let s : ℝ := goldenRatio
  let t : ℝ := 1 / s
  let n_r : ℝ := n
  let term1_int : ℤ := Int.floor (n_r * r / s)
  let term2_int : ℤ := Int.floor (n_r * t / s)
  let result_int : ℤ := n.cast + term1_int + term2_int
  result_int.toNat



noncomputable def s := goldenRatio
noncomputable def t := 1 / s
noncomputable def F (x : ℝ) : ℤ :=
  Int.floor (x * 5) + Int.floor (x * s) + Int.floor (x * t)

lemma s_pos : (0 : ℝ) < s := goldenRatio_pos
lemma t_pos : (0 : ℝ) < t := div_pos (by norm_num) goldenRatio_pos
lemma irr_s : Irrational s := goldenRatio_irrational

lemma F_lower_bound (x : ℝ) (hx : x ≥ 0) : (x * 5 : ℝ) - 1 < (F x : ℝ) := by
  dsimp [F]
  have h1 : (x * 5 : ℝ) - 1 < (Int.floor (x * 5) : ℝ) := Int.sub_one_lt_floor (x * 5)
  have h2 : 0 ≤ (Int.floor (x * s) : ℝ) := by
    have : 0 ≤ x * s := mul_nonneg hx (le_of_lt s_pos)
    exact_mod_cast Int.floor_nonneg.mpr this
  have h3 : 0 ≤ (Int.floor (x * t) : ℝ) := by
    have : 0 ≤ x * t := mul_nonneg hx (le_of_lt t_pos)
    exact_mod_cast Int.floor_nonneg.mpr this
  push_cast
  linarith

lemma F_zero : F 0 = 0 := by
  dsimp [F]
  norm_num

lemma sSup_prop (A : Set ℝ) (h_nonempty : A.Nonempty) (h_bdd : BddAbove A) :
  let x := sSup A
  (∀ ε > 0, ∃ y ∈ A, y > x - ε) ∧ (∀ ε > 0, x + ε ∉ A) := by
  intro x
  constructor
  · intro ε hε
    have h1 : x - ε < x := sub_lt_self x hε
    have h3 := exists_lt_of_lt_csSup h_nonempty h1
    rcases h3 with ⟨y, hy1, hy2⟩
    exact ⟨y, hy1, hy2⟩
  · intro ε hε
    have h1 : x < x + ε := lt_add_of_pos_right x hε
    intro h2
    have h3 := le_csSup h_bdd h2
    linarith

lemma F_mono {a b : ℝ} (h : a ≤ b) : F a ≤ F b := by
  dsimp [F]
  have h1 : a * 5 ≤ b * 5 := mul_le_mul_of_nonneg_right h (by norm_num)
  have h2 : a * s ≤ b * s := mul_le_mul_of_nonneg_right h (le_of_lt s_pos)
  have h3 : a * t ≤ b * t := mul_le_mul_of_nonneg_right h (le_of_lt t_pos)
  have f1 := Int.floor_mono h1
  have f2 := Int.floor_mono h2
  have f3 := Int.floor_mono h3
  linarith

lemma floor_right_cont (y : ℝ) : 
  ∃ ε > 0, ∀ δ, 0 ≤ δ → δ < ε → Int.floor (y + δ) = Int.floor y := by
  by_cases h : y = ↑(Int.floor y)
  · use (1/2 : ℝ)
    refine ⟨by norm_num, fun δ hδ1 hδ2 => ?_⟩
    apply Int.floor_eq_iff.mpr
    constructor
    · linarith [Int.floor_le y]
    · rw [← h]; linarith
  · have h1 : (Int.floor y : ℝ) < y := lt_of_le_of_ne (Int.floor_le y) (Ne.symm h)
    use (Int.floor y : ℝ) + 1 - y
    have hlt : y < (Int.floor y : ℝ) + 1 := Int.lt_floor_add_one y
    refine ⟨by linarith, fun δ hδ1 hδ2 => ?_⟩
    apply Int.floor_eq_iff.mpr
    constructor
    · linarith
    · linarith

lemma F_right_cont (x : ℝ) : ∃ ε > 0, ∀ δ, 0 ≤ δ → δ < ε → F (x + δ) = F x := by
  rcases floor_right_cont (x * 5) with ⟨ε1, hε1, h1⟩
  rcases floor_right_cont (x * s) with ⟨ε2, hε2, h2⟩
  rcases floor_right_cont (x * t) with ⟨ε3, hε3, h3⟩
  use min (ε1 / 5) (min (ε2 / s) (ε3 / t))
  have e1p : 0 < ε1 / 5 := div_pos hε1 (by norm_num)
  have e2p : 0 < ε2 / s := div_pos hε2 s_pos
  have e3p : 0 < ε3 / t := div_pos hε3 t_pos
  have m1 : 0 < min (ε2 / s) (ε3 / t) := lt_min e2p e3p
  refine ⟨lt_min e1p m1, fun δ hδ1 hδ2 => ?_⟩
  dsimp [F]
  have hd1 : δ * 5 < ε1 := by
    have : δ < ε1 / 5 := lt_of_lt_of_le hδ2 (min_le_left _ _)
    linarith
  have hd2 : δ * s < ε2 := by
    have : δ < ε2 / s := lt_of_lt_of_le hδ2 (le_trans (min_le_right _ _) (min_le_left _ _))
    exact (lt_div_iff₀ s_pos).mp this
  have hd3 : δ * t < ε3 := by
    have : δ < ε3 / t := lt_of_lt_of_le hδ2 (le_trans (min_le_right _ _) (min_le_right _ _))
    exact (lt_div_iff₀ t_pos).mp this
  have p1 : 0 ≤ δ * 5 := mul_nonneg hδ1 (by norm_num)
  have p2 : 0 ≤ δ * s := mul_nonneg hδ1 (le_of_lt s_pos)
  have p3 : 0 ≤ δ * t := mul_nonneg hδ1 (le_of_lt t_pos)
  have hr1 := h1 (δ * 5) p1 hd1
  have hr2 := h2 (δ * s) p2 hd2
  have hr3 := h3 (δ * t) p3 hd3
  have hx1 : (x + δ) * 5 = x * 5 + δ * 5 := by ring
  have hx2 : (x + δ) * s = x * s + δ * s := by ring
  have hx3 : (x + δ) * t = x * t + δ * t := by ring
  rw [hx1, hx2, hx3, hr1, hr2, hr3]

lemma floor_left_jump (y : ℝ) : 
  ∃ ε > 0, ∀ δ, 0 < δ → δ < ε → Int.floor (y - δ) = Int.floor y - if (∃ k : ℤ, y = (k : ℝ)) then 1 else 0 := by
  by_cases h : ∃ k : ℤ, y = k
  · rcases h with ⟨k, rfl⟩
    use (1/2 : ℝ)
    refine ⟨by norm_num, fun δ hδ1 hδ2 => ?_⟩
    have hp : (∃ (k_1 : ℤ), (k : ℝ) = ↑k_1) := ⟨k, rfl⟩
    rw [if_pos hp]
    have hz : Int.floor (k : ℝ) = k := Int.floor_intCast k
    rw [hz]
    apply Int.floor_eq_iff.mpr
    push_cast
    constructor
    · linarith
    · linarith
  · use y - (Int.floor y : ℝ)
    have h1 : (Int.floor y : ℝ) ≤ y := Int.floor_le y
    have h2 : (Int.floor y : ℝ) ≠ y := by
      intro hc
      apply h
      use (Int.floor y)
      exact hc.symm
    have h3 : (Int.floor y : ℝ) < y := lt_of_le_of_ne h1 h2
    refine ⟨by linarith, fun δ hδ1 hδ2 => ?_⟩
    rw [if_neg h]
    have hz : Int.floor y - 0 = Int.floor y := sub_zero _
    rw [hz]
    apply Int.floor_eq_iff.mpr
    have h4 : y < (Int.floor y : ℝ) + 1 := Int.lt_floor_add_one y
    constructor
    · linarith
    · linarith

lemma F_left_jump (x : ℝ) : 
  ∃ ε > 0, ∀ δ, 0 < δ → δ < ε → F (x - δ) = F x - (if ∃ k:ℤ, x * 5 = k then 1 else 0) - (if ∃ k:ℤ, x * s = k then 1 else 0) - (if ∃ k:ℤ, x * t = k then 1 else 0) := by
  rcases floor_left_jump (x * 5) with ⟨ε1, hε1, h1⟩
  rcases floor_left_jump (x * s) with ⟨ε2, hε2, h2⟩
  rcases floor_left_jump (x * t) with ⟨ε3, hε3, h3⟩
  use min (ε1 / 5) (min (ε2 / s) (ε3 / t))
  have e1p : 0 < ε1 / 5 := div_pos hε1 (by norm_num)
  have e2p : 0 < ε2 / s := div_pos hε2 s_pos
  have e3p : 0 < ε3 / t := div_pos hε3 t_pos
  have m1 : 0 < min (ε2 / s) (ε3 / t) := lt_min e2p e3p
  refine ⟨lt_min e1p m1, fun δ hδ1 hδ2 => ?_⟩
  dsimp [F]
  have hd1 : δ * 5 < ε1 := by
    have : δ < ε1 / 5 := lt_of_lt_of_le hδ2 (min_le_left _ _)
    linarith
  have hd2 : δ * s < ε2 := by
    have : δ < ε2 / s := lt_of_lt_of_le hδ2 (le_trans (min_le_right _ _) (min_le_left _ _))
    exact (lt_div_iff₀ s_pos).mp this
  have hd3 : δ * t < ε3 := by
    have : δ < ε3 / t := lt_of_lt_of_le hδ2 (le_trans (min_le_right _ _) (min_le_right _ _))
    exact (lt_div_iff₀ t_pos).mp this
  have p1 : 0 < δ * 5 := mul_pos hδ1 (by norm_num)
  have p2 : 0 < δ * s := mul_pos hδ1 s_pos
  have p3 : 0 < δ * t := mul_pos hδ1 t_pos
  have hr1 := h1 (δ * 5) p1 hd1
  have hr2 := h2 (δ * s) p2 hd2
  have hr3 := h3 (δ * t) p3 hd3
  have hx1 : (x - δ) * 5 = x * 5 - δ * 5 := by ring
  have hx2 : (x - δ) * s = x * s - δ * s := by ring
  have hx3 : (x - δ) * t = x * t - δ * t := by ring
  rw [hx1, hx2, hx3, hr1, hr2, hr3]
  ring

lemma irrational_of_eq_div (a : ℝ) (h_irr : Irrational a) (n m : ℤ) (h : a = (n : ℝ) / (m : ℝ)) : False := by
  have : a = ((n : ℚ) : ℝ) / ((m : ℚ) : ℝ) := by
    push_cast
    exact h
  have h2 : a = (((n / m : ℚ) : ℝ)) := by
    push_cast
    exact this
  exact h_irr ⟨n / m, h2.symm⟩

lemma F_jump_le_one (x : ℝ) (hx : x > 0) (h1 : ¬ ∃ k:ℤ, x * 5 = k) :
  (if ∃ k:ℤ, x * 5 = (k : ℝ) then 1 else 0) + (if ∃ k:ℤ, x * s = (k : ℝ) then 1 else 0) + (if ∃ k:ℤ, x * t = (k : ℝ) then 1 else 0) ≤ (1 : ℤ) := by
  by_cases h2 : ∃ k:ℤ, x * s = k
  · by_cases h3 : ∃ k:ℤ, x * t = k
    · rcases h2 with ⟨k2, hk2⟩; rcases h3 with ⟨k3, hk3⟩
      have hk3_neq : (k3 : ℝ) ≠ 0 := by
        have : 0 < x * t := mul_pos hx t_pos
        rw [hk3] at this
        intro hc; rw [hc] at this; linarith
      have h_st : s / t = (k2 : ℝ) / (k3 : ℝ) := by
        calc s / t = (x * s) / (x * t) := by
               rw [mul_div_mul_left _ _ (ne_of_gt hx)]
             _ = k2 / k3 := by rw [hk2, hk3]
      have hs2 : s^2 = s + 1 := goldenRatio_sq
      have h_st2 : s / t = s^2 := by
        dsimp [t]
        have hinv : 1 / (1 / s) = s := by rw [one_div_one_div]
        calc s / (1 / s) = s * (1 / (1 / s)) := div_eq_mul_one_div s (1/s)
             _ = s * s := by rw [hinv]
             _ = s^2 := by ring
      rw [h_st2, hs2] at h_st
      have hs_rat : s = (k2 - k3 : ℝ) / (k3 : ℝ) := by
        calc s = s + 1 - 1 := by ring
             _ = k2 / k3 - 1 := by rw [h_st]
             _ = (k2 - k3) / k3 := by
               have : (1 : ℝ) = k3 / k3 := (div_self hk3_neq).symm
               rw [this]
               ring
      exfalso
      have h_cast : s = ((k2 - k3 : ℤ) : ℝ) / (k3 : ℝ) := by
        push_cast
        exact hs_rat
      apply irrational_of_eq_div s irr_s (k2 - k3) k3 h_cast
    · rw [if_neg h1, if_pos h2, if_neg h3]
      linarith
  · rw [if_neg h1, if_neg h2]
    have : (if ∃ k:ℤ, x * t = ↑k then 1 else 0) ≤ 1 := by split <;> linarith
    linarith

lemma F_jump_le_one_full (x : ℝ) (hx : x > 0) :
  (if ∃ k:ℤ, x * 5 = (k : ℝ) then 1 else 0) + (if ∃ k:ℤ, x * s = (k : ℝ) then 1 else 0) + (if ∃ k:ℤ, x * t = (k : ℝ) then 1 else 0) ≤ (1 : ℤ) := by
  by_cases h1 : ∃ k:ℤ, x * 5 = k
  · by_cases h2 : ∃ k:ℤ, x * s = k
    · rcases h1 with ⟨k1, hk1⟩; rcases h2 with ⟨k2, hk2⟩
      have hk1_neq : (k1 : ℝ) ≠ 0 := by intro hc; rw [hc] at hk1; linarith
      have hs : s = (5 * k2 : ℝ) / (k1 : ℝ) := by
        apply mul_right_cancel₀ hk1_neq
        calc s * k1 = s * (x * 5) := by rw [←hk1]
             _ = (x * s) * 5 := by ring
             _ = k2 * 5 := by rw [hk2]
             _ = (5 * k2) / k1 * k1 := by
               rw [div_mul_cancel₀ _ hk1_neq]
               ring
      exfalso
      have h_cast : s = ( (5 * k2 : ℤ) : ℝ) / (k1 : ℝ) := by
        push_cast
        exact hs
      apply irrational_of_eq_div s irr_s (5 * k2) k1 h_cast
    · by_cases h3 : ∃ k:ℤ, x * t = k
      · rcases h1 with ⟨k1, hk1⟩; rcases h3 with ⟨k3, hk3⟩
        have hk1_neq : (k1 : ℝ) ≠ 0 := by intro hc; rw [hc] at hk1; linarith
        have ht : t = (5 * k3 : ℝ) / (k1 : ℝ) := by
          apply mul_right_cancel₀ hk1_neq
          calc t * k1 = t * (x * 5) := by rw [←hk1]
               _ = (x * t) * 5 := by ring
               _ = k3 * 5 := by rw [hk3]
               _ = (5 * k3) / k1 * k1 := by
                 rw [div_mul_cancel₀ _ hk1_neq]
                 ring
        have hs : s = (k1 : ℝ) / (5 * k3 : ℝ) := by
          dsimp [t] at ht
          have hinv : (1 / s)⁻¹ = ((5 * k3 : ℝ) / (k1 : ℝ))⁻¹ := by rw [ht]
          have h1 : (1 / s)⁻¹ = s := by
             rw [inv_eq_one_div (1/s), one_div_one_div]
          rw [h1] at hinv
          rw [hinv]
          exact inv_div _ _
        exfalso
        have h_cast : s = (k1 : ℝ) / ((5 * k3 : ℤ) : ℝ) := by
          push_cast
          exact hs
        apply irrational_of_eq_div s irr_s k1 (5 * k3) h_cast
      · rw [if_pos h1, if_neg h2, if_neg h3]
        linarith
  · exact F_jump_le_one x hx h1

lemma F_surj (m : ℤ) (hm : m ≥ 1) : 
  ∃ x > 0, F x = m ∧ ((∃ k:ℤ, x * 5 = (k:ℝ)) ∨ (∃ k:ℤ, x * s = (k:ℝ)) ∨ (∃ k:ℤ, x * t = (k:ℝ))) := by
  let A := {x : ℝ | x ≥ 0 ∧ F x < m}
  have h_nonempty : A.Nonempty := ⟨0, by norm_num, by rw [F_zero]; linarith⟩
  have h_bdd : BddAbove A := by
    use (m + 1) / 5
    intro x hx
    rcases hx with ⟨hx1, hx2⟩
    have h_bound := F_lower_bound x hx1
    have : (x * 5 : ℝ) - 1 < m := by
      calc (x * 5 : ℝ) - 1 < F x := h_bound
           _ < m := by exact_mod_cast hx2
    linarith
  have h_sup := sSup_prop A h_nonempty h_bdd
  let x := sSup A
  have h_x_def : x = sSup A := rfl
  have hx_nonneg : x ≥ 0 := le_csSup h_bdd ⟨by norm_num, by rw [F_zero]; linarith⟩
  have h_F_ge : F x ≥ m := by
    rcases F_right_cont x with ⟨ε, hε, h_cont⟩
    have h1 : x + (ε / 2) ∉ A := (h_sup.2) (ε / 2) (by linarith)
    have h2 : x + (ε / 2) ≥ 0 := by linarith
    have h3 : F (x + (ε / 2)) ≥ m := by
      by_contra hc
      have hc_lt : F (x + (ε / 2)) < m := not_le.mp hc
      apply h1
      exact ⟨h2, hc_lt⟩
    have h4 : F (x + (ε / 2)) = F x := h_cont (ε / 2) (by linarith) (by linarith)
    rw [h4] at h3
    exact h3
  have hx_pos : x > 0 := by
    by_contra hc
    have h_zero : x = 0 := le_antisymm (not_lt.mp hc) hx_nonneg
    rw [h_zero, F_zero] at h_F_ge
    linarith
  rcases F_left_jump x with ⟨ε, hε, h_jump⟩
  let J_def : ℤ := (if ∃ k:ℤ, x * 5 = (k:ℝ) then (1:ℤ) else 0) + (if ∃ k:ℤ, x * s = (k:ℝ) then (1:ℤ) else 0) + (if ∃ k:ℤ, x * t = (k:ℝ) then (1:ℤ) else 0)
  have h_J : ∃ y ∈ A, y > x - ε ∧ F y = F x - J_def := by
    rcases (h_sup.1) (ε / 2) (by linarith) with ⟨y, hy_mem, hy_gt⟩
    use y
    refine ⟨hy_mem, by linarith, ?_⟩
    have hy_lt : y ≤ x := le_csSup h_bdd hy_mem
    by_cases h_eq : y = x
    · rw [h_eq] at hy_mem
      have : F x < m := hy_mem.2
      linarith
    have hy_lt_strict : y < x := lt_of_le_of_ne hy_lt h_eq
    have h_delta : 0 < x - y ∧ x - y < ε := ⟨by linarith, by linarith⟩
    have h_jump_y := h_jump (x - y) h_delta.1 h_delta.2
    have h_sub : x - (x - y) = y := by ring
    rw [h_sub] at h_jump_y
    have hj_eq : (if ∃ k:ℤ, x * 5 = ↑k then 1 else 0) = (if ∃ k:ℤ, x * 5 = (k:ℝ) then (1:ℤ) else 0) := rfl
    have hj_eq2 : (if ∃ k:ℤ, x * s = ↑k then 1 else 0) = (if ∃ k:ℤ, x * s = (k:ℝ) then (1:ℤ) else 0) := rfl
    have hj_eq3 : (if ∃ k:ℤ, x * t = ↑k then 1 else 0) = (if ∃ k:ℤ, x * t = (k:ℝ) then (1:ℤ) else 0) := rfl
    rw [hj_eq, hj_eq2, hj_eq3] at h_jump_y
    have h_jump_y_rewritten : F y = F x - J_def := by
      calc F y = F x - (if ∃ k:ℤ, x * 5 = (k:ℝ) then (1:ℤ) else 0) - (if ∃ k:ℤ, x * s = (k:ℝ) then (1:ℤ) else 0) - (if ∃ k:ℤ, x * t = (k:ℝ) then (1:ℤ) else 0) := h_jump_y
           _ = F x - J_def := by
             dsimp [J_def]
             ring
    exact h_jump_y_rewritten
  rcases h_J with ⟨y, hy_mem, hy_gt, h_Fy⟩
  have h_Fy_lt : F x - J_def < m := by
    rw [← h_Fy]
    exact hy_mem.2
  have h_J_ge : J_def ≥ 1 := by linarith
  have h_jump_exists : (∃ k:ℤ, x * 5 = (k:ℝ)) ∨ (∃ k:ℤ, x * s = (k:ℝ)) ∨ (∃ k:ℤ, x * t = (k:ℝ)) := by
    by_contra hc
    have hc1 : ¬ (∃ k:ℤ, x * 5 = (k:ℝ)) := by intro h; exact hc (Or.inl h)
    have hc2 : ¬ (∃ k:ℤ, x * s = (k:ℝ)) := by intro h; exact hc (Or.inr (Or.inl h))
    have hc3 : ¬ (∃ k:ℤ, x * t = (k:ℝ)) := by intro h; exact hc (Or.inr (Or.inr h))
    have h1 : J_def = 0 := by
      dsimp [J_def]
      rw [if_neg hc1, if_neg hc2, if_neg hc3]
      ring
    linarith
  have h_J_le : J_def ≤ 1 := by
    dsimp [J_def]
    by_cases h1 : ∃ k:ℤ, x * 5 = (k:ℝ)
    · rcases h1 with ⟨k1, hk1⟩
      have h2 : ¬ ∃ k:ℤ, x * s = (k:ℝ) := by
        rintro ⟨k2, hk2⟩
        have hk1_neq : (k1:ℝ) ≠ 0 := by
          intro hc
          have h_x_zero : x = 0 := by linarith
          linarith
        have h_s_eq : s = ((k2 * 5 : ℤ):ℝ) / (k1:ℝ) := by
          calc s = (x * s) * 5 / (x * 5) := by
                   have h_x_neq : x ≠ 0 := ne_of_gt hx_pos
                   have h_div : (x * s) * 5 / (x * 5) = s * (x * 5) / (x * 5) := by ring
                   rw [h_div]
                   exact (mul_div_cancel_right₀ s (by linarith)).symm
               _ = (k2:ℝ) * 5 / (k1:ℝ) := by rw [hk2, hk1]
               _ = ((k2 * 5 : ℤ):ℝ) / (k1:ℝ) := by push_cast; rfl
        exact irrational_of_eq_div s irr_s (k2 * 5) k1 h_s_eq
      have h3 : ¬ ∃ k:ℤ, x * t = (k:ℝ) := by
        rintro ⟨k3, hk3⟩
        have hk1_neq : (k1:ℝ) ≠ 0 := by
          intro hc
          have h_x_zero : x = 0 := by linarith
          linarith
        have h_s_eq : s = (k1:ℝ) / ((k3 * 5 : ℤ):ℝ) := by
          have ht2 : x * (1 / s) = (k3:ℝ) := hk3
          have h_st : 1 / s = (k3:ℝ) * 5 / (k1:ℝ) := by
            calc 1 / s = (x * (1 / s)) * 5 / (x * 5) := by
                   have h_x_neq : x ≠ 0 := ne_of_gt hx_pos
                   have h_div : (x * (1 / s)) * 5 / (x * 5) = (1 / s) * (x * 5) / (x * 5) := by ring
                   rw [h_div]
                   exact (mul_div_cancel_right₀ (1 / s) (by linarith)).symm
                 _ = (k3:ℝ) * 5 / (k1:ℝ) := by rw [ht2, hk1]
          have hinv : (1 / s)⁻¹ = ((k3:ℝ) * 5 / (k1:ℝ))⁻¹ := by rw [h_st]
          rw [inv_eq_one_div (1/s), one_div_one_div] at hinv
          calc s = ((k3:ℝ) * 5 / (k1:ℝ))⁻¹ := hinv
               _ = (k1:ℝ) / ((k3:ℝ) * 5) := inv_div _ _
               _ = (k1:ℝ) / ((k3 * 5 : ℤ):ℝ) := by push_cast; rfl
        exact irrational_of_eq_div s irr_s k1 (k3 * 5) h_s_eq
      rw [if_pos ⟨k1, hk1⟩, if_neg h2, if_neg h3]
      linarith
    · exact F_jump_le_one x hx_pos h1
  have h_J_eq : J_def = 1 := le_antisymm h_J_le h_J_ge
  have h_Fx_eq : F x = m := by linarith
  exact ⟨x, hx_pos, h_Fx_eq, h_jump_exists⟩


lemma A_eq_F (n : ℕ) : (A207672 (n+1) : ℤ) = F (((n+1:ℕ) : ℝ) / 5) := by
  dsimp [A207672, F]
  have h1 : (((n+1:ℕ) : ℝ) / 5) * 5 = ((n+1 : ℤ) : ℝ) := by
    push_cast
    ring
  have h2 : Int.floor ((((n+1:ℕ) : ℝ) / 5) * 5) = ((n+1:ℕ) : ℤ) := by
    rw [h1]
    exact_mod_cast Int.floor_natCast (n+1)
  have h3 : (((n+1:ℕ) : ℝ) / 5) * s = ((n+1:ℕ) : ℝ) * s / 5 := by ring
  have h4 : (((n+1:ℕ) : ℝ) / 5) * t = ((n+1:ℕ) : ℝ) * t / 5 := by ring
  rw [h2, h3, h4]
  have h_pos : 0 ≤ ((n+1:ℕ):ℤ) + ⌊((n+1:ℕ) : ℝ) * s / 5⌋ + ⌊((n+1:ℕ) : ℝ) * t / 5⌋ := by
    have hp1 : 0 ≤ ((n+1:ℕ):ℤ) := by positivity
    have hp2 : 0 ≤ ⌊((n+1:ℕ) : ℝ) * s / 5⌋ := by
      apply Int.floor_nonneg.mpr
      have : (0:ℝ) ≤ ((n+1:ℕ):ℝ) := by positivity
      exact mul_nonneg (mul_nonneg this (le_of_lt s_pos)) (by norm_num)
    have hp3 : 0 ≤ ⌊((n+1:ℕ) : ℝ) * t / 5⌋ := by
      apply Int.floor_nonneg.mpr
      have : (0:ℝ) ≤ ((n+1:ℕ):ℝ) := by positivity
      exact mul_nonneg (mul_nonneg this (le_of_lt t_pos)) (by norm_num)
    linarith
  exact Int.toNat_of_nonneg h_pos

lemma F_pos_of_ge_15 (x : ℝ) (hx : x ≥ 1 / 5) : F x > 0 := by
  dsimp [F]
  have h2 : 0 ≤ Int.floor (x * s) := by
    apply Int.floor_nonneg.mpr
    have : 0 ≤ x := by linarith
    exact mul_nonneg this (le_of_lt s_pos)
  have h1 : 0 ≤ Int.floor (x * 5) := by
    apply Int.floor_nonneg.mpr
    have : 0 ≤ x := by linarith
    linarith
  have h3 : 0 ≤ Int.floor (x * t) := by
    apply Int.floor_nonneg.mpr
    have : 0 ≤ x := by linarith
    exact mul_nonneg this (le_of_lt t_pos)
  have h4 : Int.floor (x * 5) ≥ 1 := by
    apply Int.le_floor.mpr
    have : (1:ℝ) ≤ x * 5 := by linarith
    exact_mod_cast this
  linarith

lemma F_pos_of_ge_1s (x : ℝ) (hx : x ≥ 1 / s) : F x > 0 := by
  dsimp [F]
  have h2 : 0 ≤ Int.floor (x * s) := by
    apply Int.floor_nonneg.mpr
    have : 0 ≤ x := by
      have : 0 ≤ 1 / s := le_of_lt t_pos
      linarith
    exact mul_nonneg this (le_of_lt s_pos)
  have h1 : 0 ≤ Int.floor (x * 5) := by
    apply Int.floor_nonneg.mpr
    have : 0 ≤ x := by
      have : 0 ≤ 1 / s := le_of_lt t_pos
      linarith
    linarith
  have h3 : 0 ≤ Int.floor (x * t) := by
    apply Int.floor_nonneg.mpr
    have : 0 ≤ x := by
      have : 0 ≤ 1 / s := le_of_lt t_pos
      linarith
    exact mul_nonneg this (le_of_lt t_pos)
  have h4 : Int.floor (x * s) ≥ 1 := by
    apply Int.le_floor.mpr
    have : (1:ℝ) ≤ x * s := by
      calc (1:ℝ) = (1 / s) * s := by rw [div_mul_cancel₀ _ (ne_of_gt s_pos)]
           _ ≤ x * s := mul_le_mul_of_nonneg_right hx (le_of_lt s_pos)
    exact_mod_cast this
  linarith

lemma F_pos_of_ge_1t (x : ℝ) (hx : x ≥ 1 / t) : F x > 0 := by
  dsimp [F]
  have h2 : 0 ≤ Int.floor (x * s) := by
    apply Int.floor_nonneg.mpr
    have : 0 ≤ x := by
      have : 0 ≤ 1 / t := le_of_lt (div_pos (by norm_num) t_pos)
      linarith
    exact mul_nonneg this (le_of_lt s_pos)
  have h1 : 0 ≤ Int.floor (x * 5) := by
    apply Int.floor_nonneg.mpr
    have : 0 ≤ x := by
      have : 0 ≤ 1 / t := le_of_lt (div_pos (by norm_num) t_pos)
      linarith
    linarith
  have h3 : 0 ≤ Int.floor (x * t) := by
    apply Int.floor_nonneg.mpr
    have : 0 ≤ x := by
      have : 0 ≤ 1 / t := le_of_lt (div_pos (by norm_num) t_pos)
      linarith
    exact mul_nonneg this (le_of_lt t_pos)
  have h4 : Int.floor (x * t) ≥ 1 := by
    apply Int.le_floor.mpr
    have : (1:ℝ) ≤ x * t := by
      calc (1:ℝ) = (1 / t) * t := by rw [div_mul_cancel₀ _ (ne_of_gt t_pos)]
           _ ≤ x * t := mul_le_mul_of_nonneg_right hx (le_of_lt t_pos)
    exact_mod_cast this
  linarith


lemma F_injective_on_S (x1 x2 : ℝ) (_h1_pos : x1 > 0) (_h2_pos : x2 > 0) 
  (h1S : (∃ k:ℤ, x1 * 5 = (k:ℝ)) ∨ (∃ k:ℤ, x1 * s = (k:ℝ)) ∨ (∃ k:ℤ, x1 * t = (k:ℝ)))
  (h2S : (∃ k:ℤ, x2 * 5 = (k:ℝ)) ∨ (∃ k:ℤ, x2 * s = (k:ℝ)) ∨ (∃ k:ℤ, x2 * t = (k:ℝ)))
  (heq : F x1 = F x2) : x1 = x2 := by
  by_contra hc
  have h_cases : x1 < x2 ∨ x2 < x1 := ne_iff_lt_or_gt.mp hc
  rcases h_cases with h_lt | h_gt
  · rcases F_left_jump x2 with ⟨ε, hε, h_jump⟩
    have h_del : ∃ δ, 0 < δ ∧ δ < ε ∧ x1 ≤ x2 - δ := by
      let d := min (ε / 2) ((x2 - x1) / 2)
      use d
      have dp : d > 0 := lt_min (half_pos hε) (half_pos (sub_pos.mpr h_lt))
      constructor
      · exact dp
      · constructor
        · exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
        · have : d ≤ (x2 - x1) / 2 := min_le_right _ _
          linarith
    rcases h_del with ⟨δ, hδ1, hδ2, h_le⟩
    have hF_mono : F x1 ≤ F (x2 - δ) := F_mono h_le
    have h_jump_eq : F (x2 - δ) = F x2 - (if ∃ k:ℤ, x2 * 5 = (k:ℝ) then (1:ℤ) else 0) - (if ∃ k:ℤ, x2 * s = (k:ℝ) then (1:ℤ) else 0) - (if ∃ k:ℤ, x2 * t = (k:ℝ) then (1:ℤ) else 0) := h_jump δ hδ1 hδ2
    let j5 : ℤ := if ∃ k:ℤ, x2 * 5 = (k:ℝ) then 1 else 0
    let js : ℤ := if ∃ k:ℤ, x2 * s = (k:ℝ) then 1 else 0
    let jt : ℤ := if ∃ k:ℤ, x2 * t = (k:ℝ) then 1 else 0
    have h_j_ge_1 : j5 + js + jt ≥ 1 := by
      rcases h2S with hc1 | hc2 | hc3
      · have : j5 = 1 := if_pos hc1
        have : js ≥ 0 := by dsimp [js]; split <;> norm_num
        have : jt ≥ 0 := by dsimp [jt]; split <;> norm_num
        linarith
      · have : js = 1 := if_pos hc2
        have : j5 ≥ 0 := by dsimp [j5]; split <;> norm_num
        have : jt ≥ 0 := by dsimp [jt]; split <;> norm_num
        linarith
      · have : jt = 1 := if_pos hc3
        have : j5 ≥ 0 := by dsimp [j5]; split <;> norm_num
        have : js ≥ 0 := by dsimp [js]; split <;> norm_num
        linarith
    have : F (x2 - δ) < F x2 := by
      calc F (x2 - δ) = F x2 - (j5 + js + jt) := by
             rw [h_jump_eq]
             ring
           _ ≤ F x2 - 1 := by linarith
           _ < F x2 := by linarith
    have : F x1 < F x2 := lt_of_le_of_lt hF_mono this
    linarith
  · rcases F_left_jump x1 with ⟨ε, hε, h_jump⟩
    have h_del : ∃ δ, 0 < δ ∧ δ < ε ∧ x2 ≤ x1 - δ := by
      let d := min (ε / 2) ((x1 - x2) / 2)
      use d
      have dp : d > 0 := lt_min (half_pos hε) (half_pos (sub_pos.mpr h_gt))
      constructor
      · exact dp
      · constructor
        · exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
        · have : d ≤ (x1 - x2) / 2 := min_le_right _ _
          linarith
    rcases h_del with ⟨δ, hδ1, hδ2, h_le⟩
    have hF_mono : F x2 ≤ F (x1 - δ) := F_mono h_le
    have h_jump_eq : F (x1 - δ) = F x1 - (if ∃ k:ℤ, x1 * 5 = (k:ℝ) then (1:ℤ) else 0) - (if ∃ k:ℤ, x1 * s = (k:ℝ) then (1:ℤ) else 0) - (if ∃ k:ℤ, x1 * t = (k:ℝ) then (1:ℤ) else 0) := h_jump δ hδ1 hδ2
    let j5 : ℤ := if ∃ k:ℤ, x1 * 5 = (k:ℝ) then 1 else 0
    let js : ℤ := if ∃ k:ℤ, x1 * s = (k:ℝ) then 1 else 0
    let jt : ℤ := if ∃ k:ℤ, x1 * t = (k:ℝ) then 1 else 0
    have h_j_ge_1 : j5 + js + jt ≥ 1 := by
      rcases h1S with hc1 | hc2 | hc3
      · have : j5 = 1 := if_pos hc1
        have : js ≥ 0 := by dsimp [js]; split <;> norm_num
        have : jt ≥ 0 := by dsimp [jt]; split <;> norm_num
        linarith
      · have : js = 1 := if_pos hc2
        have : j5 ≥ 0 := by dsimp [j5]; split <;> norm_num
        have : jt ≥ 0 := by dsimp [jt]; split <;> norm_num
        linarith
      · have : jt = 1 := if_pos hc3
        have : j5 ≥ 0 := by dsimp [j5]; split <;> norm_num
        have : js ≥ 0 := by dsimp [js]; split <;> norm_num
        linarith
    have : F (x1 - δ) < F x1 := by
      calc F (x1 - δ) = F x1 - (j5 + js + jt) := by
             rw [h_jump_eq]
             ring
           _ ≤ F x1 - 1 := by linarith
           _ < F x1 := by linarith
    have : F x2 < F x1 := lt_of_le_of_lt hF_mono this
    linarith

lemma F_surj_proof (m : ℤ) (hm : m ≥ 1) : 
  ∃ x > 0, F x = m ∧ ((∃ k:ℤ, x * 5 = (k:ℝ)) ∨ (∃ k:ℤ, x * s = (k:ℝ)) ∨ (∃ k:ℤ, x * t = (k:ℝ))) := by
  let A := {x : ℝ | x ≥ 0 ∧ F x < m}
  have h_nonempty : A.Nonempty := ⟨0, by norm_num, by rw [F_zero]; linarith⟩
  have h_bdd : BddAbove A := by
    use (m + 1) / 5
    intro y hy
    rcases hy with ⟨hy1, hy2⟩
    have h_bound := F_lower_bound y hy1
    have : (y * 5 : ℝ) - 1 < m := by
      calc (y * 5 : ℝ) - 1 < F y := h_bound
           _ < m := by exact_mod_cast hy2
    linarith
  have h_sup := sSup_prop A h_nonempty h_bdd
  let x := sSup A
  have hx_pos : x > 0 := by
    rcases F_right_cont 0 with ⟨ε, hε, h_cont⟩
    have h_del : ∃ δ, 0 < δ ∧ δ < ε := ⟨ε / 2, half_pos hε, by linarith⟩
    rcases h_del with ⟨δ, hδ1, hδ2⟩
    have hd_in_A : δ ∈ A := by
      constructor
      · linarith
      · have : F (0 + δ) = F 0 := h_cont δ (by linarith) hδ2
        rw [zero_add] at this
        rw [this, F_zero]
        linarith
    have : x ≥ δ := le_csSup h_bdd hd_in_A
    linarith

  rcases h_sup with ⟨h_left, h_right⟩
  have h_Fx_ge_m : F x ≥ m := by
    by_contra hc
    have hlt : F x < m := by linarith
    rcases F_right_cont x with ⟨ε, hε, h_cont⟩
    have h_del : ∃ δ, 0 < δ ∧ δ < ε := ⟨ε / 2, half_pos hε, by linarith⟩
    rcases h_del with ⟨δ, hδ1, hδ2⟩
    have hd_in_A : x + δ ∈ A := by
      constructor
      · linarith
      · rw [h_cont δ (by linarith) hδ2]
        exact hlt
    have : x + δ ∉ A := h_right δ hδ1
    exact this hd_in_A

  rcases F_left_jump x with ⟨ε, hε, h_jump⟩
  have h_del : ∃ δ, 0 < δ ∧ δ < ε := ⟨ε / 2, half_pos hε, by linarith⟩
  rcases h_del with ⟨δ, hδ1, hδ2⟩
  have hy : ∃ y ∈ A, y > x - δ := h_left δ hδ1
  rcases hy with ⟨y, hyA, hy_gt⟩
  have hy_le_x : y ≤ x := le_csSup h_bdd hyA
  have hF_y : F y < m := hyA.2
  have hF_mono : F (x - δ) ≤ F y := F_mono (by linarith)
  have h_jump_eq : F (x - δ) = F x - (if ∃ k:ℤ, x * 5 = (k:ℝ) then (1:ℤ) else 0) - (if ∃ k:ℤ, x * s = (k:ℝ) then (1:ℤ) else 0) - (if ∃ k:ℤ, x * t = (k:ℝ) then (1:ℤ) else 0) := h_jump δ hδ1 hδ2
  
  have h_j_le_1 : (if ∃ k:ℤ, x * 5 = (k:ℝ) then (1:ℤ) else 0) + (if ∃ k:ℤ, x * s = (k:ℝ) then (1:ℤ) else 0) + (if ∃ k:ℤ, x * t = (k:ℝ) then (1:ℤ) else 0) ≤ 1 := F_jump_le_one_full x hx_pos
  
  have h_Fx_lt : F x - ((if ∃ k:ℤ, x * 5 = (k:ℝ) then (1:ℤ) else 0) + (if ∃ k:ℤ, x * s = (k:ℝ) then (1:ℤ) else 0) + (if ∃ k:ℤ, x * t = (k:ℝ) then (1:ℤ) else 0)) < m := by
    have : F x - ((if ∃ k:ℤ, x * 5 = (k:ℝ) then (1:ℤ) else 0) + (if ∃ k:ℤ, x * s = (k:ℝ) then (1:ℤ) else 0) + (if ∃ k:ℤ, x * t = (k:ℝ) then (1:ℤ) else 0)) = F (x - δ) := by
      calc F x - ((if ∃ k:ℤ, x * 5 = (k:ℝ) then (1:ℤ) else 0) + (if ∃ k:ℤ, x * s = (k:ℝ) then (1:ℤ) else 0) + (if ∃ k:ℤ, x * t = (k:ℝ) then (1:ℤ) else 0)) = F x - (if ∃ k:ℤ, x * 5 = (k:ℝ) then (1:ℤ) else 0) - (if ∃ k:ℤ, x * s = (k:ℝ) then (1:ℤ) else 0) - (if ∃ k:ℤ, x * t = (k:ℝ) then (1:ℤ) else 0) := by ring
           _ = F (x - δ) := h_jump_eq.symm
    rw [this]
    calc F (x - δ) ≤ F y := hF_mono
         _ < m := hF_y
         
  have h_j_ge_1 : (if ∃ k:ℤ, x * 5 = (k:ℝ) then (1:ℤ) else 0) + (if ∃ k:ℤ, x * s = (k:ℝ) then (1:ℤ) else 0) + (if ∃ k:ℤ, x * t = (k:ℝ) then (1:ℤ) else 0) ≥ 1 := by
    by_contra hc
    have h1 : (if ∃ k:ℤ, x * 5 = (k:ℝ) then (1:ℤ) else 0) ≥ 0 := by split <;> norm_num
    have h2 : (if ∃ k:ℤ, x * s = (k:ℝ) then (1:ℤ) else 0) ≥ 0 := by split <;> norm_num
    have h3 : (if ∃ k:ℤ, x * t = (k:ℝ) then (1:ℤ) else 0) ≥ 0 := by split <;> norm_num
    have : (if ∃ k:ℤ, x * 5 = (k:ℝ) then (1:ℤ) else 0) + (if ∃ k:ℤ, x * s = (k:ℝ) then (1:ℤ) else 0) + (if ∃ k:ℤ, x * t = (k:ℝ) then (1:ℤ) else 0) = 0 := by linarith
    rw [this] at h_Fx_lt
    have : F x - 0 < m := h_Fx_lt
    linarith
    
  have h_j_eq_1 : (if ∃ k:ℤ, x * 5 = (k:ℝ) then (1:ℤ) else 0) + (if ∃ k:ℤ, x * s = (k:ℝ) then (1:ℤ) else 0) + (if ∃ k:ℤ, x * t = (k:ℝ) then (1:ℤ) else 0) = 1 := by linarith
  have h_Fx_eq_m : F x = m := by
    have : F x - 1 < m := by
      rw [←h_j_eq_1]
      exact h_Fx_lt
    linarith
    
  have h_cond : (∃ k:ℤ, x * 5 = (k:ℝ)) ∨ (∃ k:ℤ, x * s = (k:ℝ)) ∨ (∃ k:ℤ, x * t = (k:ℝ)) := by
    by_contra hc
    have hc1 : ¬ (∃ k:ℤ, x * 5 = (k:ℝ)) := fun ha => hc (Or.inl ha)
    have hc2 : ¬ (∃ k:ℤ, x * s = (k:ℝ)) := fun ha => hc (Or.inr (Or.inl ha))
    have hc3 : ¬ (∃ k:ℤ, x * t = (k:ℝ)) := fun ha => hc (Or.inr (Or.inr ha))
    have hj5 : (if ∃ k:ℤ, x * 5 = (k:ℝ) then (1:ℤ) else 0) = 0 := if_neg hc1
    have hjs : (if ∃ k:ℤ, x * s = (k:ℝ) then (1:ℤ) else 0) = 0 := if_neg hc2
    have hjt : (if ∃ k:ℤ, x * t = (k:ℝ) then (1:ℤ) else 0) = 0 := if_neg hc3
    have : (if ∃ k:ℤ, x * 5 = (k:ℝ) then (1:ℤ) else 0) + (if ∃ k:ℤ, x * s = (k:ℝ) then (1:ℤ) else 0) + (if ∃ k:ℤ, x * t = (k:ℝ) then (1:ℤ) else 0) = 0 := by rw [hj5, hjs, hjt, add_zero, add_zero]
    linarith
  
  exact ⟨x, hx_pos, h_Fx_eq_m, h_cond⟩

noncomputable def A207672_def (n : ℕ) : ℕ :=
  let r : ℝ := 5
  let s : ℝ := goldenRatio
  let t : ℝ := 1 / s
  let n_r : ℝ := n
  let term1_int : ℤ := Int.floor (n_r * s / r)
  let term2_int : ℤ := Int.floor (n_r * t / r)
  let result_int : ℤ := n.cast + term1_int + term2_int
  result_int.toNat


lemma B_eq_F (n : ℕ) : (A207673 (n+1) : ℤ) = F (((n+1:ℕ) : ℝ) / s) := by
  dsimp [A207673, F]
  have h1 : (((n+1:ℕ) : ℝ) / s) * s = ((n+1 : ℤ) : ℝ) := by
    rw [div_mul_cancel₀ _ (ne_of_gt s_pos)]
    push_cast
    rfl
  have h2 : Int.floor ((((n+1:ℕ) : ℝ) / s) * s) = ((n+1:ℕ) : ℤ) := by
    rw [h1]
    exact_mod_cast Int.floor_natCast (n+1)
  have h3 : (((n+1:ℕ) : ℝ) / s) * 5 = ((n+1:ℕ) : ℝ) * 5 / s := by ring
  have h4 : (((n+1:ℕ) : ℝ) / s) * t = ((n+1:ℕ) : ℝ) * t / s := by ring
  rw [h2, h3, h4]
  have h_pos : 0 ≤ ((n+1:ℕ):ℤ) + ⌊((n+1:ℕ) : ℝ) * 5 / s⌋ + ⌊((n+1:ℕ) : ℝ) * t / s⌋ := by
    have hp1 : 0 ≤ ((n+1:ℕ):ℤ) := by positivity
    have hp2 : 0 ≤ ⌊((n+1:ℕ) : ℝ) * 5 / s⌋ := by
      apply Int.floor_nonneg.mpr
      have : (0:ℝ) ≤ ((n+1:ℕ):ℝ) := by positivity
      apply div_nonneg
      · linarith
      · exact le_of_lt s_pos
    have hp3 : 0 ≤ ⌊((n+1:ℕ) : ℝ) * t / s⌋ := by
      apply Int.floor_nonneg.mpr
      have : (0:ℝ) ≤ ((n+1:ℕ):ℝ) := by positivity
      apply div_nonneg
      · exact mul_nonneg this (le_of_lt t_pos)
      · exact le_of_lt s_pos
    linarith
  have h_toNat := Int.toNat_of_nonneg h_pos
  have h_comm : ⌊((n+1:ℕ):ℝ) * 5 / s⌋ + ((n+1:ℕ):ℤ) + ⌊((n+1:ℕ):ℝ) * t / s⌋ = ((n+1:ℕ):ℤ) + ⌊((n+1:ℕ):ℝ) * 5 / s⌋ + ⌊((n+1:ℕ):ℝ) * t / s⌋ := by ring
  rw [h_comm]
  exact h_toNat

lemma C_eq_F (n : ℕ) : (A208326 (n+1) : ℤ) = F (((n+1:ℕ) : ℝ) / t) := by
  dsimp [A208326, F]
  have h1 : (((n+1:ℕ) : ℝ) / t) * t = ((n+1 : ℤ) : ℝ) := by
    rw [div_mul_cancel₀ _ (ne_of_gt t_pos)]
    push_cast
    rfl
  have h2 : Int.floor ((((n+1:ℕ) : ℝ) / t) * t) = ((n+1:ℕ) : ℤ) := by
    rw [h1]
    exact_mod_cast Int.floor_natCast (n+1)
  have h3 : (((n+1:ℕ) : ℝ) / t) * 5 = ((n+1:ℕ) : ℝ) * 5 / t := by ring
  have h4 : (((n+1:ℕ) : ℝ) / t) * s = ((n+1:ℕ) : ℝ) * s / t := by ring
  rw [h2, h3, h4]
  have h_pos : 0 ≤ ((n+1:ℕ):ℤ) + ⌊((n+1:ℕ) : ℝ) * 5 / t⌋ + ⌊((n+1:ℕ) : ℝ) * s / t⌋ := by
    have hp1 : 0 ≤ ((n+1:ℕ):ℤ) := by positivity
    have hp2 : 0 ≤ ⌊((n+1:ℕ) : ℝ) * 5 / t⌋ := by
      apply Int.floor_nonneg.mpr
      have : (0:ℝ) ≤ ((n+1:ℕ):ℝ) := by positivity
      apply div_nonneg
      · linarith
      · exact le_of_lt t_pos
    have hp3 : 0 ≤ ⌊((n+1:ℕ) : ℝ) * s / t⌋ := by
      apply Int.floor_nonneg.mpr
      have : (0:ℝ) ≤ ((n+1:ℕ):ℝ) := by positivity
      apply div_nonneg
      · exact mul_nonneg this (le_of_lt s_pos)
      · exact le_of_lt t_pos
    linarith
  have h_toNat := Int.toNat_of_nonneg h_pos
  have h_comm : ⌊((n+1:ℕ):ℝ) * 5 / t⌋ + ⌊((n+1:ℕ):ℝ) * s / t⌋ + ((n+1:ℕ):ℤ) = ((n+1:ℕ):ℤ) + ⌊((n+1:ℕ):ℝ) * 5 / t⌋ + ⌊((n+1:ℕ):ℝ) * s / t⌋ := by ring
  rw [h_comm]
  exact h_toNat



theorem oeis_208326_conjecture_0 :
  ({n : ℕ | 0 < n} : Set ℕ) =
    (Set.range (A207672 ∘ Nat.succ)) ∪
    (Set.range (A207673 ∘ Nat.succ)) ∪
    (Set.range (A208326 ∘ Nat.succ)) ∧
  (Set.range (A207672 ∘ Nat.succ) ∩ Set.range (A207673 ∘ Nat.succ) = ∅) ∧
  (Set.range (A207672 ∘ Nat.succ) ∩ Set.range (A208326 ∘ Nat.succ) = ∅) ∧
  (Set.range (A207673 ∘ Nat.succ) ∩ Set.range (A208326 ∘ Nat.succ) = ∅)
  := by
  constructor
  · ext m
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_range, Function.comp_apply]
    constructor
    · intro hm
      have hm_pos : m > 0 := hm
      have hm_int : (m : ℤ) ≥ 1 := by exact_mod_cast hm_pos
      rcases F_surj_proof m hm_int with ⟨x, hx_pos, hFx, h_cond⟩
      rcases h_cond with ⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩
      · left; left
        have hk_pos : k > 0 := by
          have h_x5 : x * 5 > 0 := mul_pos hx_pos (by norm_num)
          have hk_r : (k:ℝ) > 0 := by linarith
          have h_cast : ((k:ℤ):ℝ) > 0 := by linarith
          exact Int.cast_pos.mp h_cast
        have hk_eq : (k.toNat : ℤ) = k := Int.toNat_of_nonneg (le_of_lt hk_pos)
        have h_k_nat_pos : k.toNat > 0 := by
          have : k.toNat ≠ 0 := by
            intro hc
            have : k ≤ 0 := Int.toNat_eq_zero.mp hc
            linarith
          exact Nat.pos_of_ne_zero this
        use k.toNat - 1
        have hn : k.toNat - 1 + 1 = k.toNat := Nat.sub_add_cancel h_k_nat_pos
        have h_succ : (k.toNat - 1).succ = k.toNat := hn
        have hF_eq : (A207672 k.toNat : ℤ) = F ((k.toNat : ℝ) / 5) := by
          have : (A207672 (k.toNat - 1 + 1) : ℤ) = F (((k.toNat - 1 + 1 : ℕ) : ℝ) / 5) := A_eq_F (k.toNat - 1)
          have h_cast : (k.toNat - 1 + 1) = k.toNat := hn
          rw [h_cast] at this
          exact this
        have hx_eq : x = (k.toNat : ℝ) / 5 := by
          have : x = (k:ℝ) / 5 := by linarith
          have h_k_nat : (k:ℝ) = (k.toNat : ℝ) := by exact_mod_cast hk_eq.symm
          rw [this, h_k_nat]
        rw [←hx_eq] at hF_eq
        have hA : (A207672 k.toNat : ℤ) = m := by rw [hF_eq, hFx]
        have hA_succ : A207672 (k.toNat - 1).succ = m := by
          rw [h_succ]
          exact_mod_cast hA
        exact hA_succ
      · left; right
        have hk_pos : k > 0 := by
          have h_xs : x * s > 0 := mul_pos hx_pos s_pos
          have hk_r : (k:ℝ) > 0 := by linarith
          have h_cast : ((k:ℤ):ℝ) > 0 := by linarith
          exact Int.cast_pos.mp h_cast
        have hk_eq : (k.toNat : ℤ) = k := Int.toNat_of_nonneg (le_of_lt hk_pos)
        have h_k_nat_pos : k.toNat > 0 := by
          have : k.toNat ≠ 0 := by
            intro hc
            have : k ≤ 0 := Int.toNat_eq_zero.mp hc
            linarith
          exact Nat.pos_of_ne_zero this
        use k.toNat - 1
        have hn : k.toNat - 1 + 1 = k.toNat := Nat.sub_add_cancel h_k_nat_pos
        have h_succ : (k.toNat - 1).succ = k.toNat := hn
        have hF_eq : (A207673 k.toNat : ℤ) = F ((k.toNat : ℝ) / s) := by
          have : (A207673 (k.toNat - 1 + 1) : ℤ) = F (((k.toNat - 1 + 1 : ℕ) : ℝ) / s) := B_eq_F (k.toNat - 1)
          have h_cast : (k.toNat - 1 + 1) = k.toNat := hn
          rw [h_cast] at this
          exact this
        have hx_eq : x = (k.toNat : ℝ) / s := by
          have : x = (x * s) / s := (mul_div_cancel_right₀ x (ne_of_gt s_pos)).symm
          have : x = (k:ℝ) / s := by rw [this, hk]
          have h_k_nat : (k:ℝ) = (k.toNat : ℝ) := by exact_mod_cast hk_eq.symm
          rw [this, h_k_nat]
        rw [←hx_eq] at hF_eq
        have hA : (A207673 k.toNat : ℤ) = m := by rw [hF_eq, hFx]
        have hA_succ : A207673 (k.toNat - 1).succ = m := by
          rw [h_succ]
          exact_mod_cast hA
        exact hA_succ
      · right
        have hk_pos : k > 0 := by
          have h_xt : x * t > 0 := mul_pos hx_pos t_pos
          have hk_r : (k:ℝ) > 0 := by linarith
          have h_cast : ((k:ℤ):ℝ) > 0 := by linarith
          exact Int.cast_pos.mp h_cast
        have hk_eq : (k.toNat : ℤ) = k := Int.toNat_of_nonneg (le_of_lt hk_pos)
        have h_k_nat_pos : k.toNat > 0 := by
          have : k.toNat ≠ 0 := by
            intro hc
            have : k ≤ 0 := Int.toNat_eq_zero.mp hc
            linarith
          exact Nat.pos_of_ne_zero this
        use k.toNat - 1
        have hn : k.toNat - 1 + 1 = k.toNat := Nat.sub_add_cancel h_k_nat_pos
        have h_succ : (k.toNat - 1).succ = k.toNat := hn
        have hF_eq : (A208326 k.toNat : ℤ) = F ((k.toNat : ℝ) / t) := by
          have : (A208326 (k.toNat - 1 + 1) : ℤ) = F (((k.toNat - 1 + 1 : ℕ) : ℝ) / t) := C_eq_F (k.toNat - 1)
          have h_cast : (k.toNat - 1 + 1) = k.toNat := hn
          rw [h_cast] at this
          exact this
        have hx_eq : x = (k.toNat : ℝ) / t := by
          have : x = (x * t) / t := (mul_div_cancel_right₀ x (ne_of_gt t_pos)).symm
          have : x = (k:ℝ) / t := by rw [this, hk]
          have h_k_nat : (k:ℝ) = (k.toNat : ℝ) := by exact_mod_cast hk_eq.symm
          rw [this, h_k_nat]
        rw [←hx_eq] at hF_eq
        have hA : (A208326 k.toNat : ℤ) = m := by rw [hF_eq, hFx]
        have hA_succ : A208326 (k.toNat - 1).succ = m := by
          rw [h_succ]
          exact_mod_cast hA
        exact hA_succ
    · intro hm
      cases hm with
      | inl h_inl =>
        cases h_inl with
        | inl hm1 =>
          rcases hm1 with ⟨n1, hn1⟩
          have : (A207672 (n1+1) : ℤ) = F (((n1+1:ℕ) : ℝ) / 5) := A_eq_F n1
          have hm_int : (m : ℤ) = F (((n1+1:ℕ) : ℝ) / 5) := by rw [←hn1, this]
          have h_lb : (((n1+1:ℕ) : ℝ) / 5) ≥ 1 / 5 := by
            have : ((n1+1:ℕ):ℝ) ≥ 1 := by exact_mod_cast (Nat.le_add_left 1 n1)
            linarith
          have h_m_pos : (m : ℤ) > 0 := by
            rw [hm_int]
            exact F_pos_of_ge_15 (((n1+1:ℕ):ℝ) / 5) h_lb
          exact_mod_cast h_m_pos
        | inr hm2 =>
          rcases hm2 with ⟨n2, hn2⟩
          have : (A207673 (n2+1) : ℤ) = F (((n2+1:ℕ) : ℝ) / s) := B_eq_F n2
          have hm_int : (m : ℤ) = F (((n2+1:ℕ) : ℝ) / s) := by rw [←hn2, this]
          have h_lb : (((n2+1:ℕ) : ℝ) / s) ≥ 1 / s := by
            have h1 : ((n2+1:ℕ):ℝ) ≥ 1 := by exact_mod_cast (Nat.le_add_left 1 n2)
            have hp : s > 0 := s_pos
            exact div_le_div_of_nonneg_right h1 (le_of_lt hp)
          have h_m_pos : (m : ℤ) > 0 := by
            rw [hm_int]
            exact F_pos_of_ge_1s (((n2+1:ℕ):ℝ) / s) h_lb
          exact_mod_cast h_m_pos
      | inr hm3 =>
        rcases hm3 with ⟨n3, hn3⟩
        have : (A208326 (n3+1) : ℤ) = F (((n3+1:ℕ) : ℝ) / t) := C_eq_F n3
        have hm_int : (m : ℤ) = F (((n3+1:ℕ) : ℝ) / t) := by rw [←hn3, this]
        have h_lb : (((n3+1:ℕ) : ℝ) / t) ≥ 1 / t := by
          have h1 : ((n3+1:ℕ):ℝ) ≥ 1 := by exact_mod_cast (Nat.le_add_left 1 n3)
          have hp : t > 0 := t_pos
          exact div_le_div_of_nonneg_right h1 (le_of_lt hp)
        have h_m_pos : (m : ℤ) > 0 := by
          rw [hm_int]
          exact F_pos_of_ge_1t (((n3+1:ℕ):ℝ) / t) h_lb
        exact_mod_cast h_m_pos
  · constructor
    · ext m
      simp only [Set.mem_empty_iff_false, Set.mem_inter_iff, iff_false, Set.mem_range, Function.comp_apply]
      intro hm
      rcases hm with ⟨⟨n1, hn1⟩, ⟨n2, hn2⟩⟩
      have eq1 : (m:ℤ) = F (((n1+1:ℕ):ℝ) / 5) := by rw [←hn1, A_eq_F]
      have eq2 : (m:ℤ) = F (((n2+1:ℕ):ℝ) / s) := by rw [←hn2, B_eq_F]
      have h_eq : F (((n1+1:ℕ):ℝ) / 5) = F (((n2+1:ℕ):ℝ) / s) := by rw [←eq1, eq2]
      have h1S : (∃ k:ℤ, (((n1+1:ℕ):ℝ) / 5) * 5 = (k:ℝ)) ∨ (∃ k:ℤ, (((n1+1:ℕ):ℝ) / 5) * s = (k:ℝ)) ∨ (∃ k:ℤ, (((n1+1:ℕ):ℝ) / 5) * t = (k:ℝ)) := Or.inl ⟨n1+1, by push_cast; ring⟩
      have h2S : (∃ k:ℤ, (((n2+1:ℕ):ℝ) / s) * 5 = (k:ℝ)) ∨ (∃ k:ℤ, (((n2+1:ℕ):ℝ) / s) * s = (k:ℝ)) ∨ (∃ k:ℤ, (((n2+1:ℕ):ℝ) / s) * t = (k:ℝ)) := Or.inr (Or.inl ⟨n2+1, by have h_s_neq : s ≠ 0 := ne_of_gt s_pos; have : (((n2+1:ℕ):ℝ) / s) * s = ((n2+1:ℕ):ℝ) := div_mul_cancel₀ _ h_s_neq; rw [this]; exact_mod_cast rfl⟩)
      have h1_pos : (((n1+1:ℕ):ℝ) / 5) > 0 := div_pos (by exact_mod_cast Nat.zero_lt_succ n1) (by norm_num)
      have h2_pos : (((n2+1:ℕ):ℝ) / s) > 0 := div_pos (by exact_mod_cast Nat.zero_lt_succ n2) s_pos
      have h_x_eq : (((n1+1:ℕ):ℝ) / 5) = (((n2+1:ℕ):ℝ) / s) := F_injective_on_S _ _ h1_pos h2_pos h1S h2S h_eq
      have h_s_rat : s = (((n2+1:ℕ):ℝ) * 5) / ((n1+1:ℕ):ℝ) := by
        calc s = (((n2+1:ℕ):ℝ) / (((n2+1:ℕ):ℝ) / s)) := by
               have hn_pos : ((n2+1:ℕ):ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n2
               have h_s : s = (((n2+1:ℕ):ℝ) * s) / ((n2+1:ℕ):ℝ) := by
                 calc s = (s * ((n2+1:ℕ):ℝ)) / ((n2+1:ℕ):ℝ) := (mul_div_cancel_right₀ s hn_pos).symm
                      _ = (((n2+1:ℕ):ℝ) * s) / ((n2+1:ℕ):ℝ) := by ring
               have h_div : (((n2+1:ℕ):ℝ) / (((n2+1:ℕ):ℝ) / s)) = (((n2+1:ℕ):ℝ) * s) / ((n2+1:ℕ):ℝ) := (div_div_eq_mul_div _ _ _)
               exact Eq.trans h_s h_div.symm
             _ = (((n2+1:ℕ):ℝ) / (((n1+1:ℕ):ℝ) / 5)) := by rw [←h_x_eq]
             _ = (((n2+1:ℕ):ℝ) * 5) / ((n1+1:ℕ):ℝ) := by ring
      have h_cast : s = ( ((n2+1:ℤ) * 5 : ℤ) : ℝ) / ((n1+1:ℤ):ℝ) := by
        have h1 : ( ((n2+1:ℤ) * 5 : ℤ) : ℝ) = (((n2+1:ℕ):ℝ) * 5) := by push_cast; rfl
        have h2 : ((n1+1:ℤ):ℝ) = ((n1+1:ℕ):ℝ) := by push_cast; rfl
        rw [h1, h2]
        exact h_s_rat
      exact irrational_of_eq_div s irr_s ((n2+1:ℤ)*5) (n1+1:ℤ) h_cast
    · constructor
      · ext m
        simp only [Set.mem_empty_iff_false, Set.mem_inter_iff, iff_false, Set.mem_range, Function.comp_apply]
        intro hm
        rcases hm with ⟨⟨n1, hn1⟩, ⟨n3, hn3⟩⟩
        have eq1 : (m:ℤ) = F (((n1+1:ℕ):ℝ) / 5) := by rw [←hn1, A_eq_F]
        have eq3 : (m:ℤ) = F (((n3+1:ℕ):ℝ) / t) := by rw [←hn3, C_eq_F]
        have h_eq : F (((n1+1:ℕ):ℝ) / 5) = F (((n3+1:ℕ):ℝ) / t) := by rw [←eq1, eq3]
        have h1S : (∃ k:ℤ, (((n1+1:ℕ):ℝ) / 5) * 5 = (k:ℝ)) ∨ (∃ k:ℤ, (((n1+1:ℕ):ℝ) / 5) * s = (k:ℝ)) ∨ (∃ k:ℤ, (((n1+1:ℕ):ℝ) / 5) * t = (k:ℝ)) := Or.inl ⟨n1+1, by push_cast; ring⟩
        have h3S : (∃ k:ℤ, (((n3+1:ℕ):ℝ) / t) * 5 = (k:ℝ)) ∨ (∃ k:ℤ, (((n3+1:ℕ):ℝ) / t) * s = (k:ℝ)) ∨ (∃ k:ℤ, (((n3+1:ℕ):ℝ) / t) * t = (k:ℝ)) := Or.inr (Or.inr ⟨n3+1, by have h_t_neq : t ≠ 0 := ne_of_gt t_pos; have : (((n3+1:ℕ):ℝ) / t) * t = ((n3+1:ℕ):ℝ) := div_mul_cancel₀ _ h_t_neq; rw [this]; exact_mod_cast rfl⟩)
        have h1_pos : (((n1+1:ℕ):ℝ) / 5) > 0 := div_pos (by exact_mod_cast Nat.zero_lt_succ n1) (by norm_num)
        have h3_pos : (((n3+1:ℕ):ℝ) / t) > 0 := div_pos (by exact_mod_cast Nat.zero_lt_succ n3) t_pos
        have h_x_eq : (((n1+1:ℕ):ℝ) / 5) = (((n3+1:ℕ):ℝ) / t) := F_injective_on_S _ _ h1_pos h3_pos h1S h3S h_eq
        have hn1_neq : ((n1+1:ℕ):ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n1
        have hn3_neq : ((n3+1:ℕ):ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n3
        have ht_neq : t ≠ 0 := ne_of_gt t_pos
        have h_t_rat : t = (((n3+1:ℕ):ℝ) * 5) / ((n1+1:ℕ):ℝ) := by
          calc t = (((n3+1:ℕ):ℝ) / (((n1+1:ℕ):ℝ) / 5)) := by
                 have h1 : (((n1+1:ℕ):ℝ) / 5) * t = ((n3+1:ℕ):ℝ) := by
                   rw [h_x_eq, div_mul_cancel₀ _ ht_neq]
                 have h2 : t = ((n3+1:ℕ):ℝ) / (((n1+1:ℕ):ℝ) / 5) := by
                   rw [← h1, mul_comm, mul_div_cancel_right₀ t (by intro hc; rw [hc, zero_mul] at h1; exact hn3_neq h1.symm)]
                 exact h2
               _ = (((n3+1:ℕ):ℝ) * 5) / ((n1+1:ℕ):ℝ) := by
                 rw [div_div_eq_mul_div]
        have hs : s = ((n1+1:ℕ):ℝ) / (((n3+1:ℕ):ℝ) * 5) := by
          dsimp [t] at h_t_rat
          have hinv : (1 / s)⁻¹ = ((((n3+1:ℕ):ℝ) * 5) / ((n1+1:ℕ):ℝ))⁻¹ := by rw [h_t_rat]
          have h1 : (1 / s)⁻¹ = s := by
             rw [inv_eq_one_div (1/s), one_div_one_div]
          rw [h1] at hinv
          rw [hinv]
          exact inv_div _ _
        have h_cast : s = ((n1+1:ℤ):ℝ) / ( ((n3+1:ℤ) * 5 : ℤ) : ℝ) := by
          have h1 : ((n1+1:ℤ):ℝ) = ((n1+1:ℕ):ℝ) := by push_cast; rfl
          have h2 : ( ((n3+1:ℤ) * 5 : ℤ) : ℝ) = (((n3+1:ℕ):ℝ) * 5) := by push_cast; rfl
          rw [h1, h2]
          exact hs
        exact irrational_of_eq_div s irr_s (n1+1:ℤ) ((n3+1:ℤ)*5) h_cast
      · ext m
        simp only [Set.mem_empty_iff_false, Set.mem_inter_iff, iff_false, Set.mem_range, Function.comp_apply]
        intro hm
        rcases hm with ⟨⟨n2, hn2⟩, ⟨n3, hn3⟩⟩
        have eq2 : (m:ℤ) = F (((n2+1:ℕ):ℝ) / s) := by rw [←hn2, B_eq_F]
        have eq3 : (m:ℤ) = F (((n3+1:ℕ):ℝ) / t) := by rw [←hn3, C_eq_F]
        have h_eq : F (((n2+1:ℕ):ℝ) / s) = F (((n3+1:ℕ):ℝ) / t) := by rw [←eq2, eq3]
        have h2S : (∃ k:ℤ, (((n2+1:ℕ):ℝ) / s) * 5 = (k:ℝ)) ∨ (∃ k:ℤ, (((n2+1:ℕ):ℝ) / s) * s = (k:ℝ)) ∨ (∃ k:ℤ, (((n2+1:ℕ):ℝ) / s) * t = (k:ℝ)) := Or.inr (Or.inl ⟨n2+1, by have h_s_neq : s ≠ 0 := ne_of_gt s_pos; have : (((n2+1:ℕ):ℝ) / s) * s = ((n2+1:ℕ):ℝ) := div_mul_cancel₀ _ h_s_neq; rw [this]; exact_mod_cast rfl⟩)
        have h3S : (∃ k:ℤ, (((n3+1:ℕ):ℝ) / t) * 5 = (k:ℝ)) ∨ (∃ k:ℤ, (((n3+1:ℕ):ℝ) / t) * s = (k:ℝ)) ∨ (∃ k:ℤ, (((n3+1:ℕ):ℝ) / t) * t = (k:ℝ)) := Or.inr (Or.inr ⟨n3+1, by have h_t_neq : t ≠ 0 := ne_of_gt t_pos; have : (((n3+1:ℕ):ℝ) / t) * t = ((n3+1:ℕ):ℝ) := div_mul_cancel₀ _ h_t_neq; rw [this]; exact_mod_cast rfl⟩)
        have h2_pos : (((n2+1:ℕ):ℝ) / s) > 0 := div_pos (by exact_mod_cast Nat.zero_lt_succ n2) s_pos
        have h3_pos : (((n3+1:ℕ):ℝ) / t) > 0 := div_pos (by exact_mod_cast Nat.zero_lt_succ n3) t_pos
        have h_x_eq : (((n2+1:ℕ):ℝ) / s) = (((n3+1:ℕ):ℝ) / t) := F_injective_on_S _ _ h2_pos h3_pos h2S h3S h_eq
        have hs_rat : s = (((n2+1:ℕ):ℝ) - ((n3+1:ℕ):ℝ)) / ((n3+1:ℕ):ℝ) := by
          have hn3_neq : ((n3+1:ℕ):ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n3
          have ht_def : t = 1 / s := rfl
          have hs_neq : s ≠ 0 := ne_of_gt s_pos
          have ht_neq : t ≠ 0 := by
            rw [ht_def, one_div]
            exact inv_ne_zero hs_neq
          have h1 : ((n2+1:ℕ):ℝ) * t = ((n3+1:ℕ):ℝ) * s := by
            calc ((n2+1:ℕ):ℝ) * t = (((n2+1:ℕ):ℝ) / s) * s * t := by rw [div_mul_cancel₀ _ hs_neq]
                 _ = (((n3+1:ℕ):ℝ) / t) * s * t := by rw [h_x_eq]
                 _ = ((n3+1:ℕ):ℝ) / t * t * s := by ring
                 _ = ((n3+1:ℕ):ℝ) * s := by rw [div_mul_cancel₀ _ ht_neq]
          have h2 : ((n2+1:ℕ):ℝ) / s = ((n3+1:ℕ):ℝ) * s := by
            calc ((n2+1:ℕ):ℝ) / s = ((n2+1:ℕ):ℝ) * (1 / s) := by exact div_eq_mul_one_div ((n2+1:ℕ):ℝ) s
                 _ = ((n2+1:ℕ):ℝ) * t := by rw [← ht_def]
                 _ = ((n3+1:ℕ):ℝ) * s := h1
          have hs2 : s^2 = s + 1 := goldenRatio_sq
          have h3 : ((n2+1:ℕ):ℝ) = ((n3+1:ℕ):ℝ) * s^2 := by
            calc ((n2+1:ℕ):ℝ) = (((n2+1:ℕ):ℝ) / s) * s := by rw [div_mul_cancel₀ _ hs_neq]
                 _ = ((n3+1:ℕ):ℝ) * s * s := by rw [h2]
                 _ = ((n3+1:ℕ):ℝ) * s^2 := by ring
          have h4 : ((n2+1:ℕ):ℝ) = ((n3+1:ℕ):ℝ) * (s + 1) := by
            rw [hs2] at h3
            exact h3
          have h5 : ((n2+1:ℕ):ℝ) = ((n3+1:ℕ):ℝ) * s + ((n3+1:ℕ):ℝ) := by
            calc ((n2+1:ℕ):ℝ) = ((n3+1:ℕ):ℝ) * (s + 1) := h4
                 _ = ((n3+1:ℕ):ℝ) * s + ((n3+1:ℕ):ℝ) := by ring
          have h6 : ((n3+1:ℕ):ℝ) * s = ((n2+1:ℕ):ℝ) - ((n3+1:ℕ):ℝ) := by
            calc ((n3+1:ℕ):ℝ) * s = ((n3+1:ℕ):ℝ) * s + ((n3+1:ℕ):ℝ) - ((n3+1:ℕ):ℝ) := by ring
                 _ = ((n2+1:ℕ):ℝ) - ((n3+1:ℕ):ℝ) := by rw [← h5]
          calc s = ((n3+1:ℕ):ℝ) * s / ((n3+1:ℕ):ℝ) := by rw [mul_comm, mul_div_cancel_right₀ _ hn3_neq]
               _ = (((n2+1:ℕ):ℝ) - ((n3+1:ℕ):ℝ)) / ((n3+1:ℕ):ℝ) := by rw [h6]
        have h_cast : s = (((n2+1:ℤ) - (n3+1:ℤ) : ℤ) : ℝ) / ((n3+1:ℤ):ℝ) := by
          have h1 : (((n2+1:ℤ) - (n3+1:ℤ) : ℤ) : ℝ) = ((n2+1:ℕ):ℝ) - ((n3+1:ℕ):ℝ) := by push_cast; rfl
          have h2 : ((n3+1:ℤ):ℝ) = ((n3+1:ℕ):ℝ) := by push_cast; rfl
          rw [h1, h2]
          exact hs_rat
        exact irrational_of_eq_div s irr_s ((n2+1:ℤ) - (n3+1:ℤ)) (n3+1:ℤ) h_cast

theorem oeis_208326_conjecture_0.disproof : ¬ (type_of% @oeis_208326_conjecture_0) := by
  sorry