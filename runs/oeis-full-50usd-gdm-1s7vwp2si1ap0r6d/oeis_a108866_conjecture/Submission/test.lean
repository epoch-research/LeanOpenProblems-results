import FormalConjectures.Util.ProblemImports

lemma prime_coprime_pow {p : ℕ} (hp : p.Prime) {a : ℕ} (ha_pos : a > 0) (ha_lt : a < p) :
    Nat.Coprime a (p^2) := by
  have hp_cop : Nat.Coprime a p := Nat.Coprime.symm (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt ha_pos ha_lt))
  exact Nat.Coprime.pow_right 2 hp_cop

lemma wolstenholme_inv {p : ℕ} (hp : p.Prime) (hp3 : p > 3) :
    Finset.sum (Finset.range (p - 1)) (fun i => (i + 1 : ZMod (p^2))⁻¹) =
    Finset.sum (Finset.range (p - 1)) (fun i => (p - 1 - i : ZMod (p^2))⁻¹) := by
  have h_sum := Finset.sum_range_reflect (fun i => (i + 1 : ZMod (p^2))⁻¹) (p - 1)
  have h_sub : p - 1 - 1 = p - 2 := by omega
  rw [h_sub] at h_sum
  rw [← h_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  have h_eq : p - 2 - i + 1 = p - 1 - i := by omega
  have h_cast : ( (p - 2 - i + 1 : ℕ) : ZMod (p^2) ) = ( (p - 1 - i : ℕ) : ZMod (p^2) ) := by congr 1
  push_cast at h_cast
  rw [h_cast]
  have h_push : ((p - 1 - i : ℕ) : ZMod (p^2)) = (p : ZMod (p^2)) - 1 - i := by
    have h_nat : p - 1 - i + (i + 1) = p := by omega
    have h_cast2 : (((p - 1 - i + (i + 1) : ℕ) : ZMod (p^2))) = ((p : ℕ) : ZMod (p^2)) := by congr 1
    push_cast at h_cast2
    calc ((p - 1 - i : ℕ) : ZMod (p^2)) = ((p - 1 - i : ℕ) : ZMod (p^2)) + (i + 1 : ZMod (p^2)) - 1 - i := by ring
      _ = (p : ZMod (p^2)) - 1 - i := by rw [h_cast2]
  rw [h_push]

lemma wolstenholme_inv_sum {p : ℕ} (hp : p.Prime) (hp3 : p > 3) :
    2 * Finset.sum (Finset.range (p - 1)) (fun i => (i + 1 : ZMod (p^2))⁻¹) =
    Finset.sum (Finset.range (p - 1)) (fun i => (p : ZMod (p^2)) * (i + 1 : ZMod (p^2))⁻¹ * (p - 1 - i : ZMod (p^2))⁻¹) := by
  have h_two_S : 2 * Finset.sum (Finset.range (p - 1)) (fun i => (i + 1 : ZMod (p^2))⁻¹) =
      Finset.sum (Finset.range (p - 1)) (fun i => (i + 1 : ZMod (p^2))⁻¹ + (p - 1 - i : ZMod (p^2))⁻¹) := by
    calc 2 * Finset.sum (Finset.range (p - 1)) (fun i => (i + 1 : ZMod (p^2))⁻¹)
      _ = Finset.sum (Finset.range (p - 1)) (fun i => (i + 1 : ZMod (p^2))⁻¹) + Finset.sum (Finset.range (p - 1)) (fun i => (i + 1 : ZMod (p^2))⁻¹) := by ring
      _ = Finset.sum (Finset.range (p - 1)) (fun i => (i + 1 : ZMod (p^2))⁻¹) + Finset.sum (Finset.range (p - 1)) (fun i => (p - 1 - i : ZMod (p^2))⁻¹) := by rw [wolstenholme_inv hp hp3]
      _ = Finset.sum (Finset.range (p - 1)) (fun i => (i + 1 : ZMod (p^2))⁻¹ + (p - 1 - i : ZMod (p^2))⁻¹) := by rw [← Finset.sum_add_distrib]
  rw [h_two_S]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  have h_push : (p : ZMod (p^2)) - 1 - i = ((p - 1 - i : ℕ) : ZMod (p^2)) := by
    have h_nat : p - 1 - i + (i + 1) = p := by omega
    have h_cast2 : (((p - 1 - i + (i + 1) : ℕ) : ZMod (p^2))) = ((p : ℕ) : ZMod (p^2)) := by congr 1
    push_cast at h_cast2
    calc (p : ZMod (p^2)) - 1 - i = ((p - 1 - i : ℕ) : ZMod (p^2)) + (i + 1 : ZMod (p^2)) - 1 - i := by rw [h_cast2]
      _ = ((p - 1 - i : ℕ) : ZMod (p^2)) := by ring
  have h_push_inv : (p - 1 - i : ZMod (p^2))⁻¹ = (((p - 1 - i : ℕ) : ZMod (p^2)))⁻¹ := by
    rw [h_push]
  rw [h_push_inv]
  have h_unit_A : IsUnit (i + 1 : ZMod (p^2)) := by
    have : (i + 1 : ZMod (p^2)) = ((i + 1 : ℕ) : ZMod (p^2)) := by push_cast; rfl
    rw [this]
    rw [ZMod.isUnit_iff_coprime]
    exact prime_coprime_pow hp (Nat.succ_pos i) (by omega)
  have h_unit_B : IsUnit ((p - 1 - i : ℕ) : ZMod (p^2)) := by
    rw [ZMod.isUnit_iff_coprime]
    apply prime_coprime_pow hp
    · omega
    · omega
  have h_inv : (i + 1 : ZMod (p^2))⁻¹ + (((p - 1 - i : ℕ) : ZMod (p^2)))⁻¹ =
      (i + 1 + ((p - 1 - i : ℕ) : ZMod (p^2))) * (i + 1 : ZMod (p^2))⁻¹ * (((p - 1 - i : ℕ) : ZMod (p^2)))⁻¹ := by
    have h1 : (i + 1 : ZMod (p^2)) * (i + 1 : ZMod (p^2))⁻¹ = 1 := ZMod.mul_inv_of_unit (i + 1 : ZMod (p^2)) h_unit_A
    have h2 : ((p - 1 - i : ℕ) : ZMod (p^2)) * (((p - 1 - i : ℕ) : ZMod (p^2)))⁻¹ = 1 := ZMod.mul_inv_of_unit (((p - 1 - i : ℕ) : ZMod (p^2))) h_unit_B
    have h_rhs : (i + 1 + ((p - 1 - i : ℕ) : ZMod (p^2))) * (i + 1 : ZMod (p^2))⁻¹ * (((p - 1 - i : ℕ) : ZMod (p^2)))⁻¹ =
        ((i + 1 : ZMod (p^2)) * (i + 1 : ZMod (p^2))⁻¹) * (((p - 1 - i : ℕ) : ZMod (p^2)))⁻¹ +
        (((p - 1 - i : ℕ) : ZMod (p^2)) * (((p - 1 - i : ℕ) : ZMod (p^2)))⁻¹) * (i + 1 : ZMod (p^2))⁻¹ := by ring
    rw [h_rhs, h1, h2]
    ring
  rw [h_inv]
  congr 2
  have h_nat : i + 1 + (p - 1 - i) = p := by omega
  have h_cast : (((i + 1 + (p - 1 - i) : ℕ) : ZMod (p^2))) = ((p : ℕ) : ZMod (p^2)) := by congr 1
  push_cast at h_cast
  exact h_cast


lemma p_mul_inv_eq_neg_p_mul_inv {p : ℕ} (hp : p.Prime) (i : ℕ) (hi : i < p - 1) :
    (p : ZMod (p^2)) * (p - 1 - i : ZMod (p^2))⁻¹ = - (p : ZMod (p^2)) * (i + 1 : ZMod (p^2))⁻¹ := by
  have h_unit_A : IsUnit (i + 1 : ZMod (p^2)) := by
    have : (i + 1 : ZMod (p^2)) = ((i + 1 : ℕ) : ZMod (p^2)) := by push_cast; rfl
    rw [this]
    rw [ZMod.isUnit_iff_coprime]
    exact prime_coprime_pow hp (Nat.succ_pos i) (by omega)
  have h_unit_B : IsUnit ((p - 1 - i : ℕ) : ZMod (p^2)) := by
    rw [ZMod.isUnit_iff_coprime]
    apply prime_coprime_pow hp
    · omega
    · omega
  have h_add : (i + 1 : ZMod (p^2))⁻¹ + (((p - 1 - i : ℕ) : ZMod (p^2)))⁻¹ =
      (i + 1 + ((p - 1 - i : ℕ) : ZMod (p^2))) * (i + 1 : ZMod (p^2))⁻¹ * (((p - 1 - i : ℕ) : ZMod (p^2)))⁻¹ := by
    have h1 : (i + 1 : ZMod (p^2)) * (i + 1 : ZMod (p^2))⁻¹ = 1 := ZMod.mul_inv_of_unit (i + 1 : ZMod (p^2)) h_unit_A
    have h2 : ((p - 1 - i : ℕ) : ZMod (p^2)) * (((p - 1 - i : ℕ) : ZMod (p^2)))⁻¹ = 1 := ZMod.mul_inv_of_unit (((p - 1 - i : ℕ) : ZMod (p^2))) h_unit_B
    have h_rhs : (i + 1 + ((p - 1 - i : ℕ) : ZMod (p^2))) * (i + 1 : ZMod (p^2))⁻¹ * (((p - 1 - i : ℕ) : ZMod (p^2)))⁻¹ =
        ((i + 1 : ZMod (p^2)) * (i + 1 : ZMod (p^2))⁻¹) * (((p - 1 - i : ℕ) : ZMod (p^2)))⁻¹ +
        (((p - 1 - i : ℕ) : ZMod (p^2)) * (((p - 1 - i : ℕ) : ZMod (p^2)))⁻¹) * (i + 1 : ZMod (p^2))⁻¹ := by ring
    rw [h_rhs, h1, h2]
    ring
  have h_push : (p : ZMod (p^2)) - 1 - i = ((p - 1 - i : ℕ) : ZMod (p^2)) := by
    have h_nat : p - 1 - i + (i + 1) = p := by omega
    have h_cast2 : (((p - 1 - i + (i + 1) : ℕ) : ZMod (p^2))) = ((p : ℕ) : ZMod (p^2)) := by congr 1
    push_cast at h_cast2
    calc (p : ZMod (p^2)) - 1 - i = ((p - 1 - i : ℕ) : ZMod (p^2)) + (i + 1 : ZMod (p^2)) - 1 - i := by rw [h_cast2]
      _ = ((p - 1 - i : ℕ) : ZMod (p^2)) := by ring
  have h_push_inv : (p - 1 - i : ZMod (p^2))⁻¹ = (((p - 1 - i : ℕ) : ZMod (p^2)))⁻¹ := by
    rw [h_push]
  have h_p2 : (p : ZMod (p^2)) * (p : ZMod (p^2)) = 0 := by
    have : (p : ZMod (p^2)) * (p : ZMod (p^2)) = ((p^2 : ℕ) : ZMod (p^2)) := by push_cast; ring
    rw [this, ZMod.natCast_self]
  have h_mul_zero : (p : ZMod (p^2)) * (i + 1 + ((p - 1 - i : ℕ) : ZMod (p^2))) = (p : ZMod (p^2)) * (p : ZMod (p^2)) := by
    congr 1
    have h_nat : i + 1 + (p - 1 - i) = p := by omega
    have h_cast : (((i + 1 + (p - 1 - i) : ℕ) : ZMod (p^2))) = ((p : ℕ) : ZMod (p^2)) := by congr 1
    push_cast at h_cast
    exact h_cast
  have h_sum_zero : (p : ZMod (p^2)) * (((p - 1 - i : ℕ) : ZMod (p^2)))⁻¹ + (p : ZMod (p^2)) * (i + 1 : ZMod (p^2))⁻¹ = 0 := by
    calc (p : ZMod (p^2)) * (((p - 1 - i : ℕ) : ZMod (p^2)))⁻¹ + (p : ZMod (p^2)) * (i + 1 : ZMod (p^2))⁻¹
      _ = (p : ZMod (p^2)) * ((i + 1 : ZMod (p^2))⁻¹ + (((p - 1 - i : ℕ) : ZMod (p^2)))⁻¹) := by ring
      _ = (p : ZMod (p^2)) * ((i + 1 + ((p - 1 - i : ℕ) : ZMod (p^2))) * (i + 1 : ZMod (p^2))⁻¹ * (((p - 1 - i : ℕ) : ZMod (p^2)))⁻¹) := by rw [h_add]
      _ = ((p : ZMod (p^2)) * (i + 1 + ((p - 1 - i : ℕ) : ZMod (p^2)))) * (i + 1 : ZMod (p^2))⁻¹ * (((p - 1 - i : ℕ) : ZMod (p^2)))⁻¹ := by ring
      _ = ((p : ZMod (p^2)) * (p : ZMod (p^2))) * (i + 1 : ZMod (p^2))⁻¹ * (((p - 1 - i : ℕ) : ZMod (p^2)))⁻¹ := by rw [h_mul_zero]
      _ = 0 := by rw [h_p2, zero_mul, zero_mul]
  rw [h_push_inv]
  calc (p : ZMod (p^2)) * (((p - 1 - i : ℕ) : ZMod (p^2)))⁻¹
    _ = (p : ZMod (p^2)) * (((p - 1 - i : ℕ) : ZMod (p^2)))⁻¹ + (p : ZMod (p^2)) * (i + 1 : ZMod (p^2))⁻¹ - (p : ZMod (p^2)) * (i + 1 : ZMod (p^2))⁻¹ := by ring
    _ = 0 - (p : ZMod (p^2)) * (i + 1 : ZMod (p^2))⁻¹ := by rw [h_sum_zero]
    _ = - (p : ZMod (p^2)) * (i + 1 : ZMod (p^2))⁻¹ := by ring


lemma sum_sq_eq_sum_four_mul_sq {p : ℕ} (hp : p.Prime) (hp3 : p > 3) :
    Finset.sum (Finset.range (p - 1)) (fun i => (i + 1 : ZMod p)^2) =
    Finset.sum (Finset.range (p - 1)) (fun i => (2 * (i + 1 : ZMod p))^2) := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  refine @Finset.sum_bij ℕ ℕ (ZMod p) _ (Finset.range (p - 1)) (Finset.range (p - 1))
    (fun i => (i + 1 : ZMod p)^2) (fun i => (2 * (i + 1 : ZMod p))^2)
    (fun i _ => (2⁻¹ * (i + 1 : ZMod p)).val - 1) ?subgoal1 ?subgoal2 ?subgoal3 ?subgoal4
  · -- subgoal1
    intro i hi
    simp only [Finset.mem_range] at hi
    have h_lt : i + 1 < p := by omega
    have h_pos : i + 1 > 0 := by omega
    have h_unit_two : IsUnit (2 : ZMod p) := by
      have : (2 : ZMod p) = ((2 : ℕ) : ZMod p) := by push_cast; rfl
      rw [this]
      rw [ZMod.isUnit_iff_coprime]
      have h_not_dvd : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
      exact Nat.Coprime.symm (hp.coprime_iff_not_dvd.mpr h_not_dvd)
    have h_unit_A : IsUnit (i + 1 : ZMod p) := by
      have h_eq : (i + 1 : ZMod p) = ((i + 1 : ℕ) : ZMod p) := by push_cast; rfl
      rw [h_eq]
      rw [ZMod.isUnit_iff_coprime]
      exact (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt h_pos h_lt)).symm
    have h_unit : IsUnit (2⁻¹ * (i + 1 : ZMod p)) := IsUnit.mul (IsUnit.inv h_unit_two) h_unit_A
    have h_val_lt : (2⁻¹ * (i + 1 : ZMod p)).val < p := ZMod.val_lt _
    have h_val_pos : (2⁻¹ * (i + 1 : ZMod p)).val > 0 := by
      have h_zero : (2⁻¹ * (i + 1 : ZMod p)).val ≠ 0 := by
        intro h_z
        rw [ZMod.val_eq_zero] at h_z
        exact IsUnit.ne_zero h_unit h_z
      omega
    simp only [Finset.mem_range]
    omega
  · -- subgoal2
    intro i hi j hj h_eq
    simp only [Finset.mem_range] at hi hj
    dsimp only at h_eq
    have h_lt_i : i + 1 < p := by omega
    have h_pos_i : i + 1 > 0 := by omega
    have h_lt_j : j + 1 < p := by omega
    have h_pos_j : j + 1 > 0 := by omega
    have h_unit_two : IsUnit (2 : ZMod p) := by
      have : (2 : ZMod p) = ((2 : ℕ) : ZMod p) := by push_cast; rfl
      rw [this]
      rw [ZMod.isUnit_iff_coprime]
      have h_not_dvd : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
      exact Nat.Coprime.symm (hp.coprime_iff_not_dvd.mpr h_not_dvd)
    have h_unit_A : IsUnit (i + 1 : ZMod p) := by
      have h_eq : (i + 1 : ZMod p) = ((i + 1 : ℕ) : ZMod p) := by push_cast; rfl
      rw [h_eq]
      rw [ZMod.isUnit_iff_coprime]
      exact (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt h_pos_i h_lt_i)).symm
    have h_unit_Bi : IsUnit (2⁻¹ * (i + 1 : ZMod p)) := IsUnit.mul (IsUnit.inv h_unit_two) h_unit_A
    have h_pos_i_val : (2⁻¹ * (i + 1 : ZMod p)).val > 0 := by
      have h_zero : (2⁻¹ * (i + 1 : ZMod p)).val ≠ 0 := by
        intro h_z
        rw [ZMod.val_eq_zero] at h_z
        exact IsUnit.ne_zero h_unit_Bi h_z
      omega
    have h_unit_B : IsUnit (j + 1 : ZMod p) := by
      have h_eq : (j + 1 : ZMod p) = ((j + 1 : ℕ) : ZMod p) := by push_cast; rfl
      rw [h_eq]
      rw [ZMod.isUnit_iff_coprime]
      exact (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt h_pos_j h_lt_j)).symm
    have h_unit_Bj : IsUnit (2⁻¹ * (j + 1 : ZMod p)) := IsUnit.mul (IsUnit.inv h_unit_two) h_unit_B
    have h_pos_j_val : (2⁻¹ * (j + 1 : ZMod p)).val > 0 := by
      have h_zero : (2⁻¹ * (j + 1 : ZMod p)).val ≠ 0 := by
        intro h_z
        rw [ZMod.val_eq_zero] at h_z
        exact IsUnit.ne_zero h_unit_Bj h_z
      omega
    have h_val_i : (i + 1 : ZMod p).val = i + 1 := by
      have h_eq : (i + 1 : ZMod p) = ((i + 1 : ℕ) : ZMod p) := by push_cast; rfl
      rw [h_eq]
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt h_lt_i]
    have h_val_j : (j + 1 : ZMod p).val = j + 1 := by
      have h_eq : (j + 1 : ZMod p) = ((j + 1 : ℕ) : ZMod p) := by push_cast; rfl
      rw [h_eq]
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt h_lt_j]
    have h_val_eq : (2⁻¹ * (i + 1 : ZMod p)).val = (2⁻¹ * (j + 1 : ZMod p)).val := by omega
    have h_zmod_eq : 2⁻¹ * (i + 1 : ZMod p) = 2⁻¹ * (j + 1 : ZMod p) := by
      have h1 : ( (2⁻¹ * (i + 1 : ZMod p)).val : ZMod p ) = 2⁻¹ * (i + 1 : ZMod p) := ZMod.natCast_zmod_val _
      have h2 : ( (2⁻¹ * (j + 1 : ZMod p)).val : ZMod p ) = 2⁻¹ * (j + 1 : ZMod p) := ZMod.natCast_zmod_val _
      rw [← h1, ← h2, h_val_eq]
    have h_eq_base : (i + 1 : ZMod p) = (j + 1 : ZMod p) := (IsUnit.mul_right_inj (IsUnit.inv h_unit_two)).mp h_zmod_eq
    have h_val_base : (i + 1 : ZMod p).val = (j + 1 : ZMod p).val := congrArg ZMod.val h_eq_base
    rw [h_val_i, h_val_j] at h_val_base
    omega
  · -- subgoal3
    intro b hb
    simp only [Finset.mem_range] at hb
    have h_lt_b : b + 1 < p := by omega
    have h_pos_b : b + 1 > 0 := by omega
    have h_unit_two : IsUnit (2 : ZMod p) := by
      have : (2 : ZMod p) = ((2 : ℕ) : ZMod p) := by push_cast; rfl
      rw [this]
      rw [ZMod.isUnit_iff_coprime]
      have h_not_dvd : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
      exact Nat.Coprime.symm (hp.coprime_iff_not_dvd.mpr h_not_dvd)
    have h_unit_b : IsUnit (b + 1 : ZMod p) := by
      have h_eq : (b + 1 : ZMod p) = ((b + 1 : ℕ) : ZMod p) := by push_cast; rfl
      rw [h_eq]
      rw [ZMod.isUnit_iff_coprime]
      exact (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt h_pos_b h_lt_b)).symm
    have h_unit_inv : IsUnit (2 * (b + 1 : ZMod p)) := IsUnit.mul h_unit_two h_unit_b
    have h_val_lt : (2 * (b + 1 : ZMod p)).val < p := ZMod.val_lt _
    have h_val_pos : (2 * (b + 1 : ZMod p)).val > 0 := by
      have h_zero : (2 * (b + 1 : ZMod p)).val ≠ 0 := by
        intro h_z
        rw [ZMod.val_eq_zero] at h_z
        exact IsUnit.ne_zero h_unit_inv h_z
      omega
    use (2 * (b + 1 : ZMod p)).val - 1
    have h_mem : (2 * (b + 1 : ZMod p)).val - 1 ∈ Finset.range (p - 1) := by
      simp only [Finset.mem_range]
      omega
    refine ⟨h_mem, ?_⟩
    dsimp only
    have h_eq_cast : (((2 * (b + 1 : ZMod p)).val - 1 : ℕ) : ZMod p) + 1 = 2 * (b + 1 : ZMod p) := by
      have : (((2 * (b + 1 : ZMod p)).val - 1 : ℕ) : ZMod p) + 1 = (((2 * (b + 1 : ZMod p)).val - 1 + 1 : ℕ) : ZMod p) := by push_cast; rfl
      rw [this]
      rw [Nat.sub_add_cancel h_val_pos]
      exact ZMod.natCast_zmod_val (2 * (b + 1 : ZMod p))
    have h_eq_mul : 2⁻¹ * ((((2 * (b + 1 : ZMod p)).val - 1 : ℕ) : ZMod p) + 1) = b + 1 := by
      rw [h_eq_cast]
      have h_two_inv : 2⁻¹ * (2 : ZMod p) = 1 := by
        rw [mul_comm]
        exact ZMod.mul_inv_of_unit 2 h_unit_two
      calc 2⁻¹ * (2 * (b + 1 : ZMod p)) = (2⁻¹ * 2) * (b + 1 : ZMod p) := by ring
        _ = b + 1 := by rw [h_two_inv, one_mul]
    have h_val_eq : (2⁻¹ * ((((2 * (b + 1 : ZMod p)).val - 1 : ℕ) : ZMod p) + 1)).val = b + 1 := by
      have h_val_b : (b + 1 : ZMod p).val = b + 1 := by
        have h_eq : (b + 1 : ZMod p) = ((b + 1 : ℕ) : ZMod p) := by push_cast; rfl
        rw [h_eq]
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt h_lt_b]
      rw [h_eq_mul, h_val_b]
    exact by omega
  · -- subgoal4
    intro i hi
    simp only [Finset.mem_range] at hi
    dsimp only
    congr 1
    have h_lt : i + 1 < p := by omega
    have h_pos : i + 1 > 0 := by omega
    have h_unit_two : IsUnit (2 : ZMod p) := by
      have : (2 : ZMod p) = ((2 : ℕ) : ZMod p) := by push_cast; rfl
      rw [this]
      rw [ZMod.isUnit_iff_coprime]
      have h_not_dvd : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
      exact Nat.Coprime.symm (hp.coprime_iff_not_dvd.mpr h_not_dvd)
    have h_unit_A : IsUnit (i + 1 : ZMod p) := by
      have h_eq : (i + 1 : ZMod p) = ((i + 1 : ℕ) : ZMod p) := by push_cast; rfl
      rw [h_eq]
      rw [ZMod.isUnit_iff_coprime]
      exact (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt h_pos h_lt)).symm
    have h_unit : IsUnit (2⁻¹ * (i + 1 : ZMod p)) := IsUnit.mul (IsUnit.inv h_unit_two) h_unit_A
    have h_val_pos : (2⁻¹ * (i + 1 : ZMod p)).val > 0 := by
      have h_zero : (2⁻¹ * (i + 1 : ZMod p)).val ≠ 0 := by
        intro h_z
        rw [ZMod.val_eq_zero] at h_z
        exact IsUnit.ne_zero h_unit h_z
      omega
    have h_eq_cast : (((2⁻¹ * (i + 1 : ZMod p)).val - 1 : ℕ) : ZMod p) + 1 = 2⁻¹ * (i + 1 : ZMod p) := by
      have : (((2⁻¹ * (i + 1 : ZMod p)).val - 1 : ℕ) : ZMod p) + 1 = (((2⁻¹ * (i + 1 : ZMod p)).val - 1 + 1 : ℕ) : ZMod p) := by push_cast; rfl
      rw [this]
      rw [Nat.sub_add_cancel h_val_pos]
      exact ZMod.natCast_zmod_val (2⁻¹ * (i + 1 : ZMod p))
    have h_goal : 2 * ((((2⁻¹ * (i + 1 : ZMod p)).val - 1 : ℕ) : ZMod p) + 1) = i + 1 := by
      have h_two_inv : (2 : ZMod p) * 2⁻¹ = 1 := ZMod.mul_inv_of_unit 2 h_unit_two
      calc 2 * ((((2⁻¹ * (i + 1 : ZMod p)).val - 1 : ℕ) : ZMod p) + 1)
        _ = 2 * (2⁻¹ * (i + 1 : ZMod p)) := by rw [h_eq_cast]
        _ = (2 * 2⁻¹) * (i + 1 : ZMod p) := by ring
        _ = i + 1 := by rw [h_two_inv, one_mul]
    exact h_goal.symm


lemma sum_sq_eq_zero {p : ℕ} (hp : p.Prime) (hp3 : p > 3) :
    Finset.sum (Finset.range (p - 1)) (fun i => (i + 1 : ZMod p)^2) = 0 := by
  have hS := sum_sq_eq_sum_four_mul_sq hp hp3
  have h_four : Finset.sum (Finset.range (p - 1)) (fun i => (2 * (i + 1 : ZMod p))^2) =
      4 * Finset.sum (Finset.range (p - 1)) (fun i => (i + 1 : ZMod p)^2) := by
    rw [← Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h_four] at hS
  have h_three : 3 * Finset.sum (Finset.range (p - 1)) (fun i => (i + 1 : ZMod p)^2) = 0 := by
    calc 3 * Finset.sum (Finset.range (p - 1)) (fun i => (i + 1 : ZMod p)^2)
      _ = 4 * Finset.sum (Finset.range (p - 1)) (fun i => (i + 1 : ZMod p)^2) - Finset.sum (Finset.range (p - 1)) (fun i => (i + 1 : ZMod p)^2) := by ring
      _ = Finset.sum (Finset.range (p - 1)) (fun i => (i + 1 : ZMod p)^2) - Finset.sum (Finset.range (p - 1)) (fun i => (i + 1 : ZMod p)^2) := by rw [hS]
      _ = 0 := by ring
  have h_unit : IsUnit (3 : ZMod p) := by
    have : (3 : ZMod p) = ((3 : ℕ) : ZMod p) := by push_cast; rfl
    rw [this]
    rw [ZMod.isUnit_iff_coprime]
    have h_not_dvd : ¬ p ∣ 3 := Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
    exact Nat.Coprime.symm (hp.coprime_iff_not_dvd.mpr h_not_dvd)
  exact (IsUnit.mul_right_inj h_unit).mp (by rw [mul_zero, h_three])
