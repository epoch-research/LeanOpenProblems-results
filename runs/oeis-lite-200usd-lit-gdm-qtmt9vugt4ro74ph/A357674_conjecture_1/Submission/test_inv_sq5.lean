import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

lemma sum_range_zmod_zero (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
    ∑ i ∈ range p, (i : ZMod p) = 0 := by
  have h_sum : ∑ i ∈ range p, i = p * (p - 1) / 2 := sum_range_id p
  have h_cast : (∑ i ∈ range p, (i : ZMod p)) = ((∑ i ∈ range p, i : ℕ) : ZMod p) := by
    simp only [Nat.cast_sum]
  rw [h_cast, h_sum]
  have h_odd : p % 2 = 1 := hp.mod_two_eq_one_iff_ne_two.mpr (by omega)
  have h_dvd : 2 ∣ p - 1 := by omega
  rw [Nat.mul_div_assoc p h_dvd]
  push_cast
  rw [ZMod.natCast_self p]
  ring

lemma sum_inv_eq_zero (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
    ∑ j ∈ Ico 1 p, ((j : ZMod p)⁻¹) = 0 := by
  have h_fact : Fact p.Prime := ⟨hp⟩
  have h_sum : ∑ j ∈ Ico 1 p, ((j : ZMod p)⁻¹) = ∑ j ∈ Ico 1 p, ((j : ZMod p)) := by
    apply Finset.sum_nbij' (fun (j : ℕ) => ((j : ZMod p)⁻¹).val) (fun (j : ℕ) => ((j : ZMod p)⁻¹).val)
    · intro a ha
      rw [mem_Ico] at ha ⊢
      have ha_nz : (a : ZMod p) ≠ 0 := by
        change ¬ (((a : ℕ) : ZMod p) = 0)
        rw [ZMod.natCast_eq_zero_iff]
        intro hdvd
        have : p ≤ a := Nat.le_of_dvd (by omega) hdvd
        omega
      have h_inv_nz : (a : ZMod p)⁻¹ ≠ 0 := inv_ne_zero ha_nz
      have h_val_nz : ((a : ZMod p)⁻¹).val ≠ 0 := by
        intro h_zero
        apply h_inv_nz
        have h_val : (((a : ZMod p)⁻¹).val : ZMod p) = 0 := by
          rw [h_zero, Nat.cast_zero]
        rw [ZMod.natCast_zmod_val] at h_val
        exact h_val
      constructor
      · omega
      · exact ZMod.val_lt ((a : ZMod p)⁻¹)
    · intro a ha
      rw [mem_Ico] at ha ⊢
      have ha_nz : (a : ZMod p) ≠ 0 := by
        change ¬ (((a : ℕ) : ZMod p) = 0)
        rw [ZMod.natCast_eq_zero_iff]
        intro hdvd
        have : p ≤ a := Nat.le_of_dvd (by omega) hdvd
        omega
      have h_inv_nz : (a : ZMod p)⁻¹ ≠ 0 := inv_ne_zero ha_nz
      have h_val_nz : ((a : ZMod p)⁻¹).val ≠ 0 := by
        intro h_zero
        apply h_inv_nz
        have h_val : (((a : ZMod p)⁻¹).val : ZMod p) = 0 := by
          rw [h_zero, Nat.cast_zero]
        rw [ZMod.natCast_zmod_val] at h_val
        exact h_val
      constructor
      · omega
      · exact ZMod.val_lt ((a : ZMod p)⁻¹)
    · intro a ha
      rw [mem_Ico] at ha
      have : (((a : ZMod p)⁻¹).val : ZMod p) = (a : ZMod p)⁻¹ := ZMod.natCast_zmod_val ((a : ZMod p)⁻¹)
      rw [this, inv_inv]
      exact ZMod.val_natCast_of_lt ha.2
    · intro a ha
      rw [mem_Ico] at ha
      have : (((a : ZMod p)⁻¹).val : ZMod p) = (a : ZMod p)⁻¹ := ZMod.natCast_zmod_val ((a : ZMod p)⁻¹)
      rw [this, inv_inv]
      exact ZMod.val_natCast_of_lt ha.2
    · intro a ha
      have : (((a : ZMod p)⁻¹).val : ZMod p) = (a : ZMod p)⁻¹ := ZMod.natCast_zmod_val ((a : ZMod p)⁻¹)
      rw [this]
  rw [h_sum]
  -- Now we show that ∑ j ∈ Ico 1 p, ((j : ZMod p)) = 0
  have h_split : ∑ j ∈ range p, ((j : ZMod p)) = ∑ j ∈ Ico 1 p, ((j : ZMod p)) := by
    rw [Finset.range_eq_Ico]
    have h_insert : Ico 0 p = insert 0 (Ico 1 p) := by
      symm
      apply Finset.insert_Ico_add_one_left_eq_Ico
      omega
    rw [h_insert]
    rw [Finset.sum_insert]
    · simp
    · simp
  rw [← h_split]
  exact sum_range_zmod_zero p hp hp3
