import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

theorem sum_inv_sq_zero (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    letI : NeZero p := ⟨by omega⟩
    (∑ k : ZMod p, (k ^ 2)⁻¹) = 0 := by
  haveI : NeZero p := ⟨by omega⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h_dvd : p ∣ 2 := by
      exact (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
    have h_le : p ≤ 2 := Nat.le_of_dvd (by decide) h_dvd
    omega
  let E : ZMod p ≃ ZMod p := Equiv.mulLeft₀ (2 : ZMod p) h2
  have h_comp : (∑ k : ZMod p, ((2 * k) ^ 2)⁻¹) = ∑ k : ZMod p, (k ^ 2)⁻¹ := by
    have hE := Equiv.sum_comp E (fun x => (x ^ 2)⁻¹)
    have h_rw : ∀ x, E x = 2 * x := fun x => rfl
    simp_rw [h_rw] at hE
    exact hE
  have h_mul : ∀ x : ZMod p, ((2 * x) ^ 2)⁻¹ = 4⁻¹ * (x ^ 2)⁻¹ := by
    intro x
    have : (2 * x) ^ 2 = 4 * x ^ 2 := by ring
    rw [this, mul_inv]
  have h_sum_rw : (∑ k : ZMod p, ((2 * k) ^ 2)⁻¹) = 4⁻¹ * ∑ k : ZMod p, (k ^ 2)⁻¹ := by
    rw [sum_congr rfl (fun x _ => h_mul x), ← mul_sum]
  have h_eq : (∑ k : ZMod p, (k ^ 2)⁻¹) = 4⁻¹ * ∑ k : ZMod p, (k ^ 2)⁻¹ := by
    calc (∑ k : ZMod p, (k ^ 2)⁻¹)
      _ = ∑ k : ZMod p, ((2 * k) ^ 2)⁻¹ := h_comp.symm
      _ = 4⁻¹ * ∑ k : ZMod p, (k ^ 2)⁻¹ := h_sum_rw
  have h_4 : (4 : ZMod p) * (∑ k : ZMod p, (k ^ 2)⁻¹) = (4 : ZMod p) * (4⁻¹ * ∑ k : ZMod p, (k ^ 2)⁻¹) :=
    congr_arg (fun x => (4 : ZMod p) * x) h_eq
  have h_4_inv : (4 : ZMod p) * 4⁻¹ = 1 := by
    apply mul_inv_cancel₀
    intro h4
    have h_dvd4 : p ∣ 4 := by
      exact (CharP.cast_eq_zero_iff (ZMod p) p 4).mp h4
    have h_le4 : p ≤ 4 := Nat.le_of_dvd (by decide) h_dvd4
    omega
  rw [← mul_assoc] at h_4
  rw [h_4_inv] at h_4
  rw [one_mul] at h_4
  have h_sub : (3 : ZMod p) * (∑ k : ZMod p, (k ^ 2)⁻¹) = 0 := by
    linear_combination h_4
  have h_3_ne_zero : (3 : ZMod p) ≠ 0 := by
    intro h3
    have h_dvd3 : p ∣ 3 := by
      exact (CharP.cast_eq_zero_iff (ZMod p) p 3).mp h3
    have h_le3 : p ≤ 3 := Nat.le_of_dvd (by decide) h_dvd3
    omega
  have h_goal : (3 : ZMod p)⁻¹ * ((3 : ZMod p) * (∑ k : ZMod p, (k ^ 2)⁻¹)) = 0 := by
    rw [h_sub, mul_zero]
  rw [← mul_assoc, inv_mul_cancel₀ h_3_ne_zero, one_mul] at h_goal
  exact h_goal
