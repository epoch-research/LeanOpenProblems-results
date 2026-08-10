import FormalConjectures.Util.ProblemImports

lemma coprime_27_p5 (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) : Nat.Coprime 27 (p^5) := by
  have h1 : p ≠ 3 := by omega
  have h2 : ¬ p ∣ 3 := by
    intro hdvd
    have : p ≤ 3 := Nat.le_of_dvd (by decide) hdvd
    omega
  have h3 : Nat.Coprime 3 p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr h2).symm
  have h4 : Nat.Coprime 27 p := by
    have : 27 = 3^3 := by rfl
    rw [this]
    exact Nat.Coprime.pow_left 3 h3
  exact Nat.Coprime.pow_right 5 h4

lemma cancel_27 {p : ℕ} (hp : p.Prime) (hp5 : p ≥ 5) (A B : ZMod (p^5)) (h : (27 : ZMod (p^5)) * A = (27 : ZMod (p^5)) * B) : A = B := by
  have h_cop := coprime_27_p5 p hp hp5
  have h_inv := ZMod.coe_mul_inv_eq_one 27 h_cop
  have h_inv2 : ((27 : ZMod (p^5)) * (27 : ZMod (p^5))⁻¹) = 1 := by
    have : (27 : ZMod (p^5)) = ((27 : ℕ) : ZMod (p^5)) := by rfl
    rw [this]
    exact h_inv
  calc A
    _ = 1 * A := by ring
    _ = ((27 : ZMod (p^5)) * (27 : ZMod (p^5))⁻¹) * A := by rw [h_inv2]
    _ = (27 : ZMod (p^5))⁻¹ * ((27 : ZMod (p^5)) * A) := by ring
    _ = (27 : ZMod (p^5))⁻¹ * ((27 : ZMod (p^5)) * B) := by rw [h]
    _ = ((27 : ZMod (p^5)) * (27 : ZMod (p^5))⁻¹) * B := by ring
    _ = 1 * B := by rw [h_inv2]
    _ = B := by ring

