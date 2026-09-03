import Submission.KloostermanIntervals

/-!
# Completion of modular hyperbola sums

The product congruence is expanded before taking absolute values. The zero
frequency is retained as an exact main term. This file does not assert prime
successor counts or a growing-modulus distribution theorem.
-/
open Finset
open scoped Classical BigOperators
namespace Erdos821.Kloosterman

section FiniteField
variable {F : Type*} [Field F] [Fintype F]

noncomputable def unitMass (w : F → ℂ) : ℂ := ∑ u : Fˣ, w u

noncomputable def hyperbolaWeight (w z : F → ℂ) (r : F) : ℂ :=
  ∑ u : Fˣ, w u * z (r/(u : F))

lemma fieldFourier_zero (ψ : AddChar F ℂ) (w : F → ℂ) :
    fieldFourier ψ w 0 = ∑ x : F, w x := by
  simp [fieldFourier]

lemma weightedKloosterman_zero (ψ : AddChar F ℂ) (w : F → ℂ) :
    weightedKloosterman ψ w 0 0 = unitMass w := by
  simp [weightedKloosterman, unitMass]

lemma hyperbolaWeight_completion (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (w z : F → ℂ) (r : F) :
    (Fintype.card F : ℂ)*hyperbolaWeight w z r =
      ∑ t : F, fieldFourier ψ z t * weightedKloosterman ψ w 0 (t*r) := by
  calc
    _ = ∑ u : Fˣ, w u * (∑ t : F, fieldFourier ψ z t * ψ (t*(r/(u : F)))) := by
      simp only [fieldFourier_inversion ψ hψ, hyperbolaWeight, mul_sum]
      apply sum_congr rfl
      intro u _
      ring
    _ = ∑ u : Fˣ, ∑ t : F, fieldFourier ψ z t *
        (w u * ψ ((t*r)*(u : F)⁻¹)) := by
      simp only [mul_sum]
      apply sum_congr rfl
      intro u _
      apply sum_congr rfl
      intro t _
      rw [div_eq_mul_inv, ← mul_assoc t r (u : F)⁻¹]
      ring
    _ = _ := by
      rw [sum_comm]
      simp only [weightedKloosterman, zero_mul, zero_add, mul_sum]

/-- The complete zero-frequency contribution is removed exactly. -/
theorem hyperbolaWeight_error_identity (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (w z : F → ℂ) (r : F) :
    (Fintype.card F : ℂ)*hyperbolaWeight w z r - (∑ x : F, z x)*unitMass w =
      ∑ t : Fˣ, fieldFourier ψ z t * weightedKloosterman ψ w 0 ((t : F)*r) := by
  have hh := sum_units_add_zero (fun t : F =>
    fieldFourier ψ z t * weightedKloosterman ψ w 0 (t*r))
  rw [← hyperbolaWeight_completion ψ hψ w z r, zero_mul,
    fieldFourier_zero, weightedKloosterman_zero] at hh
  exact eq_sub_of_add_eq hh |>.symm

lemma hyperbolaWeight_error_norm_le (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (w z : F → ℂ) (r : F) (B : ℝ)
    (hB : ∀ t : Fˣ, ‖weightedKloosterman ψ w 0 ((t : F)*r)‖ ≤ B) :
    ‖(Fintype.card F : ℂ)*hyperbolaWeight w z r - (∑ x : F, z x)*unitMass w‖ ≤
      B * ∑ t : Fˣ, ‖fieldFourier ψ z t‖ := by
  rw [hyperbolaWeight_error_identity ψ hψ]
  apply (norm_sum_le _ _).trans
  rw [mul_sum]
  apply sum_le_sum
  intro t _
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left (hB t) (norm_nonneg _)).trans_eq (mul_comm _ _)

end FiniteField

section PrimeModulus
variable {q : ℕ} [Fact q.Prime]
noncomputable local instance : DecidableEq (ZMod q) := fun a b => Classical.propDecidable (a=b)

lemma intervalResidueWeight_mass (M : ℤ) (L : ℕ) :
    (∑ x : ZMod q, intervalResidueWeight q M L x) = (L : ℂ) := by
  have hh := intervalResidueWeight_pairing (q := q) M L (fun _ => 1)
  simpa using hh

lemma nonzero_fourierMass_interval_le (M : ℤ) (L : ℕ) :
    (∑ t : (ZMod q)ˣ, ‖fieldFourier ZMod.stdAddChar (intervalResidueWeight q M L) t‖) ≤
      (q : ℝ)*(harmonic (q-1) : ℝ) := by
  have hh := sum_units_add_zero (fun t : ZMod q =>
    ‖fieldFourier ZMod.stdAddChar (intervalResidueWeight q M L) t‖)
  rw [fieldFourier_zero, intervalResidueWeight_mass, Complex.norm_natCast] at hh
  have hb := fourierMass_intervalResidueWeight_le (q := q) M L
  unfold fourierMass at hb
  rw [← hh] at hb
  linarith only [hb]

/-- A uniform rectangle estimate with the first interval's unit mass retained
in the main term. The interval lengths are unrestricted. -/
theorem interval_hyperbola_error_le (M N : ℤ) (B C : ℕ) (r : ZMod q) (hr : r ≠ 0) :
    ‖hyperbolaWeight (intervalResidueWeight q M B) (intervalResidueWeight q N C) r -
        (C : ℂ)*unitMass (intervalResidueWeight q M B)/(q : ℂ)‖ ≤
      Real.sqrt (Real.sqrt (3*(q : ℝ)^3)) *
        ((B : ℝ)/q + (harmonic (q-1) : ℝ))*(harmonic (q-1) : ℝ) := by
  let K : ℝ := Real.sqrt (Real.sqrt (3*(q : ℝ)^3)) *
    ((B : ℝ)/q+(harmonic (q-1) : ℝ))
  have hH : 0 ≤ (harmonic (q-1) : ℝ) := by
    have hq2 := (Fact.out : q.Prime).two_le
    exact_mod_cast (harmonic_pos (show q-1 ≠ 0 by omega)).le
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hh := hyperbolaWeight_error_norm_le ZMod.stdAddChar (ZMod.isPrimitive_stdAddChar q)
    (intervalResidueWeight q M B) (intervalResidueWeight q N C) r K (by
      intro t
      rw [← intervalKloosterman_eq_weighted]
      exact intervalKloosterman_norm_le_harmonic M B 0 ((t : ZMod q)*r)
        (mul_ne_zero t.ne_zero hr))
  rw [ZMod.card, intervalResidueWeight_mass] at hh
  have he := hh.trans (mul_le_mul_of_nonneg_left (nonzero_fourierMass_interval_le (q := q) N C) hK)
  have hq : (0 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  apply (mul_le_mul_iff_right₀ hq).mp
  calc
    _ = ‖(q : ℂ)*hyperbolaWeight (intervalResidueWeight q M B)
          (intervalResidueWeight q N C) r -
        (C : ℂ)*unitMass (intervalResidueWeight q M B)‖ := by
      rw [← Complex.norm_natCast, ← norm_mul]
      congr 1
      field_simp
    _ ≤ K*((q : ℝ)*(harmonic (q-1) : ℝ)) := he
    _ = _ := by dsimp [K]; ring

end PrimeModulus
end Erdos821.Kloosterman
