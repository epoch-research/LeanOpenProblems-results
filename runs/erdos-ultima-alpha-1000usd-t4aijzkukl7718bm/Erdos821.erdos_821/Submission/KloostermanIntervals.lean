import Submission.KloostermanSpectral
import Submission.PolyaVinogradov

/-!
# Incomplete Kloosterman sums over integer intervals

Weighted completion and the previously proved harmonic Fourier bound give
an unconditional three-quarter-power estimate modulo a prime. The interval
may wrap around the modulus and may have any integer starting point.
-/
open Finset
open scoped Classical BigOperators
namespace Erdos821.Kloosterman
open Erdos821.AnalyticSieve

variable {q : ℕ} [Fact q.Prime]

noncomputable def intervalResidueWeight (q : ℕ) (M : ℤ) (L : ℕ) (x : ZMod q) : ℂ :=
  ∑ n ∈ range L, if ((M+n : ℤ) : ZMod q)=x then 1 else 0

lemma intervalResidueWeight_pairing (M : ℤ) (L : ℕ) (f : ZMod q → ℂ) :
    (∑ x : ZMod q, intervalResidueWeight q M L x * f x) =
      ∑ n ∈ range L, f ((M+n : ℤ) : ZMod q) := by
  classical
  letI : DecidableEq (ZMod q) := fun a b => Classical.propDecidable (a=b)
  simp only [intervalResidueWeight, sum_mul, ite_mul, one_mul, zero_mul]
  rw [sum_comm]
  simp

lemma fieldFourier_intervalResidueWeight (M : ℤ) (L : ℕ) (t : ZMod q) :
    fieldFourier ZMod.stdAddChar (intervalResidueWeight q M L) t =
      intervalWaveSum M L (((-t).val : ℝ)/q) := by
  classical
  letI : DecidableEq (ZMod q) := fun a b => Classical.propDecidable (a=b)
  rw [fieldFourier, intervalResidueWeight_pairing]
  unfold intervalWaveSum
  apply sum_congr rfl
  intro n _
  rw [mul_comm (-t), stdAddChar_int_mul]

lemma fourierMass_intervalResidueWeight_le (M : ℤ) (L : ℕ) :
    fourierMass ZMod.stdAddChar (intervalResidueWeight q M L) ≤
      (L : ℝ) + (q : ℝ)*(harmonic (q-1) : ℝ) := by
  classical
  letI : DecidableEq (ZMod q) := fun a b => Classical.propDecidable (a=b)
  have hq : 2 ≤ q := (Fact.out : q.Prime).two_le
  have he : (∑ t : ZMod q, ‖intervalWaveSum M L (((-t).val : ℝ)/q)‖) =
      ∑ t : ZMod q, ‖intervalWaveSum M L ((t.val : ℝ)/q)‖ := by
    apply Fintype.sum_equiv (Equiv.neg (ZMod q))
    intro t
    rfl
  have hz : ‖intervalWaveSum M L (((0 : ZMod q).val : ℝ)/q)‖ = L := by
    simp [intervalWaveSum, wave]
  unfold fourierMass
  simp_rw [fieldFourier_intervalResidueWeight]
  rw [he, ← sum_units_add_zero, hz]
  have hh := sum_norm_intervalWaveSum_units_le (q := q) hq M L
  have hh' : (∑ u : (ZMod q)ˣ, ‖intervalWaveSum M L (((u : ZMod q).val : ℝ)/q)‖) ≤
      (q : ℝ)*(harmonic (q-1) : ℝ) := by
    convert hh using 1
    apply sum_congr (by ext u; simp)
    intro u _
    rfl
  simpa only [add_comm] using add_le_add_right hh' (L : ℝ)

noncomputable def intervalKloosterman (M : ℤ) (L : ℕ) (a b : ZMod q) : ℂ :=
  ∑ n ∈ range L, let x : ZMod q := ((M+n : ℤ) : ZMod q)
    if x=0 then 0 else ZMod.stdAddChar (a*x+b*x⁻¹)

lemma intervalKloosterman_eq_weighted (M : ℤ) (L : ℕ) (a b : ZMod q) :
    intervalKloosterman M L a b =
      weightedKloosterman ZMod.stdAddChar (intervalResidueWeight q M L) a b := by
  classical
  letI : DecidableEq (ZMod q) := fun a b => Classical.propDecidable (a=b)
  calc
    _ = ∑ x : ZMod q, intervalResidueWeight q M L x *
        (if x=0 then 0 else ZMod.stdAddChar (a*x+b*x⁻¹)) := by
      rw [intervalResidueWeight_pairing]
      unfold intervalKloosterman
      apply sum_congr rfl
      intro n _
      dsimp only
      split_ifs <;> rfl
    _ = ∑ u : (ZMod q)ˣ, intervalResidueWeight q M L u *
        (if (u : ZMod q)=0 then 0 else ZMod.stdAddChar (a*(u : ZMod q)+b*(u : ZMod q)⁻¹)) := by
      have he := sum_units_add_zero (fun x : ZMod q => intervalResidueWeight q M L x *
        (if x=0 then 0 else ZMod.stdAddChar (a*x+b*x⁻¹)))
      simpa only [if_pos rfl, ite_true, mul_zero, add_zero] using he.symm
    _ = _ := by
      unfold weightedKloosterman
      apply sum_congr rfl
      intro u _
      rw [if_neg u.ne_zero]

/-- The elementary complete-sum bound after interval completion. -/
theorem intervalKloosterman_norm_le_harmonic (M : ℤ) (L : ℕ) (a b : ZMod q) (hb : b ≠ 0) :
    ‖intervalKloosterman M L a b‖ ≤
      Real.sqrt (Real.sqrt (3*(q : ℝ)^3)) *
        ((L : ℝ)/q + (harmonic (q-1) : ℝ)) := by
  classical
  letI : DecidableEq (ZMod q) := fun a b => Classical.propDecidable (a=b)
  have hq : (0 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
  have hh := weightedKloosterman_norm_le ZMod.stdAddChar (ZMod.isPrimitive_stdAddChar q)
    (intervalResidueWeight q M L) a b hb
  rw [← intervalKloosterman_eq_weighted, ZMod.card, elementaryBound, ZMod.card] at hh
  have hF := mul_le_mul_of_nonneg_left (fourierMass_intervalResidueWeight_le (q := q) M L)
    (Real.sqrt_nonneg (Real.sqrt (3*(q : ℝ)^3)))
  apply (mul_le_mul_iff_right₀ hq).mp
  calc
    _ ≤ Real.sqrt (Real.sqrt (3*(q : ℝ)^3))*fourierMass ZMod.stdAddChar
        (intervalResidueWeight q M L) := hh
    _ ≤ Real.sqrt (Real.sqrt (3*(q : ℝ)^3)) *
        ((L : ℝ)+(q : ℝ)*(harmonic (q-1) : ℝ)) := hF
    _ = _ := by field_simp

/-- For intervals of length at most the modulus the completion loss is
logarithmic. No hypothesis on the starting integer is needed. -/
theorem intervalKloosterman_norm_le_log (M : ℤ) (L : ℕ) (hL : L ≤ q)
    (a b : ZMod q) (hb : b ≠ 0) :
    ‖intervalKloosterman M L a b‖ ≤
      Real.sqrt (Real.sqrt (3*(q : ℝ)^3)) * (2+Real.log q) := by
  classical
  letI : DecidableEq (ZMod q) := fun a b => Classical.propDecidable (a=b)
  apply (intervalKloosterman_norm_le_harmonic M L a b hb).trans
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  have hq : (0 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le
  have hL' : (L : ℝ)/q ≤ 1 := (div_le_one hq).mpr (by exact_mod_cast hL)
  have hH : (harmonic (q-1) : ℝ) ≤ 1+Real.log q := by
    apply (harmonic_le_one_add_log (q-1)).trans
    apply add_le_add le_rfl
    apply Real.log_le_log
    · exact_mod_cast (show 0 < q-1 by omega)
    · exact_mod_cast Nat.sub_le q 1
  linarith only [hL', hH]

end Erdos821.Kloosterman
