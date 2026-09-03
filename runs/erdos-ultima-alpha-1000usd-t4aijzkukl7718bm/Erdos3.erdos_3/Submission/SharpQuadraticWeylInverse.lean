import Submission.DilatedQuadraticShift
import Submission.MultipleLinearOrbitInverse
import Submission.CircleIntegerApproximation

/-! An inverse-square leading-coefficient estimate for quadratic circle phases.
The denominator and error numerator are polynomial in the inverse mean size.
This theorem is not an inverse theorem for arbitrary functions. -/
namespace Erdos3SharpQuadraticWeylInverse
open Finset Erdos3HigherPhaseDifferences Erdos3QuadraticRecurrenceAverages
  Erdos3DilatedQuadraticShift Erdos3MultipleLinearOrbitInverse
  Erdos3CircleIntegerApproximation
open scoped BigOperators Classical
set_option maxHeartbeats 3000000

/-- A quadratic circle phase with interval mean at least 2^-s has a bounded
positive denominator approximating its top difference with error O_s(N^-2). -/
theorem sharp_quadratic_leading_inverse (f : ℕ → Additive Circle) (z : Additive Circle)
    (hf : diffIter 2 f = fun _ ↦ z) (s N : ℕ)
    (hN : 2^(14*s+42) ≤ N)
    (hmean : (1/2 : ℝ)^s ≤ ‖intervalMean N (fun n ↦ phase (f n))‖) :
    ∃ q : ℕ, 0 < q ∧ q ≤ 2^(14*s+42) ∧
      ‖(phase z)^q-1‖ ≤ (2 : ℝ)^(14*s+42)/(N : ℝ)^2 := by
  let H := 2^(2*s+4)
  let D := 2^(3*s+6)
  let δ : ℝ := (1/2)^s
  let α := unitAngle (phase z)
  have hH : 0 < H := Nat.two_pow_pos _
  have hD : 0 < D := Nat.two_pow_pos _
  have hδ : 0 < δ := pow_pos (by norm_num) _
  have hN0 : 0 < N := (Nat.two_pow_pos _).trans_le hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hDeq : D = 4*H*2^s := by
    dsimp only [D,H]
    rw [show 4 = 2^2 by norm_num,← pow_add,← pow_add]
    congr 1
    omega
  have hδH : (H : ℝ)*δ^2 = 16 := by
    dsimp only [H,δ]
    push_cast
    rw [show 2*s+4 = s*2+4 by omega,pow_add,pow_mul,div_pow,one_pow]
    field_simp
    ring
  have hthreshold : 8*(2*D*H)*(6*H+1) ≤ N := by
    have hlin : 6*H+1 ≤ 7*H := by omega
    have hm := Nat.mul_le_mul_left (8*(2*D*H)) hlin
    have hpow : 128*D*H^2 = 2^(7*s+21) := by
      dsimp only [D,H]
      rw [show 128 = 2^7 by norm_num,← pow_mul,← pow_add,← pow_add]
      congr 1
      omega
    calc
      _ ≤ 128*D*H^2 := by nlinarith only [hm,Nat.zero_le (D*H^2)]
      _ = _ := hpow
      _ ≤ 2^(14*s+42) := Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ _ := hN
  have hgood : ∀ t < N/D, ∃ d : ℕ, ∃ b : ℤ, 0 < d ∧ d < H ∧
      |α*((d*t : ℕ) : ℝ)-(b : ℝ)| ≤ (H : ℝ)/(N : ℝ) := by
    intro t ht
    have hDt : D*t ≤ N := (Nat.mul_le_mul_left D ht.le).trans (Nat.mul_div_le N D)
    rw [hDeq] at hDt
    have hDtr : 4*(H : ℝ)*(2 : ℝ)^s*(t : ℝ) ≤ N := by exact_mod_cast hDt
    have hshift : 2*(H : ℝ)*(t : ℝ)/(N : ℝ) ≤ δ/2 := by
      dsimp only [δ]
      rw [div_pow,one_pow,div_div]
      apply (div_le_div_iff₀ hNr (by positivity : 0 < (2 : ℝ)^s*2)).mpr
      nlinarith only [hDtr]
    have hdiag : 1/(H : ℝ) ≤ δ^2/8 := by
      apply (div_le_iff₀ hHr).mpr
      nlinarith only [hδH]
    obtain ⟨d,hd,hdH,hchord⟩ := quadratic_dilate_inverse f z hf hN0 hH hδ hmean hshift hdiag
    have hephase : ephase (α*((d*t : ℕ) : ℝ)) = (phase z)^(d*t) := by
      rw [mul_comm α,← ephase_pow]
      dsimp only [α]
      rw [ephase_unitAngle _ (phase_norm z)]
    obtain ⟨b,hb⟩ := exists_integer_near (α*((d*t : ℕ) : ℝ))
    rw [hephase] at hb
    have hscale : 32/(δ^2*(N : ℝ)) = 2*(H : ℝ)/(N : ℝ) := by
      apply (div_eq_div_iff (mul_ne_zero (pow_ne_zero _ hδ.ne') hNr.ne') hNr.ne').mpr
      nlinarith only [congrArg (fun x : ℝ ↦ x*(2*(N : ℝ))) hδH]
    rw [hscale, mul_div_assoc] at hchord
    refine ⟨d,b,hd,hdH,?_⟩
    have hhn : 0 ≤ (H : ℝ)/(N : ℝ) := div_nonneg hHr.le hNr.le
    linarith only [hb,hchord,hhn]
  obtain ⟨q,b,hq,hqb,herr⟩ := multiple_linear_orbit_inverse α hD hH hthreshold hgood
  have hqbound : q ≤ 2^(14*s+42) := by
    have hp : 8*D*H^2 = 2^(7*s+17) := by
      dsimp only [D,H]
      rw [show 8 = 2^3 by norm_num,← pow_mul,← pow_add,← pow_add]
      congr 1
      omega
    exact hqb.le.trans (hp.le.trans (Nat.pow_le_pow_right (by decide) (by omega)))
  refine ⟨q,hq,hqbound,?_⟩
  have hephase : ephase (α*(q : ℝ)) = (phase z)^q := by
    rw [mul_comm α,← ephase_pow]
    dsimp only [α]
    rw [ephase_unitAngle _ (phase_norm z)]
  have hch := ephase_near_integer (α*(q : ℝ)) b
  rw [hephase] at hch
  have herror := mul_le_mul_of_nonneg_left herr (by norm_num : (0 : ℝ) ≤ 8)
  have hlin : 6*(H : ℝ)+1 ≤ 7*(H : ℝ) := by
    have hh : (1 : ℝ) ≤ H := by exact_mod_cast hH
    linarith only [hh]
  have hm := mul_le_mul_of_nonneg_left hlin
    (by positivity : 0 ≤ 2048*(D : ℝ)^2*(H : ℝ)^3)
  have hnum : 2048*(D : ℝ)^2*(H : ℝ)^3*(6*(H : ℝ)+1) ≤
      16384*(D : ℝ)^2*(H : ℝ)^4 := by
    nlinarith only [hm,show 0 ≤ (D : ℝ)^2*(H : ℝ)^4 by positivity]
  have hpow : 16384*(D : ℝ)^2*(H : ℝ)^4 = (2 : ℝ)^(14*s+42) := by
    dsimp only [D,H]
    push_cast
    rw [show (16384 : ℝ) = 2^14 by norm_num,← pow_mul,← pow_mul,← pow_add,← pow_add]
    congr 1
    omega
  calc
    _ ≤ 8*|α*(q : ℝ)-(b : ℝ)| := hch
    _ ≤ 2048*(D : ℝ)^2*(H : ℝ)^3*(6*(H : ℝ)+1)/(N : ℝ)^2 :=
      herror.trans_eq (by ring)
    _ ≤ 16384*(D : ℝ)^2*(H : ℝ)^4/(N : ℝ)^2 :=
      div_le_div_of_nonneg_right hnum (sq_nonneg _)
    _ = _ := by rw [hpow]

#print axioms sharp_quadratic_leading_inverse
end Erdos3SharpQuadraticWeylInverse
