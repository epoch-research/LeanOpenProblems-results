import Submission.BeattyRowScales

/-! Direct simultaneous rational approximations to reciprocal row frequencies.
The denominator loss is polynomial in the number of rows, rather than factorial. -/
namespace Erdos972DirectRowApproximation

open Finset ArithmeticFunction
open Erdos972PrimeRotation Erdos972PrefixPrimeRotation Erdos972VaughanSums
open Erdos972ExponentialSum Erdos972WeightedPrimeRotation Erdos972BeattyRows Erdos972BeattyRowScales

lemma den_div_nat_bounds (r : ℚ) {m : ℕ} (hm : 0 < m) :
    r.den ≤ (r/(m : ℚ)).den ∧ (r/(m : ℚ)).den ≤ m*r.den := by
  have hm0 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  constructor
  · have hh := den_nat_mul_le m (r/(m : ℚ))
    have he : (m : ℚ)*(r/(m : ℚ)) = r := by field_simp
    rwa [he] at hh
  · have hh := Rat.mul_den_dvd r (m : ℚ)⁻¹
    rw [Rat.den_inv_of_ne_zero hm0, Rat.num_natCast, Int.natAbs_natCast] at hh
    have hpos : 0 < r.den*m := Nat.mul_pos r.pos hm
    simpa only [div_eq_mul_inv, Nat.mul_comm] using Nat.le_of_dvd hpos hh

/-- Dividing the target by `m` loses only a factor `m` in the upper denominator
bound, and no factor `m` in the lower bound. -/
theorem divided_approximant {θ : ℝ} (r : ℚ)
    (hr : |θ-r| ≤ 1/(r.den : ℝ)^2) (m : ℕ) (hm : 0 < m) :
    ∃ s : ℚ, r.den ≤ 2*s.den ∧ s.den ≤ 4*m*r.den ∧
      |θ/m-s| ≤ 1/(s.den : ℝ)^2 := by
  let T := 4*m*r.den
  have hT : 0 < T := by dsimp [T]; positivity
  obtain ⟨s, hs, hsT⟩ := Real.exists_rat_abs_sub_le_and_den_le (θ/m) hT
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hq : (0 : ℝ) < r.den := Nat.cast_pos.mpr r.pos
  have hd : (0 : ℝ) < s.den := Nat.cast_pos.mpr s.pos
  refine ⟨s, ?_, hsT, ?_⟩
  · by_contra hh
    have hsmall : 2*s.den < r.den := Nat.lt_of_not_ge hh
    obtain ⟨hdenlo, hdenhi⟩ := den_div_nat_bounds r hm
    by_cases he : r/(m : ℚ) = s
    · rw [he] at hdenlo
      omega
    have hsep := rational_separation (r/(m : ℚ)) s he
    have hsep' : (1 : ℝ) ≤ |(r : ℝ)/m-s| *(m*r.den)*s.den := by
      simp only [Rat.cast_div, Rat.cast_natCast] at hsep
      have hdenhiR : ((r/(m : ℚ)).den : ℝ) ≤ (m : ℝ)*r.den := by exact_mod_cast hdenhi
      exact hsep.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hdenhiR (abs_nonneg _)) hd.le)
    have htriangle : |(r : ℝ)/m-s| ≤ 1/((m : ℝ)*(r.den : ℝ)^2)+1/(((T : ℝ)+1)*s.den) := by
      calc
        _ ≤ |(r : ℝ)/m-θ/m|+|θ/m-s| := abs_sub_le _ _ _
        _ = |θ-r|/m+|θ/m-s| := by rw [← sub_div, abs_div, abs_of_nonneg hmR.le, abs_sub_comm (r : ℝ) θ]
        _ ≤ _ := by
          have hh := div_le_div_of_nonneg_right hr hmR.le
          rw [div_div] at hh
          simpa only [mul_comm (m : ℝ) ((r.den : ℝ)^2)] using add_le_add hh hs
    have hhalf : (s.den : ℝ)/r.den < 1/2 := by
      apply (div_lt_iff₀ hq).mpr
      have hh : 2*(s.den : ℝ) < r.den := by exact_mod_cast hsmall
      linarith
    have hhalf' : (m : ℝ)*r.den/((T : ℝ)+1) < 1/2 := by
      apply (div_lt_iff₀ (by positivity : 0 < (T : ℝ)+1)).mpr
      dsimp [T]
      push_cast
      nlinarith
    have hbound := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right htriangle (mul_nonneg hmR.le hq.le)) hd.le
    have heq : (1/((m : ℝ)*(r.den : ℝ)^2)+1/(((T : ℝ)+1)*s.den))*(m*r.den)*s.den =
        (s.den : ℝ)/r.den+(m : ℝ)*r.den/((T : ℝ)+1) := by field_simp
    rw [heq] at hbound
    linarith
  · apply hs.trans
    apply one_div_le_one_div_of_le (sq_pos_of_pos hd)
    have hh : (s.den : ℝ) ≤ T := Nat.cast_le.mpr hsT
    nlinarith

/-- A polynomial-cost common approximation for all reciprocal rows and their
first `H` harmonics. An integer shift keeps every target positive. -/
theorem reciprocal_harmonic_approximant {θ : ℝ} (r : ℚ)
    (hr : |θ-r| ≤ 1/(r.den : ℝ)^2) (m h H : ℕ)
    (hm : 0 < m) (hh : 0 < h) (hhH : h ≤ H) :
    ∃ s : ℚ, r.den ≤ 4*H*s.den ∧ s.den ≤ 16*H*m*r.den ∧
      |(h : ℝ)*(2+θ/m)-s| ≤ 1/(s.den : ℝ)^2 := by
  obtain ⟨t, htlo, hthi, ht⟩ := divided_approximant r hr m hm
  have hden : (2+t).den = t.den := Rat.ofNat_add_den 2 t
  have happ : |(2+θ/m)-(2+t : ℚ)| ≤ 1/((2+t : ℚ).den : ℝ)^2 := by
    rw [hden]
    push_cast
    simpa only [add_sub_add_left_eq_sub] using ht
  obtain ⟨s, hslo, hshi, hs⟩ := simultaneous_approximant (2+t) happ h H hh hhH
  rw [hden] at hslo hshi
  refine ⟨s, ?_, ?_, hs⟩ <;> nlinarith

/-- Uniform-prefix cancellation for a rectangular family of reciprocal row
frequencies. Both `M` and `H` may grow with the base rational denominator. -/
theorem reciprocal_rows_prefix_bound {θ : ℝ} (hθ : 0 ≤ θ)
    (r : ℚ) (hr : |θ-r| ≤ 1/(r.den : ℝ)^2)
    (u M H : ℕ) (hM : 0 < M) (hH : 0 < H) (hu : 2048*H*M ≤ u)
    (hlo : u^4 ≤ r.den) (hhi : r.den ≤ 16*u^4)
    (m h X : ℕ) (hm : 0 < m) (hmM : m ≤ M) (hh : 0 < h) (hhH : h ≤ H) (hX : X ≤ u^6) :
    ‖expSum vonMangoldt ((h : ℝ)*(2+θ/m)) X‖ ≤
      rotationConstant (256*H*M)*(1+Real.log u)^5*(u : ℝ)^5*Real.sqrt u := by
  obtain ⟨s, hslo, hshi, hsapprox⟩ := reciprocal_harmonic_approximant r hr m h H hm hh hhH
  have hspos : (0 : ℝ) < s := by
    have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
    have hd1 : (1 : ℝ) ≤ s.den := by exact_mod_cast s.pos
    have herr : |(h : ℝ)*(2+θ/m)-s| ≤ 1 := hsapprox.trans
      ((div_le_one (by positivity)).mpr (by nlinarith))
    have hfreq : 2 ≤ (h : ℝ)*(2+θ/m) := by
      have hh0 : 0 ≤ θ/(m : ℝ) := by positivity
      nlinarith
    linarith [(abs_le.mp herr).2]
  have hrep := nonneg_rat_eq_natAbs_div s (by exact_mod_cast hspos.le)
  have hlow : u^4 ≤ (256*H*M)*s.den := by nlinarith
  have hhigh : s.den ≤ (256*H*M)*u^4 := by
    calc
      _ ≤ 16*H*m*r.den := hshi
      _ ≤ 16*H*M*(16*u^4) := by gcongr
      _ = _ := by ring
  letI : NeZero s.den := ⟨s.den_ne_zero⟩
  exact expSum_sixth_scale_prefix_bound s.num.natAbs s.reduced ((h : ℝ)*(2+θ/m))
    (by simpa only [← hrep] using hsapprox) u (256*H*M) (by positivity) (by convert hu using 1 <;> ring) hlow hhigh X hX

/-- The direct reciprocal-row estimate for the actual Beatty sums. This removes
the factorial common-denominator loss in the earlier fixed-row theorem. -/
theorem beatty_row_discrepancy {α : ℝ} (hα : 1 < α) (hI : Irrational α)
    (r : ℚ) (hr : |1/α-r| ≤ 1/(r.den : ℝ)^2)
    (u M H : ℕ) (hM : 0 < M) (hH : 0 < H) (hu : 2048*H*M ≤ u)
    (hlo : u^4 ≤ r.den) (hhi : r.den ≤ 16*u^4)
    (δ : ℝ) (hδ : 0 < δ) (hmargin : δ ≤ rowArcLeft α)
    (m L : ℕ) (hm : 0 < m) (hmM : m ≤ M) (hL : Erdos972PrimePowerError.floorMul (α*m) L ≤ u^6) :
    |mangoldtRow (α*m) L-Chebyshev.psi ((α*m)*L)/(α*m)| ≤
      (2*δ+1/(H : ℝ)+4/((4*δ)^2*H))*Chebyshev.psi ((α*m)*L)+
        H*(rotationConstant (256*H*M)*(1+Real.log u)^5*(u : ℝ)^5*Real.sqrt u) := by
  have hα0 : 0 < α := by linarith
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hβ : 1 < α*m := by nlinarith
  have hβI := hI.mul_natCast (Nat.ne_of_gt hm)
  have harc := rowArcLeft_bounds hβ
  have hleft : δ ≤ rowArcLeft (α*m) := hmargin.trans (rowArcLeft_mono hα0 (by nlinarith))
  letI : NeZero H := ⟨Nat.ne_of_gt hH⟩
  let X := Erdos972PrimePowerError.floorMul (α*m) L
  have hh := mangoldt_arc_discrepancy (2+(1/α)/m) (-rowArcLeft (α*m)) X
    (rowArcLeft (α*m)) (1-rowArcLeft (α*m)) δ
    (rotationConstant (256*H*M)*(1+Real.log u)^5*(u : ℝ)^5*Real.sqrt u)
    (by linarith) hδ hleft (by linarith)
    (by positivity [rotationConstant_pos (256*H*M), Real.log_natCast_nonneg u])
    (fun h hh hhH => reciprocal_rows_prefix_bound (show 0 ≤ 1/α by positivity) r hr u M H hM hH hu hlo hhi
      m h X hm hmM hh hhH hL)
  have he : (1/α)/(m : ℝ) = 1/(α*m) := div_div _ _ _
  rw [he, show (2 : ℝ) = (2 : ℕ) by norm_num, mangoldtArcSum_nat_add, ← mangoldtRow_eq_arc hβ hβI L] at hh
  have hwidth : (1-rowArcLeft (α*m))-rowArcLeft (α*m) = 1/(α*m) := by unfold rowArcLeft; ring
  have hpsi : Chebyshev.psi X = Chebyshev.psi ((α*m)*L) := by
    simp only [X, Erdos972PrimePowerError.floorMul, Chebyshev.psi, Nat.floor_natCast]
  simpa only [hwidth, hpsi, one_div_mul_eq_div] using hh

#print axioms divided_approximant
#print axioms reciprocal_rows_prefix_bound
#print axioms beatty_row_discrepancy

end Erdos972DirectRowApproximation
