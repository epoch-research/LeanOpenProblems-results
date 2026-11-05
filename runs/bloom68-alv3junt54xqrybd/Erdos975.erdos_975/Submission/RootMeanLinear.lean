import Submission.RootMeanBasic
import Submission.RootMeanPeriodic
import Submission.RootReciprocalAverage

/-!
# The complete root-count mean theorem in degree one

For a primitive affine integer polynomial `a * X + b`, with `a ≠ 0`,
the root count at a positive modulus `q` is `1` if `gcd(|a|, q) = 1`
and `0` otherwise. Consequently its mean is the strictly positive constant
`φ(|a|) / |a|`. This includes every irreducible degree-one polynomial,
not just monic polynomials, and uses no assumed root-count asymptotic.

No higher-degree root-count mean is claimed here.
-/

namespace Erdos975Support

open Filter Polynomial
open scoped Topology

/-- An integer is a unit modulo `q` exactly when its absolute value is
coprime to `q`. -/
theorem isUnit_intCast_zmod_iff (a : ℤ) (q : ℕ) :
    IsUnit (a : ZMod q) ↔ a.natAbs.Coprime q := by
  rcases Int.natAbs_eq a with ha | ha
  · conv_lhs => rw [ha]
    simpa only [Int.cast_natCast] using ZMod.isUnit_iff_coprime a.natAbs q
  · conv_lhs => rw [ha]
    simpa only [Int.cast_neg, Int.cast_natCast, IsUnit.neg_iff] using
      ZMod.isUnit_iff_coprime a.natAbs q

/-- Primitivity of an affine polynomial forces its two coefficients to
be coprime. -/
theorem affine_coefficients_isCoprime (a b : ℤ)
    (hf : (C a * X + C b).IsPrimitive) : IsCoprime a b := by
  have hg : IsUnit (Int.gcd a b : ℤ) := hf _ <| dvd_add
    (dvd_mul_of_dvd_left (map_dvd C (Int.gcd_dvd_left a b)) X)
    (map_dvd C (Int.gcd_dvd_right a b))
  rw [Int.isCoprime_iff_nat_coprime, Nat.coprime_iff_gcd_eq_one]
  simpa only [Int.natAbs_natCast, Int.gcd_def] using Int.isUnit_iff_natAbs_eq.mp hg

/-- The exact root count of a primitive affine polynomial at every positive
modulus, including moduli dividing its leading coefficient. -/
theorem rootCount_affine (a b : ℤ) (hab : IsCoprime a b) (q : ℕ) (hq : 0 < q) :
    rootCount (polynomialAbsValue (C a * X + C b)) q =
      if a.natAbs.Coprime q then 1 else 0 := by
  letI : NeZero q := ⟨hq.ne'⟩
  rw [rootCount_polynomial_eq_card_zmod, Nat.card_eq_fintype_card]
  have heval (x : ZMod q) :
      (C a * X + C b).eval₂ (Int.castRingHom (ZMod q)) x = (a : ZMod q) * x + b := by
    simp only [eval₂_add, eval₂_mul, eval₂_C, eval₂_X, Int.coe_castRingHom]
  by_cases hcop : a.natAbs.Coprime q
  · rw [if_pos hcop]
    have hua : IsUnit (a : ZMod q) := (isUnit_intCast_zmod_iff a q).mpr hcop
    let r : ZMod q := -((a : ZMod q)⁻¹ * (b : ZMod q))
    have hr : (a : ZMod q) * r + b = 0 := by
      dsimp only [r]
      rw [mul_neg, ← mul_assoc, ZMod.mul_inv_of_unit _ hua]
      simp
    apply Fintype.card_eq_one_iff.mpr
    refine ⟨⟨r, (heval r).trans hr⟩, ?_⟩
    intro x
    apply Subtype.ext
    apply hua.mul_left_cancel
    have hx := (heval x.1).symm.trans x.2
    linear_combination hx - hr
  · rw [if_neg hcop]
    apply Fintype.card_eq_zero_iff.mpr
    refine ⟨fun x ↦ ?_⟩
    have hx := (heval x.1).symm.trans x.2
    have hdiv : (a : ZMod q) ∣ (b : ZMod q) := by
      refine ⟨-x.1, ?_⟩
      linear_combination hx
    have hua : IsUnit (a : ZMod q) :=
      (hab.map (Int.castRingHom (ZMod q))).isUnit_of_dvd hdiv
    exact hcop ((isUnit_intCast_zmod_iff a q).mp hua)

/-- Unconditional positive linear root-count mean for every primitive affine
polynomial with nonzero leading coefficient. The constant is explicit. -/
theorem tendsto_rootCountSummatory_affine (a b : ℤ) (ha : a ≠ 0)
    (hab : IsCoprime a b) :
    Tendsto (fun N : ℕ ↦
      rootCountSummatory (polynomialAbsValue (C a * X + C b)) N / (N : ℝ))
      atTop (𝓝 ((a.natAbs.totient : ℝ) / (a.natAbs : ℝ))) := by
  have hsum (N : ℕ) :
      rootCountSummatory (polynomialAbsValue (C a * X + C b)) N =
        (((Finset.Ioc 0 N).filter (fun q ↦ a.natAbs.Coprime q)).card : ℝ) := by
    unfold rootCountSummatory
    rw [← Finset.sum_boole]
    apply Finset.sum_congr rfl
    intro q hq
    rw [rootCount_affine a b hab q (Finset.mem_Ioc.mp hq).1]
    split_ifs <;> norm_num
  simpa only [hsum] using tendsto_coprime_count_div a.natAbs (Int.natAbs_pos.mpr ha)

/-- The requested prerequisite, fully proved for all irreducible degree-one
integer polynomials, including nonmonic ones. -/
theorem exists_pos_rootMean_of_natDegree_eq_one (f : ℤ[X]) (hf : Irreducible f)
    (hdeg : f.natDegree = 1) :
    ∃ κ > (0 : ℝ), Tendsto (fun N : ℕ ↦
      rootCountSummatory (polynomialAbsValue f) N / (N : ℝ)) atTop (𝓝 κ) := by
  obtain ⟨a, ha, b, rfl⟩ := natDegree_eq_one.mp hdeg
  have hab := affine_coefficients_isCoprime a b (hf.isPrimitive (by omega))
  refine ⟨(a.natAbs.totient : ℝ) / (a.natAbs : ℝ), ?_,
    tendsto_rootCountSummatory_affine a b ha hab⟩
  exact div_pos (Nat.cast_pos.mpr (Nat.totient_pos.mpr (Int.natAbs_pos.mpr ha)))
    (Nat.cast_pos.mpr (Int.natAbs_pos.mpr ha))

/-- A direct unconditional downstream consequence in degree one: the
root-reciprocal sum has a strictly positive logarithmic mean. -/
theorem exists_pos_rootReciprocalMean_of_natDegree_eq_one (f : ℤ[X]) (hf : Irreducible f)
    (hdeg : f.natDegree = 1) :
    ∃ κ > (0 : ℝ), Tendsto (fun N : ℕ ↦
      rootReciprocalSum (polynomialAbsValue f) N / Real.log (N : ℝ)) atTop (𝓝 κ) := by
  obtain ⟨κ, hκ, hP⟩ := exists_pos_rootMean_of_natDegree_eq_one f hf hdeg
  exact ⟨κ, hκ, tendsto_rootReciprocalSum_of_rootCountSummatory hP⟩

end Erdos975Support
