import Submission.DifferenceSignEnergyExplore
import Submission.MixedPrimeIntervalExplore

/-! One prime and one nested parameter family with short signed fibers for
both sums and differences. These estimates are within one finite field. -/
namespace Erdos66SumDifferenceParameters
open Polynomial Erdos66CrossGraph Erdos66FiniteField Erdos66PrimeInterval
  Erdos66MixedPrimeInterval Erdos66DifferenceSignEnergy Erdos66PolynomialMixedEnergy
  Erdos66PrefixSign Erdos66SignEnergy Erdos66IntervalSign
open scoped Classical

lemma crossCharFiber_neg {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (U V : Finset F) (w : F) :
    crossCharFiber U (V.image Neg.neg) w = quadraticChar F (-1) *
      ∑ u ∈ U, ∑ v ∈ V, if u-v=w then quadraticChar F u * quadraticChar F v else 0 := by
  unfold crossCharFiber
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.sum_image (fun _ _ _ _ h ↦ neg_injective h),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  have hn : quadraticChar F (-v) = quadraticChar F (-1)*quadraticChar F v := by
    rw [← map_mul,neg_one_mul]
  rw [hn]
  simp only [sub_eq_add_neg]
  split_ifs <;> ring

lemma interval_reflected_cross_eq {p a h k : ℕ} [Fact p.Prime]
    (hp : a+h < p) (hq : a+k < p) (P Q : ℤ[X])
    (hcP : ∀ i < h, quadraticChar (ZMod p) ((a+i : ℕ) : ZMod p) = P.coeff i)
    (hcQ : ∀ i < k, quadraticChar (ZMod p) ((a+i : ℕ) : ZMod p) = Q.coeff i)
    (w : ZMod p) :
    (crossCharFiber (parameterInterval p a h) ((parameterInterval p a k).image Neg.neg) w : ℝ) =
      (quadraticChar (ZMod p) (-1) : ℝ)*differencePush p h k P Q w := by
  rw [crossCharFiber_neg,Int.cast_mul,differencePush_formula]
  congr 1
  unfold parameterInterval
  rw [Finset.sum_image (interval_injOn hp)]
  simp_rw [Finset.sum_image (interval_injOn hq)]
  simp only [Int.cast_sum,Int.cast_ite,Int.cast_mul,Int.cast_zero]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hcP i (Finset.mem_range.mp hi),hcQ j (Finset.mem_range.mp hj)]
  simp only [Nat.cast_add,add_sub_add_left_eq_sub]

lemma interval_reflected_cross_l1_sq {p a h k : ℕ} [Fact p.Prime]
    (hp : a+h < p) (hq : a+k < p) (hp2 : 2*h ≤ p) (hq2 : 2*k ≤ p)
    {P Q : ℤ[X]} (hP : SupportedBelow P h) (hQ : SupportedBelow Q k)
    (hcP : ∀ i < h, quadraticChar (ZMod p) ((a+i : ℕ) : ZMod p) = P.coeff i)
    (hcQ : ∀ i < k, quadraticChar (ZMod p) ((a+i : ℕ) : ZMod p) = Q.coeff i)
    (hPE : Erdos66SignEnergy.energy P h ≤ 2*(h : ℤ)^2)
    (hQE : Erdos66SignEnergy.energy Q k ≤ 2*(k : ℤ)^2) :
    (∑ w : ZMod p, |crossCharFiber (parameterInterval p a h)
      ((parameterInterval p a k).image Neg.neg) w|)^2 ≤
        2*(h : ℤ)*k*(h+k+1) := by
  have hle : (∑ w : ZMod p, |(crossCharFiber (parameterInterval p a h)
      ((parameterInterval p a k).image Neg.neg) w : ℝ)|) ≤
        ∑ w : ZMod p, |differencePush p h k P Q w| := by
    apply Finset.sum_le_sum
    intro w hw
    rw [interval_reflected_cross_eq hp hq P Q hcP hcQ,abs_mul]
    have hchar : |(quadraticChar (ZMod p) (-1) : ℝ)| ≤ 1 := by
      exact_mod_cast quadraticChar_abs_le_one (-(1 : ZMod p))
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hchar (abs_nonneg _)
  have hE := differencePush_l1_sq_le p hP hQ hp2 hq2 hPE hQE
  have hl0 : 0 ≤ ∑ w : ZMod p, |(crossCharFiber (parameterInterval p a h)
      ((parameterInterval p a k).image Neg.neg) w : ℝ)| :=
    Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
  have hr0 : 0 ≤ ∑ w : ZMod p, |differencePush p h k P Q w| :=
    Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
  have hh := ((sq_le_sq₀ hl0 hr0).mpr hle).trans hE
  exact_mod_cast hh

/-- Simultaneous signed sum and difference bounds for every pair of prefixes.
The prime can still be chosen arbitrarily large after the maximum index. -/
theorem exists_sum_difference_parameter_family (H N : ℕ) :
    ∃ p : ℕ, ∃ hp : p.Prime,
      letI : Fact p.Prime := ⟨hp⟩
      N < p ∧ p%8=1 ∧ ∃ U : ℕ → Finset (ZMod p), Monotone U ∧
        (∀ h ≤ H, (U h).card=h) ∧ (∀ u ∈ U H, u ≠ 0) ∧
        (∀ u ∈ U H, ∀ v ∈ U H, u+v ≠ 0) ∧
        ∀ h ≤ H, ∀ k ≤ H,
          (∑ w : ZMod p, |crossCharFiber (U h) (U k) w|)^2 ≤ 2*(h : ℤ)*k*(h+k+1) ∧
          (∑ w : ZMod p, |crossCharFiber (U h) ((U k).image Neg.neg) w|)^2 ≤
            2*(h : ℤ)*k*(h+k+1) := by
  obtain ⟨P,hP,hsign,hE⟩ := exists_all_prefix_energies H
  obtain ⟨a,ha,hall⟩ := exists_interval_all_signs H
  obtain ⟨p,hp,hpN,hp8,hchars⟩ := hall (fun i ↦ P.coeff i.val)
    (fun i ↦ hsign i.val i.isLt) (max N (2*(a+H)))
  letI : Fact p.Prime := ⟨hp⟩
  have hbig : 2*(a+H) < p := lt_of_le_of_lt (le_max_right _ _) hpN
  have hchar (i : ℕ) (hi : i < H) :
      quadraticChar (ZMod p) ((a+i : ℕ) : ZMod p) = P.coeff i := by
    simpa only [legendreSym,Int.cast_natCast] using hchars ⟨i,hi⟩
  refine ⟨p,hp,lt_of_le_of_lt (le_max_left _ _) hpN,hp8,
    parameterInterval p a,parameterInterval_mono p a,?_,?_,?_,?_⟩
  · intro h hh
    exact parameterInterval_card (by omega)
  · intro u hu
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hu
    have hi' := Finset.mem_range.mp hi
    intro hz
    have hv := congrArg ZMod.val hz
    rw [ZMod.val_natCast_of_lt (by omega),ZMod.val_zero] at hv
    omega
  · intro u hu v hv
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hv
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    intro hz
    rw [← Nat.cast_add] at hz
    have hv := congrArg ZMod.val hz
    rw [ZMod.val_natCast_of_lt (by omega),ZMod.val_zero] at hv
    omega
  · intro h hh k hk
    have hPE := (hE h hh).trans (show 2*(h : ℤ)^2-h ≤ 2*(h : ℤ)^2 by omega)
    have hQE := (hE k hk).trans (show 2*(k : ℤ)^2-k ≤ 2*(k : ℤ)^2 by omega)
    have hcP (i : ℕ) (hi : i < h) :
        quadraticChar (ZMod p) ((a+i : ℕ) : ZMod p) = (cutPoly P h).coeff i := by
      rw [coeff_cutPoly,if_pos hi]
      exact hchar i (by omega)
    have hcQ (i : ℕ) (hi : i < k) :
        quadraticChar (ZMod p) ((a+i : ℕ) : ZMod p) = (cutPoly P k).coeff i := by
      rw [coeff_cutPoly,if_pos hi]
      exact hchar i (by omega)
    constructor
    · have hh' := interval_cross_l1_sq (by omega : a+h < p) (by omega : a+k < p)
        (cutPoly_supported P h) (cutPoly_supported P k) hcP hcQ
        (polynomial_mixed_l1_sq (cutPoly_supported P h) (cutPoly_supported P k) hPE hQE)
      exact hh'.trans (by nlinarith [mul_nonneg (Int.natCast_nonneg h) (Int.natCast_nonneg k)])
    · exact interval_reflected_cross_l1_sq (by omega) (by omega) (by omega) (by omega)
        (cutPoly_supported P h) (cutPoly_supported P k) hcP hcQ hPE hQE

end Erdos66SumDifferenceParameters
