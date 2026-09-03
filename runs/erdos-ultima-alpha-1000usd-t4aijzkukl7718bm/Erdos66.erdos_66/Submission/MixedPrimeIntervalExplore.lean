import Submission.CrossGraphExplore
import Submission.PrimeIntervalExplore
import Submission.PolynomialMixedEnergyExplore

/-! Coherent parameter intervals with simultaneous mixed-fiber estimates.
All sets here live in the same prime-field plane. -/
namespace Erdos66MixedPrimeInterval
open Polynomial Erdos66CrossGraph Erdos66PrimeInterval Erdos66SignEnergy
  Erdos66PrefixSign Erdos66PolynomialMixedEnergy Erdos66IntervalSign

lemma finitePush_l1_le {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {ι : Type*} (S : Finset ι) (f : ι → G) (c : ι → ℝ) :
    (∑ z : G, |finitePush S f c z|) ≤ ∑ i ∈ S, |c i| := by
  calc
    _ ≤ ∑ z : G, ∑ i ∈ S, |if f i = z then c i else 0| :=
      Finset.sum_le_sum (fun _ _ ↦ Finset.abs_sum_le_sum_abs _ _)
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [apply_ite abs, abs_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma interval_cross_eq_conv {p a h k : ℕ} [Fact p.Prime]
    (hp : a + h < p) (hq : a + k < p) (P Q : ℤ[X])
    (hcP : ∀ i < h, quadraticChar (ZMod p) ((a + i : ℕ) : ZMod p) = P.coeff i)
    (hcQ : ∀ i < k, quadraticChar (ZMod p) ((a + i : ℕ) : ZMod p) = Q.coeff i)
    (w : ZMod p) :
    (crossCharFiber (parameterInterval p a h) (parameterInterval p a k) w : ℝ) =
      Erdos66MixedEnergy.conv (polyPush p h P) (polyPush p k Q) (w - (2 * a : ℕ)) := by
  unfold crossCharFiber parameterInterval
  rw [Finset.sum_image (interval_injOn hp)]
  simp_rw [Finset.sum_image (interval_injOn hq)]
  simp only [Int.cast_sum, Int.cast_ite, Int.cast_mul, Int.cast_zero]
  rw [polyPush, polyPush, conv_finitePush]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hcP i (Finset.mem_range.mp hi), hcQ j (Finset.mem_range.mp hj)]
  congr 1
  apply propext
  constructor <;> intro he <;> push_cast at he ⊢ <;> linear_combination he

lemma interval_cross_l1_sq {p a h k : ℕ} [Fact p.Prime]
    (hp : a + h < p) (hq : a + k < p) {P Q : ℤ[X]}
    (hP : SupportedBelow P h) (hQ : SupportedBelow Q k)
    (hcP : ∀ i < h, quadraticChar (ZMod p) ((a + i : ℕ) : ZMod p) = P.coeff i)
    (hcQ : ∀ i < k, quadraticChar (ZMod p) ((a + i : ℕ) : ZMod p) = Q.coeff i)
    (hE : (∑ i ∈ Finset.range (h + k), |(P * Q).coeff i|) ^ 2 ≤ 2 * (h : ℤ) * k * (h + k)) :
    (∑ w : ZMod p, |crossCharFiber (parameterInterval p a h) (parameterInterval p a k) w|) ^ 2 ≤
      2 * (h : ℤ) * k * (h + k) := by
  have hb :
      (∑ w : ZMod p, |(crossCharFiber (parameterInterval p a h) (parameterInterval p a k) w : ℝ)|) ≤
        ∑ i ∈ Finset.range (h + k), |((P * Q).coeff i : ℝ)| := by
    simp_rw [interval_cross_eq_conv hp hq P Q hcP hcQ, conv_polyPush p hP hQ]
    have he := Equiv.sum_comp (Equiv.subRight ((2 * a : ℕ) : ZMod p))
      (fun w ↦ |polyPush p (h + k) (P * Q) w|)
    change (∑ w : ZMod p, |polyPush p (h + k) (P * Q) (w - (2 * a : ℕ))|) = _ at he
    rw [he]
    exact finitePush_l1_le _ _ _
  have hb' :
      (∑ w : ZMod p, |crossCharFiber (parameterInterval p a h) (parameterInterval p a k) w|) ≤
        ∑ i ∈ Finset.range (h + k), |(P * Q).coeff i| := by exact_mod_cast hb
  have hnon : 0 ≤ ∑ w : ZMod p,
      |crossCharFiber (parameterInterval p a h) (parameterInterval p a k) w| :=
    Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
  have hnon' : 0 ≤ ∑ i ∈ Finset.range (h + k), |(P * Q).coeff i| :=
    Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
  nlinarith

lemma parameterInterval_mono (p a : ℕ) : Monotone (parameterInterval p a) := by
  intro h k hk
  apply Finset.image_subset_image
  exact Finset.range_mono hk

/-- Arbitrarily large primes support one nested interval family with all mixed
signed-fiber bounds, not merely separate self-convolution bounds. -/
theorem exists_prime_parameter_family (H N : ℕ) :
    ∃ p : ℕ, ∃ hp : p.Prime,
      letI : Fact p.Prime := ⟨hp⟩
      N < p ∧ p % 8 = 1 ∧ ∃ U : ℕ → Finset (ZMod p), Monotone U ∧
        (∀ h ≤ H, (U h).card = h) ∧
        (∀ u ∈ U H, u ≠ 0) ∧
        (∀ u ∈ U H, ∀ v ∈ U H, u + v ≠ 0) ∧
        ∀ h ≤ H, ∀ k ≤ H,
          (∑ w : ZMod p, |crossCharFiber (U h) (U k) w|) ^ 2 ≤
            2 * (h : ℤ) * k * (h + k) := by
  obtain ⟨P, hP, hsign, hE⟩ := exists_all_mixed_prefix_bounds H
  obtain ⟨a, ha, hall⟩ := exists_interval_all_signs H
  obtain ⟨p, hp, hpN, hp8, hchars⟩ := hall (fun i ↦ P.coeff i.val)
    (fun i ↦ hsign i.val i.isLt) (max N (2 * (a + H)))
  letI : Fact p.Prime := ⟨hp⟩
  have hbig : 2 * (a + H) < p := lt_of_le_of_lt (le_max_right _ _) hpN
  have hsmall : a + H < p := by omega
  have hchar (i : ℕ) (hi : i < H) :
      quadraticChar (ZMod p) ((a + i : ℕ) : ZMod p) = P.coeff i := by
    simpa only [legendreSym, Int.cast_natCast] using hchars ⟨i, hi⟩
  refine ⟨p, hp, lt_of_le_of_lt (le_max_left _ _) hpN, hp8,
    parameterInterval p a, parameterInterval_mono p a, ?_, ?_, ?_, ?_⟩
  · intro h hh
    exact parameterInterval_card (by omega)
  · intro u hu
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    have hi' := Finset.mem_range.mp hi
    intro hz
    have hv := congrArg ZMod.val hz
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_zero] at hv
    omega
  · intro u hu v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    intro hz
    rw [← Nat.cast_add] at hz
    have hv := congrArg ZMod.val hz
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_zero] at hv
    omega
  · intro h hh k hk
    apply interval_cross_l1_sq (by omega : a + h < p) (by omega : a + k < p)
      (cutPoly_supported P h) (cutPoly_supported P k) ?_ ?_ (hE h hh k hk)
    · intro i hi
      rw [coeff_cutPoly, if_pos hi]
      exact hchar i (lt_of_lt_of_le hi hh)
    · intro i hi
      rw [coeff_cutPoly, if_pos hi]
      exact hchar i (lt_of_lt_of_le hi hk)

end Erdos66MixedPrimeInterval
