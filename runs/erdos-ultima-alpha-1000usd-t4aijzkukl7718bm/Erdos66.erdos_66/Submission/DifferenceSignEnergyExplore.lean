import Submission.PolynomialMixedEnergyExplore

/-! A small self-convolution energy also controls signed difference fibers.
The support-size estimate retains the short interval scale, not the much
larger ambient modulus. -/
namespace Erdos66DifferenceSignEnergy
open Polynomial Erdos66MixedEnergy Erdos66PolynomialMixedEnergy Erdos66SignEnergy
open scoped Classical

section Group
variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def reflect (f : G → ℝ) (z : G) : ℝ := f (-z)

lemma corr_reflect (f : G → ℝ) (t : G) : corr (reflect f) t = corr f t := by
  unfold corr reflect
  rw [← Equiv.sum_comp (Equiv.neg G)]
  simp only [Equiv.neg_apply,neg_neg,neg_add_rev]
  have hh := corr_neg f t
  unfold corr at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro x hx
  congr 2
  abel

lemma energy_reflect_right (f g : G → ℝ) :
    Erdos66MixedEnergy.energy f (reflect g) = Erdos66MixedEnergy.energy f g := by
  simp only [energy_eq_corr_inner,corr_reflect]

omit [AddCommGroup G] in
lemma l1_sq_le_support_energy [DecidableEq G] (f : G → ℝ) (S : Finset G)
    (hs : ∀ z, z ∉ S → f z = 0) :
    (∑ z : G, |f z|)^2 ≤ (S.card : ℝ)*(∑ z : G, f z^2) := by
  have he : (∑ z : G, |f z|) = ∑ z ∈ S, |f z| := by
    symm
    apply Finset.sum_subset (Finset.subset_univ S)
    intro z hz hzS
    rw [hs z hzS,abs_zero]
  rw [he]
  have hcs := sq_sum_le_card_mul_sum_sq (s := S) (f := fun z ↦ |f z|)
  simp only [sq_abs] at hcs
  apply hcs.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    (fun z hz hz' ↦ sq_nonneg _)

end Group

noncomputable def differencePush (p h k : ℕ) [NeZero p] (P Q : ℤ[X]) : ZMod p → ℝ :=
  conv (polyPush p h P) (reflect (polyPush p k Q))

lemma reflect_polyPush (p k : ℕ) (Q : ℤ[X]) :
    reflect (polyPush p k Q) =
      finitePush (Finset.range k) (fun j : ℕ ↦ -(j : ZMod p)) (fun j ↦ (Q.coeff j : ℝ)) := by
  funext z
  unfold reflect polyPush finitePush
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  apply propext
  constructor <;> intro hh <;> simpa only [neg_neg] using congrArg Neg.neg hh

lemma differencePush_formula (p h k : ℕ) [NeZero p] (P Q : ℤ[X]) (z : ZMod p) :
    differencePush p h k P Q z =
      ∑ i ∈ Finset.range h, ∑ j ∈ Finset.range k,
        if (i : ZMod p)-(j : ZMod p)=z then (P.coeff i : ℝ)*Q.coeff j else 0 := by
  unfold differencePush
  rw [reflect_polyPush,polyPush,conv_finitePush]
  simp only [sub_eq_add_neg]

noncomputable def differenceSupport (p h k : ℕ) : Finset (ZMod p) :=
  (Finset.Icc (-(k : ℤ)) (h : ℤ)).image (fun x : ℤ ↦ (x : ZMod p))

lemma differenceSupport_card (p h k : ℕ) : (differenceSupport p h k).card ≤ h+k+1 := by
  apply Finset.card_image_le.trans
  rw [Int.card_Icc]
  omega

lemma difference_mem_support (p h k i j : ℕ) (hi : i < h) (hj : j < k) :
    (i : ZMod p)-(j : ZMod p) ∈ differenceSupport p h k := by
  apply Finset.mem_image.mpr
  refine ⟨(i : ℤ)-(j : ℤ),Finset.mem_Icc.mpr ⟨by omega,by omega⟩,?_⟩
  simp

lemma differencePush_zero_off (p h k : ℕ) [NeZero p] (P Q : ℤ[X]) (z : ZMod p)
    (hz : z ∉ differenceSupport p h k) : differencePush p h k P Q z = 0 := by
  rw [differencePush_formula]
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  apply if_neg
  intro he
  exact hz (he ▸ difference_mem_support p h k i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj))

lemma differencePush_energy_le (p : ℕ) [NeZero p] {P Q : ℤ[X]} {h k : ℕ}
    (hP : SupportedBelow P h) (hQ : SupportedBelow Q k)
    (hp : 2*h ≤ p) (hq : 2*k ≤ p)
    (hPE : Erdos66SignEnergy.energy P h ≤ 2*(h : ℤ)^2)
    (hQE : Erdos66SignEnergy.energy Q k ≤ 2*(k : ℤ)^2) :
    (∑ z : ZMod p, differencePush p h k P Q z ^ 2) ≤ 2*(h : ℝ)*k := by
  change Erdos66MixedEnergy.energy (polyPush p h P) (reflect (polyPush p k Q)) ≤ _
  rw [energy_reflect_right]
  apply mixed_energy_le (Nat.cast_nonneg h) (Nat.cast_nonneg k)
  · rw [mixed_energy_polyPush p hP hP (by omega)]
    have he : h+h = 2*h := by omega
    rw [he,← pow_two]
    exact_mod_cast hPE
  · rw [mixed_energy_polyPush p hQ hQ (by omega)]
    have he : k+k = 2*k := by omega
    rw [he,← pow_two]
    exact_mod_cast hQE

/-- The reflected short-interval convolution has the same `O((hk(h+k))^(1/2))`
L1 bound as the ordinary signed sum convolution. -/
theorem differencePush_l1_sq_le (p : ℕ) [NeZero p] {P Q : ℤ[X]} {h k : ℕ}
    (hP : SupportedBelow P h) (hQ : SupportedBelow Q k)
    (hp : 2*h ≤ p) (hq : 2*k ≤ p)
    (hPE : Erdos66SignEnergy.energy P h ≤ 2*(h : ℤ)^2)
    (hQE : Erdos66SignEnergy.energy Q k ≤ 2*(k : ℤ)^2) :
    (∑ z : ZMod p, |differencePush p h k P Q z|)^2 ≤
      2*(h : ℝ)*k*(h+k+1) := by
  have he := differencePush_energy_le p hP hQ hp hq hPE hQE
  have hcs := l1_sq_le_support_energy (differencePush p h k P Q) (differenceSupport p h k)
    (differencePush_zero_off p h k P Q)
  have hc : ((differenceSupport p h k).card : ℝ) ≤ (h : ℝ)+k+1 := by
    exact_mod_cast differenceSupport_card p h k
  have hh := mul_le_mul hc he (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)) (by positivity : (0 : ℝ) ≤ h+k+1)
  nlinarith

end Erdos66DifferenceSignEnergy
