import Submission.AutocorrelationStabilityExplore

/-! Stability of convolution energy under a real sign character. Auxiliary
estimates only; these do not settle the logarithmic representation conjecture. -/
namespace Erdos66TwistedEnergy
open Erdos66MixedEnergy Erdos66AutocorrelationStability
  Erdos66ResidueSeries Erdos66Generating Erdos66WeightedPushEnergy
  Erdos66WeightedSquareStability
open scoped Classical Topology
open Filter AdditiveCombinatorics
set_option maxHeartbeats 2000000

section Finite
variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma corr_twist (χ f : G → ℝ) (hχ : ∀ x y, χ (x+y)=χ x*χ y)
    (hχ2 : ∀ x, χ x^2=1) (z : G) :
    corr (fun x ↦ χ x*f x) z=χ z*corr f z := by
  simp only [corr,hχ,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  calc
    _ = χ x^2*(χ z*(f x*f (x+z))) := by ring
    _ = _ := by rw [hχ2,one_mul]

/-- A sign character turns mixed convolution energy into a signed
inner product of autocorrelations. -/
lemma twisted_energy_eq (χ f : G → ℝ) (hχ : ∀ x y, χ (x+y)=χ x*χ y)
    (hχ2 : ∀ x, χ x^2=1) :
    energy f (fun x ↦ χ x*f x)=∑ z : G, χ z*corr f z^2 := by
  rw [energy_eq_corr_inner]
  simp_rw [corr_twist χ f hχ hχ2]
  apply Finset.sum_congr rfl
  intro z hz
  ring

/-- Stability in the self-convolution squared norm controls the DIFFERENCE
of the two twisted energies. This is not a pointwise estimate. -/
theorem twisted_energy_difference_sq (χ f g : G → ℝ)
    (hχ : ∀ x y, χ (x+y)=χ x*χ y) (hχ2 : ∀ x, χ x^2=1) :
    (energy f (fun x ↦ χ x*f x)-energy g (fun x ↦ χ x*g x))^2 ≤
      (∑ z : G, (conv f f z-conv g g z)^2)*(2*energy f f+2*energy g g) := by
  have hid : energy f (fun x ↦ χ x*f x)-energy g (fun x ↦ χ x*g x)=
      ∑ z : G, (corr f z-corr g z)*(χ z*(corr f z+corr g z)) := by
    rw [twisted_energy_eq χ f hχ hχ2,twisted_energy_eq χ g hχ hχ2,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro z hz
    ring
  rw [hid]
  have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun z ↦ corr f z-corr g z) (fun z ↦ χ z*(corr f z+corr g z))
  have hb : (∑ z : G, (χ z*(corr f z+corr g z))^2) ≤
      2*energy f f+2*energy g g := by
    simp_rw [mul_pow,hχ2,one_mul]
    rw [energy_eq_corr_inner f f,energy_eq_corr_inner g g,
      Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun z _ ↦ by nlinarith [sq_nonneg (corr f z-corr g z)])
  exact hs.trans (mul_le_mul (corr_error_le_conv_error f g) hb
    (Finset.sum_nonneg (fun z _ ↦ sq_nonneg _))
    (Finset.sum_nonneg (fun z _ ↦ sq_nonneg _)))

end Finite

noncomputable def alt (f : ℕ → ℝ) (n : ℕ) : ℝ := (-1)^n*f n
noncomputable def twistConv (f : ℕ → ℝ) (n : ℕ) : ℝ := sumConv f (alt f) n
noncomputable def parityChar (m : ℕ) (z : ZMod m) : ℝ := (-1)^z.val

lemma parityChar_nat (m : ℕ) [NeZero m] (hm : Even m) (n : ℕ) :
    parityChar m (n : ZMod m)=(-1 : ℝ)^n := by
  simpa only [parityChar,ZMod.val_natCast] using
    (pow_eq_pow_mod n (hm.neg_one_pow (α := ℝ))).symm

lemma parityChar_add (m : ℕ) [NeZero m] (hm : Even m) (x y : ZMod m) :
    parityChar m (x+y)=parityChar m x*parityChar m y := by
  simp only [parityChar,ZMod.val_add]
  rw [← pow_eq_pow_mod _ (hm.neg_one_pow (α := ℝ)),pow_add]

lemma parityChar_sq (m : ℕ) (x : ZMod m) : parityChar m x^2=1 := by
  rw [parityChar,← pow_mul,Nat.mul_comm x.val 2,pow_mul]
  norm_num

lemma summable_alt {f : ℕ → ℝ} (hf : Summable f) : Summable (alt f) := hf.alternating

lemma push_alt (m : ℕ) [NeZero m] (hm : Even m) (f : ℕ → ℝ) (z : ZMod m) :
    push m (alt f) z=parityChar m z*push m f z := by
  unfold push
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  by_cases hn : (n : ZMod m)=z
  · simp only [residueTerm,if_pos hn,alt]
    rw [← hn,parityChar_nat m hm]
  · simp only [residueTerm,if_neg hn,mul_zero]

lemma push_tendsto {f : ℕ → ℝ} (hf : Summable f) (n : ℕ) :
    Tendsto (fun k : ℕ ↦ push (k+1) f (n : ZMod (k+1))) atTop (𝓝 (f n)) := by
  have hh : Tendsto (fun k : ℕ ↦ ∑' j : ℕ,
      if (j : ZMod (k+1))=(n : ZMod (k+1)) then f j else 0)
      atTop (𝓝 (∑' j : ℕ, if j=n then f j else 0)) := by
    apply tendsto_tsum_of_dominated_convergence hf.norm
    · intro j
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (max j n)] with k hk
      have hj : j<k+1 := by omega
      have hn : n<k+1 := by omega
      simp only [ZMod.natCast_eq_natCast_iff',Nat.mod_eq_of_lt hj,Nat.mod_eq_of_lt hn]
    · apply Eventually.of_forall
      intro k j
      split_ifs
      · exact le_rfl
      · simpa only [norm_zero] using norm_nonneg (f j)
  simpa only [push,residueTerm,tsum_ite_eq] using hh

lemma push_even_tendsto {f : ℕ → ℝ} (hf : Summable f) (n : ℕ) :
    Tendsto (fun k : ℕ ↦ push (2*(k+1)) f (n : ZMod (2*(k+1)))) atTop (𝓝 (f n)) := by
  have ht : Tendsto (fun k : ℕ ↦ 2*k+1) atTop atTop :=
    tendsto_atTop_mono (fun k ↦ by dsimp; omega) tendsto_id
  simpa only [Function.comp_apply,show ∀ k : ℕ, 2*k+1+1=2*(k+1) from fun k ↦ by omega]
    using (push_tendsto hf n).comp ht

end Erdos66TwistedEnergy
