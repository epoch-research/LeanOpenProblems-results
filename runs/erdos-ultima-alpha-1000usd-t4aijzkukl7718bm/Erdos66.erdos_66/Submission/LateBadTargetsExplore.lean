import Submission.WeightedProfileCharacterExplore
import Submission.SignedRepBernoulliExplore

/-! A large shift forces the exceptional signed-mean targets to occur late.
The bound is uniform in the field and in the selected character translation. -/
namespace Erdos66LateBadTargets
open Erdos66WeightedProfileCharacter Erdos66RealWeightedCharacterEnergy
  Erdos66SignedRepBernoulli Erdos66FiniteRepBernoulli Erdos66ConstantProfile
open scoped Classical
set_option maxHeartbeats 1500000

lemma profileWeight_product_uniform (μ : ℝ) (s i j : ℕ) (hμ : 0 ≤ μ) :
    profileWeight μ s i*profileWeight μ s j ≤ μ/((s : ℝ)+1) := by
  have hb : b (i+s)*b (j+s) ≤ (b s)^2 := by
    simpa only [pow_two] using mul_le_mul (b_antitone (by omega : s ≤ i+s))
      (b_antitone (by omega : s ≤ j+s)) (b_pos _).le (b_pos _).le
  have hb' : (b s)^2 ≤ 1/((s : ℝ)+1) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ)<(s : ℝ)+1)).mpr
    nlinarith [b_square_bound s]
  have hm := mul_le_mul_of_nonneg_left (hb.trans hb') hμ
  have he : profileWeight μ s i*profileWeight μ s j=μ*(b (i+s)*b (j+s)) := by
    dsimp [profileWeight]
    rw [show Real.sqrt μ*b (i+s)*(Real.sqrt μ*b (j+s)) =
      (Real.sqrt μ)^2*(b (i+s)*b (j+s)) by ring,Real.sq_sqrt hμ]
  simpa only [he,mul_one_div] using hm

lemma profile_signed_fiber_bound (p : ℕ) [Fact p.Prime]
    (μ : ℝ) (s L q : ℕ) (hμ : 0 ≤ μ) (a : ZMod p) :
    |signedFiber (L+1) (profileWeight μ s) a q| ≤
      ((q : ℝ)+1)*μ/((s : ℝ)+1) := by
  let f : ℕ → ℝ := fun i ↦ profileWeight μ s i*(quadraticChar (ZMod p) (a+i) : ℝ)
  have hχ (i : ℕ) : |(quadraticChar (ZMod p) (a+i) : ℝ)| ≤ 1 := by
    exact_mod_cast Erdos66FiniteField.quadraticChar_abs_le_one (a+(i : ZMod p))
  have hf (i : ℕ) : |f i| ≤ profileWeight μ s i := by
    have hp : 0 ≤ profileWeight μ s i := mul_nonneg (Real.sqrt_nonneg μ) (b_pos _).le
    dsimp [f]
    rw [abs_mul,abs_of_nonneg hp]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hχ i) hp
  have hprod (i j : ℕ) : |f i*f j| ≤ μ/((s : ℝ)+1) := by
    rw [abs_mul]
    exact (mul_le_mul (hf i) (hf j) (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg μ) (b_pos _).le)).trans
      (profileWeight_product_uniform μ s i j hμ)
  change |Erdos66SharedParameterKernel.labelFiber (L+1) f q| ≤ _
  rw [←full_pairs_eq_labelFiber_all L q f,pairs_sum_range L q (fun i j ↦ f i*f j)]
  calc
    _ ≤ ∑ i∈Finset.range (q+1), |if i ≤ L ∧ q-i ≤ L then f i*f (q-i) else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i∈Finset.range (q+1), μ/((s : ℝ)+1) := by
      apply Finset.sum_le_sum
      intro i hi
      split_ifs
      · exact hprod i (q-i)
      · simpa only [abs_zero] using div_nonneg hμ (by positivity : (0 : ℝ) ≤ (s : ℝ)+1)
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]; ring

/-- Applied to the binary construction's threshold epsilon*mu/4, this says
that every exceptional center q satisfies epsilon*(s+1)<4*(q+1). -/
theorem badTargets_location (p : ℕ) [Fact p.Prime] (μ ε : ℝ) (hμ : 0<μ)
    (s L : ℕ) (a : ZMod p) (q : ℕ)
    (hq : q∈badTargets (L+1) (profileWeight μ s) a (ε*μ)) :
    ε*((s : ℝ)+1)<(q : ℝ)+1 := by
  have hh := (Finset.mem_filter.mp hq).2
  have hb := profile_signed_fiber_bound p μ s L q hμ.le a
  have hm := (lt_div_iff₀ (by positivity : (0 : ℝ)<(s : ℝ)+1)).mp (hh.trans_le hb)
  have he : (ε*((s : ℝ)+1))*μ<((q : ℝ)+1)*μ := by nlinarith
  exact (mul_lt_mul_iff_left₀ hμ).mp he

end Erdos66LateBadTargets
