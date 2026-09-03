import Submission.ResidueEnergyProjectionExplore
import Submission.NaturalAutocorrelationExplore

/-! Exact natural-half-line transfer of finite residue-projection stability.
All energies use the SAME geometric weighting; no periodization overhead
or change of radius is retained. -/
namespace Erdos66NaturalResidueProjection
open Erdos66ResidueEnergyProjection Erdos66MixedEnergy Erdos66NaturalAutocorrelation
  Erdos66ResidueSeries Erdos66Generating Erdos66WeightedSquareStability
open scoped Classical Topology
open Filter AdditiveCombinatorics
set_option maxHeartbeats 2400000

lemma summable_conv {f g : ℕ → ℝ} (hf : Summable f) (hg : Summable g) : Summable (sumConv f g) :=
  summable_sum_mul_antidiagonal_of_summable_mul (summable_mul_of_summable_norm hf.norm hg.norm)

lemma summable_square {f : ℕ → ℝ} (hf : Summable f) : Summable (fun n ↦ f n^2) := by
  have hi : Function.Injective (fun n : ℕ ↦ (n,n)) := by intro a b h; exact congrArg Prod.fst h
  simpa only [Function.comp_def,pow_two] using (summable_pair_mul hf).comp_injective hi

lemma push_div_const (L : ℕ) [NeZero L] (f : ℕ → ℝ) (a : ℝ) (z : ZMod L) :
    push L (fun n ↦ f n/a) z=push L f z/a := by
  unfold push
  rw [← tsum_div_const]
  apply tsum_congr
  intro n
  unfold residueTerm
  split_ifs <;> simp

variable (m : ℕ) [NeZero m]

noncomputable def quotient (k : ℕ) : ZMod (m*(k+1)) →+ ZMod m :=
  (ZMod.castHom (dvd_mul_right m (k+1)) (ZMod m)).toAddMonoidHom

lemma quotient_nat (k n : ℕ) : quotient m k (n : ZMod (m*(k+1)))=(n : ZMod m) := by
  simp [quotient]

lemma push_piece (k : ℕ) (f : ℕ → ℝ) (i : ZMod m) (z : ZMod (m*(k+1))) :
    piece (quotient m k) (push (m*(k+1)) f) i z=
      push (m*(k+1)) (residueTerm m f i) z := by
  have he (n : ℕ) : residueTerm (m*(k+1)) (residueTerm m f i) z n=
      if quotient m k z=i then residueTerm (m*(k+1)) f z n else 0 := by
    by_cases hn : (n : ZMod (m*(k+1)))=z
    · have hq : (n : ZMod m)=quotient m k z := by
        rw [← hn,quotient_nat]
      simp only [residueTerm,if_pos hn,hq]
    · simp only [residueTerm,if_neg hn,ite_self]
  unfold piece push
  simp_rw [he]
  split_ifs <;> simp

lemma push_square_tendsto {f : ℕ → ℝ} (hf : Summable f) :
    Tendsto (fun k : ℕ ↦ ∑ z : ZMod (m*(k+1)), push (m*(k+1)) f z^2)
      atTop (𝓝 (∑' n, f n^2)) := by
  have hm : 1 ≤ m := NeZero.pos m
  have hi : Tendsto (fun k : ℕ ↦ m*k+(m-1)) atTop atTop :=
    tendsto_atTop_mono (fun k ↦ by dsimp; nlinarith) tendsto_id
  have he (k : ℕ) : m*k+(m-1)+1=m*(k+1) := by
    rw [Nat.mul_add,Nat.mul_one]
    omega
  have hh := (push_corr_tendsto hf 0).comp hi
  simp only [Function.comp_def,Nat.cast_zero,corr,natCorr,add_zero,← pow_two] at hh
  have hc {a b : ℕ} [NeZero a] [NeZero b] (hab : a=b) :
      (∑ z : ZMod a, push a f z^2)=(∑ z : ZMod b, push b f z^2) := by
    subst b
    rfl
  apply hh.congr'
  exact Eventually.of_forall (fun k ↦ hc (he k))

noncomputable def natEnergy (f g : ℕ → ℝ) : ℝ := ∑' n, sumConv f g n^2
noncomputable def projectionError (f : ℕ → ℝ) (i : ZMod m) (n : ℕ) : ℝ :=
  sumConv f (residueTerm m f i) n-sumConv f f n/m
noncomputable def natVariance (f : ℕ → ℝ) : ℝ := ∑ i : ZMod m, ∑' n, projectionError m f i n^2

lemma summable_projectionError {f : ℕ → ℝ} (hf : Summable f) (i : ZMod m) :
    Summable (projectionError m f i) :=
  (summable_conv hf (summable_residueTerm m hf i)).sub ((summable_conv hf hf).div_const m)

lemma push_projectionError (k : ℕ) {f : ℕ → ℝ} (hf : Summable f)
    (i : ZMod m) (z : ZMod (m*(k+1))) :
    conv (push (m*(k+1)) f) (piece (quotient m k) (push (m*(k+1)) f) i) z-
      conv (push (m*(k+1)) f) (push (m*(k+1)) f) z/m=
        push (m*(k+1)) (projectionError m f i) z := by
  have he : piece (quotient m k) (push (m*(k+1)) f) i=
      push (m*(k+1)) (residueTerm m f i) := funext (push_piece m k f i)
  rw [he,push_convolution _ hf (summable_residueTerm m hf i),push_convolution _ hf hf,
    ← push_div_const,← push_sub _ (summable_conv hf (summable_residueTerm m hf i))
      ((summable_conv hf hf).div_const m)]
  rfl

lemma variance_tendsto {f : ℕ → ℝ} (hf : Summable f) :
    Tendsto (fun k : ℕ ↦ variance (quotient m k) (push (m*(k+1)) f))
      atTop (𝓝 (natVariance m f)) := by
  simp only [variance,natVariance,ZMod.card,push_projectionError m _ hf]
  exact tendsto_finset_sum Finset.univ (fun i _ ↦ push_square_tendsto m (summable_projectionError m hf i))

lemma energy_tendsto {f g : ℕ → ℝ} (hf : Summable f) (hg : Summable g) :
    Tendsto (fun k : ℕ ↦ energy (push (m*(k+1)) f) (push (m*(k+1)) g))
      atTop (𝓝 (natEnergy f g)) := by
  simpa only [energy,push_convolution _ hf hg,natEnergy] using
    push_square_tendsto m (summable_conv hf hg)

lemma error_energy_tendsto {f g : ℕ → ℝ} (hf : Summable f) (hg : Summable g) :
    Tendsto (fun k : ℕ ↦ ∑ z : ZMod (m*(k+1)),
      (conv (push (m*(k+1)) f) (push (m*(k+1)) f) z-
        conv (push (m*(k+1)) g) (push (m*(k+1)) g) z)^2)
      atTop (𝓝 (∑' n, (sumConv f f n-sumConv g g n)^2)) := by
  have he (k : ℕ) (z : ZMod (m*(k+1))) :
      conv (push (m*(k+1)) f) (push (m*(k+1)) f) z-
        conv (push (m*(k+1)) g) (push (m*(k+1)) g) z=
      push (m*(k+1)) (fun n ↦ sumConv f f n-sumConv g g n) z := by
    rw [push_convolution _ hf hf,push_convolution _ hg hg,
      ← push_sub _ (summable_conv hf hf) (summable_conv hg hg)]
  simp only [he]
  exact push_square_tendsto m ((summable_conv hf hf).sub (summable_conv hg hg))

/-- Exact variance stability on natural-number sequences. This does not
require positivity, only summability of the two input sequences. -/
theorem natVariance_difference_sq {f g : ℕ → ℝ} (hf : Summable f) (hg : Summable g) :
    (natVariance m f-natVariance m g)^2 ≤
      (∑' n, (sumConv f f n-sumConv g g n)^2)*(2*natEnergy f f+2*natEnergy g g) := by
  have hl := ((variance_tendsto m hf).sub (variance_tendsto m hg)).pow 2
  have hr := (error_energy_tendsto m hf hg).mul
    (((energy_tendsto m hf hf).const_mul 2).add ((energy_tendsto m hg hg).const_mul 2))
  apply le_of_tendsto_of_tendsto hl hr
  exact Eventually.of_forall (fun k ↦ variance_difference_sq (quotient m k) _ _)

lemma residueTerm_weighted (f : ℕ → ℝ) (i : ZMod m) (r : ℝ) :
    residueTerm m (fun n ↦ f n*r^n) i=(fun n ↦ residueTerm m f i n*r^n) := by
  funext n
  unfold residueTerm
  split_ifs <;> simp

lemma projectionError_weighted (f : ℕ → ℝ) (i : ZMod m) (r : ℝ) (n : ℕ) :
    projectionError m (fun n ↦ f n*r^n) i n=projectionError m f i n*r^n := by
  rw [projectionError,residueTerm_weighted,weighted_convolution,weighted_convolution]
  simp only [projectionError]
  ring

end Erdos66NaturalResidueProjection
