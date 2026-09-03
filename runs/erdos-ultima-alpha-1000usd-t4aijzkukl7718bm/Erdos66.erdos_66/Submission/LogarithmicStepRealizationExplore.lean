import Submission.IntegerPaletteQuantizationExplore

/-! Unconditional finite integer realization of every fixed bounded step
profile, uniformly in its interval geometry. This is not uniform in the
number or heights of pieces and does not settle the infinite conjecture. -/
namespace Erdos66LogarithmicStepRealization
open Filter AdditiveCombinatorics Erdos66PrefixBalancedPalette
  Erdos66IntegerPaletteQuantization Erdos66SaturatingCyclicFamily
open scoped Classical Topology
set_option maxHeartbeats 3200000

lemma quantization_factor (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ (1+2*t)*(1+t)^2-1 ∧ (1+2*t)*(1+t)^2-1 ≤ 11*t := by
  have h2 : t^2 ≤ t := by nlinarith
  have h3 : t^3 ≤ t := by nlinarith [mul_le_mul_of_nonneg_left h2 ht]
  constructor <;> nlinarith [sq_nonneg t,mul_nonneg ht (sq_nonneg t)]

/-- An arbitrarily large modulus supports actual finite natural sets with
all-target convolution close to any prescribed finite step profile of these
fixed heights. The interval endpoints may be chosen AFTER the modulus. -/
theorem exists_logarithmic_step_realization {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (hw : ∀ i∈s, 1 ≤ w i)
    (c δ : ℝ) (hc : 0<c) (hδ : 0<δ) (N₀ : ℕ) :
    ∃ M : ℕ, N₀<M ∧ 1<M ∧ ∀ a b : ι → ℕ,
      (∀ i∈s, b i ≤ M) →
      (∀ i∈s, ∀ j∈s, i ≠ j → b i ≤ a j ∨ b j ≤ a i) →
      ∃ A : Finset ℕ, A ⊆ Finset.range M ∧ ∀ n : ℕ,
        |(sumRep (A:Set ℕ) n:ℝ)/Real.log M-c*weightedProfile M s w a b n| ≤ δ := by
  have hw0 : ∀ i∈s, 0 ≤ w i := fun i hi ↦ (by linarith [hw i hi])
  let S : ℝ := (∑ i∈s, w i)^2+1
  have hS : 0<S := by dsimp [S]; positivity
  have hS1 : (∑ i∈s, w i)^2 ≤ S := by dsimp [S]; linarith
  let t := min 1 (δ/(100*(c+1)*S))
  have ht : 0<t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := min_le_left _ _
  have htδ : t ≤ δ/(100*(c+1)*S) := min_le_right _ _
  have htcost : 100*t*(c+1)*S ≤ δ := by
    have hh := (le_div_iff₀ (by positivity : 0<100*(c+1)*S)).mp htδ
    nlinarith only [hh]
  let τ := min 1 (δ/(4*S))
  have hτ : 0<τ := by dsimp [τ]; positivity
  have hτ1 : τ ≤ 1 := min_le_left _ _
  have hτcost : τ*S ≤ δ/4 := by
    have hh := (le_div_iff₀ (by positivity : 0<4*S)).mp (min_le_right 1 (δ/(4*S)))
    dsimp [τ]
    nlinarith only [hh]
  let W : ℝ := 1+∑ i∈s, w i
  have hWsum : 0 ≤ ∑ i∈s, w i := Finset.sum_nonneg hw0
  have hW : 0<W := by dsimp [W]; linarith
  have hwi : ∀ i∈s, w i ≤ W := by
    intro i hi
    have hh := Finset.single_le_sum hw0 hi
    dsimp [W]
    linarith
  have hlim : Tendsto (fun M : ℕ ↦ W^2*(c+1)*Real.log M/(M:ℝ)) atTop (𝓝 0) := by
    have hh := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop (R:=ℝ))).const_mul (W^2*(c+1))
    simpa only [Function.comp_apply,id_eq,mul_zero,mul_div_assoc] using hh
  obtain ⟨L,hL⟩ := eventually_atTop.mp (hlim.eventually_le_const (by norm_num : (0:ℝ)<1))
  obtain ⟨M,hMN,hodd,hM,B,P,hBpos,hBmem,htune,hBsub,hnest,hflat,hprefix,hfull,hPcard,hcover⟩ :=
    exists_prefix_balanced_complete_palette c τ t t hc hτ ht ht1 ht ht1 (max N₀ (max L 2))
  letI := hM
  have hM1 : 1<M := by omega
  have hMr : (0:ℝ)<M := by exact_mod_cast (show 0<M by omega)
  have hlog : 0<Real.log (M:ℝ) := Real.log_pos (by exact_mod_cast hM1)
  have hμ0 := actualMean_nonneg M B B
  have hμup : actualMean M B B ≤ (c+1)*Real.log M := by
    apply (div_le_iff₀ hlog).mp
    have hh := (abs_lt.mp htune).2
    linarith
  have hq0 : (0:ℝ) ≤ B.card := by positivity
  have hq2 : (B.card:ℝ)^2 ≤ (c+1)*Real.log M*M := by
    have hh := (div_le_iff₀ hMr).mp hμup
    nlinarith only [hh]
  have hbudget : W^2*(c+1)*Real.log M ≤ M := by
    have hh := (div_le_iff₀ hMr).mp (hL M (by omega))
    simpa only [one_mul] using hh
  have hfitW : W*(B.card:ℝ) ≤ M := by
    apply le_of_sq_le_sq _ hMr.le
    have hh1 := mul_le_mul_of_nonneg_left hq2 (sq_nonneg W)
    have hh2 := mul_le_mul_of_nonneg_right hbudget hMr.le
    nlinarith only [hh1,hh2]
  have hfit : ∀ i∈s, w i*(B.card:ℝ) ≤ M :=
    fun i hi ↦ (mul_le_mul_of_nonneg_right (hwi i hi) hq0).trans hfitW
  refine ⟨M,by omega,hM1,fun a b hb hdisj ↦ ?_⟩
  obtain ⟨A,hAs,hA⟩ := exists_quantized_assembly M s B P w a b hw hfit hdisj hb t t ht.le ht.le hcover hprefix
  refine ⟨A,hAs,fun n ↦ ?_⟩
  let F := weightedProfile M s w a b n
  have hF0 : 0 ≤ F := (weightedProfile_bounds M s w a b hw0 hb n).1
  have hFS : F ≤ S := (weightedProfile_bounds M s w a b hw0 hb n).2.trans hS1
  let Q := (1+2*t)*(1+t)^2-1
  have hQ : 0 ≤ Q := (quantization_factor t ht.le ht1).1
  have hQup : Q ≤ 11*t := (quantization_factor t ht.le ht1).2
  have hround : |(sumRep (A:Set ℕ) n:ℝ)/Real.log M-(actualMean M B B/Real.log M)*F| ≤ δ/4 := by
    have hh := div_le_div_of_nonneg_right (hA n) hlog.le
    have he : |(sumRep (A:Set ℕ) n:ℝ)/Real.log M-(actualMean M B B/Real.log M)*F| ≤
        Q*(actualMean M B B/Real.log M)*(∑ i∈s, w i)^2 := by
      convert hh using 1
      · rw [←abs_of_pos hlog,←abs_div,abs_of_pos hlog]
        congr 1
        dsimp [F]
        ring
      · dsimp [Q]
        ring
    have hmu : actualMean M B B/Real.log M ≤ c+1 := (div_le_iff₀ hlog).mpr hμup
    have h1 := mul_le_mul_of_nonneg_right hmu (mul_nonneg hQ (sq_nonneg (∑ i∈s, w i)))
    have h2 := mul_le_mul_of_nonneg_right hQup (mul_nonneg (by linarith : 0 ≤ c+1) (sq_nonneg (∑ i∈s, w i)))
    have h3 := mul_le_mul_of_nonneg_left hS1 (show 0 ≤ 11*t*(c+1) by positivity)
    nlinarith only [he,h1,h2,h3,htcost,hδ]
  have htuning : |(actualMean M B B/Real.log M)*F-c*F| ≤ δ/4 := by
    rw [←sub_mul,abs_mul,abs_of_nonneg hF0]
    have h1 := mul_le_mul_of_nonneg_right htune.le hF0
    have h2 := mul_le_mul_of_nonneg_left hFS hτ.le
    linarith
  have htri := abs_sub_le ((sumRep (A:Set ℕ) n:ℝ)/Real.log M)
    ((actualMean M B B/Real.log M)*F) (c*F)
  change |(sumRep (A:Set ℕ) n:ℝ)/Real.log M-c*F| ≤ δ
  linarith

end Erdos66LogarithmicStepRealization
