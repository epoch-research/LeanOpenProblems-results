import Submission.ThreeLabelExactDilationBias
import Submission.PrimePowerOvershoot
import Submission.HarmonicPrimeWinnerColours

/-! A single fixed stable sequence can have biased ordinary skew averages.
This is an auxiliary obstruction, NOT a disproof about maxPrimeFac itself. -/
namespace Erdos371.ExactMultiplierChirpObstruction
open Finset Filter FiniteInformation MultiplicativeChirpObstruction
open scoped Topology
set_option autoImplicit false

noncomputable def smoothIccCount (B N : ℕ) : ℕ :=
  ((Icc 1 N).filter fun n => Nat.maxPrimeFac n ≤ B).card

lemma smoothIccCount_eq (B N : ℕ) : smoothIccCount B N =
    ((range N).filter fun n => Nat.maxPrimeFac (n+1) ≤ B).card := by
  classical
  unfold smoothIccCount
  have h := sum_Ico_add' (fun n => if Nat.maxPrimeFac n ≤ B then (1 : ℕ) else 0) 0 N 1
  simpa only [zero_add,Nat.Ico_zero_eq_range,Ico_add_one_right_eq_Icc,sum_boole] using h.symm

lemma smoothIccCount_succ_ratio_zero (B : ℕ) :
    Tendsto (fun N : ℕ => (smoothIccCount B (N+1) : ℝ)/N) atTop (𝓝 0) := by
  have h := (fixed_shifted_smooth_count_tendsto B).comp (tendsto_add_atTop_nat 1)
  have hratio : Tendsto (fun N : ℕ => (N+1 : ℝ)/N) atTop (𝓝 1) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).const_add 1
    simp only [add_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    field_simp
  have ht := h.mul hratio
  simp only [zero_mul] at ht
  convert ht using 1
  funext N
  rw [smoothIccCount_eq]
  simp only [Function.comp_apply,Nat.cast_add,Nat.cast_one]
  field_simp

lemma exists_stripped_biased_chirp_eventually (B : ℕ) (E : ℕ → Prop)
    (hE : ∀ᶠ N in atTop, E N) :
    ∃ N : ℕ, B+2 ≤ N ∧ E N ∧
      (1/120 : ℝ) ≤ imaginaryBias (strippedChirp N B) N := by
  obtain ⟨a,ha,hres,hbias⟩ := exists_chirp_subsequence_fixed_multipliers
  have he : Tendsto (fun j => ∑ p ∈ (B+1).primesBelow, ‖chirp (a j) p-1‖) atTop (𝓝 0) := by
    have ht := tendsto_finset_sum (B+1).primesBelow (fun p hp =>
      ((hres p (Nat.mem_primesBelow.mp hp).2.pos).sub_const 1).norm)
    simpa only [sub_self,norm_zero,sum_const_zero] using ht
  obtain ⟨j,⟨⟨hjN,hjE⟩,hjb⟩,hje⟩ := (ha.eventually_ge_atTop (B+2) |>.and
    (ha.eventually hE) |>.and hbias |>.and
      (he.eventually_lt_const (by norm_num : (0 : ℝ) < 1/1000))).exists
  have herr := strippedChirp_bias_error (a j) B (a j) (by omega)
  rw [imaginaryBias_chirp] at herr
  refine ⟨a j,hjN,hjE,?_⟩
  have hlo := (abs_le.mp herr).1
  linarith

lemma exists_sparse_bias_endpoint (B : ℕ) :
    ∃ N : ℕ, B+2 ≤ N ∧
      4*(smoothIccCount B (N+1) : ℝ)/N ≤ 1/240 ∧
      (1/120 : ℝ) ≤ imaginaryBias (strippedChirp N B) N := by
  have ht := (smoothIccCount_succ_ratio_zero B).const_mul 4
  simp only [mul_zero] at ht
  have hE := ht.eventually_le_const (by norm_num : (0 : ℝ) < 1/240)
  simpa only [mul_div_assoc] using exists_stripped_biased_chirp_eventually B
    (fun N => 4*(smoothIccCount B (N+1) : ℝ)/N ≤ 1/240) (by
      simpa only [mul_div_assoc] using hE)

noncomputable def biasEndpoint (B : ℕ) : ℕ := Classical.choose (exists_sparse_bias_endpoint B)
lemma biasEndpoint_spec (B : ℕ) : B+2 ≤ biasEndpoint B ∧
    4*(smoothIccCount B (biasEndpoint B+1) : ℝ)/biasEndpoint B ≤ 1/240 ∧
    (1/120 : ℝ) ≤ imaginaryBias (strippedChirp (biasEndpoint B) B) (biasEndpoint B) :=
  Classical.choose_spec (exists_sparse_bias_endpoint B)

noncomputable def biasBand : ℕ → ℕ
  | 0 => 0
  | j+1 => biasEndpoint (biasBand j)+2

lemma biasBand_strictMono : StrictMono biasBand := by
  apply strictMono_nat_of_lt_succ
  intro j
  change biasBand j < biasEndpoint (biasBand j)+2
  have := (biasEndpoint_spec (biasBand j)).1
  omega

lemma biasBand_index_exists (p : ℕ) : ∃ j : ℕ, p ≤ biasBand (j+1) := by
  exact ⟨p,(Nat.le_succ p).trans (biasBand_strictMono.le_apply)⟩

noncomputable def biasBandIndex (p : ℕ) : ℕ := Nat.find (biasBand_index_exists p)

lemma biasBandIndex_upper (p : ℕ) : p ≤ biasBand (biasBandIndex p+1) :=
  Nat.find_spec (biasBand_index_exists p)

lemma biasBandIndex_lower (p : ℕ) (hp : 0 < p) : biasBand (biasBandIndex p) < p := by
  by_cases hj : biasBandIndex p = 0
  · simpa only [hj,biasBand] using hp
  · have h := Nat.find_min (biasBand_index_exists p) (show biasBandIndex p-1 < biasBandIndex p by omega)
    simpa only [Nat.sub_add_cancel (show 1 ≤ biasBandIndex p by omega),not_le] using h

lemma biasBandIndex_eq (j p : ℕ) (hl : biasBand j < p) (hu : p ≤ biasBand (j+1)) :
    biasBandIndex p = j := by
  apply le_antisymm
  · exact Nat.find_min' (biasBand_index_exists p) hu
  · by_contra h
    have hj : biasBandIndex p+1 ≤ j := by omega
    have hp := (biasBandIndex_upper p).trans (biasBand_strictMono.monotone hj)
    omega

noncomputable def fixedBiasedPhase (n : ℕ) : ℂ :=
  let j := biasBandIndex (Nat.maxPrimeFac n)
  strippedChirp (biasEndpoint (biasBand j)) (biasBand j) n

lemma fixedBiasedPhase_norm_le (n : ℕ) : ‖fixedBiasedPhase n‖ ≤ 1 :=
  strippedChirp_norm_le_one _ _ _

lemma fixedBiasedPhase_matches (j n : ℕ) (hn : n ≤ biasEndpoint (biasBand j)+1)
    (hp : biasBand j < Nat.maxPrimeFac n) :
    fixedBiasedPhase n = strippedChirp (biasEndpoint (biasBand j)) (biasBand j) n := by
  have hu : Nat.maxPrimeFac n ≤ biasBand (j+1) := by
    have hl := Nat.maxPrimeFac_le (n := n)
    change Nat.maxPrimeFac n ≤ biasEndpoint (biasBand j)+2
    omega
  simp only [fixedBiasedPhase,biasBandIndex_eq j _ hp hu]

lemma fixedBiasedPhase_bias (j : ℕ) :
    (1/240 : ℝ) ≤ imaginaryBias fixedBiasedPhase (biasEndpoint (biasBand j)) := by
  classical
  let B := biasBand j
  let N := biasEndpoint B
  let f := strippedChirp N B
  have hs := biasEndpoint_spec B
  have hpt (n : ℕ) (hn : n ∈ Icc 1 (N+1)) :
      ‖fixedBiasedPhase n-f n‖ ≤ 2*(if Nat.maxPrimeFac n ≤ B then (1 : ℝ) else 0) := by
    by_cases hp : Nat.maxPrimeFac n ≤ B
    · rw [if_pos hp,mul_one]
      have hf : ‖f n‖ ≤ 1 := strippedChirp_norm_le_one _ _ _
      exact (norm_sub_le _ _).trans (by linarith [fixedBiasedPhase_norm_le n])
    · rw [if_neg hp,fixedBiasedPhase_matches j n (mem_Icc.mp hn).2 (by omega)]
      simp [f,N,B]
  have hsum := sum_le_sum hpt
  rw [← mul_sum,sum_boole] at hsum
  change (∑ n ∈ Icc 1 (N+1), ‖fixedBiasedPhase n-f n‖) ≤ 2*(smoothIccCount B (N+1) : ℝ) at hsum
  have he := imaginaryBias_error fixedBiasedPhase f fixedBiasedPhase_norm_le
    (strippedChirp_norm_le_one _ _) N
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hbound : 2*(∑ n ∈ Icc 1 (N+1), ‖fixedBiasedPhase n-f n‖)/N ≤ 1/240 := by
    apply le_trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsum (by norm_num)) hNr)
    convert hs.2.1 using 1; ring
  have hh := (abs_le.mp (he.trans hbound)).1
  change (1/240 : ℝ) ≤ imaginaryBias fixedBiasedPhase N
  have hb : (1/120 : ℝ) ≤ imaginaryBias f N := hs.2.2
  linarith

lemma fixedBiasedPhase_small_multiplier (k n : ℕ) (hk : 0 < k)
    (hn : biasBand k < Nat.maxPrimeFac n) : fixedBiasedPhase (k*n) = fixedBiasedPhase n := by
  have hnp : 0 < Nat.maxPrimeFac n := (Nat.zero_le _).trans_lt hn
  have hn0 : n ≠ 0 := by intro h; simp [h] at hnp
  have hkP : Nat.maxPrimeFac k ≤ Nat.maxPrimeFac n := by
    have hkB : k ≤ biasBand k := biasBand_strictMono.le_apply
    have hPk := Nat.maxPrimeFac_le (n := k)
    omega
  have he : Nat.maxPrimeFac (k*n) = Nat.maxPrimeFac n := by
    rw [Nat.maxPrimeFac_mul hk.ne' hn0,max_eq_right hkP]
  have hj : k ≤ biasBandIndex (Nat.maxPrimeFac n) := by
    by_contra h
    have hle : biasBandIndex (Nat.maxPrimeFac n)+1 ≤ k := by omega
    have := (biasBandIndex_upper (Nat.maxPrimeFac n)).trans (biasBand_strictMono.monotone hle)
    omega
  have hkB : k ≤ biasBand (biasBandIndex (Nat.maxPrimeFac n)) :=
    hj.trans (biasBand_strictMono.id_le _)
  simp only [fixedBiasedPhase,he]
  exact strippedChirp_small_multiplier _ _ _ _ hk hkB

lemma fixedBiasedPhase_mean_dilation_defect_zero (k : ℕ) (hk : 0 < k) :
    Tendsto (fun N => prefixMean N (labelDilationDefect k fixedBiasedPhase)) atTop (𝓝 0) := by
  classical
  have ht := (density_iff_count _ 0).mp (bounded_maxPrimeFac_hasDensity_zero (biasBand k))
  apply squeeze_zero (fun N => by unfold prefixMean labelDilationDefect; positivity) _ ht
  intro N
  unfold prefixMean
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  rw [Finset.natCast_card_filter]
  apply sum_le_sum
  intro n _
  unfold labelDilationDefect
  by_cases hn : Nat.maxPrimeFac n ≤ biasBand k
  · simp only [hn,if_true]
    split_ifs <;> norm_num
  · simp [hn,fixedBiasedPhase_small_multiplier k n hk (by omega)]

lemma fixedBiasedPhase_endpoint_tendsto :
    Tendsto (fun j => biasEndpoint (biasBand j)) atTop atTop := by
  apply tendsto_atTop_mono _ biasBand_strictMono.tendsto_atTop
  intro j
  have := (biasEndpoint_spec (biasBand j)).1
  omega

lemma mean_dilation_defect_comp_zero {A D : Type*} (L : ℕ → A) (g : A → D)
    (k : ℕ) (h : Tendsto (fun N => prefixMean N (labelDilationDefect k L)) atTop (𝓝 0)) :
    Tendsto (fun N => prefixMean N (labelDilationDefect k (g ∘ L))) atTop (𝓝 0) := by
  classical
  apply squeeze_zero (fun N => by unfold prefixMean labelDilationDefect; positivity) _ h
  intro N
  unfold prefixMean
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  exact sum_le_sum fun n _ => labelDilationDefect_comp_le k L g n

/-- The alphabet, sequence, and observable here are all fixed. Only the
subsequence of biased natural endpoints varies. -/
theorem exists_fixed_finite_stable_skew_bias :
    ∃ Q : ℕ, ∃ L : ℕ → Fin Q, ∃ C : Fin Q → Fin Q → ℝ, ∃ D : ℕ → ℕ,
      Tendsto D atTop atTop ∧
      (∀ a b, C b a = -C a b) ∧ (∀ a b, |C a b| ≤ 1) ∧
      (∀ k, 0 < k → Tendsto (fun N => prefixMean N (labelDilationDefect k L)) atTop (𝓝 0)) ∧
      ∀ j, (1/480 : ℝ) ≤ (∑ n ∈ Icc 1 (D j), C (L n) (L (n+1)))/D j := by
  obtain ⟨Q,v,q,hv,hq⟩ := finite_unitBall_quantizer (1/10000) (by norm_num)
  let L := q ∘ fixedBiasedPhase
  refine ⟨Q,L,phaseSkew v,fun j => biasEndpoint (biasBand j),fixedBiasedPhase_endpoint_tendsto,
    phaseSkew_swap v,phaseSkew_abs_le v hv,?_,?_⟩
  · intro k hk
    exact mean_dilation_defect_comp_zero fixedBiasedPhase q k (fixedBiasedPhase_mean_dilation_defect_zero k hk)
  · intro j
    have hN : 0 < biasEndpoint (biasBand j) := by have := (biasEndpoint_spec (biasBand j)).1; omega
    have he := imaginaryBias_uniform_error (v ∘ L) fixedBiasedPhase (fun n => hv _)
      fixedBiasedPhase_norm_le (1/10000) (fun n => (hq _ (fixedBiasedPhase_norm_le n)).le)
      (biasEndpoint (biasBand j)) hN
    change (1/480 : ℝ) ≤ imaginaryBias (v ∘ L) (biasEndpoint (biasBand j))
    have hh := (abs_le.mp he).1
    linarith [fixedBiasedPhase_bias j]

/-- Unlike the older endpoint-dependent examples, this is ONE sequence on
THREE ordered labels. Its harmonic skew mean tends to zero, but its ordinary
skew mean does not. Fixed-multiplier stability alone cannot bridge that gap. -/
theorem exists_fixed_three_label_harmonic_natural_gap :
    ∃ L : ℕ → Fin 3,
      (∀ k, 0 < k → Tendsto (fun N => prefixMean N (labelDilationDefect k L)) atTop (𝓝 0)) ∧
      Tendsto (fun N => harmonicMean (N+1) (fun n => orderSkew (L n) (L (n+1)))) atTop (𝓝 0) ∧
      ¬Tendsto (orderedMean L) atTop (𝓝 0) := by
  obtain ⟨Q,L,C,D,hD,hC,hCb,hL,hbias⟩ := exists_fixed_finite_stable_skew_bias
  have hex : ∃ a b : Fin Q, ¬Tendsto (orderedMean (pairOrder a b ∘ L)) atTop (𝓝 0) := by
    by_contra! hn
    have ht := tendsto_finset_sum (univ : Finset (Fin Q)) (fun a _ =>
      tendsto_finset_sum (univ : Finset (Fin Q)) (fun b _ =>
        ((hn a b).sub (hn b a)).const_mul (C a b)))
    simp only [sub_zero,mul_zero,sum_const_zero] at ht
    have hbad : (4 : ℝ)*(1/480) ≤ 0 := by
      apply ge_of_tendsto (ht.comp hD)
      apply Eventually.of_forall
      intro j
      simp only [Function.comp_apply]
      rw [← skew_mean_expansion_pairOrders L C hC]
      linarith [hbias j]
    norm_num at hbad
  obtain ⟨a,b,hab⟩ := hex
  let T := pairOrder a b ∘ L
  have hT (k : ℕ) (hk : 0 < k) :
      Tendsto (fun N => prefixMean N (labelDilationDefect k T)) atTop (𝓝 0) :=
    mean_dilation_defect_comp_zero L (pairOrder a b) k (hL k hk)
  exact ⟨T,hT,DilationSpectrum.stable_finite_labels_harmonic_skew_zero T hT
    orderSkew orderSkew_swap orderSkew_abs_le,hab⟩

#print axioms fixedBiasedPhase_bias
#print axioms fixedBiasedPhase_mean_dilation_defect_zero
#print axioms exists_fixed_finite_stable_skew_bias
#print axioms exists_fixed_three_label_harmonic_natural_gap
end Erdos371.ExactMultiplierChirpObstruction
