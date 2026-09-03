import Submission.UniformAmbientSampling
import Submission.ControlledSquareSampling
import Submission.GaussianIncidentDegree
import Submission.UniformSquareSamplingScales

/-! Progression-free square-root samples with simultaneous control of every
four-support degree, without maximum-degree trimming. -/
namespace Erdos773.UniformSquareSampling
open Finset Filter SquareCollisionCodegrees SquareProgressionSupports HypergraphDegreeTrim
set_option maxHeartbeats 2000000
noncomputable section

theorem finite_selection (N K q : ℕ) (p T D : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hT : 0<T)
    (hdegree : ∀ a ∈ Icc 1 N, (degree (edges (Icc 1 N)) a:ℝ) ≤ D)
    (hpair : ∀ a ∈ Icc 1 N, ∀ b ∈ Icc 1 N, a ≠ b → (pairEdges (Icc 1 N) a b).card ≤ K)
    (hpositive : 0 < p*N-p^3*(progressions (Icc 1 N)).card-
      (N:ℝ)^2*((p^3*D+(3*q:ℕ)*K)/T)^q) :
    ∃ B ⊆ Icc 1 N, ThreeAPFree ((B.image (fun n : ℕ => n^2)) : Set ℕ) ∧
      (∀ a ∈ Icc 1 N, (degree (edges B) a:ℝ)<T) ∧
      p*N-p^3*(progressions (Icc 1 N)).card-
        (N:ℝ)^2*((p^3*D+(3*q:ℕ)*K)/T)^q ≤ (B.card:ℝ) := by
  classical
  obtain ⟨B,hB,hP,hcap,hcard⟩ := UniformAmbientSampling.finite_selection
    (Icc 1 N) (edges (Icc 1 N)) (progressions (Icc 1 N)) K q p T D hp hp1 hT
    (fun e he => mem_powerset.mp (mem_filter.mp he).1)
    (fun e he => (mem_progressions.mp he).1)
    (fun e he => (mem_filter.mp he).2.1)
    (fun e he => (mem_progressions.mp he).2.1) hdegree hpair
    (by simpa only [Nat.card_Icc,Nat.add_sub_cancel] using hpositive)
  refine ⟨B,hB,ap_free_of_avoids hB hP,?_,?_⟩
  · rw [ControlledSquareSampling.edges_restrict hB]
    exact hcap
  · simpa only [Nat.card_Icc,Nat.add_sub_cancel] using hcard

open UniformSquareSamplingScales

/-- Finite sufficient conditions for a logarithmic-density sample with no
    maximum-degree trimming loss. -/
theorem finite_log_sampling (N : ℕ) (δ : ℝ) (hN : 1 ≤ N)
    (hδ : 0<δ) (hδ1 : δ<1) (hL : 2 ≤ Real.log (N:ℝ))
    (hlarge : 25/δ ≤ Real.log (N:ℝ))
    (hsmall : 16000*Real.log (N:ℝ) ≤ (N:ℝ)^(1/100:ℝ))
    (hdegree : ∀ a ∈ Icc 1 N, (degree (edges (Icc 1 N)) a:ℝ) ≤
      (333/1000:ℝ)*(N:ℝ)*Real.log N)
    (hpair : ∀ a ∈ Icc 1 N, ∀ b ∈ Icc 1 N, a ≠ b →
      ((pairEdges (Icc 1 N) a b).card:ℝ) ≤ (N:ℝ)^(1/100:ℝ)) :
    ∃ B ⊆ Icc 1 N, ThreeAPFree ((B.image (fun n : ℕ => n^2)) : Set ℕ) ∧
      (∀ a ∈ Icc 1 N, (degree (edges B) a:ℝ)<(1999/6000:ℝ)*(N:ℝ)/(Real.log N)^2) ∧
      (1-δ)*(N:ℝ)/Real.log N ≤ (B.card:ℝ) := by
  have hX1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hX : (0:ℝ)<N := by linarith only [hX1]
  have hL0 : 0<Real.log (N:ℝ) := by linarith only [hL]
  let p : ℝ := 1/Real.log (N:ℝ)
  let D : ℝ := (333/1000:ℝ)*(N:ℝ)*Real.log N
  let T : ℝ := (1999/6000:ℝ)*(N:ℝ)/(Real.log N)^2
  let q := momentOrder (N:ℝ)
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hp1 : p ≤ 1 := by dsimp [p]; exact (div_le_one hL0).mpr (by linarith)
  have hT : 0<T := by dsimp [T]; positivity
  have hAP := ControlledSquareSampling.progression_log_bound N (by omega) hL
  have hcost := sampling_loss hX1 hL0 hsmall
  have hAPmul := mul_le_mul_of_nonneg_left hAP (pow_nonneg hp 3)
  have htotal : p^3*(progressions (Icc 1 N)).card+
      (N:ℝ)^2*((p^3*D+(3*q:ℕ)*q)/T)^q ≤ 25*(N:ℝ)/(Real.log N)^2 := by
    exact (add_le_add hAPmul le_rfl).trans hcost
  have h25 : 25 ≤ δ*Real.log (N:ℝ) := by
    have hh := (div_le_iff₀ hδ).mp hlarge
    linarith only [hh]
  have herror : 25*(N:ℝ)/(Real.log N)^2 ≤ δ*(N:ℝ)/Real.log N := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hL0) hL0).mpr
    have hh := mul_le_mul_of_nonneg_right h25 (show 0 ≤ (N:ℝ)*Real.log N by positivity)
    nlinarith only [hh]
  have htarget : (1-δ)*(N:ℝ)/Real.log N ≤ p*N-p^3*(progressions (Icc 1 N)).card-
      (N:ℝ)^2*((p^3*D+(3*q:ℕ)*q)/T)^q := by
    dsimp [p] at htotal herror ⊢
    have he : (1-δ)*(N:ℝ)/Real.log N = (1/Real.log N)*(N:ℝ)-δ*(N:ℝ)/Real.log N := by ring
    rw [he]
    linarith only [htotal,herror]
  have hpos : 0 < p*N-p^3*(progressions (Icc 1 N)).card-
      (N:ℝ)^2*((p^3*D+(3*q:ℕ)*q)/T)^q := by
    apply lt_of_lt_of_le _ htarget
    have hgap : 0<1-δ := by linarith only [hδ1]
    positivity
  obtain ⟨B,hB,hAP,hcap,hcard⟩ := finite_selection N q q p T D hp hp1 hT hdegree
    (by
      intro a ha b hb hab
      have hh := (hpair a ha b hb hab).trans (momentOrder_bounds hX1).1
      exact_mod_cast hh) hpos
  exact ⟨B,hB,hAP,hcap,htarget.trans hcard⟩

/-- Actual progression-free samples of size (1-delta)N/log N, with a uniform
    degree coefficient strictly below one third. This is not a Sidon bound. -/
theorem logarithmic_sampling (δ : ℝ) (hδ : 0<δ) (hδ1 : δ<1) :
    ∀ᶠ N : ℕ in atTop, ∃ B ⊆ Icc 1 N,
      ThreeAPFree ((B.image (fun n : ℕ => n^2)) : Set ℕ) ∧
      (∀ a ∈ Icc 1 N, (degree (edges B) a:ℝ)<(1999/6000:ℝ)*(N:ℝ)/(Real.log N)^2) ∧
      (1-δ)*(N:ℝ)/Real.log N ≤ (B.card:ℝ) := by
  have ht : Tendsto (fun N : ℕ => Real.log (N:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall := ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/100)).comp_tendsto
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop)).bound
      (by norm_num : (0:ℝ)<1/16000)
  filter_upwards [GaussianIncidentDegree.eventual_degree_bound,
    eventually_pair_codegree_bound (1/100) (by norm_num),ht.eventually_ge_atTop 2,
    ht.eventually_ge_atTop (25/δ),hsmall,eventually_ge_atTop 1] with N hdeg hpair hL hlarge hsmall hN
  have hX : (0:ℝ) ≤ N := Nat.cast_nonneg N
  have hL0 : 0 ≤ Real.log (N:ℝ) := by linarith only [hL]
  have hsmall' : Real.log (N:ℝ) ≤ (1/16000:ℝ)*(N:ℝ)^(1/100:ℝ) := by
    simpa only [Function.comp_apply,Real.norm_eq_abs,abs_of_nonneg hL0,
      abs_of_nonneg (Real.rpow_nonneg hX _)] using hsmall
  exact finite_log_sampling N δ hN hδ hδ1 hL hlarge (by linarith only [hsmall']) hdeg hpair

#print axioms finite_selection
#print axioms finite_log_sampling
#print axioms logarithmic_sampling
end
end Erdos773.UniformSquareSampling
