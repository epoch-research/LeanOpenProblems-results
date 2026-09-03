import Submission.ShiftedHarmonicWordLimit
import Submission.HarmonicPrefixFloorReindex
import Submission.LogWindowPrefixMeans

/-! Harmonic sampling of global ordinary-prefix endpoints in a moving window.
This is not the decreasing-prefix law of a translated array. -/
namespace Erdos371.FiniteInformation
open Finset Filter
open scoped Topology
set_option autoImplicit false

noncomputable def shiftedEndpointLaw (A M : ℕ) : Law (Fin (M+1)) where
  mass i := shiftedHarmonicWeight A M i
  nonneg i := shiftedHarmonicWeight_nonneg A M i
  total := by simpa only [Fin.sum_univ_eq_sum_range] using shiftedHarmonicWeight_sum A M

def shiftedEndpoint (A M : ℕ) (i : Fin (M+1)) : ℕ := A+i.val+1

lemma shiftedEndpoint_pos (A M : ℕ) (i : Fin (M+1)) : 0 < shiftedEndpoint A M i := by
  unfold shiftedEndpoint
  omega

instance shiftedEndpoint_neZero (A M : ℕ) (i : Fin (M+1)) :
    NeZero (shiftedEndpoint A M i) := ⟨(shiftedEndpoint_pos A M i).ne'⟩

lemma shiftedEndpointLaw_mean (A M : ℕ) (G : ℕ → ℝ) :
    mean (shiftedEndpointLaw A M) (fun i => G (shiftedEndpoint A M i)) =
      shiftedHarmonicMean A M G := by
  unfold mean shiftedEndpointLaw shiftedEndpoint shiftedHarmonicWeight
  change (∑ i : Fin (M+1), ((1/(A+i.val+1 : ℝ))/shiftedHarmonicMass A M)*G (A+i.val+1)) = _
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ((1/(A+i+1 : ℝ))/shiftedHarmonicMass A M)*G (A+i+1)) (M+1)]
  unfold shiftedHarmonicMean shiftedHarmonicRaw
  rw [sum_div]
  apply sum_congr rfl
  intro i _
  ring

lemma shiftedHarmonicMean_reciprocal_bound (A M : ℕ) :
    shiftedHarmonicMean A M (fun n => (1 : ℝ)/n) ≤ 2/shiftedHarmonicMass A M := by
  unfold shiftedHarmonicMean shiftedHarmonicRaw
  apply div_le_div_of_nonneg_right _ (shiftedHarmonicMass_pos A M).le
  simp only [Nat.cast_add,Nat.cast_one]
  have hb (i : ℕ) : (1/(A+i+1 : ℝ))/(A+i+1 : ℝ) ≤
      2*(1/((i+1 : ℝ)*(i+2))) := by
    have ha : (0 : ℝ) ≤ A := Nat.cast_nonneg A
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have h₁ : (0 : ℝ) < A+i+1 := by positivity
    have h₂ : (0 : ℝ) < (i+1 : ℝ)*(i+2) := by positivity
    rw [div_div, mul_one_div]
    apply (div_le_div_iff₀ (mul_pos h₁ h₁) h₂).mpr
    nlinarith
  calc
    _ ≤ ∑ i ∈ range (M+1), 2*(1/((i+1 : ℝ)*(i+2))) := sum_le_sum (fun i _ => hb i)
    _ = 2*(1-1/(M+2 : ℝ)) := by
      rw [← mul_sum,reciprocal_product_sum]
      push_cast
      ring
    _ ≤ 2 := by
      have : (0 : ℝ) ≤ 1/(M+2 : ℝ) := by positivity
      linarith

lemma shiftedEndpointLaw_reciprocal_bound (A M : ℕ) :
    mean (shiftedEndpointLaw A M) (fun i => (1 : ℝ)/shiftedEndpoint A M i) ≤
      2/shiftedHarmonicMass A M := by
  rw [shiftedEndpointLaw_mean A M (fun n => (1 : ℝ)/n)]
  exact shiftedHarmonicMean_reciprocal_bound A M

lemma shiftedHarmonicMean_nonneg (A M : ℕ) (G : ℕ → ℝ) (hG : ∀ n, 0 ≤ G n) :
    0 ≤ shiftedHarmonicMean A M G := by
  have h := shiftedHarmonicMean_mono A M (fun _ => 0) G hG
  simpa only [shiftedHarmonicMean_const] using h

/-- A bounded sequence tending to zero has vanishing absolute mean on every
sequence of windows with diverging harmonic mass. -/
lemma shiftedHarmonicMean_abs_zero (G : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hG : ∀ n, |G n| ≤ B) (h : Tendsto G atTop (𝓝 0)) (A M : ℕ → ℕ)
    (hH : Tendsto (fun j => shiftedHarmonicMass (A j) (M j)) atTop atTop) :
    Tendsto (fun j => shiftedHarmonicMean (A j) (M j) (fun n => |G n|)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    (h.abs.eventually_lt_const (show |(0 : ℝ)| < ε/2 by simpa using half_pos hε))
  have hp (n : ℕ) (hn : 0 < n) : |G n| ≤ ε/2+B*T*(1/(n : ℝ)) := by
    by_cases ht : T ≤ n
    · exact (hT n ht).le.trans (le_add_of_nonneg_right (by positivity))
    · have hnr : (0 : ℝ) < n := by exact_mod_cast hn
      have hnt : (n : ℝ) ≤ T := by exact_mod_cast (show n ≤ T by omega)
      have hb : B ≤ B*T*(1/(n : ℝ)) := by
        rw [mul_one_div]
        apply (le_div_iff₀ hnr).mpr
        exact mul_le_mul_of_nonneg_left hnt hB
      linarith [hG n]
  have ht : Tendsto (fun j => 2*B*T/shiftedHarmonicMass (A j) (M j)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hH
  filter_upwards [ht.eventually_lt_const (half_pos hε)] with j hj
  have hm := shiftedHarmonicMean_local_mono (A j) (M j) (fun n => |G n|)
    (fun n => ε/2+B*T*(1/(n : ℝ))) (fun k _ => hp _ (by omega))
  rw [shiftedHarmonicMean_add,shiftedHarmonicMean_const,shiftedHarmonicMean_const_mul] at hm
  have hr := mul_le_mul_of_nonneg_left (shiftedHarmonicMean_reciprocal_bound (A j) (M j))
    (show 0 ≤ B*(T : ℝ) by positivity)
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (shiftedHarmonicMean_nonneg _ _ _ (fun _ => abs_nonneg _))]
  have he : B*T*(2/shiftedHarmonicMass (A j) (M j)) =
      2*B*T/shiftedHarmonicMass (A j) (M j) := by ring
  rw [he] at hr
  linarith

lemma prefixMean_const_mul (N : ℕ) (c : ℝ) (f : ℕ → ℝ) :
    prefixMean N (fun n => c*f n) = c*prefixMean N f := by
  simp only [prefixMean,← mul_sum,mul_div_assoc]

lemma shiftedHarmonicMean_prefix_error_bounded (f : ℕ → ℝ) (B : ℝ) (hB : 0 < B)
    (hf : ∀ n, |f n| ≤ B) (A M : ℕ) :
    |shiftedHarmonicMean A M f-shiftedHarmonicMean A M (fun n => prefixMean n f)| ≤
      6*B/shiftedHarmonicMass A M := by
  have hb (n : ℕ) : |B⁻¹*f n| ≤ 1 := by
    rw [abs_mul,abs_of_pos (inv_pos.mpr hB)]
    simpa only [inv_mul_cancel₀ hB.ne'] using
      mul_le_mul_of_nonneg_left (hf n) (inv_nonneg.mpr hB.le)
  have h := shiftedHarmonicMean_prefix_error (fun n => B⁻¹*f n) hb A M
  simp only [prefixMean_const_mul,shiftedHarmonicMean_const_mul,← mul_sub,abs_mul,
    abs_of_pos (inv_pos.mpr hB)] at h
  have hh := mul_le_mul_of_nonneg_left h hB.le
  rw [← mul_assoc,mul_inv_cancel₀ hB.ne',one_mul] at hh
  convert hh using 1 <;> ring

lemma positiveRawSum_floor_reindex_error (p N : ℕ) (hp : 0 < p)
    (G : ℕ → ℝ) (hG : ∀ n, |G n| ≤ 1) :
    |positiveRawSum N (fun n => G (n/p))-positiveRawSum N G| ≤ 3*p+12 := by
  have h₁ := harmonicRawRange_Icc_error N (fun n => G (n/p)) (fun n => hG _)
  have h₂ := harmonicRawRange_Icc_error N G hG
  have h₃ := harmonicRawRange_floor_reindex_error p N hp G hG
  change |harmonicRawRange N (fun n => G (n/p))-positiveRawSum N (fun n => G (n/p))| ≤ 2 at h₁
  change |harmonicRawRange N G-positiveRawSum N G| ≤ 2 at h₂
  have ht₁ := abs_sub_le (positiveRawSum N (fun n => G (n/p)))
    (harmonicRawRange N (fun n => G (n/p))) (positiveRawSum N G)
  have ht₂ := abs_sub_le (harmonicRawRange N (fun n => G (n/p)))
    (harmonicRawRange N G) (positiveRawSum N G)
  rw [abs_sub_comm (harmonicRawRange N (fun n => G (n/p)))] at h₁
  linarith

lemma shiftedHarmonicMean_floor_reindex_error (p A M : ℕ) (hp : 0 < p)
    (G : ℕ → ℝ) (hG : ∀ n, |G n| ≤ 1) :
    |shiftedHarmonicMean A M (fun n => G (n/p))-shiftedHarmonicMean A M G| ≤
      (6*p+24 : ℝ)/shiftedHarmonicMass A M := by
  unfold shiftedHarmonicMean
  rw [← sub_div,abs_div,abs_of_pos (shiftedHarmonicMass_pos A M)]
  apply div_le_div_of_nonneg_right _ (shiftedHarmonicMass_pos A M).le
  rw [shiftedHarmonicRaw_eq_sub,shiftedHarmonicRaw_eq_sub]
  have h₁ := positiveRawSum_floor_reindex_error p (A+M+1) hp G hG
  have h₂ := positiveRawSum_floor_reindex_error p A hp G hG
  have he : (positiveRawSum (A+M+1) (fun n => G (n/p))-positiveRawSum A (fun n => G (n/p)))-
      (positiveRawSum (A+M+1) G-positiveRawSum A G) =
      (positiveRawSum (A+M+1) (fun n => G (n/p))-positiveRawSum (A+M+1) G)-
        (positiveRawSum A (fun n => G (n/p))-positiveRawSum A G) := by ring
  rw [he]
  exact (abs_sub _ _).trans (by linarith)

#print axioms shiftedEndpointLaw_reciprocal_bound
#print axioms shiftedHarmonicMean_abs_zero
#print axioms shiftedHarmonicMean_floor_reindex_error
end Erdos371.FiniteInformation
