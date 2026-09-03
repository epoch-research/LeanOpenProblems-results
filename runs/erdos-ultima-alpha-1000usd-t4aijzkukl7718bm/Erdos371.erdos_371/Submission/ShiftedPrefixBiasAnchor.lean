import Submission.ComparablePrefixQuotients
import Submission.ShiftedPrefixStableAdjacent
import Submission.ShiftedPrefixPrimeSkewL1

/-! A finite anchor inequality for the L1 ordinary-prefix bias. Every
shorter endpoint N/p is retained until comparable-quotient and reindexing
bounds have explicitly accounted for it. -/
namespace Erdos371.FiniteInformation
open Finset
set_option autoImplicit false

noncomputable def shiftedPrefixBias (A N : ℕ) (f : ℕ → ℝ) : ℝ :=
  mean (shiftedEndpointLaw A N) (fun i => |prefixMean (shiftedEndpoint A N i) f|)

lemma shiftedPrefixBias_anchor_bound (A N q : ℕ) (hq : 0 < q)
    (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1) (P : Finset ℕ) (hne : P.Nonempty)
    (hP : ∀ p ∈ P, 0 < p ∧ p ≤ q) (δ : ℝ) (hδ : 0 ≤ δ)
    (hclose : ∀ p ∈ P, (1-δ)*(q : ℝ) ≤ p) :
    shiftedPrefixBias A N f ≤
      mean (shiftedEndpointLaw A N) (fun i => |(∑ p ∈ P,
        prefixMean (shiftedEndpoint A N i/p) f)/(P.card : ℝ)|)+
      2*δ+(10*q+24 : ℝ)/shiftedHarmonicMass A N := by
  let V (i : Fin (N+1)) := (∑ p ∈ P, prefixMean (shiftedEndpoint A N i/p) f)/(P.card : ℝ)
  have hcard : (P.card : ℝ) ≠ 0 := by exact_mod_cast (card_pos.mpr hne).ne'
  have hdiff (i : Fin (N+1)) : |V i-prefixMean (shiftedEndpoint A N i/q) f| ≤
      2*δ+2*q/(shiftedEndpoint A N i : ℝ) := by
    have he : V i-prefixMean (shiftedEndpoint A N i/q) f =
        (∑ p ∈ P, (prefixMean (shiftedEndpoint A N i/p) f-
          prefixMean (shiftedEndpoint A N i/q) f))/(P.card : ℝ) := by
      dsimp [V]
      rw [sum_sub_distrib,sum_const,nsmul_eq_mul,sub_div,mul_div_cancel_left₀ _ hcard]
    rw [he]
    exact abs_finset_average_le P hne _ _ (fun p hp =>
      prefixMean_quotient_comparable f hf _ p q (hP p hp).1 (hP p hp).2 δ hδ (hclose p hp))
  have hpoint (i : Fin (N+1)) : |prefixMean (shiftedEndpoint A N i/q) f| ≤
      |V i|+(2*δ+2*q/(shiftedEndpoint A N i : ℝ)) := by
    have ht := abs_sub_le (prefixMean (shiftedEndpoint A N i/q) f) (V i) 0
    simp only [sub_zero] at ht
    have he := hdiff i
    rw [abs_sub_comm (V i)] at he
    linarith
  have hm := mean_mono (shiftedEndpointLaw A N) _ _ hpoint
  rw [mean_add,mean_add,mean_const] at hm
  have he : (fun i : Fin (N+1) => 2*(q : ℝ)/(shiftedEndpoint A N i : ℝ)) =
      (fun i => (2*(q : ℝ))*((1 : ℝ)/shiftedEndpoint A N i)) := by funext i; ring
  rw [he,mean_const_mul] at hm
  have hrec := mul_le_mul_of_nonneg_left (shiftedEndpointLaw_reciprocal_bound A N)
    (show 0 ≤ 2*(q : ℝ) by positivity)
  have heq : (2*(q : ℝ))*(2/shiftedHarmonicMass A N) = 4*q/shiftedHarmonicMass A N := by ring
  rw [heq] at hrec
  have hr := shiftedHarmonicMean_floor_reindex_error q A N hq
    (fun n => |prefixMean n f|) (fun n => by simpa only [abs_abs] using prefixMean_unit_bound f hf n)
  rw [← shiftedEndpointLaw_mean A N (fun n => |prefixMean (n/q) f|),
    ← shiftedEndpointLaw_mean A N (fun n => |prefixMean n f|)] at hr
  have hlo := (abs_le.mp hr).1
  change -((6*q+24 : ℝ)/shiftedHarmonicMass A N) ≤
    mean (shiftedEndpointLaw A N) (fun i => |prefixMean (shiftedEndpoint A N i/q) f|)-
      shiftedPrefixBias A N f at hlo
  have hb : shiftedPrefixBias A N f ≤ mean (shiftedEndpointLaw A N) (fun i => |V i|)+
      (2*δ+4*q/shiftedHarmonicMass A N)+(6*q+24 : ℝ)/shiftedHarmonicMass A N := by linarith
  convert hb using 1
  ring

variable {X : Type*} [Fintype X] [DecidableEq X]

lemma shiftedPrefixBias_transfer_bound (A N q : ℕ) (hq : 0 < q)
    (L : ℕ → X) (C : X → X → ℝ) (hC : ∀ a b, |C a b| ≤ 1)
    (P : Finset ℕ) (hne : P.Nonempty) (hP : ∀ p ∈ P, 0 < p ∧ p ≤ q)
    (δ : ℝ) (hδ : 0 ≤ δ) (hclose : ∀ p ∈ P, (1-δ)*(q : ℝ) ≤ p) :
    shiftedPrefixBias A N (fun n => C (L n) (L (n+1))) ≤
      mean (shiftedEndpointLaw A N) (fun i => |(∑ p ∈ P,
        naturalGapDiscrepancy (shiftedEndpoint A N i) p L C)/(P.card : ℝ)|)+
      shiftedPrefixPrimeSkewL1 A N L P (fun _ => C)+
      mean (shiftedEndpointLaw A N) (fun i => |(∑ p ∈ P,
        naturalAdjacentTransferError p (shiftedEndpoint A N i) L C)/(P.card : ℝ)|)+
      2*δ+(10*q+24 : ℝ)/shiftedHarmonicMass A N := by
  have ha := shiftedPrefixBias_anchor_bound A N q hq (fun n => C (L n) (L (n+1)))
    (fun n => hC _ _) P hne hP δ hδ hclose
  have hpoint (i : Fin (N+1)) :
      |(∑ p ∈ P, prefixMean (shiftedEndpoint A N i/p) (fun n => C (L n) (L (n+1))))/(P.card : ℝ)| ≤
      |(∑ p ∈ P, naturalGapDiscrepancy (shiftedEndpoint A N i) p L C)/(P.card : ℝ)|+
      |naturalPrimeSkewAverage (shiftedEndpoint A N i) L P C|+
      |(∑ p ∈ P, naturalAdjacentTransferError p (shiftedEndpoint A N i) L C)/(P.card : ℝ)| := by
    have he : (∑ p ∈ P, prefixMean (shiftedEndpoint A N i/p) (fun n => C (L n) (L (n+1))))/(P.card : ℝ) =
        (∑ p ∈ P, naturalGapDiscrepancy (shiftedEndpoint A N i) p L C)/(P.card : ℝ)+
        naturalPrimeSkewAverage (shiftedEndpoint A N i) L P C-
        (∑ p ∈ P, naturalAdjacentTransferError p (shiftedEndpoint A N i) L C)/(P.card : ℝ) := by
      unfold naturalPrimeSkewAverage naturalAdjacentTransferError
      simp only [sum_sub_distrib,sub_div]
      ring
    rw [he]
    exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  have hm := mean_mono (shiftedEndpointLaw A N) _ _ hpoint
  simp only [mean_add] at hm
  change _ ≤ _+shiftedPrefixPrimeSkewL1 A N L P (fun _ => C)+_ at hm
  linarith

#print axioms shiftedPrefixBias_anchor_bound
#print axioms shiftedPrefixBias_transfer_bound
end Erdos371.FiniteInformation
