import Submission.ComparablePrefixQuotients
import Submission.HarmonicPrefixStableAdjacent
import Submission.HarmonicPrefixPrimeSkewL1

/-! A finite anchor inequality for the L1 ordinary-prefix bias. Every
shorter endpoint N/p is retained until comparable-quotient and reindexing
bounds have explicitly accounted for it. -/
namespace Erdos371.FiniteInformation
open Finset
set_option autoImplicit false

noncomputable def harmonicPrefixBias (N : ℕ) (f : ℕ → ℝ) : ℝ :=
  mean (harmonicPrefixLaw N) (fun i => |prefixMean (harmonicPrefixLength N i) f|)

lemma harmonicPrefixBias_anchor_bound (N q : ℕ) (hq : 0 < q)
    (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1) (P : Finset ℕ) (hne : P.Nonempty)
    (hP : ∀ p ∈ P, 0 < p ∧ p ≤ q) (δ : ℝ) (hδ : 0 ≤ δ)
    (hclose : ∀ p ∈ P, (1-δ)*(q : ℝ) ≤ p) :
    harmonicPrefixBias N f ≤
      mean (harmonicPrefixLaw N) (fun i => |(∑ p ∈ P,
        prefixMean (harmonicPrefixLength N i/p) f)/(P.card : ℝ)|)+
      2*δ+(5*q+12 : ℝ)/(harmonic (N+1) : ℝ) := by
  let V (i : Fin (N+1)) := (∑ p ∈ P, prefixMean (harmonicPrefixLength N i/p) f)/(P.card : ℝ)
  have hcard : (P.card : ℝ) ≠ 0 := by exact_mod_cast (card_pos.mpr hne).ne'
  have hdiff (i : Fin (N+1)) : |V i-prefixMean (harmonicPrefixLength N i/q) f| ≤
      2*δ+2*q/(harmonicPrefixLength N i : ℝ) := by
    have he : V i-prefixMean (harmonicPrefixLength N i/q) f =
        (∑ p ∈ P, (prefixMean (harmonicPrefixLength N i/p) f-
          prefixMean (harmonicPrefixLength N i/q) f))/(P.card : ℝ) := by
      dsimp [V]
      rw [sum_sub_distrib,sum_const,nsmul_eq_mul,sub_div,mul_div_cancel_left₀ _ hcard]
    rw [he]
    exact abs_finset_average_le P hne _ _ (fun p hp =>
      prefixMean_quotient_comparable f hf _ p q (hP p hp).1 (hP p hp).2 δ hδ (hclose p hp))
  have hpoint (i : Fin (N+1)) : |prefixMean (harmonicPrefixLength N i/q) f| ≤
      |V i|+(2*δ+2*q/(harmonicPrefixLength N i : ℝ)) := by
    have ht := abs_sub_le (prefixMean (harmonicPrefixLength N i/q) f) (V i) 0
    simp only [sub_zero] at ht
    have he := hdiff i
    rw [abs_sub_comm (V i)] at he
    linarith
  have hm := mean_mono (harmonicPrefixLaw N) _ _ hpoint
  rw [mean_add,mean_add,mean_const] at hm
  have he : (fun i : Fin (N+1) => 2*(q : ℝ)/(harmonicPrefixLength N i : ℝ)) =
      (fun i => (2*(q : ℝ))*((1 : ℝ)/harmonicPrefixLength N i)) := by funext i; ring
  rw [he,mean_const_mul,harmonicPrefixLaw_reciprocal_length] at hm
  have hr := harmonicPrefixLaw_floor_reindex_error q N hq
    (fun n => |prefixMean n f|) (fun n => by simpa only [abs_abs] using prefixMean_unit_bound f hf n)
  have hlo := (abs_le.mp hr).1
  change -((3*q+12 : ℝ)/(harmonic (N+1) : ℝ)) ≤
    mean (harmonicPrefixLaw N) (fun i => |prefixMean (harmonicPrefixLength N i/q) f|)-
      harmonicPrefixBias N f at hlo
  have hb : harmonicPrefixBias N f ≤ mean (harmonicPrefixLaw N) (fun i => |V i|)+
      (2*δ+2*q*(1/(harmonic (N+1) : ℝ)))+(3*q+12 : ℝ)/(harmonic (N+1) : ℝ) := by linarith
  convert hb using 1
  ring

variable {A : Type*} [Fintype A] [DecidableEq A]

lemma harmonicPrefixBias_transfer_bound (N q : ℕ) (hq : 0 < q)
    (L : ℕ → A) (C : A → A → ℝ) (hC : ∀ a b, |C a b| ≤ 1)
    (P : Finset ℕ) (hne : P.Nonempty) (hP : ∀ p ∈ P, 0 < p ∧ p ≤ q)
    (δ : ℝ) (hδ : 0 ≤ δ) (hclose : ∀ p ∈ P, (1-δ)*(q : ℝ) ≤ p) :
    harmonicPrefixBias N (fun n => C (L n) (L (n+1))) ≤
      mean (harmonicPrefixLaw N) (fun i => |(∑ p ∈ P,
        naturalGapDiscrepancy (harmonicPrefixLength N i) p L C)/(P.card : ℝ)|)+
      harmonicPrefixPrimeSkewL1 N L P (fun _ => C)+
      mean (harmonicPrefixLaw N) (fun i => |(∑ p ∈ P,
        naturalAdjacentTransferError p (harmonicPrefixLength N i) L C)/(P.card : ℝ)|)+
      2*δ+(5*q+12 : ℝ)/(harmonic (N+1) : ℝ) := by
  have ha := harmonicPrefixBias_anchor_bound N q hq (fun n => C (L n) (L (n+1)))
    (fun n => hC _ _) P hne hP δ hδ hclose
  have hpoint (i : Fin (N+1)) :
      |(∑ p ∈ P, prefixMean (harmonicPrefixLength N i/p) (fun n => C (L n) (L (n+1))))/(P.card : ℝ)| ≤
      |(∑ p ∈ P, naturalGapDiscrepancy (harmonicPrefixLength N i) p L C)/(P.card : ℝ)|+
      |naturalPrimeSkewAverage (harmonicPrefixLength N i) L P C|+
      |(∑ p ∈ P, naturalAdjacentTransferError p (harmonicPrefixLength N i) L C)/(P.card : ℝ)| := by
    have he : (∑ p ∈ P, prefixMean (harmonicPrefixLength N i/p) (fun n => C (L n) (L (n+1))))/(P.card : ℝ) =
        (∑ p ∈ P, naturalGapDiscrepancy (harmonicPrefixLength N i) p L C)/(P.card : ℝ)+
        naturalPrimeSkewAverage (harmonicPrefixLength N i) L P C-
        (∑ p ∈ P, naturalAdjacentTransferError p (harmonicPrefixLength N i) L C)/(P.card : ℝ) := by
      unfold naturalPrimeSkewAverage naturalAdjacentTransferError
      simp only [sum_sub_distrib,sub_div]
      ring
    rw [he]
    exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  have hm := mean_mono (harmonicPrefixLaw N) _ _ hpoint
  simp only [mean_add] at hm
  change _ ≤ _+harmonicPrefixPrimeSkewL1 N L P (fun _ => C)+_ at hm
  linarith

#print axioms harmonicPrefixBias_anchor_bound
#print axioms harmonicPrefixBias_transfer_bound
end Erdos371.FiniteInformation
