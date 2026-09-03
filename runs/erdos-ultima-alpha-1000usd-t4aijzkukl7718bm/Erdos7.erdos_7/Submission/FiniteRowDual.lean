import Submission.EnvelopeMulti

/-! The ordered-envelope theorem for a finite set of actual real row labels.
Rows are sorted in reverse order; repetitions in the original data do not
require a common argument for the component families. -/
namespace Erdos7FiniteRowDual
open scoped BigOperators
open Erdos7EnvelopeMulti
set_option maxHeartbeats 1500000

theorem antitone_finite_dual_split {ι : Type*} (S : Finset ι)
    (φ : ι → ℝ → ℝ) (a : ℝ → ι → ℝ) (U loss V : ℝ → ℝ)
    (T : Finset ℝ) (hT : T.Nonempty) (lo hi : ℝ) (hlh : lo ≤ hi)
    (hφ : ∀ i ∈ S, ConvexOn ℝ Set.univ (φ i))
    (hmφ : ∀ i ∈ S, Monotone (φ i))
    (ha : ∀ k ∈ T, ∀ i ∈ S, 0 ≤ a k i)
    (hma : ∀ i ∈ S, Antitone (fun k => a k i))
    (hV : ∀ x ∈ Set.Icc lo hi, 0 ≤ V x)
    (hdual : ∀ k ∈ T, ∀ x ∈ Set.Icc lo hi,
      loss k + (∑ i ∈ S, a k i * φ i x) ≤ U k + V x) :
    ∃ (b : ℝ) (h : ι → ℝ → ℝ),
      (∀ i ∈ S, ConvexOn ℝ Set.univ (h i) ∧ Monotone (h i)) ∧
      (∀ x ∈ Set.Icc lo hi, b + (∑ i ∈ S, h i x) ≤ V x) ∧
      (∀ k ∈ T, ∀ x : ι → ℝ, (∀ i ∈ S, x i ∈ Set.Icc lo hi) →
        loss k + (∑ i ∈ S, a k i * φ i (x i)) ≤ U k + b + ∑ i ∈ S, h i (x i)) := by
  classical
  have hcard : 0 < T.card := Finset.card_pos.mpr hT
  let clamp (r : ℕ) : Fin T.card := ⟨min r (T.card-1), by omega⟩
  have hmclamp : Monotone clamp := by
    intro r s hrs
    change min r (T.card-1) ≤ min s (T.card-1)
    exact min_le_min_right _ hrs
  let k (r : ℕ) : ℝ := T.orderEmbOfFin rfl (clamp r).rev
  have hk : Antitone k := by
    intro r s hrs
    exact (T.orderEmbOfFin rfl).monotone (Fin.rev_anti (hmclamp hrs))
  have hkT (r : ℕ) : k r ∈ T := T.orderEmbOfFin_mem rfl _
  obtain ⟨b, h, hh, hdiag, hmaj⟩ := ordered_convex_dual_split S φ
    (fun r i => a (k r) i) (fun r => U (k r)) (fun r => loss (k r)) V
    lo hi hlh hφ hmφ
    (fun r i hi => ha (k r) (hkT r) i hi)
    (fun i hi => (hma i hi).comp hk) T.card hV
    (fun r _ x hx => hdual (k r) (hkT r) x hx)
  refine ⟨b, h, hh, hdiag, ?_⟩
  intro t ht x hx
  obtain ⟨i, hi⟩ := (T.orderIsoOfFin rfl).surjective (⟨t, ht⟩ : T)
  have hit : T.orderEmbOfFin rfl i = t := congrArg Subtype.val hi
  have hcl : clamp i.rev.val = i.rev := by
    apply Fin.ext
    change min i.rev.val (T.card-1) = i.rev.val
    exact min_eq_left (by have := i.rev.isLt; omega)
  have hkt : k i.rev.val = t := by
    dsimp only [k]
    rw [hcl, Fin.rev_rev, hit]
  simpa only [hkt] using hmaj i.rev.val i.rev.isLt x hx

#print axioms antitone_finite_dual_split
end Erdos7FiniteRowDual
