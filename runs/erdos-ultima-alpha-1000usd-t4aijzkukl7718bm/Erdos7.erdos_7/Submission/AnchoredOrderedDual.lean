import Submission.EnvelopeMulti

/-! An ordered separable dual can be anchored at the lower endpoint whenever
its scalar majorant is monotone. This is a comparison lemma, not a covering
obstruction, and does not give exact diagonal completion at every point. -/
namespace Erdos7AnchoredOrderedDual
open scoped BigOperators
open Erdos7EnvelopeMulti
set_option autoImplicit false
set_option maxHeartbeats 1500000

lemma rowEnvelope_nonneg {ι : Type*} (S : Finset ι) (φ : ι → ℝ → ℝ)
    (a : ℕ → ι → ℝ) (d : ℕ → ℝ) (n : ℕ) (x : ι → ℝ) :
    0 ≤ rowEnvelope S φ a d n x := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact ih.trans (le_max_left _ _)

/-- The constant is exactly V(lo), and every component is zero at lo and
nonnegative to its right. Different components may still have different
actual arguments; no common maximizer is assumed. -/
theorem anchored_dual_split {ι : Type*} (S : Finset ι) (φ : ι → ℝ → ℝ)
    (a : ℕ → ι → ℝ) (U loss : ℕ → ℝ) (V : ℝ → ℝ)
    (lo hi : ℝ) (hlh : lo ≤ hi)
    (hφ : ∀ i ∈ S, ConvexOn ℝ Set.univ (φ i))
    (hmφ : ∀ i ∈ S, Monotone (φ i))
    (ha : ∀ k i, i ∈ S → 0 ≤ a k i)
    (hma : ∀ i ∈ S, Monotone (fun k => a k i)) (n : ℕ)
    (hmV : MonotoneOn V (Set.Icc lo hi))
    (hdual : ∀ k < n, ∀ x ∈ Set.Icc lo hi,
      loss k + (∑ i ∈ S, a k i * φ i x) ≤ U k + V x) :
    ∃ ψ : ι → ℝ → ℝ,
      (∀ i ∈ S, ConvexOn ℝ Set.univ (ψ i) ∧ Monotone (ψ i) ∧ ψ i lo = 0 ∧
        ∀ x,lo ≤ x → 0 ≤ ψ i x) ∧
      (∀ x ∈ Set.Icc lo hi, V lo + (∑ i ∈ S,ψ i x) ≤ V x) ∧
      (∀ k < n,∀ x : ι → ℝ,(∀ i ∈ S,x i ∈ Set.Icc lo hi) →
        loss k + (∑ i ∈ S,a k i*φ i (x i)) ≤ U k+V lo+∑ i ∈ S,ψ i (x i)) := by
  let d := fun k => loss k-U k-V lo
  obtain ⟨b,h,hh,hdiag,hmaj⟩ := ordered_envelope_split S φ a d lo hi hlh hφ hmφ ha hma n
  have hlo : lo ∈ Set.Icc lo hi := ⟨le_rfl,hlh⟩
  have henv (x : ℝ) (hx : x ∈ Set.Icc lo hi) :
      rowEnvelope S φ a d n (fun _ => x) ≤ V x-V lo := by
    apply rowEnvelope_le S φ a d n (fun _ => x) (V x-V lo)
      (sub_nonneg.mpr (hmV hlo hx hx.1))
    intro k hk
    have hd := hdual k hk x hx
    dsimp only [d]
    linarith
  have hz : b+(∑ i ∈ S,h i lo) = 0 := by
    rw [hdiag lo hlo]
    have hh₀ := henv lo hlo
    have hh₁ := rowEnvelope_nonneg S φ a d n (fun _ => lo)
    linarith
  let ψ := fun i x => h i x-h i lo
  refine ⟨ψ,?_,?_,?_⟩
  · intro i hi
    refine ⟨?_,?_,by simp only [ψ,sub_self],?_⟩
    · simpa only [ψ,sub_eq_add_neg,Pi.add_apply] using (hh i hi).1.add_const (-(h i lo))
    · intro x y hxy
      exact sub_le_sub_right ((hh i hi).2.1 hxy) _
    · intro x hx
      exact sub_nonneg.mpr ((hh i hi).2.1 hx)
  · intro x hx
    have hd := hdiag x hx
    have he := henv x hx
    simp only [ψ,Finset.sum_sub_distrib]
    linarith
  · intro k hk x hx
    have hh₀ := (row_le_rowEnvelope S φ a d n k hk x).trans (hmaj x hx)
    dsimp only [d] at hh₀
    simp only [ψ,Finset.sum_sub_distrib]
    linarith

#print axioms anchored_dual_split
end Erdos7AnchoredOrderedDual
