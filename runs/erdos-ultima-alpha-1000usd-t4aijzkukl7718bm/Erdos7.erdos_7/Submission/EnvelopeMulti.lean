import Submission.EnvelopeExtension

/-! Finite ordered families admit a common separable convex majorant,
with no loss on the diagonal. This is an auxiliary comparison result. -/
namespace Erdos7EnvelopeMulti
open scoped BigOperators
open Erdos7EnvelopeExtension
set_option maxHeartbeats 1500000

def rowEnvelope {ι : Type*} (S : Finset ι) (φ : ι → ℝ → ℝ)
    (a : ℕ → ι → ℝ) (d : ℕ → ℝ) : ℕ → (ι → ℝ) → ℝ
  | 0, _ => 0
  | n + 1, x => max (rowEnvelope S φ a d n x) (d n + ∑ i ∈ S, a n i * φ i (x i))

/-- Monotone coefficient rows can be split simultaneously, even though the
individual component arguments in the resulting bound need not agree. -/
theorem ordered_envelope_split {ι : Type*} (S : Finset ι) (φ : ι → ℝ → ℝ)
    (a : ℕ → ι → ℝ) (d : ℕ → ℝ) (lo hi : ℝ) (hlh : lo ≤ hi)
    (hφ : ∀ i ∈ S, ConvexOn ℝ Set.univ (φ i))
    (hmφ : ∀ i ∈ S, Monotone (φ i))
    (ha : ∀ k i, i ∈ S → 0 ≤ a k i)
    (hma : ∀ i ∈ S, Monotone (fun k => a k i)) (n : ℕ) :
    ∃ (b : ℝ) (h : ι → ℝ → ℝ),
      (∀ i ∈ S, ConvexOn ℝ Set.univ (h i) ∧ Monotone (h i) ∧
        Monotone (fun x => a n i * φ i x - h i x)) ∧
      (∀ x ∈ Set.Icc lo hi, b + (∑ i ∈ S, h i x) =
        rowEnvelope S φ a d n (fun _ => x)) ∧
      (∀ x : ι → ℝ, (∀ i ∈ S, x i ∈ Set.Icc lo hi) →
        rowEnvelope S φ a d n x ≤ b + ∑ i ∈ S, h i (x i)) := by
  induction n with
  | zero =>
    refine ⟨0, fun _ _ => 0, ?_, ?_, ?_⟩
    · intro i hi
      refine ⟨convexOn_const 0 convex_univ, monotone_const, ?_⟩
      intro x y hxy
      simpa only [sub_zero] using mul_le_mul_of_nonneg_left (hmφ i hi hxy) (ha 0 i hi)
    · intro x _
      simp [rowEnvelope]
    · intro x _
      simp [rowEnvelope]
  | succ n ih =>
    obtain ⟨b, h, hh, hdiag, hmaj⟩ := ih
    let g (i : ι) (x : ℝ) := a n i * φ i x
    have hg (i : ι) (hi : i ∈ S) : ConvexOn ℝ Set.univ (g i) := by
      simpa only [smul_eq_mul] using ConvexOn.smul (ha n i hi) (hφ i hi)
    have hmg (i : ι) (hi : i ∈ S) : Monotone (g i) := by
      intro x y hxy
      exact mul_le_mul_of_nonneg_left (hmφ i hi hxy) (ha n i hi)
    obtain ⟨b', h', hh', hdiag', hmaj'⟩ := extend_envelope S h g b (d n) lo hi hlh
      (fun i hi => (hh i hi).1) hg (fun i hi => (hh i hi).2.1) hmg
      (fun i hi => (hh i hi).2.2)
    refine ⟨b', h', ?_, ?_, ?_⟩
    · intro i hi
      refine ⟨(hh' i hi).1, (hh' i hi).2.1, ?_⟩
      have hdelta : 0 ≤ a (n + 1) i - a n i := sub_nonneg.mpr (hma i hi (by omega))
      have hmono : Monotone (fun x => (a (n + 1) i - a n i) * φ i x) := by
        intro x y hxy
        exact mul_le_mul_of_nonneg_left (hmφ i hi hxy) hdelta
      have hadd := hmono.add (hh' i hi).2.2
      convert hadd using 1
      funext x
      dsimp [g]
      ring
    · intro x hx
      rw [hdiag' x hx, hdiag x hx]
      rfl
    · intro x hx
      exact (max_le_max (hmaj x hx) le_rfl).trans (hmaj' x hx)

lemma rowEnvelope_le {ι : Type*} (S : Finset ι) (φ : ι → ℝ → ℝ)
    (a : ℕ → ι → ℝ) (d : ℕ → ℝ) (n : ℕ) (x : ι → ℝ) (v : ℝ)
    (hv : 0 ≤ v) (hrows : ∀ k < n, d k + (∑ i ∈ S, a k i * φ i (x i)) ≤ v) :
    rowEnvelope S φ a d n x ≤ v := by
  induction n with
  | zero => exact hv
  | succ n ih =>
    exact max_le (ih (fun k hk => hrows k (by omega))) (hrows n (by omega))

lemma row_le_rowEnvelope {ι : Type*} (S : Finset ι) (φ : ι → ℝ → ℝ)
    (a : ℕ → ι → ℝ) (d : ℕ → ℝ) (n k : ℕ) (hk : k < n) (x : ι → ℝ) :
    d k + (∑ i ∈ S, a k i * φ i (x i)) ≤ rowEnvelope S φ a d n x := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : k = n
    · subst k
      exact le_max_right _ _
    · exact (ih (by omega)).trans (le_max_left _ _)

/-- A diagonal dual inequality for ordered nonnegative coefficient rows lifts
to a separable convex dual for independently evaluated component families.
This avoids assuming that the actual families share a common extremizer. -/
theorem ordered_convex_dual_split {ι : Type*} (S : Finset ι) (φ : ι → ℝ → ℝ)
    (a : ℕ → ι → ℝ) (U loss : ℕ → ℝ) (V : ℝ → ℝ)
    (lo hi : ℝ) (hlh : lo ≤ hi)
    (hφ : ∀ i ∈ S, ConvexOn ℝ Set.univ (φ i))
    (hmφ : ∀ i ∈ S, Monotone (φ i))
    (ha : ∀ k i, i ∈ S → 0 ≤ a k i)
    (hma : ∀ i ∈ S, Monotone (fun k => a k i)) (n : ℕ)
    (hV : ∀ x ∈ Set.Icc lo hi, 0 ≤ V x)
    (hdual : ∀ k < n, ∀ x ∈ Set.Icc lo hi,
      loss k + (∑ i ∈ S, a k i * φ i x) ≤ U k + V x) :
    ∃ (b : ℝ) (h : ι → ℝ → ℝ),
      (∀ i ∈ S, ConvexOn ℝ Set.univ (h i) ∧ Monotone (h i)) ∧
      (∀ x ∈ Set.Icc lo hi, b + (∑ i ∈ S, h i x) ≤ V x) ∧
      (∀ k < n, ∀ x : ι → ℝ, (∀ i ∈ S, x i ∈ Set.Icc lo hi) →
        loss k + (∑ i ∈ S, a k i * φ i (x i)) ≤ U k + b + ∑ i ∈ S, h i (x i)) := by
  let d (k : ℕ) := loss k - U k
  obtain ⟨b, h, hh, hdiag, hmaj⟩ := ordered_envelope_split S φ a d lo hi hlh hφ hmφ ha hma n
  refine ⟨b, h, (fun i hi => ⟨(hh i hi).1, (hh i hi).2.1⟩), ?_, ?_⟩
  · intro x hx
    rw [hdiag x hx]
    apply rowEnvelope_le S φ a d n (fun _ => x) (V x) (hV x hx)
    intro k hk
    have hd := hdual k hk x hx
    dsimp [d]
    linarith
  · intro k hk x hx
    have hb := (row_le_rowEnvelope S φ a d n k hk x).trans (hmaj x hx)
    dsimp [d] at hb
    linarith

#print axioms ordered_convex_dual_split

#print axioms ordered_envelope_split
end Erdos7EnvelopeMulti
