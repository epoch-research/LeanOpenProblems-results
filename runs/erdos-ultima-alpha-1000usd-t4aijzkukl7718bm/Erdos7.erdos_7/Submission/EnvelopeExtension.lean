import Submission.RealEnvelopeSplit

/-! A finite-interval extension step for ordered, separable convex envelopes.
This is not the full covering-system comparison or a solution of Erdos7. -/
namespace Erdos7EnvelopeExtension
open scoped BigOperators
open Erdos7RealEnvelopeSplit
set_option maxHeartbeats 1500000

/-- When component differences are monotone, the maximum of two separable
rows has a separable convex majorant that agrees with it on the diagonal.
The new components remain below the second row in slope order. -/
theorem extend_envelope {ι : Type*} (S : Finset ι)
    (f g : ι → ℝ → ℝ) (c d lo hi : ℝ) (hlh : lo ≤ hi)
    (hf : ∀ i ∈ S, ConvexOn ℝ Set.univ (f i))
    (hg : ∀ i ∈ S, ConvexOn ℝ Set.univ (g i))
    (hmf : ∀ i ∈ S, Monotone (f i)) (hmg : ∀ i ∈ S, Monotone (g i))
    (hgf : ∀ i ∈ S, Monotone (fun x => g i x - f i x)) :
    ∃ (b : ℝ) (h : ι → ℝ → ℝ),
      (∀ i ∈ S, ConvexOn ℝ Set.univ (h i) ∧ Monotone (h i) ∧
        Monotone (fun x => g i x - h i x)) ∧
      (∀ x ∈ Set.Icc lo hi, b + (∑ i ∈ S, h i x) =
        max (c + ∑ i ∈ S, f i x) (d + ∑ i ∈ S, g i x)) ∧
      (∀ x : ι → ℝ, (∀ i ∈ S, x i ∈ Set.Icc lo hi) →
        max (c + ∑ i ∈ S, f i (x i)) (d + ∑ i ∈ S, g i (x i)) ≤
          b + ∑ i ∈ S, h i (x i)) := by
  classical
  let diff (x : ℝ) := d - c + ∑ i ∈ S, (g i x - f i x)
  have hdiff : Monotone diff := by
    intro x y hxy
    exact add_le_add le_rfl (Finset.sum_le_sum (fun i hi => hgf i hi hxy))
  have hdiffcont : Continuous diff := by
    apply continuous_const.add
    apply continuous_finset_sum
    intro i hi
    have hfc : Continuous (f i) := by
      simpa only [continuousOn_univ] using ConvexOn.continuousOn isOpen_univ (hf i hi)
    have hgc : Continuous (g i) := by
      simpa only [continuousOn_univ] using ConvexOn.continuousOn isOpen_univ (hg i hi)
    exact hgc.sub hfc
  by_cases hLo : 0 ≤ diff lo
  · refine ⟨d, g, ?_, ?_, ?_⟩
    · intro i hi
      exact ⟨hg i hi, hmg i hi, by simpa only [sub_self] using (monotone_const : Monotone (fun _ : ℝ => (0 : ℝ)))⟩
    · intro x hx
      have hh := hdiff hx.1
      dsimp [diff] at hh hLo
      simp only [Finset.sum_sub_distrib] at hh hLo
      exact (max_eq_right (by linarith)).symm
    · intro x hx
      have hh : (∑ i ∈ S, (g i lo - f i lo)) ≤
          ∑ i ∈ S, (g i (x i) - f i (x i)) :=
        Finset.sum_le_sum (fun i hi => hgf i hi (hx i hi).1)
      dsimp [diff] at hLo
      simp only [Finset.sum_sub_distrib] at hh hLo
      exact max_le (by linarith) le_rfl
  · by_cases hHi : diff hi ≤ 0
    · refine ⟨c, f, ?_, ?_, ?_⟩
      · intro i hi
        exact ⟨hf i hi, hmf i hi, hgf i hi⟩
      · intro x hx
        have hh := hdiff hx.2
        dsimp [diff] at hh hHi
        simp only [Finset.sum_sub_distrib] at hh hHi
        exact (max_eq_left (by linarith)).symm
      · intro x hx
        have hh : (∑ i ∈ S, (g i (x i) - f i (x i))) ≤
            ∑ i ∈ S, (g i hi - f i hi) :=
          Finset.sum_le_sum (fun i hi' => hgf i hi' (hx i hi').2)
        dsimp [diff] at hHi
        simp only [Finset.sum_sub_distrib] at hh hHi
        exact max_le le_rfl (by linarith)
    · have hz : (0 : ℝ) ∈ Set.Icc (diff lo) (diff hi) := ⟨by linarith, by linarith⟩
      obtain ⟨t, ht, hzero⟩ := intermediate_value_Icc hlh hdiffcont.continuousOn hz
      have hcross : c + (∑ i ∈ S, f i t) = d + ∑ i ∈ S, g i t := by
        dsimp [diff] at hzero
        simp only [Finset.sum_sub_distrib] at hzero
        linarith
      let h (i : ι) (x : ℝ) := max (f i x) (g i x + f i t - g i t)
      refine ⟨c, h, ?_, ?_, ?_⟩
      · intro i hi
        refine ⟨split_component_convex (f i) (g i) (hf i hi) (hg i hi) t,
          split_component_monotone (f i) (g i) (hmf i hi) (hmg i hi) t, ?_⟩
        have he : (fun x => g i x - h i x) = fun x => min (g i x - f i x) (g i t - f i t) := by
          funext x
          dsimp [h]
          simp only [max_def, min_def]
          split_ifs <;> linarith
        rw [he]
        exact (hgf i hi).min monotone_const
      · intro x _
        exact (two_row_envelope_identity S f g hgf c d t x hcross).symm
      · intro x _
        exact two_row_separable_majorant S f g c d t x hcross

#print axioms extend_envelope
end Erdos7EnvelopeExtension
