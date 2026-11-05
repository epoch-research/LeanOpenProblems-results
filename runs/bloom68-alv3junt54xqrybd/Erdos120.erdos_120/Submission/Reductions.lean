import FormalConjecturesUtil

/-!
# Elementary affine-avoidance reductions

These helpers are independent of `Submission.Spec`. Avoidance is monotone under
inclusion and invariant under nonzero affine changes of variables. Unbounded sets
have the unit interval as an avoidance witness. Inner regularity of real volume
also permits any avoidance witness to be replaced by a compact positive witness.

No result about avoidance for arbitrary bounded infinite sets is proved here.
-/

open Set MeasureTheory

namespace Erdos120Aux

/-- A measurable positive-volume set containing no nonzero affine copy of `A`. -/
def Avoidance (A : Set ℝ) : Prop := ∃ E : Set ℝ,
  MeasurableSet E ∧ 0 < volume E ∧
    ∀ a b : ℝ, a ≠ 0 → ¬ Set.image (fun x => a * x + b) A ⊆ E

/-- Avoidance of a subset implies avoidance of every set containing it. -/
theorem Avoidance.mono {A B : Set ℝ} (hB : Avoidance B) (hBA : B ⊆ A) :
    Avoidance A := by
  obtain ⟨E, hE, hpos, havoid⟩ := hB
  refine ⟨E, hE, hpos, ?_⟩
  intro a b ha hsub
  exact havoid a b ha ((Set.image_mono hBA).trans hsub)

/-- Composition of two affine images, with the resulting coefficients explicit. -/
theorem affine_image_comp (A : Set ℝ) (a b c d : ℝ) :
    Set.image (fun x => a * x + b) (Set.image (fun x => c * x + d) A) =
      Set.image (fun x => (a * c) * x + (a * d + b)) A := by
  rw [Set.image_image]
  congr 1
  funext x
  ring

/-- Applying the inverse affine map recovers the original set. -/
theorem affine_image_inverse (A : Set ℝ) {a : ℝ} (ha : a ≠ 0) (b : ℝ) :
    Set.image (fun x => a⁻¹ * x + -(a⁻¹ * b))
      (Set.image (fun x => a * x + b) A) = A := by
  rw [affine_image_comp]
  simp [ha]

/-- The same avoidance witness works after a nonzero affine change of variables. -/
theorem Avoidance.affine_image {A : Set ℝ} (hA : Avoidance A) {c : ℝ}
    (hc : c ≠ 0) (d : ℝ) : Avoidance (Set.image (fun x => c * x + d) A) := by
  obtain ⟨E, hE, hpos, havoid⟩ := hA
  refine ⟨E, hE, hpos, ?_⟩
  intro a b ha hsub
  exact havoid (a * c) (a * d + b) (mul_ne_zero ha hc)
    (by simpa only [affine_image_comp] using hsub)

/-- Avoidance is invariant under nonzero affine images, in both directions. -/
theorem avoidance_affine_image_iff {A : Set ℝ} {c : ℝ} (hc : c ≠ 0) (d : ℝ) :
    Avoidance (Set.image (fun x => c * x + d) A) ↔ Avoidance A := by
  constructor
  · intro h
    simpa only [affine_image_inverse A hc d] using
      h.affine_image (inv_ne_zero hc) (-(c⁻¹ * d))
  · intro h
    exact h.affine_image hc d

/-- An affine image of a bounded real set is bounded, even for zero slope. -/
theorem isBounded_affine_image {A : Set ℝ} (hA : Bornology.IsBounded A) (a b : ℝ) :
    Bornology.IsBounded (Set.image (fun x => a * x + b) A) := by
  have hcompact : IsCompact (Set.image (fun x => a * x + b) (closure A)) :=
    hA.isCompact_closure.image ((continuous_const.mul continuous_id).add continuous_const)
  exact hcompact.isBounded.subset (Set.image_mono subset_closure)

/-- An embedding by a nonzero affine map into a bounded set forces boundedness. -/
theorem isBounded_of_affine_image_subset {A E : Set ℝ} (hE : Bornology.IsBounded E)
    {a b : ℝ} (ha : a ≠ 0) (hsub : Set.image (fun x => a * x + b) A ⊆ E) :
    Bornology.IsBounded A := by
  have hbounded := isBounded_affine_image hE a⁻¹ (-(a⁻¹ * b))
  have hinv : A ⊆ Set.image (fun x => a⁻¹ * x + -(a⁻¹ * b)) E := by
    rw [← affine_image_inverse A ha b]
    exact Set.image_mono hsub
  exact hbounded.subset hinv

/-- Boundedness is invariant under nonzero affine images. -/
theorem isBounded_affine_image_iff {A : Set ℝ} {a : ℝ} (ha : a ≠ 0) (b : ℝ) :
    Bornology.IsBounded (Set.image (fun x => a * x + b) A) ↔ Bornology.IsBounded A := by
  constructor
  · intro h
    exact isBounded_of_affine_image_subset h ha Set.Subset.rfl
  · intro h
    exact isBounded_affine_image h a b

/-- No nonzero affine copy of an unbounded set fits inside a bounded set. -/
theorem not_affine_image_subset_of_unbounded {A E : Set ℝ}
    (hA : ¬ Bornology.IsBounded A) (hE : Bornology.IsBounded E) {a b : ℝ}
    (ha : a ≠ 0) : ¬ Set.image (fun x => a * x + b) A ⊆ E := by
  intro hsub
  exact hA (isBounded_of_affine_image_subset hE ha hsub)

/-- The measurable positive-volume interval `[0, 1]` witnesses avoidance of an unbounded set. -/
theorem avoidance_of_unbounded {A : Set ℝ} (hA : ¬ Bornology.IsBounded A) :
    Avoidance A := by
  refine ⟨Set.Icc (0 : ℝ) 1, measurableSet_Icc, ?_, ?_⟩
  · simp [Real.volume_Icc]
  · intro a b ha
    exact not_affine_image_subset_of_unbounded hA (Metric.isBounded_Icc 0 1) ha

/-- Every measurable set of positive real volume, finite or infinite, has a compact
positive-volume subset; the latter automatically has finite volume. -/
theorem exists_compact_positive_subset {E : Set ℝ} (hE : MeasurableSet E)
    (hpos : 0 < volume E) :
    ∃ K : Set ℝ, K ⊆ E ∧ IsCompact K ∧ 0 < volume K ∧ volume K < ⊤ := by
  obtain ⟨K, hKE, hK, hposK⟩ := hE.exists_lt_isCompact hpos
  exact ⟨K, hKE, hK, hposK, hK.measure_lt_top⟩

/-- Avoidance witnesses may be required to be compact (and hence measurable and finite-volume). -/
theorem avoidance_iff_exists_compact {A : Set ℝ} :
    Avoidance A ↔ ∃ K : Set ℝ, IsCompact K ∧ 0 < volume K ∧
      ∀ a b : ℝ, a ≠ 0 → ¬ Set.image (fun x => a * x + b) A ⊆ K := by
  constructor
  · rintro ⟨E, hE, hpos, havoid⟩
    obtain ⟨K, hKE, hK, hposK, _⟩ := exists_compact_positive_subset hE hpos
    refine ⟨K, hK, hposK, ?_⟩
    intro a b ha hsub
    exact havoid a b ha (hsub.trans hKE)
  · rintro ⟨K, hK, hpos, havoid⟩
    exact ⟨K, hK.measurableSet, hpos, havoid⟩

end Erdos120Aux
