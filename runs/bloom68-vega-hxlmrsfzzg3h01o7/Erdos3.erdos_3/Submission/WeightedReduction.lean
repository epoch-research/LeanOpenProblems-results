import FormalConjecturesUtil

/-!
# Finite weighted formulations of the arithmetic-progression conjecture

These are reductions only. No bound for general AP-free finite sets is assumed
without appearing explicitly as a hypothesis.
-/

namespace Erdos3Weighted

open Filter

/-- The reciprocal weight of a finite set. The contribution at zero is zero. -/
noncomputable def weight (F : Finset ℕ) : ℝ := ∑ n ∈ F, 1 / (n : ℝ)

/-- Exclusion of an AP of a specified finite length. -/
def Avoids (k : ℕ) (A : Set ℕ) : Prop :=
  ∀ S ⊆ A, ¬ S.IsAPOfLength (k : ℕ∞)

/-- The finite, uniform weighted estimate for a fixed length. -/
def UniformBound (k : ℕ) : Prop :=
  ∃ C : ℝ, ∀ F : Finset ℕ, Avoids k (F : Set ℕ) → weight F ≤ C

lemma avoids_subset {k : ℕ} {A B : Set ℕ} (hB : Avoids k B) (hAB : A ⊆ B) :
    Avoids k A := fun S hSA hS ↦ hB S (hSA.trans hAB) hS

/-- For a fixed set, summability is equivalent to bounded finite reciprocal sums. -/
theorem summable_iff_bounded_finite_weight (A : Set ℕ) :
    Summable (fun a : A ↦ 1 / (a : ℝ)) ↔
      ∃ C : ℝ, ∀ F : Finset ℕ, (F : Set ℕ) ⊆ A → weight F ≤ C := by
  classical
  constructor
  · intro h
    have hs : Summable (A.indicator (fun n : ℕ ↦ 1 / (n : ℝ))) :=
      summable_subtype_iff_indicator.mp h
    refine ⟨∑' n : ℕ, A.indicator (fun n : ℕ ↦ 1 / (n : ℝ)) n, ?_⟩
    intro F hFA
    calc
      weight F = ∑ n ∈ F, A.indicator (fun n : ℕ ↦ 1 / (n : ℝ)) n := by
        unfold weight
        apply Finset.sum_congr rfl
        intro n hn
        exact (Set.indicator_of_mem (hFA hn) (fun n : ℕ ↦ 1 / (n : ℝ))).symm
      _ ≤ ∑' n : ℕ, A.indicator (fun n : ℕ ↦ 1 / (n : ℝ)) n :=
        hs.sum_le_tsum F (fun n _ ↦ Set.indicator_nonneg (fun a _ ↦ by positivity) n)
  · rintro ⟨C, hC⟩
    apply (summable_subtype_iff_indicator (f := fun n : ℕ ↦ 1 / (n : ℝ)) (s := A)).mpr
    apply summable_of_sum_le (c := C)
      (fun n ↦ Set.indicator_nonneg (fun a _ ↦ by positivity) n)
    intro F
    have heq : (∑ n ∈ F, A.indicator (fun n : ℕ ↦ 1 / (n : ℝ)) n) =
        weight (F.filter (· ∈ A)) := by
      simp only [weight, Set.indicator, Finset.sum_filter]
    rw [heq]
    exact hC _ (by intro n hn; exact (Finset.mem_filter.mp hn).2)

/-- A uniform finite estimate implies reciprocal summability for every set
excluding that length. -/
theorem summable_of_uniformBound {k : ℕ} (h : UniformBound k)
    {A : Set ℕ} (hA : Avoids k A) :
    Summable (fun a : A ↦ 1 / (a : ℝ)) := by
  obtain ⟨C, hC⟩ := h
  apply (summable_iff_bounded_finite_weight A).mpr
  exact ⟨C, fun F hFA ↦ hC F (avoids_subset hA hFA)⟩

/-- The finite weighted estimates, if supplied for all lengths at least three,
prove exactly the conjecture's conclusion. -/
theorem erdos3_of_uniformBounds (h : ∀ k : ℕ, 3 ≤ k → UniformBound k) :
    ∀ A : Set ℕ, (¬ Summable (fun a : A ↦ 1 / (a : ℝ))) →
      ∃ᶠ k : ℕ in atTop, ∃ S ⊆ A, S.IsAPOfLength (k : ℕ∞) := by
  intro A hA
  apply Filter.frequently_atTop.mpr
  intro b
  let k := max b 3
  have hk : 3 ≤ k := le_max_right b 3
  have hb : b ≤ k := le_max_left b 3
  by_contra! hnone
  apply hA
  apply summable_of_uniformBound (h k hk)
  intro S hSA hS
  exact hnone k hb S hSA hS

end Erdos3Weighted
