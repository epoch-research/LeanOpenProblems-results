import Submission.OriginRepairExplore

/-!
# An obstruction to exact transfer of uniformly represented finite sets

A finite set with at least two representations at every target cannot be embedded
injectively in the reals while preserving all its two-term additive relations.
This does not rule out approximate or multiscale transfers, and does not disprove
Erdős Problem 66.
-/

namespace Erdos66EmbeddingObstruction
open Erdos66OriginRepair

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Every injective relation-preserving map to the reals forces a uniquely represented sum. -/
lemma single_rep_of_freiman_map (A : Finset G) (hA : A.Nonempty) (e : G → ℝ)
    (hinj : Set.InjOn e (A : Set G))
    (hadd : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
      a + b = c + d → e a + e b = e c + e d) :
    ∃ a ∈ A, pairCount A A (a + a) = 1 := by
  obtain ⟨a, ha, hmax⟩ := A.exists_max_image e hA
  refine ⟨a, ha, ?_⟩
  unfold pairCount
  apply Finset.card_eq_one.mpr
  refine ⟨a, ?_⟩
  ext b
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hb, hc⟩
    have he := hadd b hb (a + a - b) hc a ha a ha (by abel)
    have hbmax := hmax b hb
    have hcmax := hmax (a + a - b) hc
    exact hinj hb ha (by linarith)
  · rintro rfl
    exact ⟨ha, by simpa only [add_sub_cancel_right] using ha⟩

lemma no_freiman_embedding_of_two_reps (A : Finset G)
    (hrep : ∀ z : G, 2 ≤ pairCount A A z) (e : G → ℝ)
    (hinj : Set.InjOn e (A : Set G)) :
    ¬ (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
      a + b = c + d → e a + e b = e c + e d) := by
  intro hadd
  have hA : A.Nonempty := by
    have h := hrep 0
    unfold pairCount at h
    have hh : 0 < (A.filter (fun a ↦ (0 : G) - a ∈ A)).card := by omega
    exact (Finset.card_pos.mp hh).mono (Finset.filter_subset _ _)
  obtain ⟨a, ha, hsingle⟩ := single_rep_of_freiman_map A hA e hinj hadd
  have h := hrep (a + a)
  omega

/-- The quantitative finite-field estimate already puts every count above one when `q ≥ 16`. -/
lemma flat_error_forces_two_reps (A : Finset G) (q : ℕ) (hq : 16 ≤ q)
    (E : ℤ) (hE0 : 0 ≤ E) (hE : E ^ 2 ≤ 3 * (q : ℤ) ^ 3)
    (hflat : ∀ z : G, |(pairCount A A z : ℤ) - (q : ℤ) ^ 2| ≤ E + 2 * q + 6) :
    ∀ z : G, 2 ≤ pairCount A A z := by
  have hq' : (16 : ℤ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℤ) ≤ q := Nat.cast_nonneg _
  have hpow : 12 * (q : ℤ) ^ 3 ≤ (q : ℤ) ^ 4 := by
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ q - 12 by omega) (pow_nonneg hq0 3)]
  have hhalf : 2 * E ≤ (q : ℤ) ^ 2 := by
    apply (sq_le_sq₀ (by positivity) (sq_nonneg _)).mp
    nlinarith
  intro z
  have hlow := (abs_le.mp (hflat z)).1
  have hr : (2 : ℤ) ≤ pairCount A A z := by nlinarith
  exact_mod_cast hr

lemma no_freiman_embedding_of_flat_error (A : Finset G) (q : ℕ) (hq : 16 ≤ q)
    (E : ℤ) (hE0 : 0 ≤ E) (hE : E ^ 2 ≤ 3 * (q : ℤ) ^ 3)
    (hflat : ∀ z : G, |(pairCount A A z : ℤ) - (q : ℤ) ^ 2| ≤ E + 2 * q + 6)
    (e : G → ℝ) (hinj : Set.InjOn e (A : Set G)) :
    ¬ (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
      a + b = c + d → e a + e b = e c + e d) :=
  no_freiman_embedding_of_two_reps A (flat_error_forces_two_reps A q hq E hE0 hE hflat) e hinj

end Erdos66EmbeddingObstruction
