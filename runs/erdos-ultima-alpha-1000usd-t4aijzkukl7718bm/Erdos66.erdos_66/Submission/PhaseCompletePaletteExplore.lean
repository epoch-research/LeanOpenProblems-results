import Submission.TranslatedPrefixPaletteExplore
import Submission.BoundedWeightPaletteExplore

/-! Translation-complete logarithmic palettes. Phase closure retains cardinality
coverage and joint prefix bounds, but deliberately does not claim nesting. -/
namespace Erdos66PhaseCompletePalette
open Erdos66TranslatedPrefixPalette Erdos66PrefixBalancedPalette
  Erdos66OuterMixedPrefix Erdos66OuterCarryProfile Erdos66SaturatingCyclicFamily
  Erdos66BoundedWeightPalette
open scoped Classical
set_option maxHeartbeats 2600000

variable (M : ℕ) [NeZero M]

noncomputable def phaseClosure (P : Finset (Finset (ZMod M))) : Finset (Finset (ZMod M)) :=
  Finset.univ.biUnion (fun t : ZMod M ↦ P.image (fun C ↦ shift M C t))

lemma mem_phaseClosure (P : Finset (Finset (ZMod M))) (B : Finset (ZMod M)) :
    B ∈ phaseClosure M P ↔ ∃ C ∈ P, ∃ t : ZMod M, shift M C t = B := by
  simp only [phaseClosure, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
  aesop

lemma subset_phaseClosure (P : Finset (Finset (ZMod M))) : P ⊆ phaseClosure M P := by
  intro C hC
  exact (mem_phaseClosure M P C).mpr ⟨C, hC, 0, shift_zero M C⟩

lemma phaseClosure_closed (P : Finset (Finset (ZMod M)))
    (B : Finset (ZMod M)) (hB : B ∈ phaseClosure M P) (t : ZMod M) :
    shift M B t ∈ phaseClosure M P := by
  obtain ⟨C, hC, s, rfl⟩ := (mem_phaseClosure M P B).mp hB
  exact (mem_phaseClosure M P _).mpr ⟨C, hC, t+s, (shift_shift M C s t).symm⟩

lemma phaseClosure_card (P : Finset (Finset (ZMod M))) :
    (phaseClosure M P).card ≤ M * P.card := by
  calc
    _ ≤ ∑ _t : ZMod M, (P.image (fun C ↦ shift M C _t)).card := Finset.card_biUnion_le
    _ ≤ ∑ _t : ZMod M, P.card := Finset.sum_le_sum (fun _ _ ↦ Finset.card_image_le)
    _ = _ := by simp

lemma phaseClosure_prefix_error (P : Finset (Finset (ZMod M))) (η : ℝ) (hη : 0 ≤ η)
    (hprefix : ∀ C ∈ P, ∀ D ∈ P, ∀ z u, u ≤ M →
      |(prefixCount M C D z u : ℝ) - (u : ℝ)/M*actualMean M C D| ≤
        η * actualMean M C D) :
    ∀ B ∈ phaseClosure M P, ∀ E ∈ phaseClosure M P, ∀ z u, u ≤ M →
      |(prefixCount M B E z u : ℝ) - (u : ℝ)/M*actualMean M B E| ≤
        3*η*actualMean M B E := by
  intro B hB E hE z u hu
  obtain ⟨C, hCP, s, rfl⟩ := (mem_phaseClosure M P B).mp hB
  obtain ⟨D, hDP, t, rfl⟩ := (mem_phaseClosure M P E).mp hE
  rw [shift_mean]
  simpa only [mul_assoc] using shifted_prefix_error M C D s t z u hu
    (actualMean M C D) (η*actualMean M C D)
    (mul_nonneg hη (actualMean_nonneg M C D)) (hprefix C hCP D hDP)

/-- One finite palette supports all independent phases, with no density or
logarithmic-coefficient inflation. Nesting is not asserted for this closure. -/
theorem exists_phase_complete_palette (c τ η ε : ℝ)
    (hc : 0 < c) (hτ : 0 < τ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (N₀ : ℕ) :
    ∃ M : ℕ, N₀ < M ∧ Odd M ∧ ∃ hM : NeZero M,
      ∃ (B₀ : Finset (ZMod M)) (Q : Finset (Finset (ZMod M))),
        0 < B₀.card ∧ B₀ ∈ Q ∧
        |actualMean M B₀ B₀ / Real.log M - c| < τ ∧
        (∀ B ∈ Q, B₀.card ≤ B.card) ∧
        (∀ B ∈ Q, ∀ t : ZMod M, shift M B t ∈ Q) ∧
        (∀ B ∈ Q, ∀ C ∈ Q, ∀ z,
          |(cyclicCount M B C z : ℝ) - actualMean M B C| ≤ η*actualMean M B C) ∧
        (∀ B ∈ Q, ∀ C ∈ Q, ∀ z u, u ≤ M →
          |(prefixCount M B C z u : ℝ) - (u : ℝ)/M*actualMean M B C| ≤ η*actualMean M B C) ∧
        (Finset.univ : Finset (ZMod M)) ∈ Q ∧ Q.card ≤ M*(M+1) ∧
        ∀ x : ℝ, (B₀.card : ℝ) ≤ x → x ≤ M →
          ∃ B ∈ Q, x ≤ (B.card : ℝ) ∧ (B.card : ℝ) ≤ (1+ε)*x := by
  obtain ⟨M, hMN, hodd, hM, B₀, P, hBpos, hBmem, htune, hsub, hnest,
    hflat, hprefix, hfull, hcard, hcover⟩ :=
    exists_prefix_balanced_complete_palette c τ (η/3) ε hc hτ (by positivity)
      (by linarith) hε hε1 N₀
  letI := hM
  refine ⟨M, hMN, hodd, hM, B₀, phaseClosure M P, hBpos,
    subset_phaseClosure M P hBmem, htune, ?_, phaseClosure_closed M P, ?_, ?_,
    subset_phaseClosure M P hfull,
    (phaseClosure_card M P).trans (Nat.mul_le_mul_left M hcard), ?_⟩
  · intro B hB
    obtain ⟨C, hCP, t, rfl⟩ := (mem_phaseClosure M P B).mp hB
    rw [shift_card]
    exact Finset.card_le_card (hsub C hCP)
  · intro B hB C hC z
    obtain ⟨D, hDP, s, rfl⟩ := (mem_phaseClosure M P B).mp hB
    obtain ⟨E, hEP, t, rfl⟩ := (mem_phaseClosure M P C).mp hC
    rw [shift_cyclicCount, shift_mean]
    exact (hflat D hDP E hEP _).trans
      (mul_le_mul_of_nonneg_right (by linarith : η/3 ≤ η) (actualMean_nonneg M D E))
  · intro B hB C hC z u hu
    have hh := phaseClosure_prefix_error M P (η/3) (by positivity) hprefix B hB C hC z u hu
    convert hh using 1 <;> ring
  · intro x hx hxM
    obtain ⟨B, hBP, hlow, hhigh⟩ := hcover x hx hxM
    exact ⟨B, subset_phaseClosure M P hBP, hlow, hhigh⟩

/-- The bounded-weight version is convenient for integer interval assemblies. -/
theorem exists_fitting_phase_palette (c τ η ε W : ℝ)
    (hc : 0 < c) (hτ : 0 < τ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hW : 0 ≤ W) (N₀ : ℕ) :
    ∃ M : ℕ, N₀ < M ∧ 1 < M ∧ ∃ hM : NeZero M,
      ∃ (B : Finset (ZMod M)) (Q : Finset (Finset (ZMod M))),
        0 < B.card ∧ B ∈ Q ∧ W*(B.card : ℝ) ≤ M ∧
        |actualMean M B B / Real.log M - c| < τ ∧
        (∀ C ∈ Q, ∀ t : ZMod M, shift M C t ∈ Q) ∧
        (∀ C ∈ Q, ∀ D ∈ Q, ∀ z u, u ≤ M →
          |(prefixCount M C D z u : ℝ) - (u : ℝ)/M*actualMean M C D| ≤ η*actualMean M C D) ∧
        ∀ x : ℝ, (B.card : ℝ) ≤ x → x ≤ M →
          ∃ C ∈ Q, x ≤ (C.card : ℝ) ∧ (C.card : ℝ) ≤ (1+ε)*x := by
  obtain ⟨M, hMN, hM1, hM, B, P, hBpos, hBmem, hfit, htune, hprefix, hcover⟩ :=
    exists_fitting_prefix_palette c τ (η/3) ε W hc hτ (by positivity)
      (by linarith) hε hε1 hW N₀
  letI := hM
  refine ⟨M, hMN, hM1, hM, B, phaseClosure M P, hBpos,
    subset_phaseClosure M P hBmem, hfit, htune, phaseClosure_closed M P, ?_, ?_⟩
  · intro C hC D hD z u hu
    have hh := phaseClosure_prefix_error M P (η/3) (by positivity) hprefix C hC D hD z u hu
    convert hh using 1 <;> ring
  · intro x hx hxM
    obtain ⟨C, hCP, hlow, hhigh⟩ := hcover x hx hxM
    exact ⟨C, subset_phaseClosure M P hCP, hlow, hhigh⟩

end Erdos66PhaseCompletePalette
