import Submission.ClippedSumPerturbation

/-! Bounded clipped factors of finitely many sampled unit phases. Their
Lipschitz cost depends on the number of tests, not the samples per test. -/
namespace Erdos3SampledClippedFactor
open Finset Erdos3ClippedWeakRegularity Erdos3ClippedSumPerturbation
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 3000000

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def sampledCoordinate (c : I → J → ℂ) (i : I) (v : I × J → ℂ) : ℝ :=
  𝔼 j : J, (c i j*conj (v (i,j))).re

lemma sampledCoordinate_lipschitz [Nonempty J] (c : I → J → ℂ)
    (hc : ∀ i j, ‖c i j‖ ≤ 1) (i : I) : LipschitzWith 1 (sampledCoordinate c i) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simp only [NNReal.coe_one,one_mul,dist_eq_norm,sampledCoordinate,
    ← expect_sub_distrib]
  apply (Finset.abs_expect_le _ _).trans
  apply expect_le univ_nonempty
  intro j _
  calc
    _ = |(c i j*conj (v (i,j)-w (i,j))).re| := by
      rw [map_sub,mul_sub,Complex.sub_re]
    _ ≤ ‖c i j*conj (v (i,j)-w (i,j))‖ := Complex.abs_re_le_norm _
    _ ≤ ‖v (i,j)-w (i,j)‖ := by
      rw [norm_mul,Complex.norm_conj]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hc i j) (norm_nonneg _)
    _ ≤ ‖v-w‖ := norm_le_pi_norm (v-w) (i,j)

noncomputable def clippedFactor (l : List I) (ρ : ℝ) (c : I → J → ℂ) :
    (I × J → ℂ) → ℝ := clippedSum ρ (l.map (sampledCoordinate c))

lemma clippedFactor_bounds (l : List I) (ρ : ℝ) (c : I → J → ℂ) (v : I × J → ℂ) :
    0 ≤ clippedFactor l ρ c v ∧ clippedFactor l ρ c v ≤ 1 := by
  cases l with
  | nil => simp [clippedFactor,clippedSum]
  | cons i l => exact clip01_bounds _

lemma clippedFactor_lipschitz [Nonempty J] (l : List I) (ρ : ℝ) (c : I → J → ℂ)
    (hc : ∀ i j, ‖c i j‖ ≤ 1) :
    LipschitzWith (⟨|ρ|,abs_nonneg ρ⟩*(l.length : NNReal)) (clippedFactor l ρ c) := by
  simpa only [mul_one] using clippedSum_map_lipschitz l ρ (sampledCoordinate c) 1
    (fun i _ ↦ sampledCoordinate_lipschitz c hc i)

lemma clippedSum_comp {X Y : Type*} (l : List (Y → ℝ)) (ρ : ℝ) (u : X → Y) (x : X) :
    clippedSum ρ (l.map (fun ψ ↦ ψ ∘ u)) x = clippedSum ρ l (u x) := by
  induction l with
  | nil => rfl
  | cons ψ l ih => simp only [List.map_cons,clippedSum,Function.comp_apply,ih]

lemma clippedFactor_evaluate {X : Type*} (l : List I) (ρ : ℝ) (c : I → J → ℂ)
    (Q : I × J → X → ℂ) (x : X) :
    clippedFactor l ρ c (fun p ↦ Q p x) =
      clippedSum ρ (l.map (fun i t ↦ 𝔼 j : J, (c i j*conj (Q (i,j) t)).re)) x := by
  have h := clippedSum_comp (l.map (sampledCoordinate c)) ρ (fun t p ↦ Q p t) x
  simpa only [List.map_map,Function.comp_def,clippedFactor,sampledCoordinate] using h.symm

#print axioms clippedFactor_lipschitz
#print axioms clippedFactor_evaluate
end Erdos3SampledClippedFactor
