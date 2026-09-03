import Submission.SelbergPositiveOptimum

/-! An exact dual optimality test for squared-L1-penalized sieve kernels.
The test allows arbitrary signed coefficients. -/
namespace Erdos970.SelbergSignedOptimum
open Finset
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

noncomputable def image (A : κ → ι → ℝ) (c : ι → ℝ) (t : κ) : ℝ := ∑ i, A t i * c i
noncomputable def cost (A : κ → ι → ℝ) (c : ι → ℝ) : ℝ := ∑ t, |image A c t|
noncomputable def adjoint (A : κ → ι → ℝ) (s : κ → ℝ) (i : ι) : ℝ := ∑ t, s t * A t i
noncomputable def objective (v : ι → ℝ) (A : κ → ι → ℝ) (X : ℝ) (c : ι → ℝ) : ℝ :=
  X * (∑ i, v i * c i ^ 2) + cost A c ^ 2

lemma cost_nonneg (A : κ → ι → ℝ) (c : ι → ℝ) : 0 ≤ cost A c :=
  sum_nonneg (fun _ _ => abs_nonneg _)

lemma adjoint_pairing (A : κ → ι → ℝ) (s : κ → ℝ) (c : ι → ℝ) :
    (∑ i, adjoint A s i * c i) = ∑ t, s t * image A c t := by
  simp only [adjoint, image, sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro t ht
  apply sum_congr rfl
  intro i hi
  ring

lemma cost_subgradient (A : κ → ι → ℝ) (s : κ → ℝ) (b : ι → ℝ)
    (hs : ∀ t, |s t| ≤ 1) (hb : ∀ t, s t * image A b t = |image A b t|)
    (c : ι → ℝ) :
    (∑ i, adjoint A s i * (c i - b i)) ≤ cost A c - cost A b := by
  have hc : (∑ t, s t * image A c t) ≤ cost A c := by
    apply sum_le_sum
    intro t ht
    calc
      _ ≤ |s t * image A c t| := le_abs_self _
      _ = |s t| * |image A c t| := abs_mul _ _
      _ ≤ 1 * |image A c t| := mul_le_mul_of_nonneg_right (hs t) (abs_nonneg _)
      _ = _ := one_mul _
  have hb' : (∑ t, s t * image A b t) = cost A b := sum_congr rfl (fun t _ => hb t)
  simp only [mul_sub, sum_sub_distrib]
  rw [adjoint_pairing, adjoint_pairing, hb']
  linarith

/-- A dual certificate proves global optimality among all real signed vectors
with a prescribed sum. No local-minimum or numerical-convergence assumption is used. -/
theorem minimizes_all (v : ι → ℝ) (A : κ → ι → ℝ) (X : ℝ)
    (hv : ∀ i, 0 ≤ v i) (hX : 0 ≤ X) (b : ι → ℝ) (s : κ → ℝ) (α : ℝ)
    (hs : ∀ t, |s t| ≤ 1) (hb : ∀ t, s t * image A b t = |image A b t|)
    (hstationary : ∀ i, X * v i * b i + cost A b * adjoint A s i = α)
    (c : ι → ℝ) (hsum : (∑ i, c i) = ∑ i, b i) :
    objective v A X b ≤ objective v A X c := by
  have hstat : X * (∑ i, v i * b i * (c i - b i)) +
      cost A b * (∑ i, adjoint A s i * (c i - b i)) = 0 := by
    have h := sum_congr (s₁ := univ) rfl
      (fun i _ => congrArg (fun z : ℝ => z * (c i - b i)) (hstationary i))
    have heq : (∑ i, α * (c i - b i)) = 0 := by
      rw [← mul_sum, sum_sub_distrib, hsum, sub_self, mul_zero]
    rw [heq] at h
    convert h using 1
    simp only [add_mul, sum_add_distrib, mul_sum, mul_assoc]
  have hlin : 0 ≤ X * (∑ i, v i * b i * (c i - b i)) +
      cost A b * (cost A c - cost A b) := by
    have h := mul_le_mul_of_nonneg_left (cost_subgradient A s b hs hb c) (cost_nonneg A b)
    linarith
  have hsq : (∑ i, v i * c i ^ 2) - (∑ i, v i * b i ^ 2) =
      (∑ i, v i * (c i - b i) ^ 2) + 2 * (∑ i, v i * b i * (c i - b i)) := by
    rw [← sum_sub_distrib, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    ring
  have hq : 0 ≤ X * (∑ i, v i * (c i - b i) ^ 2) :=
    mul_nonneg hX (sum_nonneg (fun i _ => mul_nonneg (hv i) (sq_nonneg _)))
  have hgap : objective v A X c - objective v A X b =
      X * (∑ i, v i * (c i - b i) ^ 2) + (cost A c - cost A b) ^ 2 +
      2 * (X * (∑ i, v i * b i * (c i - b i)) + cost A b * (cost A c - cost A b)) := by
    dsimp only [objective]
    linear_combination X * hsq
  linarith [sq_nonneg (cost A c - cost A b)]

#print axioms minimizes_all
end Erdos970.SelbergSignedOptimum
