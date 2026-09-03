import Submission.PairWeightedRootTransferExplore

/-! One admissible character translation controls every later linear
combination of a fixed finite family of pair matrices. -/
namespace Erdos66UniformMatrixSpan
open Erdos66PairWeightedCharacterEnergy Erdos66PairWeightedRootTransfer
open scoped Classical
set_option maxHeartbeats 2200000

noncomputable def matrixCombination {ι : Type*} (S : Finset ι)
    (W : ι → ℕ → ℕ → ℝ) (c : ι → ℝ) (i j : ℕ) : ℝ :=
  ∑ k∈S, c k*W k i j

lemma matrixSum_combination {ι : Type*} (h : ℕ) (S : Finset ι)
    (W : ι → ℕ → ℕ → ℝ) (c : ι → ℝ) :
    matrixSum h (matrixCombination S W c) = ∑ k∈S, c k*matrixSum h (W k) := by
  simp only [matrixSum, matrixCombination, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]

variable {p : ℕ} [Fact p.Prime]

lemma matrixRootCount_combination {ι : Type*} (h : ℕ) (a : ZMod p)
    (S : Finset ι) (W : ι → ℕ → ℕ → ℝ) (c : ι → ℝ) (t s : ZMod p) :
    matrixRootCount h a (matrixCombination S W c) t s =
      ∑ k∈S, c k*matrixRootCount h a (W k) t s := by
  simp only [matrixRootCount, matrixCombination, Finset.sum_mul, Finset.mul_sum,
    mul_assoc]
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]

lemma matrixDeviation_combination {ι : Type*} (h : ℕ) (a : ZMod p)
    (S : Finset ι) (W : ι → ℕ → ℕ → ℝ) (c : ι → ℝ) (t s : ZMod p) :
    matrixRootCount h a (matrixCombination S W c) t s-
      matrixSum h (matrixCombination S W c) =
      ∑ k∈S, c k*(matrixRootCount h a (W k) t s-matrixSum h (W k)) := by
  rw [matrixRootCount_combination, matrixSum_combination]
  simp only [mul_sub, Finset.sum_sub_distrib]

/-- The coefficient vector is chosen AFTER the translate. The subspace data
must still be chosen before it; no bound for all matrices is asserted. -/
theorem exists_uniform_matrix_span {ι : Type*} (hp : p≠2) (h : ℕ) (hh : 4*h<p)
    (S : Finset ι) (W : ι → ℕ → ℕ → ℝ) :
    ∃ a : ZMod p,
      (∀ i<h, a+(i:ZMod p)≠0) ∧ (∀ q<2*h, 2*a+(q:ZMod p)≠0) ∧
      ∀ c : ι → ℝ, ∀ t s : ZMod p,
        (matrixRootCount h a (matrixCombination S W c) t s-
          matrixSum h (matrixCombination S W c))^2 ≤
          16*(h:ℝ)*(∑ k∈S, matrixMass h (W k))*(∑ k∈S, (c k)^2) := by
  obtain ⟨a,ha,hop,he,he'⟩ := exists_admissible_matrix_budget hp h hh S W
    (fun _ ↦ (1:ℝ)) (by intros; norm_num)
  simp only [one_mul] at he
  refine ⟨a,ha,hop,fun c t s ↦ ?_⟩
  rw [matrixDeviation_combination]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S c
    (fun k ↦ matrixRootCount h a (W k) t s-matrixSum h (W k))
  have hs : (∑ k∈S, (matrixRootCount h a (W k) t s-matrixSum h (W k))^2) ≤
      16*(h:ℝ)*(∑ k∈S, matrixMass h (W k)) := by
    have hh' := Finset.sum_le_sum (s := S) (fun k _ ↦
      matrixRootCount_error_sq hp h a (W k) ha hop t s)
    rw [←Finset.mul_sum] at hh'
    have he'' := mul_le_mul_of_nonneg_left he (show (0:ℝ)≤2*h by positivity)
    nlinarith only [hh',he'']
  have hm := mul_le_mul_of_nonneg_left hs (Finset.sum_nonneg (s := S) (fun k _ ↦ sq_nonneg (c k)))
  exact hcs.trans (by nlinarith only [hm])

/-- In particular a finite list of unit-Frobenius-mass matrices costs its
size, uniformly for every subsequent coefficient vector and fine target. -/
theorem exists_normalized_matrix_span {ι : Type*} (hp : p≠2) (h : ℕ) (hh : 4*h<p)
    (S : Finset ι) (W : ι → ℕ → ℕ → ℝ)
    (hW : ∀ k∈S, matrixMass h (W k)≤1) :
    ∃ a : ZMod p,
      (∀ i<h, a+(i:ZMod p)≠0) ∧ (∀ q<2*h, 2*a+(q:ZMod p)≠0) ∧
      ∀ c : ι → ℝ, ∀ t s : ZMod p,
        (matrixRootCount h a (matrixCombination S W c) t s-
          matrixSum h (matrixCombination S W c))^2 ≤
          16*(h:ℝ)*S.card*(∑ k∈S, (c k)^2) := by
  obtain ⟨a,ha,hop,he⟩ := exists_uniform_matrix_span hp h hh S W
  refine ⟨a,ha,hop,fun c t s ↦ (he c t s).trans ?_⟩
  have hs : (∑ k∈S, matrixMass h (W k))≤(S.card:ℝ) := by
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using Finset.sum_le_sum hW
  have hm := mul_le_mul_of_nonneg_right hs (Finset.sum_nonneg (s := S) (fun k _ ↦ sq_nonneg (c k)))
  have hm' := mul_le_mul_of_nonneg_left hm (show (0:ℝ)≤16*h by positivity)
  nlinarith only [hm']

end Erdos66UniformMatrixSpan
