import Submission.PairWeightedCharacterEnergyExplore
import Submission.AffineRootAggregateExplore

/-! A pair-weight matrix can encode aggregate coarse interactions. The same
energy controls all fine targets, but the translation is selected after the
matrix data. These are parameter-weighted root counts, not yet a global set. -/
namespace Erdos66PairWeightedRootTransfer
open Erdos66PairWeightedCharacterEnergy Erdos66IndexedCharacterEnergy
  Erdos66FiniteField
open scoped Classical
set_option maxHeartbeats 2200000

noncomputable def matrixSum (h : ℕ) (W : ℕ → ℕ → ℝ) : ℝ :=
  ∑ i∈Finset.range h, ∑ j∈Finset.range h, W i j

variable {p : ℕ} [Fact p.Prime]

noncomputable def matrixRootCount (h : ℕ) (a : ZMod p) (W : ℕ → ℕ → ℝ)
    (t s : ZMod p) : ℝ :=
  ∑ i∈Finset.range h, ∑ j∈Finset.range h,
    W i j*(Fintype.card {x : ZMod p // x^2/(a+i)+(t-x)^2/(a+j)=s}:ℝ)

lemma matrixRootCount_identity (hp : p≠2) (h : ℕ) (a : ZMod p)
    (W : ℕ → ℕ → ℝ) (ha : ∀ i<h, a+(i:ZMod p)≠0)
    (hop : ∀ q<2*h, 2*a+(q:ZMod p)≠0) (t s : ZMod p) :
    matrixRootCount h a W t s = matrixSum h W+
      ∑ q∈Finset.range (2*h), matrixFiber h W a q*
        (quadraticChar (ZMod p) ((2*a+(q:ZMod p))*s-t^2):ℝ) := by
  have hroot (i j : ℕ) (hi : i∈Finset.range h) (hj : j∈Finset.range h) :
      (Fintype.card {x : ZMod p // x^2/(a+i)+(t-x)^2/(a+j)=s}:ℝ) =
        1+(quadraticChar (ZMod p) (a+i):ℝ)*(quadraticChar (ZMod p) (a+j):ℝ)*
          (quadraticChar (ZMod p) ((2*a+((i+j:ℕ):ZMod p))*s-t^2):ℝ) := by
    have hij : i+j<2*h := by
      have := Finset.mem_range.mp hi; have := Finset.mem_range.mp hj; omega
    have he : (a+(i:ZMod p))+(a+(j:ZMod p))=2*a+((i+j:ℕ):ZMod p) := by
      push_cast; ring
    have hh := parabola_sum_count (F := ZMod p)
      (by simpa only [ZMod.ringChar_zmod_n] using hp)
      (a+i) (a+j) t s (ha i (Finset.mem_range.mp hi))
      (ha j (Finset.mem_range.mp hj)) (by rw [he]; exact hop (i+j) hij)
    rw [he] at hh
    exact_mod_cast hh
  have he : matrixRootCount h a W t s = matrixSum h W+
      ∑ i∈Finset.range h, ∑ j∈Finset.range h,
        W i j*(quadraticChar (ZMod p) (a+i):ℝ)*(quadraticChar (ZMod p) (a+j):ℝ)*
          (quadraticChar (ZMod p) ((2*a+((i+j:ℕ):ZMod p))*s-t^2):ℝ) := by
    unfold matrixRootCount matrixSum
    simp only [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hroot i j hi hj]
    ring
  rw [he]
  congr 1
  rw [←sum_pairFiber h (fun i j ↦
    W i j*(quadraticChar (ZMod p) (a+i):ℝ)*(quadraticChar (ZMod p) (a+j):ℝ)*
      (quadraticChar (ZMod p) ((2*a+((i+j:ℕ):ZMod p))*s-t^2):ℝ))]
  apply Finset.sum_congr rfl
  intro q hq
  rw [matrixFiber, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [(mem_pairFiber.mp hij).2.2]

/-- The number of fine field-plane targets does not occur in the bound. -/
theorem matrixRootCount_error_sq (hp : p≠2) (h : ℕ) (a : ZMod p)
    (W : ℕ → ℕ → ℝ) (ha : ∀ i<h, a+(i:ZMod p)≠0)
    (hop : ∀ q<2*h, 2*a+(q:ZMod p)≠0) (t s : ZMod p) :
    (matrixRootCount h a W t s-matrixSum h W)^2 ≤
      2*(h:ℝ)*matrixEnergy h W a := by
  rw [matrixRootCount_identity hp h a W ha hop, add_sub_cancel_left]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (2*h))
    (matrixFiber h W a)
    (fun q ↦ (quadraticChar (ZMod p) ((2*a+(q:ZMod p))*s-t^2):ℝ))
  have hchar (q : ℕ) :
      ((quadraticChar (ZMod p) ((2*a+(q:ZMod p))*s-t^2):ℝ))^2 ≤ 1 := by
    have hh : |(quadraticChar (ZMod p) ((2*a+(q:ZMod p))*s-t^2):ℝ)|≤1 := by
      exact_mod_cast quadraticChar_abs_le_one (F := ZMod p) ((2*a+(q:ZMod p))*s-t^(2:ℕ))
    have hh2 := mul_self_le_mul_self (abs_nonneg _) hh
    rw [←pow_two, sq_abs] at hh2
    simpa using hh2
  have hsum : (∑ q∈Finset.range (2*h),
      ((quadraticChar (ZMod p) ((2*a+(q:ZMod p))*s-t^2):ℝ))^2) ≤ 2*(h:ℝ) := by
    calc
      _ ≤ ∑ _q∈Finset.range (2*h), (1:ℝ) := Finset.sum_le_sum (fun q _ ↦ hchar q)
      _ = _ := by simp
  have hmul := mul_le_mul_of_nonneg_left hsum (matrixEnergy_nonneg h W a)
  change _ ≤ matrixEnergy h W a*_ at hcs
  exact hcs.trans (by nlinarith only [hmul])

/-- Weighted simultaneous selection for an arbitrary finite list of coarse
pair matrices. All fine targets are covered by the same selected translate. -/
theorem exists_matrix_root_budget {ι : Type*} (hp : p≠2) (h : ℕ) (hh : 4*h<p)
    (S : Finset ι) (W : ι → ℕ → ℕ → ℝ) (wgt : ι → ℝ)
    (hwgt : ∀ i∈S, 0≤wgt i) :
    ∃ a : ZMod p,
      (∀ i<h, a+(i:ZMod p)≠0) ∧ (∀ q<2*h, 2*a+(q:ZMod p)≠0) ∧
      ∀ k∈S, ∀ t s : ZMod p,
        wgt k*(matrixRootCount h a (W k) t s-matrixSum h (W k))^2 ≤
          16*(h:ℝ)*(∑ j∈S, wgt j*matrixMass h (W j)) := by
  obtain ⟨a,ha,hop,hbudget,he⟩ := exists_admissible_matrix_budget hp h hh S W wgt hwgt
  refine ⟨a,ha,hop,fun k hk t s ↦ ?_⟩
  have h₁ := mul_le_mul_of_nonneg_left
    (matrixRootCount_error_sq hp h a (W k) ha hop t s) (hwgt k hk)
  have h₂ := mul_le_mul_of_nonneg_left (he k hk) (show (0:ℝ)≤2*h by positivity)
  nlinarith only [h₁,h₂]

/-- Single-matrix form: error squared is at most 16 h times the Frobenius
mass, without requiring a separable weight or any sign restriction. -/
theorem exists_matrix_root_transfer (hp : p≠2) (h : ℕ) (hh : 4*h<p)
    (W : ℕ → ℕ → ℝ) :
    ∃ a : ZMod p,
      (∀ i<h, a+(i:ZMod p)≠0) ∧ (∀ q<2*h, 2*a+(q:ZMod p)≠0) ∧
      ∀ t s : ZMod p,
        (matrixRootCount h a W t s-matrixSum h W)^2 ≤ 16*(h:ℝ)*matrixMass h W := by
  obtain ⟨a,ha,hop,he⟩ := exists_matrix_root_budget hp h hh
    ({()} : Finset Unit) (fun _ ↦ W) (fun _ ↦ (1:ℝ)) (by intros; norm_num)
  refine ⟨a,ha,hop,fun t s ↦ ?_⟩
  simpa using he () (by simp) t s

end Erdos66PairWeightedRootTransfer
