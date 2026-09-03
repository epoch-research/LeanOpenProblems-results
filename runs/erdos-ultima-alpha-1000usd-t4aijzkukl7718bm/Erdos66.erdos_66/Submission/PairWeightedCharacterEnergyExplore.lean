import Submission.RealWeightedCharacterEnergyExplore

/-! Character energy for arbitrary pair-weight matrices. In particular the
weights need not factor into two one-variable weights. -/
namespace Erdos66PairWeightedCharacterEnergy
open Erdos66RealWeightedCharacterEnergy Erdos66IndexedCharacterEnergy
  Erdos66TranslatedCharacterEnergy Erdos66CharacterTranslateSelection
open scoped Classical
set_option maxHeartbeats 1800000

noncomputable def matrixMass (h : ℕ) (W : ℕ → ℕ → ℝ) : ℝ :=
  ∑ i∈Finset.range h, ∑ j∈Finset.range h, (W i j)^2

variable {p : ℕ} [Fact p.Prime]

noncomputable def matrixFiber (h : ℕ) (W : ℕ → ℕ → ℝ)
    (a : ZMod p) (q : ℕ) : ℝ :=
  ∑ ij∈pairFiber h q, W ij.1 ij.2 *
    (quadraticChar (ZMod p) (a+ij.1):ℝ)*(quadraticChar (ZMod p) (a+ij.2):ℝ)

noncomputable def matrixEnergy (h : ℕ) (W : ℕ → ℕ → ℝ) (a : ZMod p) : ℝ :=
  ∑ q∈Finset.range (2*h), (matrixFiber h W a q)^2

lemma matrixEnergy_nonneg (h : ℕ) (W : ℕ → ℕ → ℝ) (a : ZMod p) :
    0 ≤ matrixEnergy h W a := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)

lemma matrixFiber_as_shiftSum (hp : p≠2) (h : ℕ) (W : ℕ → ℕ → ℝ)
    (a : ZMod p) (q : ℕ) :
    matrixFiber h W a q = realShiftSum (pairFiber h q)
      (fun ij ↦ ((ij.1:ZMod p)-(q:ZMod p)/2)^2)
      (fun ij ↦ W ij.1 ij.2) ((a+(q:ZMod p)/2)^2) := by
  unfold matrixFiber realShiftSum
  apply Finset.sum_congr rfl
  intro ij hij
  obtain ⟨hi,hj,hsum⟩ := mem_pairFiber.mp hij
  have he : (ij.2:ZMod p)=(q:ZMod p)-ij.1 := by
    rw [←hsum]; push_cast; ring
  have hc := character_product_square
    (by simpa only [ZMod.ringChar_zmod_n] using hp) a (q:ZMod p) (ij.1:ZMod p)
  rw [←he] at hc
  have hc' : (quadraticChar (ZMod p) (a+ij.1):ℝ)*
      (quadraticChar (ZMod p) (a+ij.2):ℝ) =
      (quadraticChar (ZMod p) ((a+(q:ZMod p)/2)^2-
        ((ij.1:ZMod p)-(q:ZMod p)/2)^2):ℝ) := by exact_mod_cast hc
  rw [mul_assoc, hc']

/-- The energy cost of one label-sum fiber is its squared pair-weight mass. -/
theorem average_matrix_fiber_energy (hp : p≠2) (h q : ℕ) (hh : h≤p)
    (W : ℕ → ℕ → ℝ) :
    (∑ a : ZMod p, (matrixFiber h W a q)^2) ≤
      4*(p:ℝ)*(∑ ij∈pairFiber h q, (W ij.1 ij.2)^2) := by
  simp_rw [matrixFiber_as_shiftSum hp]
  have he := Equiv.sum_comp (Equiv.addRight ((q:ZMod p)/2))
    (fun a : ZMod p ↦ (realShiftSum (pairFiber h q)
      (fun ij ↦ ((ij.1:ZMod p)-(q:ZMod p)/2)^2)
      (fun ij ↦ W ij.1 ij.2) (a^2))^2)
  simp only [Equiv.coe_addRight] at he
  rw [he]
  have h₁ := real_sum_sq_comp_square_le_two (realShiftSum (pairFiber h q)
    (fun ij ↦ ((ij.1:ZMod p)-(q:ZMod p)/2)^2) (fun ij ↦ W ij.1 ij.2))
  have h₂ := realShiftSum_energy_le
    (by simpa only [ZMod.ringChar_zmod_n] using hp) (pairFiber h q)
    (fun ij ↦ ((ij.1:ZMod p)-(q:ZMod p)/2)^2) (fun ij ↦ W ij.1 ij.2)
    (fun ij hij ↦ indexed_square_fiber_le_two hp h q hh ij hij)
  rw [ZMod.card] at h₂
  nlinarith

lemma sum_pairFiber (h : ℕ) (V : ℕ → ℕ → ℝ) :
    (∑ q∈Finset.range (2*h), ∑ ij∈pairFiber h q, V ij.1 ij.2) =
      ∑ i∈Finset.range h, ∑ j∈Finset.range h, V i j := by
  simp only [pairFiber, Finset.sum_filter, Finset.sum_product]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  have hij : i+j∈Finset.range (2*h) := by
    simp only [Finset.mem_range] at hi hj ⊢; omega
  simp only [Finset.sum_ite_eq, hij, if_true]

/-- An arbitrary pair-weight matrix, not merely a rank-one matrix, has the
same field-size-independent normalized average energy. -/
theorem average_matrix_energy (hp : p≠2) (h : ℕ) (hh : h≤p)
    (W : ℕ → ℕ → ℝ) :
    (∑ a : ZMod p, matrixEnergy h W a) ≤ 4*(p:ℝ)*matrixMass h W := by
  unfold matrixEnergy
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ q∈Finset.range (2*h),
        4*(p:ℝ)*(∑ ij∈pairFiber h q, (W ij.1 ij.2)^2) :=
      Finset.sum_le_sum (fun q _ ↦ average_matrix_fiber_energy hp h q hh W)
    _ = _ := by rw [←Finset.mul_sum, sum_pairFiber h (fun i j ↦ (W i j)^2)]; rfl

/-- A common translation controls finitely many matrices with a weighted
budget. The matrices and weights must be fixed before selecting a. -/
theorem exists_admissible_matrix_budget {ι : Type*} (hp : p≠2) (h : ℕ)
    (hh : 4*h<p) (S : Finset ι) (W : ι → ℕ → ℕ → ℝ) (wgt : ι → ℝ)
    (hwgt : ∀ i∈S, 0≤wgt i) :
    ∃ a : ZMod p,
      (∀ i<h, a+(i:ZMod p)≠0) ∧
      (∀ q<2*h, 2*a+(q:ZMod p)≠0) ∧
      (∑ i∈S, wgt i*matrixEnergy h (W i) a) ≤
        8*(∑ i∈S, wgt i*matrixMass h (W i)) ∧
      ∀ i∈S, wgt i*matrixEnergy h (W i) a ≤
        8*(∑ j∈S, wgt j*matrixMass h (W j)) := by
  let f : ZMod p → ℝ := fun a ↦ ∑ i∈S, wgt i*matrixEnergy h (W i) a
  have hf (a : ZMod p) : 0≤f a :=
    Finset.sum_nonneg (fun i hi ↦ mul_nonneg (hwgt i hi) (matrixEnergy_nonneg _ _ _))
  have hav : (∑ a : ZMod p, f a) ≤
      (p:ℝ)*(4*(∑ i∈S, wgt i*matrixMass h (W i))) := by
    dsimp only [f]
    rw [Finset.sum_comm]
    calc
      _ = ∑ i∈S, wgt i*(∑ a : ZMod p, matrixEnergy h (W i) a) := by
        simp only [Finset.mul_sum]
      _ ≤ ∑ i∈S, wgt i*(4*(p:ℝ)*matrixMass h (W i)) :=
        Finset.sum_le_sum (fun i hi ↦ mul_le_mul_of_nonneg_left
          (average_matrix_energy hp h (by omega) (W i)) (hwgt i hi))
      _ = _ := by simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
  obtain ⟨a,ha,he⟩ := exists_small_outside (forbiddenInterval p h) f
    (4*(∑ i∈S, wgt i*matrixMass h (W i)))
    (by rw [ZMod.card]; have := forbiddenInterval_card p h; omega) hf
    (by simpa only [ZMod.card] using hav)
  have he' : f a ≤ 8*(∑ i∈S, wgt i*matrixMass h (W i)) := by linarith
  have htwo : (2:ZMod p)≠0 :=
    Ring.two_ne_zero (by simpa only [ZMod.ringChar_zmod_n] using hp)
  have hop (q : ℕ) (hq : q<2*h) : 2*a+(q:ZMod p)≠0 := by
    intro heq
    apply ha
    apply Finset.mem_image.mpr
    refine ⟨q, Finset.mem_range.mpr hq, ?_⟩
    apply (div_eq_iff htwo).mpr
    linear_combination -heq
  refine ⟨a, ?_, hop, he', ?_⟩
  · intro i hi heq
    have hn := hop (2*i) (by omega)
    apply hn
    push_cast
    linear_combination 2*heq
  · intro i hi
    apply le_trans _ he'
    exact Finset.single_le_sum
      (fun j hj ↦ mul_nonneg (hwgt j hj) (matrixEnergy_nonneg _ _ _)) hi

end Erdos66PairWeightedCharacterEnergy
