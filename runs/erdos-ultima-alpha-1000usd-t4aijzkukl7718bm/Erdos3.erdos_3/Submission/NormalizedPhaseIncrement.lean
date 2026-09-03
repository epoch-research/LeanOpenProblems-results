import Submission.AveragedMaskedPhaseIncrement

/-! Positive phase-cell increments on normalized finite probability spaces.
The center space and the local averaging space may be different finite types. -/
namespace Erdos3NormalizedPhaseIncrement
open Finset Erdos3FinitePartitionIncrement Erdos3MaskedPhaseIncrement Erdos3AveragedMaskedPhaseIncrement
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 5000000

variable {V : Type*} [Fintype V] [Nonempty V]

noncomputable def phaseCell (n : ℕ) (q : V → ℂ) (i : PhaseGrid n) : Finset V :=
  univ.filter (fun x ↦ ⌊(n : ℝ)*((q x).re+1)⌋₊ = i.1.val ∧ ⌊(n : ℝ)*((q x).im+1)⌋₊ = i.2.val)

lemma full_phase_cell_eq (n : ℕ) (q : V → ℂ) (hq : ∀ x, ‖q x‖ ≤ 1) (i : PhaseGrid n) :
    cell (maskedLabel n (univ : Finset V) q hq) (some i) = phaseCell n q i := by
  ext x
  simp [cell,maskedLabel,phaseLabel,gridCoord,phaseCell,Prod.ext_iff,Fin.ext_iff]

variable {Z : Type*} [Fintype Z] [Nonempty Z]

/-- Joint centering suffices; the function need not be centered at each center.
The output cell has polynomial relative size and a positive relative mean. -/
theorem averaged_normalized_phase_increment (f : Z → V → ℝ) (q : Z → V → ℂ)
    (hf : ∀ a x, |f a x| ≤ 1) (hf0 : (𝔼 a, 𝔼 x, f a x) = 0)
    (hq : ∀ a x, ‖q a x‖ ≤ 1) {r : ℝ} (hr : 0 < r)
    (hcorr : r ≤ 𝔼 a, ‖𝔼 x, (f a x : ℂ)*conj (q a x)‖^2) :
    ∃ a : Z, ∃ i : PhaseGrid (phaseResolution r),
      (phaseCell (phaseResolution r) (q a) i).Nonempty ∧
      r^3/2048*(Fintype.card V : ℝ) ≤ ((phaseCell (phaseResolution r) (q a) i).card : ℝ) ∧
      r/16 ≤ 𝔼 x : phaseCell (phaseResolution r) (q a) i, f a x := by
  let n := phaseResolution r
  have hn : 0 < n := phaseResolution_pos hr
  have hmesh : 2/(n : ℝ) ≤ r/2 := phaseResolution_mesh hr
  let corr : Z → ℝ := fun a ↦ ‖𝔼 x, (f a x : ℂ)*conj (q a x)‖
  let u : Z → PhaseGrid n → ℝ := fun a i ↦
    cellCharge (maskedLabel n (univ : Finset V) (q a) (hq a)) (f a) (some i)
  have hnorm (a : Z) : corr a ≤ 1 := by
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply expect_le univ_nonempty
    intro x _
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_conj]
    exact (mul_le_mul (hf a x) (hq a x) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hnormsq (a : Z) : (corr a)^2 ≤ corr a := by
    have hh : 0 ≤ corr a := norm_nonneg _
    nlinarith [hnorm a]
  have hr1 : r ≤ 1 := hcorr.trans ((expect_le_expect (fun a _ ↦ hnormsq a)).trans
    (expect_le univ_nonempty (fun a _ ↦ hnorm a)))
  have hl (a : Z) : corr a ≤ 2/(n : ℝ)+∑ i, |u a i| := by
    simpa only [mem_univ,if_true] using masked_correlation_L1_bound
      (univ : Finset V) (f a) (q a) (hf a) (hq a) hn
  have hzero : (𝔼 a, ∑ i, u a i) = 0 := by
    simp only [u,inside_charge_sum,mem_univ,if_true]
    exact hf0
  have hL : r/2 ≤ 𝔼 a, ((∑ i, |u a i|)+(∑ i, u a i)) := by
    have hh := hcorr.trans (expect_le_expect (fun a _ ↦ (hnormsq a).trans (hl a)))
    rw [expect_add_distrib,Fintype.expect_const] at hh
    rw [expect_add_distrib,hzero,add_zero]
    linarith
  obtain ⟨a,_,ha⟩ := exists_max_image univ (fun a ↦ (∑ i, |u a i|)+(∑ i, u a i)) univ_nonempty
  have hLa := hL.trans (expect_le univ_nonempty ha)
  let c := maskedLabel n (univ : Finset V) (q a) (hq a)
  obtain ⟨i,hi,hinc⟩ := positive_cell_of_L1_plus_mean
    (fun i ↦ cellMass c (some i)) (u a) (fun i ↦ cellMass_nonneg _ _)
    (inside_mass_sum_le_one n univ (q a) (hq a))
    (fun i ↦ abs_cellCharge_le _ _ (hf a) _) (by positivity : 0 < r/2) hLa
  have hM : Fintype.card (PhaseGrid n) = (2*n+1)^2 := by simp [PhaseGrid,pow_two]
  have hsize : r^3/2048 ≤ cellMass c (some i) := by
    apply le_trans _ hi
    rw [hM]
    have hMpos : (0 : ℝ) < 8*(((2*n+1)^2 : ℕ) : ℝ) := by positivity
    apply (le_div_iff₀ hMpos).mpr
    have hb := phaseGrid_card_bound hr hr1
    change (((2*n+1)^2+1 : ℕ) : ℝ)*r^2 ≤ 128 at hb
    simp only [Nat.cast_add,Nat.cast_one] at hb
    have hsmall : (((2*n+1)^2 : ℕ) : ℝ)*r^2 ≤ 128 := by nlinarith [sq_nonneg r]
    have hh := mul_le_mul_of_nonneg_left hsmall hr.le
    nlinarith only [hh]
  have hpos : 0 < cellMass c (some i) := (by positivity : 0 < r^3/2048).trans_le hsize
  have hcell : (cell c (some i)).Nonempty := by
    by_contra hn
    rw [cellMass_eq_card,Finset.not_nonempty_iff_eq_empty.mp hn,card_empty,Nat.cast_zero,zero_div] at hpos
    exact (lt_irrefl 0) hpos
  change (r/2/8)*cellMass c (some i) ≤ cellCharge c (f a) (some i) at hinc
  rw [cellCharge_eq_mean c (f a) (some i) hcell,show r/2/8 = r/16 by ring] at hinc
  have hmean : r/16 ≤ 𝔼 x : cell c (some i), f a x := by nlinarith only [hinc,hpos]
  have hc : cell c (some i) = phaseCell n (q a) i := full_phase_cell_eq n (q a) (hq a) i
  rw [cellMass_eq_card,hc] at hsize
  rw [hc] at hcell hmean
  exact ⟨a,i,hcell,(le_div_iff₀ (by exact_mod_cast Fintype.card_pos : (0 : ℝ) < Fintype.card V)).mp hsize,hmean⟩

#print axioms averaged_normalized_phase_increment
end Erdos3NormalizedPhaseIncrement
