import Submission.FinitePartitionIncrement

/-! Explicit phase-grid cells convert a masked phase correlation into a genuine
positive density increment. The selected cell may be the complement of the mask. -/
namespace Erdos3MaskedPhaseIncrement
open Finset Erdos3FinitePartitionIncrement
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 4000000

noncomputable def gridCoord (n : ℕ) (r : ℝ) (hr : |r| ≤ 1) : Fin (2*n+1) :=
  ⟨⌊(n : ℝ)*(r+1)⌋₊, by
    have hn : 0 ≤ (n : ℝ)*(r+1) := mul_nonneg (Nat.cast_nonneg _) (by linarith [(abs_le.mp hr).1])
    apply (Nat.floor_lt hn).mpr
    push_cast
    nlinarith [(abs_le.mp hr).2, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]⟩

lemma gridCoord_close {n : ℕ} (hn : 0 < n) {r s : ℝ} (hr : |r| ≤ 1) (hs : |s| ≤ 1)
    (h : gridCoord n r hr = gridCoord n s hs) : |r-s| ≤ 1/(n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hR : 0 ≤ (n : ℝ)*(r+1) := mul_nonneg hnR.le (by linarith [(abs_le.mp hr).1])
  have hS : 0 ≤ (n : ℝ)*(s+1) := mul_nonneg hnR.le (by linarith [(abs_le.mp hs).1])
  have he : ⌊(n : ℝ)*(r+1)⌋₊ = ⌊(n : ℝ)*(s+1)⌋₊ := congrArg Fin.val h
  have hr0 := Nat.floor_le hR
  have hs0 := Nat.floor_le hS
  have hr1 := Nat.lt_floor_add_one ((n : ℝ)*(r+1))
  have hs1 := Nat.lt_floor_add_one ((n : ℝ)*(s+1))
  rw [he] at hr0 hr1
  have hd : |(n : ℝ)*(r-s)| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> nlinarith
  rw [abs_mul,abs_of_pos hnR] at hd
  apply (le_div_iff₀ hnR).mpr
  nlinarith

abbrev PhaseGrid (n : ℕ) := Fin (2*n+1) × Fin (2*n+1)

variable {V : Type*} [Fintype V] [Nonempty V]

noncomputable def phaseLabel (n : ℕ) (q : V → ℂ) (hq : ∀ x, ‖q x‖ ≤ 1) (x : V) : PhaseGrid n :=
  (gridCoord n (q x).re ((Complex.abs_re_le_norm _).trans (hq x)),
   gridCoord n (q x).im ((Complex.abs_im_le_norm _).trans (hq x)))
noncomputable def maskedLabel (n : ℕ) (B : Finset V) (q : V → ℂ) (hq : ∀ x, ‖q x‖ ≤ 1)
    (x : V) : Option (PhaseGrid n) := if x ∈ B then some (phaseLabel n q hq x) else none
noncomputable def maskedTest (B : Finset V) (q : V → ℂ) (x : V) : ℂ :=
  if x ∈ B then conj (q x) else 0

lemma maskedTest_bound (B : Finset V) (q : V → ℂ) (hq : ∀ x, ‖q x‖ ≤ 1) (x : V) :
    ‖maskedTest B q x‖ ≤ 1 := by
  unfold maskedTest
  split_ifs <;> simp_all only [Complex.norm_conj,norm_zero,zero_le_one]

lemma maskedLabel_oscillation {n : ℕ} (hn : 0 < n)
    (B : Finset V) (q : V → ℂ) (hq : ∀ x, ‖q x‖ ≤ 1) {x y : V}
    (he : maskedLabel n B q hq x = maskedLabel n B q hq y) :
    ‖maskedTest B q x-maskedTest B q y‖ ≤ 2/(n : ℝ) := by
  by_cases hx : x ∈ B <;> by_cases hy : y ∈ B
  · simp only [maskedLabel,if_pos hx,if_pos hy,Option.some.injEq] at he
    have hre := gridCoord_close hn ((Complex.abs_re_le_norm _).trans (hq x))
      ((Complex.abs_re_le_norm _).trans (hq y)) (congrArg Prod.fst he)
    have him := gridCoord_close hn ((Complex.abs_im_le_norm _).trans (hq x))
      ((Complex.abs_im_le_norm _).trans (hq y)) (congrArg Prod.snd he)
    simp only [maskedTest,if_pos hx,if_pos hy,← map_sub,Complex.norm_conj]
    calc
      _ ≤ |(q x-q y).re|+|(q x-q y).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 1/(n : ℝ)+1/(n : ℝ) := by simpa only [Complex.sub_re,Complex.sub_im] using add_le_add hre him
      _ = _ := by ring
  · simp [maskedLabel,hx,hy] at he
  · simp [maskedLabel,hx,hy] at he
  · simp only [maskedTest,if_neg hx,if_neg hy,sub_self,norm_zero]
    positivity

lemma exists_cell_representatives {I : Type*} (c : V → I) (v : V → ℂ)
    (hv : ∀ x, ‖v x‖ ≤ 1) {ε : ℝ} (hε : 0 ≤ ε)
    (hosc : ∀ x y, c x = c y → ‖v x-v y‖ ≤ ε) :
    ∃ w : I → ℂ, (∀ i, ‖w i‖ ≤ 1) ∧ ∀ x, ‖v x-w (c x)‖ ≤ ε := by
  let w : I → ℂ := fun i ↦ if hi : ∃ x, c x = i then v (Classical.choose hi) else 0
  refine ⟨w,?_,?_⟩
  · intro i
    dsimp only [w]
    split_ifs with hi
    · exact hv _
    · norm_num
  · intro x
    have hi : ∃ y, c y = c x := ⟨x,rfl⟩
    dsimp only [w]
    rw [dif_pos hi]
    exact hosc x _ (Classical.choose_spec hi).symm

lemma cellMass_eq_card {I : Type*} (c : V → I) (i : I) :
    cellMass c i = ((cell c i).card : ℝ)/(Fintype.card V : ℝ) := by
  rw [cellMass,Fintype.expect_eq_sum_div_card]
  congr 1
  simp only [cell,card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

lemma cellCharge_eq_mean {I : Type*} (c : V → I) (f : V → ℝ) (i : I)
    (hi : (cell c i).Nonempty) :
    cellCharge c f i = cellMass c i*(𝔼 x : cell c i, f x) := by
  have hN : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hC : ((cell c i).card : ℝ) ≠ 0 := by exact_mod_cast hi.card_pos.ne'
  have hs : (∑ x : V, if c x = i then f x else 0) = ∑ x : cell c i, f x := by
    rw [sum_coe_sort]
    simp only [cell,sum_filter]
  rw [cellCharge,Fintype.expect_eq_sum_div_card,hs,cellMass_eq_card,Fintype.expect_eq_sum_div_card,Fintype.card_coe]
  field_simp

/-- The cell is either a phase-grid fiber inside B or the entire complement of B.
The conclusion is a positive mean, not merely a signed correlation. -/
theorem masked_phase_cell_increment (B : Finset V) (f : V → ℝ) (q : V → ℂ)
    (hf : ∀ x, |f x| ≤ 1) (hf0 : 𝔼 x, f x = 0) (hq : ∀ x, ‖q x‖ ≤ 1)
    {r : ℝ} (hr : 0 < r) {n : ℕ} (hn : 0 < n) (hmesh : 2/(n : ℝ) ≤ r/2)
    (hcorr : r ≤ ‖𝔼 x, if x ∈ B then (f x : ℂ)*conj (q x) else 0‖^2) :
    ∃ i : Option (PhaseGrid n),
      r/(16*((2*n+1 : ℕ)^2+1 : ℕ)) ≤ cellMass (maskedLabel n B q hq) i ∧
      r/16 ≤ 𝔼 x : cell (maskedLabel n B q hq) i, f x := by
  let c := maskedLabel n B q hq
  obtain ⟨w,hw,happrox⟩ := exists_cell_representatives c (maskedTest B q)
    (maskedTest_bound B q hq) (by positivity : 0 ≤ 2/(n : ℝ))
    (fun _ _ he ↦ maskedLabel_oscillation hn B q hq he)
  have hc : r ≤ ‖𝔼 x, (f x : ℂ)*maskedTest B q x‖^2 := by
    simpa only [maskedTest,mul_ite,mul_zero] using hcorr
  obtain ⟨i,hi,hinc⟩ := correlation_cell_increment c f (maskedTest B q) w hf hf0
    (maskedTest_bound B q hq) hw hr hmesh happrox hc
  have hM : Fintype.card (Option (PhaseGrid n)) = (2*n+1)^2+1 := by
    simp only [Fintype.card_option,Fintype.card_prod,Fintype.card_fin,PhaseGrid,pow_two]
  have hpos : 0 < cellMass c i := (by positivity : 0 < r/(16*(Fintype.card (Option (PhaseGrid n)) : ℝ))).trans_le hi
  have hcell : (cell c i).Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    rw [cellMass_eq_card,he,card_empty,Nat.cast_zero,zero_div] at hpos
    exact (lt_irrefl 0) hpos
  rw [cellCharge_eq_mean c f i hcell] at hinc
  refine ⟨i,by simpa only [hM] using hi,?_⟩
  exact (mul_le_mul_iff_right₀ hpos).mp (by simpa only [mul_comm] using hinc)

noncomputable def phaseResolution (r : ℝ) : ℕ := ⌈4/r⌉₊

lemma phaseResolution_pos {r : ℝ} (hr : 0 < r) : 0 < phaseResolution r := by
  exact Nat.ceil_pos.mpr (by positivity)

lemma phaseResolution_mesh {r : ℝ} (hr : 0 < r) : 2/(phaseResolution r : ℝ) ≤ r/2 := by
  have hn : (0 : ℝ) < phaseResolution r := by exact_mod_cast phaseResolution_pos hr
  have hh : 4/r ≤ (phaseResolution r : ℝ) := Nat.le_ceil _
  have hh' := (div_le_iff₀ hr).mp hh
  apply (div_le_iff₀ hn).mpr
  nlinarith

lemma phaseGrid_card_bound {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    (((2*phaseResolution r+1)^2+1 : ℕ) : ℝ)*r^2 ≤ 128 := by
  have hh := Nat.ceil_lt_add_one (by positivity : 0 ≤ 4/r)
  change (phaseResolution r : ℝ) < 4/r+1 at hh
  have hi : 1 ≤ 1/r := (le_div_iff₀ hr).mpr (by simpa using hr1)
  have hn : (phaseResolution r : ℝ)*r ≤ 5 := by
    have hx : (phaseResolution r : ℝ) ≤ 5/r := by
      calc
        _ ≤ 4/r+1 := hh.le
        _ ≤ 4/r+1/r := add_le_add le_rfl hi
        _ = _ := by ring
    exact (le_div_iff₀ hr).mp hx
  have hp : 0 ≤ (2*(phaseResolution r : ℝ)+1)*r := by positivity
  have hp' : (2*(phaseResolution r : ℝ)+1)*r ≤ 11 := by nlinarith
  have hsq := pow_le_pow_left₀ hp hp' 2
  push_cast
  nlinarith [sq_nonneg r]

/-- A completely explicit size and increment bound for the selected phase cell. -/
theorem masked_phase_cell_increment_power (B : Finset V) (f : V → ℝ) (q : V → ℂ)
    (hf : ∀ x, |f x| ≤ 1) (hf0 : 𝔼 x, f x = 0) (hq : ∀ x, ‖q x‖ ≤ 1)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hcorr : r ≤ ‖𝔼 x, if x ∈ B then (f x : ℂ)*conj (q x) else 0‖^2) :
    ∃ i : Option (PhaseGrid (phaseResolution r)),
      r^3/2048 ≤ cellMass (maskedLabel (phaseResolution r) B q hq) i ∧
      r/16 ≤ 𝔼 x : cell (maskedLabel (phaseResolution r) B q hq) i, f x := by
  obtain ⟨i,hi,hinc⟩ := masked_phase_cell_increment B f q hf hf0 hq hr
    (phaseResolution_pos hr) (phaseResolution_mesh hr) hcorr
  refine ⟨i,le_trans ?_ hi,hinc⟩
  have hM : (0 : ℝ) < 16*(((2*phaseResolution r+1)^2+1 : ℕ) : ℝ) := by positivity
  apply (le_div_iff₀ hM).mpr
  have hh := mul_le_mul_of_nonneg_left (phaseGrid_card_bound hr hr1) hr.le
  nlinarith only [hh]

/-- A phase-grid cell, or the complement of the masking set. This definition
uses only the test q and the prescribed mesh, not the function being incremented. -/
def IsMaskedPhaseCell (n : ℕ) (B : Finset V) (q : V → ℂ) (S : Finset V) : Prop :=
  S = univ\B ∨ ∃ i : PhaseGrid n,
    S = B.filter (fun x ↦ ⌊(n : ℝ)*((q x).re+1)⌋₊ = i.1.val ∧
      ⌊(n : ℝ)*((q x).im+1)⌋₊ = i.2.val)

lemma cell_masked_shape (n : ℕ) (B : Finset V) (q : V → ℂ) (hq : ∀ x, ‖q x‖ ≤ 1)
    (i : Option (PhaseGrid n)) : IsMaskedPhaseCell n B q (cell (maskedLabel n B q hq) i) := by
  cases i with
  | none =>
    left
    ext x
    simp [cell,maskedLabel]
  | some i =>
    right
    refine ⟨i,?_⟩
    ext x
    by_cases hx : x ∈ B
    · simp [cell,maskedLabel,hx,phaseLabel,gridCoord,Prod.ext_iff,Fin.ext_iff]
    · simp [cell,maskedLabel,hx]

#print axioms masked_phase_cell_increment_power
end Erdos3MaskedPhaseIncrement
