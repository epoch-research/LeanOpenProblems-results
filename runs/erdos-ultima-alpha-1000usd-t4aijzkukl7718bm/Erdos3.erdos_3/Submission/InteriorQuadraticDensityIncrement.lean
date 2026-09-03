import Submission.AveragedPolynomialRankInverse
import Submission.AveragedMaskedPhaseIncrement
import Submission.FourPatternQuadraticStructure

/-! An actual positive density increment on an interior local-quadratic phase
cell. This does not yet prove that the increment can be iterated within such cells. -/
namespace Erdos3InteriorQuadraticDensityIncrement
open Finset Erdos3FinitePartitionIncrement Erdos3MaskedPhaseIncrement
  Erdos3AveragedMaskedPhaseIncrement Erdos3AveragedPolynomialRankInverse
  Erdos3PolynomialRankQuadraticInverse Erdos3FiniteBohr Erdos3FiniteUniformity
  Erdos3CorrelationSifting Erdos3LocalQuadraticInverse
  Erdos3FourPatternQuadraticStructure Erdos3SingleExponentialQuadraticInverse
  Erdos3UniformityCounting Erdos3FiniteFourier
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 5000000
set_option maxRecDepth 3000

variable {G : Type*} [AddCommGroup G] [Fintype G]

def IsInteriorPhaseCell (n : ℕ) (B : Finset G) (q : G → ℂ) (S : Finset G) : Prop :=
  ∃ i : PhaseGrid n, S = B.filter (fun x ↦
    ⌊(n : ℝ)*((q x).re+1)⌋₊ = i.1.val ∧ ⌊(n : ℝ)*((q x).im+1)⌋₊ = i.2.val)

lemma cell_masked_some_shape (n : ℕ) (B : Finset G) (q : G → ℂ) (hq : ∀ x, ‖q x‖ ≤ 1)
    (i : PhaseGrid n) : IsInteriorPhaseCell n B q (cell (maskedLabel n B q hq) (some i)) := by
  refine ⟨i,?_⟩
  ext x
  by_cases hx : x ∈ B
  · simp [cell,maskedLabel,hx,phaseLabel,gridCoord,Prod.ext_iff,Fin.ext_iff]
  · simp [cell,maskedLabel,hx]

lemma IsInteriorPhaseCell.subset {n : ℕ} {B S : Finset G} {q : G → ℂ}
    (h : IsInteriorPhaseCell n B q S) : S ⊆ B := by
  obtain ⟨i,rfl⟩ := h
  exact filter_subset _ _

lemma centered_indicator_bound (A : Finset G) (x : G) : |indicator A x-density A| ≤ 1 := by
  have hα : 0 ≤ density A := by unfold density; positivity
  have hα1 : density A ≤ 1 := by
    unfold density
    apply (div_le_one (by exact_mod_cast Fintype.card_pos : (0 : ℝ) < Fintype.card G)).mpr
    exact_mod_cast card_le_univ A
  have hx0 := indicator_nonneg A x
  have hx1 : indicator A x ≤ 1 := by unfold indicator; split_ifs <;> norm_num
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma indicator_cell_mean (A S : Finset G) (a : G) :
    (𝔼 x : S, indicator A (a+x)) = ((S.filter (fun x ↦ a+x ∈ A)).card : ℝ)/(S.card : ℝ) := by
  rw [Fintype.expect_eq_sum_div_card,Fintype.card_coe]
  congr 1
  rw [sum_coe_sort S (fun x ↦ indicator A (a+x))]
  simp only [indicator,card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]


/-- Large U³ of a centered indicator gives a positive density increment on a
large grid cell INSIDE the quadraticity domain. The mesh, size, and increment
are independent of the ambient group order. -/
theorem interior_quadratic_density_increment
    (h2 : Function.Bijective (fun x : G ↦ x+x)) (A : Finset G)
    {δ r : ℝ} (hδ : 0 < δ)
    (hU : δ ≤ uniformityPower 2 (fun x ↦ ((indicator A x-density A : ℝ) : ℂ)))
    (hr : 0 < r) (hrcorr : r ≤ sharpCorrelation δ) :
    ∃ C : Finset (AddChar G ℂ), ∃ q : G → ℂ, ∃ a : G, ∃ S : Finset G,
      C.card ≤ sharpRank δ ∧ (∀ x, ‖q x‖ = 1) ∧
      IsLocallyQuadratic (bohr C (1/8) : Set G) q ∧
      IsInteriorPhaseCell (phaseResolution r) (bohr C (1/8)) q S ∧ S.Nonempty ∧
      r^3/2048*(Fintype.card G : ℝ) ≤ (S.card : ℝ) ∧
      density A+r/16 ≤ ((S.filter (fun x ↦ a+x ∈ A)).card : ℝ)/(S.card : ℝ) := by
  let f : G → ℝ := fun x ↦ indicator A x-density A
  have hf (x : G) : |f x| ≤ 1 := centered_indicator_bound A x
  have hfC (x : G) : ‖(f x : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real,Real.norm_eq_abs] using hf x
  have hf0 : 𝔼 x, f x = 0 := by
    simp only [f,expect_sub_distrib,expect_indicator,Fintype.expect_const,sub_self]
  obtain ⟨C,q,hC,hq,hquad,hcorr⟩ := averaged_polynomial_rank_quadratic_inverse h2
    (fun x ↦ (f x : ℂ)) hfC hδ hU
  have hr' : r ≤ 𝔼 a, ‖𝔼 x, if x ∈ bohr C (1/8) then (f (a+x) : ℂ)*conj (q a x) else 0‖^2 :=
    hrcorr.trans hcorr
  have hr1 : r ≤ 1 := by
    apply hr'.trans
    apply expect_le univ_nonempty
    intro a _
    have hh : ‖𝔼 x, if x ∈ bohr C (1/8) then (f (a+x) : ℂ)*conj (q a x) else 0‖ ≤ 1 := by
      apply (RCLike.norm_expect_le (K := ℂ)).trans
      apply expect_le univ_nonempty
      intro x _
      split_ifs
      · simpa only [norm_mul,Complex.norm_conj,hq,mul_one] using hfC (a+x)
      · norm_num
    nlinarith [norm_nonneg (𝔼 x, if x ∈ bohr C (1/8) then (f (a+x) : ℂ)*conj (q a x) else 0)]
  let hq' : ∀ a x, ‖q a x‖ ≤ 1 := fun a x ↦ (hq a x).le
  obtain ⟨a,i,hi,hinc⟩ := averaged_masked_phase_inside_increment (bohr C (1/8)) f q hf hf0 hq'
    hr (phaseResolution_pos hr) (phaseResolution_mesh hr) hr'
  let c := maskedLabel (phaseResolution r) (bohr C (1/8)) (q a) (hq' a)
  let S := cell c (some i)
  have hM : (0 : ℝ) < 16*(((2*phaseResolution r+1)^2 : ℕ) : ℝ) := by positivity
  have hsize : r^3/2048 ≤ cellMass c (some i) := by
    apply le_trans ?_ hi
    apply (le_div_iff₀ hM).mpr
    have hbound := phaseGrid_card_bound hr hr1
    push_cast at hbound
    have hsmall : (((2*phaseResolution r+1)^2 : ℕ) : ℝ)*r^2 ≤ 128 := by
      push_cast
      nlinarith [sq_nonneg r]
    have hh := mul_le_mul_of_nonneg_left hsmall hr.le
    nlinarith only [hh]
  have hpos : 0 < cellMass c (some i) := (by positivity : 0 < r^3/2048).trans_le hsize
  have hS : S.Nonempty := by
    by_contra hn
    rw [cellMass_eq_card,show cell c (some i) = S from rfl,
      Finset.not_nonempty_iff_eq_empty.mp hn,card_empty,Nat.cast_zero,zero_div] at hpos
    exact (lt_irrefl 0) hpos
  letI : Nonempty S := hS.to_subtype
  have hmean : density A+r/16 ≤ 𝔼 x : S, indicator A (a+x) := by
    have hinc' : r/16 ≤ 𝔼 x : S, f (a+x) := hinc
    clear hinc
    have hinc := hinc'
    simp only [f] at hinc
    rw [expect_sub_distrib,Fintype.expect_const] at hinc
    linarith
  refine ⟨C,q a,a,S,hC,hq a,hquad a,cell_masked_some_shape _ _ _ _ i,hS,?_,?_⟩
  · rw [cellMass_eq_card] at hsize
    exact (le_div_iff₀ (by exact_mod_cast Fintype.card_pos : (0 : ℝ) < Fintype.card G)).mp hsize
  · rwa [indicator_cell_mean] at hmean

noncomputable def fourIncrement (α : ℝ) : ℝ :=
  Real.exp (-fourCorrelationConstant*(1/α)^1069036416)

lemma fourIncrement_pos (α : ℝ) : 0 < fourIncrement α := Real.exp_pos _

variable {F : Type*} [Field F] [Fintype F]

/-- Four-pattern-free sets have a quantitative positive density increment on an
interior quadratic phase cell. The statement records the cell structure needed
for a future relative iteration; it does not assert such an iteration. -/
theorem four_pattern_free_interior_density_increment
    (h2 : Function.Bijective (fun x : F ↦ x+x))
    (v : Fin 4 → F) (hv : Function.Injective v) (A : Finset F) (hA : A.Nonempty)
    (hsize : 4 ≤ (density A)^3*(Fintype.card F : ℝ))
    (hdiag : ∀ x d : F, (∀ i : Fin 4, x+v i*d ∈ A) → d = 0) :
    ∃ C : Finset (AddChar F ℂ), ∃ q : F → ℂ, ∃ a : F, ∃ S : Finset F,
      (C.card : ℝ) ≤ fourRankConstant*(1/density A)^1069036416 ∧
      (∀ x, ‖q x‖ = 1) ∧ IsLocallyQuadratic (bohr C (1/8) : Set F) q ∧
      IsInteriorPhaseCell (phaseResolution (fourIncrement (density A))) (bohr C (1/8)) q S ∧
      S.Nonempty ∧ (fourIncrement (density A))^3/2048*(Fintype.card F : ℝ) ≤ (S.card : ℝ) ∧
      density A+fourIncrement (density A)/16 ≤
        ((S.filter (fun x ↦ a+x ∈ A)).card : ℝ)/(S.card : ℝ) := by
  have hα := density_pos A hA
  have hU := pattern_free_uniformity_lower 2 v hv A hA hsize hdiag
  have hU' : ((density A)^4/8)^8 ≤
      uniformityPower 2 (fun x ↦ ((indicator A x-density A : ℝ) : ℂ)) := by
    simpa only [show 2+2 = 4 from rfl,show 2^(2+1) = 8 from rfl,
      show (2 : ℝ)*(4 : ℕ) = 8 by norm_num] using hU.le
  have hδ : 0 < ((density A)^4/8)^8 := by positivity
  have hδ1 : ((density A)^4/8)^8 ≤ 1 := hU'.trans
    (uniformityPower_le_one 2 _ (fun x ↦ by
      simpa only [Complex.norm_real,Real.norm_eq_abs] using centered_indicator_bound A x))
  have hcorr : fourIncrement (density A) ≤ sharpCorrelation (((density A)^4/8)^8) := by
    have hh := sharpCorrelation_exp_lower hδ hδ1
    rw [threshold_power] at hh
    simpa only [fourIncrement,fourCorrelationConstant,neg_mul,mul_assoc] using hh
  obtain ⟨C,q,a,S,hC,hq,hquad,hcell,hS,hcard,hinc⟩ := interior_quadratic_density_increment h2 A
    hδ hU' (fourIncrement_pos (density A)) hcorr
  have hrank := sharpRank_power_bound hδ hδ1
  rw [threshold_power] at hrank
  have hC' : (C.card : ℝ) ≤ sharpRank (((density A)^4/8)^8) := by exact_mod_cast hC
  refine ⟨C,q,a,S,?_,hq,hquad,hcell,hS,hcard,hinc⟩
  simpa only [fourRankConstant,mul_assoc] using hC'.trans hrank

#print axioms interior_quadratic_density_increment
#print axioms four_pattern_free_interior_density_increment
end Erdos3InteriorQuadraticDensityIncrement
