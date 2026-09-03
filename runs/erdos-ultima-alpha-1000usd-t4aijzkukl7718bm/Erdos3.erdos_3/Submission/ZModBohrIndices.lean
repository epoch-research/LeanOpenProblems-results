import Submission.BohrLocalQuadraticPartition
import Submission.StableQuadraticDensityIncrement

/-! Exact identifications of finite cyclic Bohr sets with their natural-index
models, including normalized averages and stable-boundary cardinalities. -/
namespace Erdos3ZModBohrIndices
open Finset Erdos3BohrCoarseProgressionPartition Erdos3FiniteBohr Erdos3BohrCovering
  Erdos3RelativeStableBohr Erdos3StableQuadraticDensityIncrement
open scoped BigOperators Classical
set_option maxHeartbeats 3000000

noncomputable def indexEquiv (p : ℕ) [NeZero p] : Fin p ≃ ZMod p where
  toFun k := (k.val : ZMod p)
  invFun x := ⟨x.val,ZMod.val_lt x⟩
  left_inv k := Fin.ext (ZMod.val_natCast_of_lt k.isLt)
  right_inv x := ZMod.natCast_zmod_val x

noncomputable def bohrIndexEquiv (p : ℕ) [NeZero p] (C : Finset (AddChar (ZMod p) ℂ)) (R : ℝ) :
    bohrIndices C R 0 1 p ≃ bohr C R :=
  (indexEquiv p).subtypeEquiv (fun k ↦ by
    simp only [mem_bohrIndices,zero_add,nsmul_eq_mul,mul_one]
    rfl)

lemma bohrIndexEquiv_val (p : ℕ) [NeZero p] (C : Finset (AddChar (ZMod p) ℂ)) (R : ℝ)
    (x : bohrIndices C R 0 1 p) : (bohrIndexEquiv p C R x).val = (x.val.val : ZMod p) := rfl

lemma bohrIndices_card (p : ℕ) [NeZero p] (C : Finset (AddChar (ZMod p) ℂ)) (R : ℝ) :
    (bohrIndices C R 0 1 p).card = (bohr C R).card := by
  simpa only [Fintype.card_coe] using Fintype.card_congr (bohrIndexEquiv p C R)

lemma bohrIndices_sdiff_card (p : ℕ) [NeZero p] (C : Finset (AddChar (ZMod p) ℂ)) (R S : ℝ) :
    (bohrIndices C R 0 1 p \ bohrIndices C S 0 1 p).card = (bohr C R \ bohr C S).card := by
  apply card_equiv (indexEquiv p)
  intro k
  simp only [mem_sdiff,mem_bohrIndices,zero_add,nsmul_eq_mul,mul_one]
  rfl

lemma bohrIndices_nonempty (p : ℕ) [NeZero p] (C : Finset (AddChar (ZMod p) ℂ))
    {R : ℝ} (hR : 0 ≤ R) : (bohrIndices C R 0 1 p).Nonempty := by
  let x : bohr C R := ⟨0,bohr_zero C hR⟩
  exact ⟨((bohrIndexEquiv p C R).symm x).val,((bohrIndexEquiv p C R).symm x).property⟩

lemma bohrIndices_expect {W : Type*} [AddCommMonoid W] [Module ℚ≥0 W]
    (p : ℕ) [NeZero p] (C : Finset (AddChar (ZMod p) ℂ)) (R : ℝ) (f : ZMod p → W) :
    (𝔼 x : bohrIndices C R 0 1 p, f (x.val.val : ZMod p)) = 𝔼 x : bohr C R, f x :=
  Fintype.expect_equiv (bohrIndexEquiv p C R) _ _ (fun _ ↦ rfl)

lemma stable_index_boundary_fraction (p : ℕ) [NeZero p]
    (C : Finset (AddChar (ZMod p) ℂ)) {z : ℕ} (hz : 0 < z) {R : ℝ}
    (hR : 0 ≤ R) (hstable : RelativeStable C z R) :
    ((bohrIndices C R 0 1 p \ bohrIndices C (R-relativeWidth C z R) 0 1 p).card : ℝ)/
      ((bohrIndices C R 0 1 p).card : ℝ) ≤ 1/(z : ℝ) := by
  rw [bohrIndices_sdiff_card,bohrIndices_card]
  have hc : (0 : ℝ) < (bohr C R).card := by
    exact_mod_cast (show (bohr C R).Nonempty from ⟨0,bohr_zero C hR⟩).card_pos
  apply (div_le_iff₀ hc).mpr
  convert stable_inner_boundary C hz hR hstable using 1
  congr 1
  congr 1
  ext x
  simp only [mem_sdiff]

lemma bohrIndices_card_lower (p : ℕ) [NeZero p] (C : Finset (AddChar (ZMod p) ℂ))
    {R : ℝ} (hR : 1/64 ≤ R) : p ≤ 257^(2*C.card)*(bohrIndices C R 0 1 p).card := by
  rw [bohrIndices_card]
  have hh := card_bohr_lower C (q := 128) (by decide)
  rw [ZMod.card,show (2 : ℝ)/(128 : ℕ) = 1/64 by norm_num] at hh
  exact hh.trans (Nat.mul_le_mul_left _ (card_le_card (bohr_mono C hR)))

#print axioms bohrIndices_expect
#print axioms stable_index_boundary_fraction
end Erdos3ZModBohrIndices
