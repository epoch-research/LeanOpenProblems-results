import Submission.DensePaletteCompletionExplore
import Submission.DenseCyclicExtensionExplore

/-! Odd cyclic specialization of finite multiplicative palette completion.
The threshold involves the smallest/old-largest mixed mean, not a changing
number of iteration steps. -/
namespace Erdos66DenseCyclicPaletteCompletion
open Erdos66OuterCarryProfile Erdos66SaturatingCyclicFamily
open scoped Classical
set_option maxHeartbeats 2500000

/-- Conditional completion from the old largest cardinality to full density,
with no worsening of eta and with multiplicative overshoot at most 1+4g. -/
theorem exists_complete_cyclic_palette (M : ℕ) [NeZero M] (hodd : Odd M)
    (P₀ : Finset (Finset (ZMod M))) (C₀ : Finset (ZMod M)) (s : ℕ) (η g : ℝ)
    (hη : 0 < η) (hη1 : η ≤ 1) (hg : 0 < g) (hg1 : g ≤ 1/4)
    (hP₀ : ∀ C∈P₀, ∀ D∈P₀, C ⊆ D ∨ D ⊆ C)
    (hflat₀ : ∀ C∈P₀, ∀ D∈P₀, ∀ z,
      |(cyclicCount M C D z : ℝ)-actualMean M C D| ≤ η*actualMean M C D)
    (hC₀ : C₀∈P₀) (hmax₀ : ∀ D∈P₀, D ⊆ C₀) (hmin₀ : ∀ D∈P₀, s ≤ D.card)
    (hlarge : 32 ≤ η*g*((C₀.card : ℝ)^2/M))
    (hthreshold : 8192*Real.log (2*((M+2)*M+1)) < η^2*g^2*((s : ℝ)*C₀.card/M)) :
    ∃ P : Finset (Finset (ZMod M)), P₀ ⊆ P ∧
      (∀ C∈P, ∀ D∈P, C ⊆ D ∨ D ⊆ C) ∧
      (∀ C∈P, ∀ D∈P, ∀ z,
        |(cyclicCount M C D z : ℝ)-actualMean M C D| ≤ η*actualMean M C D) ∧
      (Finset.univ : Finset (ZMod M))∈P ∧ P.card ≤ M+1 ∧
      ∀ x : ℝ, (C₀.card : ℝ) ≤ x → x ≤ M →
        ∃ D∈P, x ≤ (D.card : ℝ) ∧ (D.card : ℝ) ≤ (1+4*g)*x := by
  letI : LinearOrder (ZMod M) := LinearOrder.lift' ZMod.val (ZMod.val_injective M)
  have hinj : Function.Injective (fun a : ZMod M ↦ a+a) := by
    have hu : IsUnit (2 : ZMod M) := (ZMod.isUnit_iff_coprime 2 M).mpr hodd.coprime_two_left
    intro a b he
    exact hu.mul_right_injective (by simpa only [two_mul] using he)
  have hcount (D E : Finset (ZMod M)) (z : ZMod M) :
      Erdos66GroupRepBernoulli.count D E z=cyclicCount M D E z := by
    unfold Erdos66GroupRepBernoulli.count cyclicCount
    congr 1
    ext a
    simp
  have hmean (D E : Finset (ZMod M)) :
      Erdos66DenseGroupExtension.actualMean D E=actualMean M D E := by
    simp only [Erdos66DenseGroupExtension.actualMean,actualMean,ZMod.card]
  let δ := η*g/32
  let v : ℝ := (s : ℝ)*C₀.card/M
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδsmall : 32*δ ≤ η*g := by dsimp [δ]; linarith
  have hsM : (s : ℝ) ≤ M := by
    have hh := (hmin₀ C₀ hC₀).trans (Finset.card_le_univ C₀)
    simp only [ZMod.card] at hh
    exact_mod_cast hh
  have hM : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hvcard : v ≤ C₀.card := by
    apply (div_le_iff₀ hM).mpr
    have hh := mul_le_mul_of_nonneg_right hsM (Nat.cast_nonneg (α := ℝ) C₀.card)
    nlinarith
  have hl : 8*Real.log (2*((M+2)*M+1)) < δ^2*v := by
    dsimp [δ,v]
    nlinarith
  have hsmall := Erdos66DenseCyclicExtension.exponential_test_of_log ((M+2)*M+1)
    (by positivity) δ v hl
  have hh := Erdos66DensePaletteCompletion.exists_complete_palette hinj P₀ C₀ s η g δ v
    hη hη1 hg hg1 hδ hδsmall hP₀
    (by simpa only [Erdos66FinitePaletteGeometry.FlatPalette,Erdos66FinitePaletteGeometry.Flat,hcount,hmean] using hflat₀)
    hC₀ hmax₀ hmin₀
    (by simpa only [ZMod.card] using hlarge)
    (by simp only [v,ZMod.card]; exact le_rfl) hvcard
    (by simpa only [ZMod.card] using hsmall)
  simpa only [Erdos66FinitePaletteGeometry.Nested,Erdos66FinitePaletteGeometry.FlatPalette,
    Erdos66FinitePaletteGeometry.Flat,hcount,hmean,ZMod.card] using hh

end Erdos66DenseCyclicPaletteCompletion
