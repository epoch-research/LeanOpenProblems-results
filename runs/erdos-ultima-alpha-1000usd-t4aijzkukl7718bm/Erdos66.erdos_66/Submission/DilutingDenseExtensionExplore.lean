import Submission.DenseGroupExtensionExplore

/-! Density growth dilutes the old representation error. With a sufficiently
small sampling error this permits a finite dense extension WITHOUT inflating
the relative flatness tolerance. The mean threshold is still explicit. -/
namespace Erdos66DilutingDenseExtension
open Erdos66FiniteBernoulli Erdos66GroupRepBernoulli Erdos66DenseGroupExtension
open scoped Classical
variable {G : Type*} [Fintype G] [AddCommGroup G] [LinearOrder G]
set_option maxHeartbeats 2500000

lemma mean_retirement (A C : Finset G) (θ g : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hgap : (C.card : ℝ) ≤ (1-g)*expectedCard C θ) :
    actualMean C C ≤ (1-g)*nominalSelf C θ ∧
      actualMean A C ≤ (1-g)*nominalMixed A C θ := by
  have hb := expectedCard_bounds C θ hθ hθ1
  have ha := Nat.cast_nonneg (α := ℝ) C.card
  have hs : (C.card : ℝ)*C.card ≤ (1-g)*(expectedCard C θ)^2 := by
    calc
      _ ≤ (expectedCard C θ)*C.card := mul_le_mul_of_nonneg_right hb.2.2 ha
      _ ≤ (expectedCard C θ)*((1-g)*expectedCard C θ) := mul_le_mul_of_nonneg_left hgap hb.1
      _ = _ := by ring
  have hm := mul_le_mul_of_nonneg_left hgap (Nat.cast_nonneg (α := ℝ) A.card)
  have hn := (card_group_pos (G := G)).le
  constructor
  · convert div_le_div_of_nonneg_right hs hn using 1 <;> dsimp [actualMean,nominalSelf] <;> ring
  · convert div_le_div_of_nonneg_right hm hn using 1 <;> dsimp [actualMean,nominalMixed] <;> ring

lemma self_mean_error_retired (hinj : Function.Injective (fun a : G ↦ a+a))
    (C : Finset G) (θ η g : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hη : 0 ≤ η)
    (hgap : (C.card : ℝ) ≤ (1-g)*expectedCard C θ)
    (hC : ∀ z, |(count C C z : ℝ)-actualMean C C| ≤ η*actualMean C C) (z : G) :
    |selfMean z (extendProb C θ)-nominalSelf C θ| ≤ η*(1-g)*nominalSelf C θ+1 := by
  have hd := diagCorrection_bounds hinj z (extendProb C θ) (extendProb_bounds C θ hθ hθ1)
  have he : selfMean z (extendProb C θ)-nominalSelf C θ =
      (1-θ)^2*((count C C z : ℝ)-actualMean C C)+diagCorrection z (extendProb C θ) := by
    rw [self_extendProb,nominal_self_identity]; ring
  have hsq : (1-θ)^2 ≤ 1 := by nlinarith
  have hmean : 0 ≤ actualMean C C := by unfold actualMean; positivity
  rw [he]
  calc
    _ ≤ |(1-θ)^2*((count C C z : ℝ)-actualMean C C)|+|diagCorrection z (extendProb C θ)| := abs_add_le _ _
    _ = (1-θ)^2*|(count C C z : ℝ)-actualMean C C|+diagCorrection z (extendProb C θ) := by
      rw [abs_mul,abs_of_nonneg (sq_nonneg _),abs_of_nonneg hd.1]
    _ ≤ η*actualMean C C+1 := add_le_add
      (by simpa only [one_mul] using mul_le_mul hsq (hC z) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)) hd.2
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (mean_retirement C C θ g hθ hθ1 hgap).1 hη
      nlinarith

lemma mixed_mean_error_retired (A C : Finset G) (θ η g : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hη : 0 ≤ η)
    (hgap : (C.card : ℝ) ≤ (1-g)*expectedCard C θ)
    (hAC : ∀ z, |(count A C z : ℝ)-actualMean A C| ≤ η*actualMean A C) (z : G) :
    |(∑ a∈A, extendProb C θ (z-a))-nominalMixed A C θ| ≤ η*(1-g)*nominalMixed A C θ := by
  have he : (∑ a∈A, extendProb C θ (z-a))-nominalMixed A C θ =
      (1-θ)*((count A C z : ℝ)-actualMean A C) := by
    rw [mixed_extendProb,nominal_mixed_identity]; ring
  rw [he,abs_mul,abs_of_nonneg (sub_nonneg.mpr hθ1)]
  calc
    _ ≤ |(count A C z : ℝ)-actualMean A C| := mul_le_of_le_one_left (abs_nonneg _) (by linarith)
    _ ≤ η*actualMean A C := hAC z
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (mean_retirement A C θ g hθ hθ1 hgap).2 hη
      nlinarith

/-- One multiplicatively growing dense extension can preserve a fixed
flatness tolerance, rather than multiplying it by 28 at each step. -/
theorem exists_flatness_preserving_extension (hinj : Function.Injective (fun a : G ↦ a+a))
    (C : Finset G) (H : ℕ) (A : Fin H → Finset G) (θ η g δ v : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1)
    (hg : 0 < g) (hg1 : g ≤ 1) (hδ : 0 < δ) (hδsmall : 32*δ ≤ η*g)
    (hgap : (C.card : ℝ) ≤ (1-g)*expectedCard C θ)
    (hC : ∀ z, |(count C C z : ℝ)-actualMean C C| ≤ η*actualMean C C)
    (hAC : ∀ i z, |(count (A i) C z : ℝ)-actualMean (A i) C| ≤ η*actualMean (A i) C)
    (hlarge : 32 ≤ η*g*nominalSelf C θ)
    (hvs : v ≤ nominalSelf C θ) (hvm : ∀ i, v ≤ nominalMixed (A i) C θ)
    (hvc : v ≤ expectedCard C θ)
    (hsmall : 2*((H+1)*Fintype.card G+1)*Real.exp (-δ^2*v/8) < 1) :
    ∃ B : Finset G, C ⊆ B ∧
      (∀ z, |(count B B z : ℝ)-actualMean B B| < η*actualMean B B) ∧
      (∀ i z, |(count (A i) B z : ℝ)-actualMean (A i) B| < η*actualMean (A i) B) ∧
      |(B.card : ℝ)-expectedCard C θ| < δ*expectedCard C θ := by
  have hδ1 : δ ≤ 1/2 := by nlinarith [mul_le_mul hη1 hg1 hg.le (by norm_num : (0 : ℝ) ≤ 1)]
  have hsn := (nominal_nonneg C C θ hθ hθ1).1
  have hmn := fun i ↦ (nominal_nonneg (A i) C θ hθ hθ1).2
  have hself := self_mean_error_retired hinj C θ η g hθ hθ1 hη.le hgap hC
  have hmix := fun i ↦ mixed_mean_error_retired (A i) C θ η g hθ hθ1 hη.le hgap (hAC i)
  obtain ⟨B,hCB,hB,hAB,hcard⟩ := exists_extension_about_means C H A θ δ v
    ((1+η)*nominalSelf C θ+1) (expectedCard C θ)
    (fun i ↦ (1+η)*nominalMixed (A i) C θ) hθ hθ1 hδ (by linarith)
    (fun z ↦ by have := (abs_le.mp (hself z)).2; have := mul_nonneg (mul_nonneg hη.le hg.le) hsn; nlinarith)
    (fun i z ↦ by have := (abs_le.mp (hmix i z)).2; have := mul_nonneg (mul_nonneg hη.le hg.le) (hmn i); nlinarith)
    le_rfl (by nlinarith) (fun i ↦ by have := hmn i; have := hvm i; nlinarith) hvc hsmall
  refine ⟨B,hCB,?_,?_,hcard⟩
  · intro z
    have hs := cardinality_mean_stability C B C θ δ hθ hθ1 hδ.le hδ1 hcard.le
    have hnom := (abs_sub_le (count B B z : ℝ) (selfMean z (extendProb C θ)) (nominalSelf C θ)).trans_lt
      (add_lt_add_of_lt_of_le (hB z) (hself z))
    have herr := (abs_sub_le (count B B z : ℝ) (nominalSelf C θ) (actualMean B B)).trans_lt
      (add_lt_add_of_lt_of_le hnom (by simpa only [abs_sub_comm] using hs.1))
    have hlow := (abs_le.mp hs.1).1
    have hlow' := mul_le_mul_of_nonneg_left hlow hη.le
    have hbudget := mul_le_mul_of_nonneg_right hδsmall hsn
    have hηδ := mul_le_mul_of_nonneg_right hη1 (mul_nonneg hδ.le hsn)
    nlinarith
  · intro i z
    have hs := cardinality_mean_stability (A i) B C θ δ hθ hθ1 hδ.le hδ1 hcard.le
    have hnom := (abs_sub_le (count (A i) B z : ℝ) (∑ a∈A i, extendProb C θ (z-a))
      (nominalMixed (A i) C θ)).trans_lt (add_lt_add_of_lt_of_le (hAB i z) (hmix i z))
    have herr := (abs_sub_le (count (A i) B z : ℝ) (nominalMixed (A i) C θ) (actualMean (A i) B)).trans_lt
      (add_lt_add_of_lt_of_le hnom (by simpa only [abs_sub_comm] using hs.2.2.1))
    have hlow := (abs_le.mp hs.2.2.1).1
    have hlow' := mul_le_mul_of_nonneg_left hlow hη.le
    have hν := hmn i
    have hnon := mul_nonneg hδ.le hν
    have hbudget := mul_le_mul_of_nonneg_right hδsmall (hmn i)
    have hηδ := mul_le_mul_of_nonneg_right hη1 (mul_nonneg hδ.le (hmn i))
    nlinarith

/-- The density-gap condition ensures genuine cardinality progress; a
hypothetical iteration therefore cannot keep returning the same finite set. -/
lemma extension_card_strict (B C : Finset G) (θ g δ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hδg : δ ≤ g)
    (hgap : (C.card : ℝ) ≤ (1-g)*expectedCard C θ)
    (hcard : |(B.card : ℝ)-expectedCard C θ| < δ*expectedCard C θ) : C.card < B.card := by
  have hb := (expectedCard_bounds C θ hθ hθ1).1
  have hlo := (abs_lt.mp hcard).1
  have hm := mul_le_mul_of_nonneg_right hδg hb
  have hh : (C.card : ℝ) < B.card := by linarith
  exact_mod_cast hh

end Erdos66DilutingDenseExtension
