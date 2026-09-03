import Submission.FinitePaletteGeometryExplore

/-! Uniform one-step enlargement of a nested finite palette. The test budget
uses only the ambient group size, not an unknown iteration length. -/
namespace Erdos66DensePaletteStep
open Erdos66GroupRepBernoulli Erdos66DenseGroupExtension
  Erdos66DilutingDenseExtension Erdos66FinitePaletteGeometry
open scoped Classical
variable {G : Type*} [Fintype G] [AddCommGroup G] [LinearOrder G]
set_option maxHeartbeats 2500000

noncomputable def growthProb (C : Finset G) (g : ℝ) : ℝ :=
  ((C.card : ℝ)/(1-g)-C.card)/(Fintype.card G-C.card)

lemma growthProb_spec (C : Finset G) (g : ℝ) (hg : 0 < g) (hg1 : g ≤ 1/4)
    (hC : (C.card : ℝ) ≤ (1-g)*Fintype.card G) :
    0 ≤ growthProb C g ∧ growthProb C g ≤ 1 ∧
      expectedCard C (growthProb C g)=(C.card : ℝ)/(1-g) := by
  have hN := card_group_pos (G := G)
  have ha := Nat.cast_nonneg (α := ℝ) C.card
  have h1g : 0 < 1-g := by linarith
  have hden : 0 < (Fintype.card G : ℝ)-C.card := by nlinarith [mul_pos hg hN]
  have hab : (C.card : ℝ) ≤ (C.card : ℝ)/(1-g) := by
    apply (le_div_iff₀ h1g).mpr
    nlinarith [mul_nonneg hg.le ha]
  have hbM : (C.card : ℝ)/(1-g) ≤ Fintype.card G :=
    (div_le_iff₀ h1g).mpr (by nlinarith)
  refine ⟨div_nonneg (sub_nonneg.mpr hab) hden.le,?_,?_⟩
  · exact (div_le_one hden).mpr (by linarith)
  · have he := div_mul_cancel₀ ((C.card : ℝ)/(1-g)-C.card) hden.ne'
    change growthProb C g*((Fintype.card G : ℝ)-C.card)=(C.card : ℝ)/(1-g)-C.card at he
    unfold expectedCard
    nlinarith

lemma growth_ratio (a g δ : ℝ) (ha : 0 ≤ a) (hg : 0 ≤ g) (hg1 : g ≤ 1/4)
    (hδ : δ ≤ g) : (1+δ)*(a/(1-g)) ≤ (1+4*g)*a := by
  have h1g : 0 < 1-g := by linarith
  rw [←mul_div_assoc]
  apply (div_le_iff₀ h1g).mpr
  have hg2 : 4*g^2 ≤ g := by nlinarith
  have hb : 1+δ ≤ (1+4*g)*(1-g) := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hb ha
  nlinarith

lemma near_full_ratio (C : Finset G) (g : ℝ) (hg : 0 ≤ g) (hg1 : g ≤ 1/4)
    (hC : (1-g)*(Fintype.card G : ℝ) ≤ C.card) :
    (Fintype.card G : ℝ) ≤ (1+4*g)*C.card := by
  have hN := (card_group_pos (G := G)).le
  have hfactor : 1 ≤ (1+4*g)*(1-g) := by nlinarith
  have h₁ := mul_le_mul_of_nonneg_right hfactor hN
  have h₂ := mul_le_mul_of_nonneg_left hC (show 0 ≤ 1+4*g by linarith)
  nlinarith

/-- The same initial lower means and the ambient-size test budget suffice at
every enlargement of a nested palette. -/
theorem palette_step (hinj : Function.Injective (fun a : G ↦ a+a))
    (P : Finset (Finset G)) (C₀ C : Finset G) (s : ℕ) (η g δ v : ℝ)
    (hη : 0 < η) (hη1 : η ≤ 1) (hg : 0 < g) (hg1 : g ≤ 1/4)
    (hδ : 0 < δ) (hδsmall : 32*δ ≤ η*g)
    (hP : Nested P) (hflat : FlatPalette η P) (hC₀ : C₀∈P) (hC : C∈P)
    (hmax : ∀ D∈P, D ⊆ C) (hmin : ∀ D∈P, s ≤ D.card)
    (hnot : (Finset.univ : Finset G) ∉ P)
    (hlarge : 32 ≤ η*g*((C₀.card : ℝ)^2/Fintype.card G))
    (hvmean : v ≤ (s : ℝ)*C₀.card/Fintype.card G) (hvcard : v ≤ C₀.card)
    (hsmall : 2*((Fintype.card G+2)*Fintype.card G+1)*Real.exp (-δ^2*v/8) < 1) :
    ∃ B : Finset G, B∉P ∧ (∀ D∈P, D ⊆ B) ∧
      Flat η B B ∧ (∀ D∈P, Flat η D B) ∧ (B.card : ℝ) ≤ (1+4*g)*C.card := by
  by_cases hnear : (1-g)*(Fintype.card G : ℝ) ≤ C.card
  · refine ⟨Finset.univ,hnot,fun D hD ↦ Finset.subset_univ D,flat_full η hη.le _,
      fun D hD ↦ flat_full η hη.le D,?_⟩
    simpa only [Finset.card_univ] using near_full_ratio C g hg.le hg1 hnear
  have hfar : (C.card : ℝ) ≤ (1-g)*Fintype.card G := (lt_of_not_ge hnear).le
  let θ := growthProb C g
  obtain ⟨hθ,hθ1,hb⟩ := growthProb_spec C g hg hg1 hfar
  have hgap : (C.card : ℝ) ≤ (1-g)*expectedCard C θ := by
    rw [hb]
    have hh : 1-g ≠ 0 := by linarith
    rw [mul_div_cancel₀ _ hh]
  have hδg : δ ≤ g := by
    have hh := mul_le_mul_of_nonneg_right hη1 hg.le
    nlinarith
  let A : Fin P.card → Finset G := fun i ↦ (P.equivFin.symm i).val
  have hAmem (i : Fin P.card) : A i∈P := (P.equivFin.symm i).property
  have hAsurj (D : Finset G) (hD : D∈P) : ∃ i, A i=D := by
    refine ⟨P.equivFin ⟨D,hD⟩,?_⟩
    simp only [A,Equiv.symm_apply_apply]
  have hbase : (C₀.card : ℝ) ≤ expectedCard C θ := by
    have hc : (C₀.card : ℝ) ≤ C.card := by exact_mod_cast Finset.card_le_card (hmax C₀ hC₀)
    exact hc.trans (expectedCard_bounds C θ hθ hθ1).2.2
  have hbase0 := Nat.cast_nonneg (α := ℝ) C₀.card
  have hb0 := (expectedCard_bounds C θ hθ hθ1).1
  have hs₀ : (s : ℝ) ≤ C₀.card := by exact_mod_cast hmin C₀ hC₀
  have hN := (card_group_pos (G := G)).le
  have hselflower : (C₀.card : ℝ)^2/Fintype.card G ≤ nominalSelf C θ := by
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hbase0 hbase 2) hN
  have hvlower : (s : ℝ)*C₀.card/Fintype.card G ≤ (C₀.card : ℝ)^2/Fintype.card G := by
    apply div_le_div_of_nonneg_right _ hN
    simpa only [pow_two] using mul_le_mul_of_nonneg_right hs₀ hbase0
  have hvself : v ≤ nominalSelf C θ := hvmean.trans (hvlower.trans hselflower)
  have hvmix (i : Fin P.card) : v ≤ nominalMixed (A i) C θ := by
    have hsi : (s : ℝ) ≤ (A i).card := by exact_mod_cast hmin (A i) (hAmem i)
    apply hvmean.trans
    apply div_le_div_of_nonneg_right _ hN
    exact mul_le_mul hsi hbase hbase0 (Nat.cast_nonneg _)
  have hlarge' : 32 ≤ η*g*nominalSelf C θ := hlarge.trans
    (mul_le_mul_of_nonneg_left hselflower (mul_nonneg hη.le hg.le))
  have hsmall' : 2*((P.card+1)*Fintype.card G+1)*Real.exp (-δ^2*v/8) < 1 := by
    have hp : P.card+1 ≤ Fintype.card G+2 := by have := nested_card_le hP; omega
    have hnat : (P.card+1)*Fintype.card G+1 ≤ (Fintype.card G+2)*Fintype.card G+1 := by gcongr
    have hcoef : (2 : ℝ)*((P.card+1)*Fintype.card G+1) ≤
        2*((Fintype.card G+2)*Fintype.card G+1) := by exact_mod_cast Nat.mul_le_mul_left 2 hnat
    have hh := mul_le_mul_of_nonneg_right hcoef (Real.exp_pos (-δ^2*v/8)).le
    exact hh.trans_lt hsmall
  obtain ⟨B,hCB,hBB,hAB,hcard⟩ := exists_flatness_preserving_extension hinj C P.card A θ η g δ v
    hθ hθ1 hη hη1 hg (by linarith) hδ hδsmall hgap (hflat C hC C hC)
    (fun i ↦ hflat (A i) (hAmem i) C hC) hlarge' hvself hvmix (hvcard.trans hbase) hsmall'
  have hstrict := extension_card_strict B C θ g δ hθ hθ1 hδg hgap hcard
  refine ⟨B,?_,fun D hD ↦ (hmax D hD).trans hCB,fun z ↦ (hBB z).le,?_,?_⟩
  · intro hBP
    have hh := Finset.card_le_card (hmax B hBP)
    omega
  · intro D hD
    obtain ⟨i,rfl⟩ := hAsurj D hD
    exact fun z ↦ (hAB i z).le
  · have hup := (abs_lt.mp hcard).2
    have hBcard : (B.card : ℝ) ≤ (1+δ)*expectedCard C θ := by linarith
    rw [hb] at hBcard
    exact hBcard.trans (growth_ratio C.card g δ (Nat.cast_nonneg _) hg.le hg1 hδg)

end Erdos66DensePaletteStep
