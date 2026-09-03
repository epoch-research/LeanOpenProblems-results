import Submission.DensePaletteStepExplore

/-! Conditional completion of a nested mixed-flat finite palette. It reaches
the full group and leaves no multiplicative cardinality gaps above the old
maximum. The original natural-number conjecture is not concluded here. -/
namespace Erdos66DensePaletteCompletion
open Erdos66GroupRepBernoulli Erdos66DenseGroupExtension
  Erdos66FinitePaletteGeometry Erdos66DensePaletteStep
open scoped Classical
variable {G : Type*} [Fintype G] [AddCommGroup G] [LinearOrder G]
set_option maxHeartbeats 2500000

/-- A single ambient-size concentration budget controls the whole finite
completion, not merely one preselected extension step. -/
theorem exists_complete_palette (hinj : Function.Injective (fun a : G ↦ a+a))
    (P₀ : Finset (Finset G)) (C₀ : Finset G) (s : ℕ) (η g δ v : ℝ)
    (hη : 0 < η) (hη1 : η ≤ 1) (hg : 0 < g) (hg1 : g ≤ 1/4)
    (hδ : 0 < δ) (hδsmall : 32*δ ≤ η*g)
    (hP₀ : Nested P₀) (hflat₀ : FlatPalette η P₀) (hC₀ : C₀∈P₀)
    (hmax₀ : ∀ D∈P₀, D ⊆ C₀) (hmin₀ : ∀ D∈P₀, s ≤ D.card)
    (hlarge : 32 ≤ η*g*((C₀.card : ℝ)^2/Fintype.card G))
    (hvmean : v ≤ (s : ℝ)*C₀.card/Fintype.card G) (hvcard : v ≤ C₀.card)
    (hsmall : 2*((Fintype.card G+2)*Fintype.card G+1)*Real.exp (-δ^2*v/8) < 1) :
    ∃ P : Finset (Finset G), P₀ ⊆ P ∧ Nested P ∧ FlatPalette η P ∧
      (Finset.univ : Finset G)∈P ∧ P.card ≤ Fintype.card G+1 ∧
      ∀ x : ℝ, (C₀.card : ℝ) ≤ x → x ≤ Fintype.card G →
        ∃ D∈P, x ≤ (D.card : ℝ) ∧ (D.card : ℝ) ≤ (1+4*g)*x := by
  let R := 1+4*g
  have hR : 1 ≤ R := by dsimp [R]; linarith
  let Good (P : Finset (Finset G)) : Prop :=
    P₀ ⊆ P ∧ Nested P ∧ FlatPalette η P ∧ (∀ D∈P, s ≤ D.card) ∧ Covers C₀ R P
  let Q : Finset (Finset (Finset G)) := Finset.univ.filter Good
  have hmem (P : Finset (Finset G)) : P∈Q ↔ Good P := by simp [Q]
  have hinit : Good P₀ :=
    ⟨Finset.Subset.refl P₀,hP₀,hflat₀,hmin₀,covers_initial hR hC₀ hmax₀⟩
  obtain ⟨P,hPQ,hmax⟩ := Q.exists_max_image Finset.card ⟨P₀,(hmem P₀).mpr hinit⟩
  obtain ⟨hsub,hP,hflat,hmin,hcover⟩ := (hmem P).mp hPQ
  have hC₀P : C₀∈P := hsub hC₀
  have hfull : (Finset.univ : Finset G)∈P := by
    by_contra hnot
    obtain ⟨C,hC,hCmax⟩ := nested_max hP ⟨C₀,hC₀P⟩
    obtain ⟨B,hBP,hBsub,hBB,hPB,hBcard⟩ := palette_step hinj P C₀ C s η g δ v
      hη hη1 hg hg1 hδ hδsmall hP hflat hC₀P hC hCmax hmin hnot
      hlarge hvmean hvcard hsmall
    have hinsert : Good (insert B P) := by
      refine ⟨?_,nested_insert hP hBsub,flatPalette_insert hflat hBB hPB,?_,?_⟩
      · intro D hD
        exact Finset.mem_insert_of_mem (hsub hD)
      · intro D hD
        rcases Finset.mem_insert.mp hD with he | hD
        · subst D
          exact (hmin C₀ hC₀P).trans (Finset.card_le_card (hBsub C₀ hC₀P))
        · exact hmin D hD
      · exact covers_insert (by linarith : 0 ≤ R) hcover hC hBcard
    have hh := hmax (insert B P) ((hmem _).mpr hinsert)
    rw [Finset.card_insert_of_notMem hBP] at hh
    omega
  refine ⟨P,hsub,hP,hflat,hfull,nested_card_le hP,?_⟩
  intro x hx hxM
  exact hcover x hx ⟨Finset.univ,hfull,by simpa only [Finset.card_univ] using hxM⟩

end Erdos66DensePaletteCompletion
