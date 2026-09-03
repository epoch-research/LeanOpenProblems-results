import Submission.IntegerFiniteSwapAlgebraExplore
import Submission.CellSidonSelectionExplore

/-! Selecting equal-cardinality deletions and insertions with a simultaneous
signed collateral bound. Candidate availability is an explicit hypothesis. -/
namespace Erdos66FiniteSwapSelection
open Erdos66IntegerFiniteSwapAlgebra Erdos66CellSidonSelection Erdos66UniformSelection
  Erdos66OriginRepair Erdos66FiniteRepair Erdos66SymmetricSidon
open scoped Classical
set_option maxHeartbeats 2200000
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

noncomputable def swapHits (A : Finset ℤ) (d f : α → ℤ) (z : ℤ) : Finset α :=
  Finset.univ.filter (fun a ↦ z-d a ∈ A ∨ z-f a ∈ A)

omit [Fintype α] [Nonempty α] in
lemma image_mixed_le_hits {ι : Type*} [Fintype ι]
    (A : Finset ℤ) (g : α → ℤ) (S : Finset α) (ω : ι → α) (z : ℤ)
    (hS : ∀ a, z-g a ∈ A → a ∈ S) :
    (pairCount (Finset.univ.image (g ∘ ω)) A z : ℝ) ≤ hits S ω := by
  have hh := pairCount_image_le (g ∘ ω) A z
  have hsub : Finset.univ.filter (fun i : ι ↦ z-(g ∘ ω) i ∈ A) ⊆
      Finset.univ.filter (fun i ↦ ω i ∈ S) := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hS _ (Finset.mem_filter.mp hi).2⟩
  have hb : (pairCount (Finset.univ.image (g ∘ ω)) A z : ℝ) ≤
      (Finset.univ.filter (fun i : ι ↦ ω i ∈ S)).card := by
    exact_mod_cast hh.trans (Finset.card_le_card hsub)
  simpa only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,hits] using hb

/-- The new positions are Sidon; the old positions are distinct. Their old
partners at the repair center are absent, whereas each insertion completes
one old/new pair. -/
theorem exists_finite_swap (A : Finset ℤ) (n : ℤ) (d f : α → ℤ)
    (hf : Function.Injective f) (H : ℕ)
    (hfiber : ∀ r, (Finset.univ.filter (fun a ↦ d a=r)).card ≤ H)
    (hdA : ∀ a, d a ∈ A) (hfA : ∀ a, f a ∉ A)
    (hdu : ∀ a, n<2*d a) (hfu : ∀ a, n<2*f a)
    (hdelete : ∀ a, n-d a ∉ A) (hpartner : ∀ a, n-f a ∈ A)
    (m : ℕ) (T : Finset ℤ) (K R t : ℝ)
    (hS : ∀ z ∈ T, (swapHits A d f z).card ≤ K) (ht : 0<t)
    (hsmall : ((m : ℝ)^4+(m : ℝ)^2*H)/Fintype.card α+
      T.card*Real.exp ((m : ℝ)*Real.exp t*K/Fintype.card α-t*R)<1) :
    ∃ ω : Fin m → α, Function.Injective ω ∧ Function.Injective (d ∘ ω) ∧
      let D := Finset.univ.image (d ∘ ω)
      let F := Finset.univ.image (f ∘ ω)
      D ⊆ A ∧ Disjoint A F ∧ D.card=m ∧ F.card=m ∧
      (swap A D F).card=A.card ∧
      pairCount (swap A D F) (swap A D F) n=pairCount A A n+2*m ∧
      (∀ z : ℤ, pairCount F F z ≤ 2) ∧
      ∀ z ∈ T, |(pairCount (swap A D F) (swap A D F) z : ℝ)-pairCount A A z|<4*R+2 := by
  classical
  let cell : Unit → α → ℤ := fun _ a ↦ d a
  have hcell : ∀ b r, (Finset.univ.filter (fun a ↦ cell b a=r)).card ≤ H :=
    by intro b r; simpa only using hfiber r
  have hsep : ∀ a, Function.Injective (fun b ↦ cell b a) := by
    intro a b c he
    exact Subsingleton.elim _ _
  have hsmall' : ((Fintype.card (Fin m) : ℝ)^4+
      (Fintype.card (Fin m) : ℝ)^2*(Fintype.card Unit : ℝ)^2*H+
      Fintype.card (Fin m)*(∅ : Finset α).card)/Fintype.card α+
      T.card*Real.exp ((Fintype.card (Fin m) : ℝ)*Real.exp t*K/Fintype.card α-t*R)<1 := by
    simpa only [Fintype.card_fin,Fintype.card_unit,Finset.card_empty,Nat.cast_one,
      Nat.cast_zero,one_pow,mul_one,mul_zero,add_zero] using hsmall
  obtain ⟨ω,hω,_,hcellω,hsidon,hhits⟩ :=
    exists_cell_sidon_avoid_and_hits (ι := Fin m) (α := α) f hf cell H
      (by intro b r; convert hcell b r using 1; congr 1; ext a; simp) hsep ∅ T
      (swapHits A d f) K R t hS ht hsmall'
  have hdω : Function.Injective (d ∘ ω) := by
    intro i j he
    have hh : (i,())=(j,()) := hcellω he
    exact congrArg Prod.fst hh
  let D := Finset.univ.image (d ∘ ω)
  let F := Finset.univ.image (f ∘ ω)
  have hD : D ⊆ A := by
    intro a ha
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    exact hdA _
  have hF : Disjoint A F := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hb
    exact hfA _ ha
  have hDcard : D.card=m := by
    dsimp only [D]
    rw [Finset.card_image_of_injective _ hdω,Finset.card_univ,Fintype.card_fin]
  have hFcard : F.card=m := by
    dsimp only [F]
    rw [Finset.card_image_of_injective _ (hf.comp hω),Finset.card_univ,Fintype.card_fin]
  have hFsidon : IsSidon F := by
    intro a ha b hb c hc e he hsum
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp he
    rcases hsidon i j k l hsum with ⟨hik,hjl⟩ | ⟨hil,hjk⟩
    · exact Or.inl ⟨congrArg (f ∘ ω) hik,congrArg (f ∘ ω) hjl⟩
    · exact Or.inr ⟨congrArg (f ∘ ω) hil,congrArg (f ∘ ω) hjk⟩
  refine ⟨ω,hω,hdω,hD,hF,hDcard,hFcard,
    swap_card A D F hD hF (hDcard.trans hFcard.symm),?_,sidon_self_le_two hFsidon,?_⟩
  · have hcenter : pairCount (swap A D F) (swap A D F) n=pairCount A A n+2*F.card := by
      apply swap_center A D F n hD hF
      · intro a ha
        obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
        exact hdelete _
      · intro a ha
        obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
        apply Finset.mem_sdiff.mpr
        refine ⟨hpartner _,?_⟩
        intro hn
        obtain ⟨j,_,he⟩ := Finset.mem_image.mp hn
        have hh := hdu (ω j)
        have hh' := hfu (ω i)
        dsimp only [Function.comp_apply] at he
        omega
      · intro a ha
        obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
        exact hfu _
    simpa only [hFcard] using hcenter
  · intro z hz
    have hdcount := image_mixed_le_hits A d (swapHits A d f z) ω z
      (fun a ha ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inl ha⟩)
    have hfcount := image_mixed_le_hits A f (swapHits A d f z) ω z
      (fun a ha ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inr ha⟩)
    have hself : (pairCount F F z : ℝ) ≤ 2 := by exact_mod_cast sidon_self_le_two hFsidon z
    have hb := swap_error_bound A D F hD hF z
    have hh := hhits z hz
    change (pairCount D A z : ℝ) ≤ _ at hdcount
    change (pairCount F A z : ℝ) ≤ _ at hfcount
    linarith

end Erdos66FiniteSwapSelection
