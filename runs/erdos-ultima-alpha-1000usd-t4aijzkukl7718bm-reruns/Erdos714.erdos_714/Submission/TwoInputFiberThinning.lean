import Submission.TranslatedNormFibers

/-!
A block cover for translated fibers with arbitrary TWO-INPUT shift and level
functions. It bounds arbitrary edge thinnings, not just vertex selections.
This is a construction obstruction, not a solution of Erdős714.
-/
noncomputable section
open Classical SimpleGraph Finset
set_option maxHeartbeats 2000000
namespace Erdos714TwoInputFibers
variable {A B G T : Type*} [Fintype A] [Fintype B] [Fintype G] [Fintype T] [AddCommGroup G]

def graph (ν : G → T) (f : A → B → G) (g : A → B → T) :
    SimpleGraph ((A × G) ⊕ (B × G)) :=
  Erdos714Tensor.incidence fun x y => ν (x.2+y.2-f x.1 y.1)=g x.1 y.1

/-- Fix a row label, a translated center, and a level. The first fiber bound
controls rows; the second controls columns. No algebraic structure on labels
or the level type is required. -/
theorem fourth_power (ν : G → T) (f : A → B → G) (g : A → B → T)
    (d : ℕ) (hν : ∀ r, (univ.filter (fun z => ν z=r)).card ≤ d)
    (hg : ∀ a r, (univ.filter (fun b => g a b=r)).card ≤ d)
    (H : SimpleGraph ((A × G) ⊕ (B × G))) (hH : H ≤ graph ν f g)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    H.edgeFinset.card^4 ≤
      10368*(Fintype.card A*Fintype.card G*Fintype.card T)^4*d^7 := by
  let I := A × G × T
  let L (p : I) : Finset ((A × G) ⊕ (B × G)) :=
    (univ.filter (fun z => ν z=p.2.2)).image (fun z => Sum.inl (p.1,p.2.1+z))
  let R (p : I) : Finset ((A × G) ⊕ (B × G)) :=
    (univ.filter (fun b => g p.1 b=p.2.2)).image (fun b => Sum.inr (b,f p.1 b-p.2.1))
  have hsize (p : I) : (L p ∪ R p).card ≤ 2*d := by
    have hl : (L p).card ≤ d := card_image_le.trans (hν p.2.2)
    have hr : (R p).card ≤ d := card_image_le.trans (hg p.1 p.2.2)
    have h := card_union_le (L p) (R p)
    omega
  have hf (x : A × G) (y : B × G) (h : ν (x.2+y.2-f x.1 y.1)=g x.1 y.1) :
      ∃ p : I, Sum.inl x ∈ L p ∪ R p ∧ Sum.inr y ∈ L p ∪ R p := by
    let w := f x.1 y.1-y.2
    refine ⟨(x.1,w,g x.1 y.1),mem_union_left _ (mem_image.mpr ⟨x.2-w,?_,?_⟩),
      mem_union_right _ (mem_image.mpr ⟨y.1,?_,?_⟩)⟩
    · apply mem_filter.mpr
      refine ⟨mem_univ _,?_⟩
      change ν (x.2-w)=g x.1 y.1
      rw [show x.2-w=x.2+y.2-f x.1 y.1 by dsimp [w]; abel]
      exact h
    · change Sum.inl (x.1,w+(x.2-w))=Sum.inl x
      simp
    · exact mem_filter.mpr ⟨mem_univ _,rfl⟩
    · change Sum.inr (y.1,f x.1 y.1-w)=Sum.inr y
      simp [w]
  have hcover : ∀ v w, H.Adj v w → ∃ p : I, v ∈ L p ∪ R p ∧ w ∈ L p ∪ R p := by
    intro v w hvw
    have h := hH hvw
    cases v with
    | inl x =>
      cases w with
      | inl y => exact False.elim h
      | inr y => exact hf x y h
    | inr y =>
      cases w with
      | inr x => exact False.elim h
      | inl x =>
        obtain ⟨p,hx,hy⟩ := hf x y h
        exact ⟨p,hy,hx⟩
  have h := Erdos714BlockThinning.fourth_power_of_block_cover H hfree
    (fun p : I => L p ∪ R p) d hsize hcover
  simpa only [I,Fintype.card_prod,mul_assoc] using h

#print axioms fourth_power
end Erdos714TwoInputFibers
