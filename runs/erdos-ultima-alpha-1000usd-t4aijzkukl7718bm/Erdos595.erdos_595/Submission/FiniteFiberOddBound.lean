import Submission.HigherConeOddBound

/-!
Finite-fiber bundles with a three-colorable bipartite-index template.
A finite odd-walk bound on the index graph ensures K4-freeness at each
fixed right-adjoint stage. No non-coverability claim is made here.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595FiniteFiberOddBound
open Erdos595HigherConeOddBound Erdos595ArcAdjoint
universe u
variable {I S A : Type u}

/-- Inside each fiber use F; between adjacent index fibers use P. -/
def bundle (F : SimpleGraph S) (P : S → S → Prop) (hP : Symmetric P)
    (B : SimpleGraph I) : SimpleGraph (I × S) where
  Adj x y := (x.1 = y.1 ∧ F.Adj x.2 y.2) ∨ (B.Adj x.1 y.1 ∧ P x.2 y.2)
  symm := fun _ _ h => h.elim (fun h => Or.inl ⟨h.1.symm,h.2.symm⟩)
    (fun h => Or.inr ⟨h.1.symm,hP h.2⟩)
  loopless := fun x h => h.elim (fun h => F.loopless _ h.2) (fun h => B.loopless _ h.1)

/-- The two fiber colorings used on the two sides of a bipartite index graph. -/
structure Template (F : SimpleGraph S) (P : S → S → Prop) where
  c₀ : F.Coloring (Fin 3)
  c₁ : F.Coloring (Fin 3)
  cross : ∀ a b, P a b → c₀ a ≠ c₁ b

lemma three_of_two (F : SimpleGraph S) (P : S → S → Prop) (hP : Symmetric P)
    (t : Template F P) (B : SimpleGraph I) (hB : B.Colorable 2) :
    (bundle F P hP B).Colorable 3 := by
  obtain ⟨c⟩ := hB
  let d : I × S → Fin 3 := fun x => if c x.1 = 0 then t.c₀ x.2 else t.c₁ x.2
  refine ⟨SimpleGraph.Coloring.mk d ?_⟩
  intro x y hxy he
  rcases hxy with ⟨hidx,hxy⟩ | ⟨hidx,hxy⟩
  · by_cases hx : c x.1 = 0
    · have hy : c y.1 = 0 := hidx ▸ hx
      exact t.c₀.valid hxy (by simpa [d,hx,hy] using he)
    · have hy : c y.1 ≠ 0 := hidx ▸ hx
      exact t.c₁.valid hxy (by simpa [d,hx,hy] using he)
  · have hc := c.valid hidx
    by_cases hx : c x.1 = 0
    · have hy : c y.1 ≠ 0 := fun hy => hc (hx.trans hy.symm)
      exact t.cross _ _ hxy (by simpa [d,hx,hy] using he)
    · have hy : c y.1 = 0 := by
        have hcx := (c x.1).isLt
        have hcy := (c y.1).isLt
        simp only [ne_eq,Fin.ext_iff] at hc hx ⊢
        omega
      exact t.cross _ _ (hP hxy) (by simpa [d,hx,hy] using he.symm)

/-- Only the finite image of the source in the index graph needs to be
bipartite. Equal indices are colored identically, even if different source
vertices map to them. -/
lemma three_of_finite_hom (H : SimpleGraph A) [Fintype A]
    (F : SimpleGraph S) (P : S → S → Prop) (hP : Symmetric P)
    (t : Template F P) (B : SimpleGraph I)
    (hB : NoShortOdd B (2 * Fintype.card A))
    (f : H →g bundle F P hP B) : H.Colorable 3 := by
  classical
  let g : A → I := fun a => (f a).1
  let T : Set I := Set.range g
  haveI : Fintype T := Set.fintypeRange g
  have hcard : Fintype.card T ≤ Fintype.card A := Fintype.card_range_le g
  have hT : NoShortOdd (B.induce T) (2 * Fintype.card T) := by
    intro a w hw ho
    apply hB a.val (w.map (SimpleGraph.Embedding.induce T).toHom)
    · simpa only [SimpleGraph.Walk.length_map] using
        hw.trans_le (Nat.mul_le_mul_left 2 hcard)
    · simpa only [SimpleGraph.Walk.length_map] using ho
  have hc := three_of_two F P hP t (B.induce T) (two_of_no_short_odd _ hT)
  let f' : H →g bundle F P hP (B.induce T) :=
    { toFun a := (⟨g a,⟨a,rfl⟩⟩,(f a).2)
      map_rel' := by
        intro a b hab
        rcases f.map_adj hab with hab | hab
        · exact Or.inl ⟨Subtype.ext hab.1,hab.2⟩
        · exact Or.inr hab }
  obtain ⟨c⟩ := hc
  exact ⟨c.comp f'⟩

/-- The same finite bound as for cones works for every such fiber template. -/
theorem cliqueFree (n : ℕ) (F : SimpleGraph S) (P : S → S → Prop)
    (hP : Symmetric P) (t : Template F P) (B : SimpleGraph I)
    (hB : NoShortOdd B (bound.{u} n)) :
    (((rightP^[n]) ⟨I × S,bundle F P hP B⟩).2).CliqueFree 4 := by
  classical
  haveI := iter_finite n four
  letI : Fintype (((arcP^[n]) four).1) := Fintype.ofFinite _
  by_contra hn
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree hn
  let f : Hom four ((rightP^[n]) ⟨I × S,bundle F P hP B⟩) :=
    e.toHom.comp ⟨ULift.down,by intro a b hab he; exact hab (ULift.ext _ _ he)⟩
  obtain ⟨g⟩ := (iter_hom_iff n four ⟨I × S,bundle F P hP B⟩).mpr ⟨f⟩
  apply four_not_three
  apply iter_three n four
  apply three_of_finite_hom (((arcP^[n]) four).2) F P hP t B _ g
  simpa only [bound,Nat.card_eq_fintype_card] using hB

namespace Prism

/-- The triangular prism: two triangles and a matching between them. -/
def fiber : SimpleGraph (Fin 6) where
  Adj a b := a ≠ b ∧ (a.val / 3 = b.val / 3 ∨ a.val % 3 = b.val % 3)
  symm := fun _ _ h => ⟨h.1.symm,h.2.imp Eq.symm Eq.symm⟩
  loopless := fun _ h => h.1 rfl

instance : DecidableRel fiber.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

def label : Fin 6 → Fin 4 := ![0,1,2,1,0,3]
def cross (a b : Fin 6) : Prop := label a = label b

lemma cross_symm : Symmetric cross := fun _ _ h => h.symm

private def c₀ : Fin 6 → Fin 3 := ![0,1,2,1,2,0]
private def c₁ : Fin 6 → Fin 3 := ![1,2,0,0,1,2]

private lemma c₀_valid : ∀ a b, fiber.Adj a b → c₀ a ≠ c₀ b := by decide +kernel
private lemma c₁_valid : ∀ a b, fiber.Adj a b → c₁ a ≠ c₁ b := by decide +kernel
private lemma cross_valid : ∀ a b, cross a b → c₀ a ≠ c₁ b := by
  unfold cross
  decide +kernel

def template : Template fiber cross :=
  ⟨SimpleGraph.Coloring.mk c₀ (fun {a b} h => c₀_valid a b h),
    SimpleGraph.Coloring.mk c₁ (fun {a b} h => c₁_valid a b h),cross_valid⟩

/-- Each cross-relation class is independent within a fiber. -/
lemma cross_independent : ∀ a b, cross a b → ¬fiber.Adj a b := by
  unfold cross
  decide +kernel

/-- These classes cannot all be folded into three independent color classes. -/
lemma no_three_fold : ¬∃ c : Fin 6 → Fin 3,
    (∀ a b, fiber.Adj a b → c a ≠ c b) ∧ (∀ a b, cross a b → c a = c b) := by
  unfold cross
  decide +kernel

/-- The template has a diagonal cross edge at every fiber vertex. -/
lemma cross_refl (a : Fin 6) : cross a a := rfl

end Prism

#print axioms Prism.template
#print axioms Prism.no_three_fold

#print axioms three_of_two
#print axioms three_of_finite_hom
#print axioms cliqueFree
end Erdos595FiniteFiberOddBound
