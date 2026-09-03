import Submission.FiniteAdaptedExtension
import Submission.FiniteCliqueUltrafilterColoring

/-!
Every prescribed valid edge coloring on a COUNTABLY PROPERLY VERTEX-COLORABLE
old induced graph extends literally over any countably edge-coverable new
induced piece. No clique restriction or adaptation hypothesis is needed.
This prevents a prescribed-color obstruction at the first-to-second mutual
ultrafilter step over a countable K4-free base. It does not settle Erdős 595.
-/
set_option autoImplicit false
open SimpleGraph Set Filter
namespace Erdos595PrescribedCountableProper
open Erdos595FiniteAdapted Erdos595Work
variable {V W X : Type*}

/-- Old colors are untouched; new-new colors are even and crossing colors
are odd, determined by a proper old vertex coloring. -/
def extend (c : Sym2 V → ℕ) (d : Sym2 W → ℕ) (f : V → ℕ) :
    Sym2 (V ⊕ W) → ℕ :=
  Sym2.lift ⟨fun x y => match x, y with
    | .inl a, .inl b => c s(a,b)
    | .inl a, .inr _ => 2 * f a + 1
    | .inr _, .inl a => 2 * f a + 1
    | .inr a, .inr b => 2 * d s(a,b),
    by intro x y; cases x <;> cases y <;> simp only [Sym2.eq_swap]⟩

theorem extend_valid (G : SimpleGraph (V ⊕ W))
    (c : Sym2 V → ℕ) (d : Sym2 W → ℕ)
    (f : (G.comap Sum.inl).Coloring ℕ)
    (hc : Valid (G.comap Sum.inl) c) (hd : Valid (G.comap Sum.inr) d) :
    Valid G (extend c d f) := by
  intro a b t hab hat hbt heq
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      cases t with
      | inl t => exact hc a b t hab hat hbt heq
      | inr t =>
        change c s(a,b) = 2 * f a + 1 ∧ c s(a,b) = 2 * f b + 1 at heq
        apply f.valid hab
        omega
    | inr b =>
      cases t with
      | inl t =>
        change 2 * f a + 1 = c s(a,t) ∧ 2 * f a + 1 = 2 * f t + 1 at heq
        apply f.valid hat
        omega
      | inr t =>
        change 2 * f a + 1 = 2 * f a + 1 ∧ 2 * f a + 1 = 2 * d s(b,t) at heq
        omega
  | inr a =>
    cases b with
    | inl b =>
      cases t with
      | inl t =>
        change 2 * f b + 1 = 2 * f t + 1 ∧ 2 * f b + 1 = c s(b,t) at heq
        apply f.valid hbt
        omega
      | inr t =>
        change 2 * f b + 1 = 2 * d s(a,t) ∧ 2 * f b + 1 = 2 * f b + 1 at heq
        omega
    | inr b =>
      cases t with
      | inl t =>
        change 2 * d s(a,b) = 2 * f t + 1 ∧ 2 * d s(a,b) = 2 * f t + 1 at heq
        omega
      | inr t =>
        change 2 * d s(a,b) = 2 * d s(a,t) ∧ 2 * d s(a,b) = 2 * d s(b,t) at heq
        exact hd a b t hab hat hbt ⟨by omega,by omega⟩

theorem exists_extension (G : SimpleGraph (V ⊕ W)) (c : Sym2 V → ℕ)
    (hc : Valid (G.comap Sum.inl) c)
    (hf : Nonempty ((G.comap Sum.inl).Coloring ℕ))
    (hnew : IsCountableUnionOfTriangleFree (G.comap Sum.inr)) :
    ∃ e : Sym2 (V ⊕ W) → ℕ, Valid G e ∧
      ∀ a b : V, e s(Sum.inl a,Sum.inl b) = c s(a,b) := by
  obtain ⟨f⟩ := hf
  obtain ⟨d,hd⟩ := (countable_union_iff_edge_coloring _).mp hnew
  exact ⟨extend c d f,extend_valid G c d f hc hd,fun _ _ => rfl⟩

/-- The same result for an arbitrary induced embedding. Only the larger
induced graph's edge cover and the old graph's proper vertex coloring are used. -/
theorem along_embedding (H : SimpleGraph V) (G : SimpleGraph X)
    (f : H ↪g G) (c : Sym2 V → ℕ) (hc : Valid H c)
    (hproper : Nonempty (H.Coloring ℕ))
    (hG : IsCountableUnionOfTriangleFree G) :
    ∃ e : Sym2 X → ℕ, Valid G e ∧ ∀ a b, e s(f a,f b) = c s(a,b) := by
  classical
  let R : Set X := Set.range f
  let t : V ⊕ {x : X // x ∉ R} ≃ X :=
    (Equiv.sumCongr (Equiv.ofInjective f f.injective) (Equiv.refl {x : X // x ∉ R})).trans
      (Equiv.Set.sumCompl R)
  have hleft : (G.comap t).comap Sum.inl = H := by
    ext a b
    exact f.map_rel_iff
  have hnew : IsCountableUnionOfTriangleFree ((G.comap t).comap Sum.inr) :=
    countable_union_of_hom (SimpleGraph.Hom.comap _ _)
      (countable_union_of_hom (SimpleGraph.Hom.comap _ _) hG)
  obtain ⟨e,he,hold⟩ := exists_extension (G.comap t) c
    (hleft.symm ▸ hc) (hleft.symm ▸ hproper) hnew
  refine ⟨fun p => e (p.map t.symm),?_,?_⟩
  · intro a b z hab haz hbz hm
    apply he (t.symm a) (t.symm b) (t.symm z)
    · simpa only [SimpleGraph.comap_adj,t.apply_symm_apply] using hab
    · simpa only [SimpleGraph.comap_adj,t.apply_symm_apply] using haz
    · simpa only [SimpleGraph.comap_adj,t.apply_symm_apply] using hbz
    · exact hm
  · intro a b
    have ha : t.symm (f a) = Sum.inl a := t.symm_apply_apply (Sum.inl a)
    have hb : t.symm (f b) = Sum.inl b := t.symm_apply_apply (Sum.inl b)
    change e s(t.symm (f a),t.symm (f b)) = c s(a,b)
    rw [ha,hb]
    exact hold a b

/-- In particular, literal extension holds from any countable old carrier. -/
theorem from_countable [Countable V] (H : SimpleGraph V) (G : SimpleGraph X)
    (f : H ↪g G) (c : Sym2 V → ℕ) (hc : Valid H c)
    (hG : IsCountableUnionOfTriangleFree G) :
    ∃ e : Sym2 X → ℕ, Valid G e ∧ ∀ a b, e s(f a,f b) = c s(a,b) := by
  obtain ⟨k,hk⟩ := exists_injective_nat V
  exact along_embedding H G f c hc
    ⟨SimpleGraph.Coloring.mk k (fun h he => h.ne (hk he))⟩ hG

def principalEmbedding (G : SimpleGraph V) (hG : G.CliqueFree 4) :
    G ↪g ultrafilterGraph G hG where
  toFun := pure
  inj' := Ultrafilter.pure_injective
  map_rel_iff' := by
    intro a b
    change (fubiniAdj G (pure a) (pure b) ∧ fubiniAdj G (pure b) (pure a)) ↔ G.Adj a b
    simp only [fubiniAdj,Ultrafilter.mem_pure,Set.mem_setOf_eq,SimpleGraph.mem_neighborSet]
    exact ⟨And.left,fun h => ⟨h,h.symm⟩⟩

/-- EVERY valid prescribed coloring of the first mutual stage extends
unchanged to the second mutual stage over a countable K4-free base. -/
theorem first_to_second {A : Type} [Countable A]
    (G : SimpleGraph A) (hG : G.CliqueFree 4)
    (c : Sym2 (Ultrafilter A) → ℕ) (hc : Valid (ultrafilterGraph G hG) c) :
    ∃ e : Sym2 (Ultrafilter (Ultrafilter A)) → ℕ,
      Valid (ultrafilterGraph (ultrafilterGraph G hG)
        (ultrafilterGraph_cliqueFree G hG)) e ∧
      ∀ p q : Ultrafilter A, e s(pure p,pure q) = c s(p,q) := by
  have hfin := Erdos595FiniteCliqueUltrafilter.finiteCliques_of_cliqueFree G hG
  obtain ⟨d⟩ := Erdos595FiniteCliqueUltrafilter.or_countable_coloring G hfin
  let inc : ultrafilterGraph G hG →g
      Erdos595FiniteCliqueUltrafilter.orGraph G hfin :=
    ⟨id,fun h => Or.inl h.1⟩
  exact along_embedding _ _ (principalEmbedding _ (ultrafilterGraph_cliqueFree G hG))
    c hc ⟨d.comp inc⟩ (countable_union_second_ultrafilterGraph_of_countable G hG)

#print axioms exists_extension
#print axioms along_embedding
#print axioms from_countable
#print axioms first_to_second
end Erdos595PrescribedCountableProper
