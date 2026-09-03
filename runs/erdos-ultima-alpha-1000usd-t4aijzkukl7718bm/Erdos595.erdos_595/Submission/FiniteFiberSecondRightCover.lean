import Submission.FiniteFiberOddBound
import Submission.MatchingBundleRightCover

/-!
Finite-fiber bundles whose cross relation is disjoint from the fiber edges
and whose triangles stay in fibers have a covered second right adjoint.
The cross relation need not be an equivalence relation. This is an exclusion
criterion, not a settlement of Erdos 595.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595FiniteFiberSecondRight
open Erdos595ArcAdjoint Erdos595MatchingBundle Erdos595FiniteFiberOddBound
universe u
variable {I S : Type u} (F : SimpleGraph S) (P : S → S → Prop)
  (hP : Symmetric P) (B : SimpleGraph I)

abbrev H := bundle F P hP B

/-- Record every oriented within-fiber edge of a biclique. -/
def code (p : Biclique (H F P hP B)) : S → S → Prop :=
  fun a b => ∃ i, (i,a) ∈ p.val.1 ∧ (i,b) ∈ p.val.2

variable
  (hdis : ∀ a b, P a b → ¬F.Adj a b)
  (htri : ∀ a b d : I × S, (H F P hP B).Adj a b →
    (H F P hP B).Adj a d → (H F P hP B).Adj b d →
    a.1 = b.1 ∧ a.1 = d.1)

lemma same_fiber {a b : I × S} (he : a.1 = b.1) (hab : (H F P hP B).Adj a b) :
    F.Adj a.2 b.2 := by
  rcases hab with hab | hab
  · exact hab.2
  · exact (hab.1.ne he).elim

include hdis htri in
/-- The raw finite relation already gives a rainbow label; no choice of
an internal fiber or an equivalence-class decomposition is necessary. -/
lemma code_ne {p q r : Biclique (H F P hP B)}
    (hpq : (right (H F P hP B)).Adj p q)
    (hpr : (right (H F P hP B)).Adj p r)
    (hqr : (right (H F P hP B)).Adj q r) : code F P hP B p ≠ code F P hP B q := by
  intro he
  let t := six (H F P hP B) hpq hpr hqr
  have ht := t.tri _
  have hf := htri t.x t.y t.z ht.1 ht.2.1 ht.2.2
  have hq : code F P hP B q t.x.2 t.y.2 :=
    ⟨t.x.1,t.hx.2,by simpa only [hf.1] using t.hy.1⟩
  have hp : code F P hP B p t.x.2 t.y.2 := he ▸ hq
  obtain ⟨i,hxi,hyi⟩ := hp
  by_cases hi : i = t.x.1
  · have hxx := p.property (i,t.x.2) hxi t.x t.hx.1
    have hx : (i,t.x.2) = t.x := Prod.ext hi rfl
    exact hxx.ne hx
  · have hzy := p.property t.z t.hz.2 (i,t.y.2) hyi
    rcases hzy with hzy | hzy
    · exact hi (hzy.1.symm.trans hf.2.symm)
    · exact hdis t.z.2 t.y.2 hzy.2
        (same_fiber F P hP B (hf.2.symm.trans hf.1) ht.2.2.symm)

include hdis htri in
theorem second_right_cover [Finite S] :
    Erdos595Work.IsCountableUnionOfTriangleFree (right (right (H F P hP B))) := by
  apply right_cover_of_rainbow (right (H F P hP B)) (code F P hP B)
  intro p q r hpq hpr hqr
  exact ⟨code_ne F P hP B hdis htri hpq hpr hqr,
    code_ne F P hP B hdis htri hpr hpq hqr.symm,
    code_ne F P hP B hdis htri hqr hpq.symm hpr.symm⟩

/-- Independent cross-neighborhoods and a triangle-free index graph imply
that all triangles stay in fibers. -/
lemma triangle_fibers
    (hind : ∀ a b d, P a b → P a d → ¬F.Adj b d) (hB : B.CliqueFree 3) :
    ∀ a b d : I × S, (H F P hP B).Adj a b →
      (H F P hP B).Adj a d → (H F P hP B).Adj b d →
      a.1 = b.1 ∧ a.1 = d.1 := by
  classical
  intro a b d hab had hbd
  rcases hab with hab | hab <;> rcases had with had | had <;> rcases hbd with hbd | hbd
  · exact ⟨hab.1,had.1⟩
  · exact ⟨hab.1,had.1⟩
  · exact ⟨hab.1,hab.1.trans hbd.1⟩
  · exact (hind d.2 a.2 b.2 (hP had.2) (hP hbd.2) hab.2).elim
  · exact ⟨had.1.trans hbd.1.symm,had.1⟩
  · exact (hind b.2 a.2 d.2 (hP hab.2) hbd.2 had.2).elim
  · exact (hind a.2 b.2 d.2 hab.2 had.2 hbd.2).elim
  · exact (hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨hab.1,had.1,hbd.1⟩)).elim

/-- A reflexive cross relation automatically avoids the fiber edges when
its neighborhoods are independent. No transitivity of P is assumed. -/
theorem second_right_cover_of_reflexive [Finite S] (hrefl : Reflexive P)
    (hind : ∀ a b d, P a b → P a d → ¬F.Adj b d) (hB : B.CliqueFree 3) :
    Erdos595Work.IsCountableUnionOfTriangleFree (right (right (H F P hP B))) := by
  apply second_right_cover F P hP B
  · intro a b hab
    exact hind a a b (hrefl a) hab
  · exact triangle_fibers F P hP B hind hB

#print axioms code_ne
#print axioms second_right_cover
#print axioms second_right_cover_of_reflexive
end Erdos595FiniteFiberSecondRight
