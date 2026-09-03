import Submission.SecondConeCliqueCover

/-!
The full independent-apex family over a triangle-free base is homomorphically
equivalent to its single cone. In particular its K4-free second right
adjoint is countably triangle-free edge-covered.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595FullApexSecondRight
open Erdos595Work Erdos595ArcAdjoint Erdos595Extension
variable {V W : Type*} (G : SimpleGraph V)

/-- Collapse all independent apices to the one universal cone point. -/
def collapse : apexFamilyGraph G →g coneGraph G where
  toFun := Sum.elim some (fun _ => none)
  map_rel' := by
    intro x y h
    cases x <;> cases y <;> simp_all [apexFamilyGraph,coneGraph]

lemma univ_admissible (hG : G.CliqueFree 3) : (G.induce Set.univ).CliqueFree 3 := by
  classical
  intro s hs
  obtain ⟨a,b,c,hab,hac,hbc,_⟩ := SimpleGraph.is3Clique_iff.mp hs
  exact hG _ (SimpleGraph.is3Clique_triple_iff.mpr
    (show G.Adj a.val b.val ∧ G.Adj a.val c.val ∧ G.Adj b.val c.val from ⟨hab,hac,hbc⟩))

/-- The full family contains the universal apex when the base is triangle-free. -/
def inclusion (hG : G.CliqueFree 3) : coneGraph G →g apexFamilyGraph G where
  toFun := fun x => x.elim (Sum.inr ⟨Set.univ,univ_admissible G hG⟩) Sum.inl
  map_rel' := by
    intro x y h
    cases x <;> cases y <;> simp_all [apexFamilyGraph,coneGraph]

def rightMap {A : SimpleGraph V} {B : SimpleGraph W} (f : A →g B) : right A →g right B where
  toFun p := ⟨(f '' p.val.1,f '' p.val.2),by
    rintro a ⟨x,hx,rfl⟩ b ⟨y,hy,rfl⟩
    exact f.map_adj (p.property x hx y hy)⟩
  map_rel' := by
    intro p q hpq
    obtain ⟨a,hap,haq⟩ := hpq.1
    obtain ⟨b,hbq,hbp⟩ := hpq.2
    exact ⟨⟨f a,⟨a,hap,rfl⟩,⟨a,haq,rfl⟩⟩,
      ⟨f b,⟨b,hbq,rfl⟩,⟨b,hbp,rfl⟩⟩⟩

lemma four_pullback {A : SimpleGraph V} {B : SimpleGraph W} (f : A →g B)
    (hB : B.CliqueFree 4) : A.CliqueFree 4 := by
  classical
  by_contra hn
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree hn
  have h : ∀ i j : Fin 4, i ≠ j → B.Adj (f (e i)) (f (e j)) :=
    fun i j hij => f.map_adj (e.map_rel_iff.mpr hij)
  exact no_adj_common_neighbors hB (h 0 1 (by decide)) (h 0 2 (by decide))
    (h 1 2 (by decide)) (h 0 3 (by decide)) (h 1 3 (by decide)) (h 2 3 (by decide))

theorem second_cliqueFree_iff (hG : G.CliqueFree 3) :
    (right (right (apexFamilyGraph G))).CliqueFree 4 ↔
      (right (right (coneGraph G))).CliqueFree 4 :=
  ⟨four_pullback (rightMap (rightMap (inclusion G hG))),
    four_pullback (rightMap (rightMap (collapse G)))⟩

theorem second_cover_iff (hG : G.CliqueFree 3) :
    IsCountableUnionOfTriangleFree (right (right (apexFamilyGraph G))) ↔
      IsCountableUnionOfTriangleFree (right (right (coneGraph G))) :=
  ⟨countable_union_of_hom (rightMap (rightMap (inclusion G hG))),
    countable_union_of_hom (rightMap (rightMap (collapse G)))⟩

/-- The full independent-apex family is excluded at its SECOND right stage
as soon as that stage is K4-free. -/
theorem countable_cover (hG : G.CliqueFree 3)
    (h : (right (right (apexFamilyGraph G))).CliqueFree 4) :
    IsCountableUnionOfTriangleFree (right (right (apexFamilyGraph G))) :=
  (second_cover_iff G hG).mpr
    (Erdos595SecondConeClique.countable_cover G ((second_cliqueFree_iff G hG).mp h))

#print axioms second_cliqueFree_iff
#print axioms second_cover_iff
#print axioms countable_cover
end Erdos595FullApexSecondRight
