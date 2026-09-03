import Submission.SubdividedFiveCycles

/-! A subdivided K5 and any touching path admit a whole pentagon plus two paths. -/
namespace Erdos583SubdividedFiveAbsorptionDevelopment
open SimpleGraph Erdos583Work Erdos583Work.TriangleAbsorption
open Erdos583SubdividedFiveFiniteDevelopment Erdos583SubdividedFiveCyclesDevelopment
open Erdos583CyclePredecessorConstraintDevelopment Erdos583RootEndpointTailCapacityDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma subdivided_five_path_to_pentagon {V : Type*} [Fintype V] {G : SimpleGraph V}
    (f : base →g G) (hf : Function.Injective f) {a b : V} (P : G.Walk a b) (hP : P.IsPath)
    (hd : Disjoint (Sym2.map f '' base.edgeSet) P.toSubgraph.edgeSet)
    (htouch : ∃ u : Fin 6, f u ∈ P.support) :
    ∃ C : G.Walk (f 0) (f 0), C.IsCycle ∧ C.length=5 ∧
      ∃ E : Set (Sym2 V), Disjoint C.toSubgraph.edgeSet E ∧
        C.toSubgraph.edgeSet ∪ E=(Sym2.map f '' base.edgeSet) ∪ P.toSubgraph.edgeSet ∧
        TwoPathCover (G := G) E := by
  classical
  by_contra hno
  obtain ⟨u,hu,A,D,hPA,hA⟩ := QuadrilateralAbsorption.first_hit_split P (Set.range f) (by
    obtain ⟨u,hu⟩ := htouch
    exact ⟨f u,hu,⟨u,rfl⟩⟩)
  obtain ⟨u,rfl⟩ := hu
  have hpred (v : Fin 6) (huv : base.Adj u v) :
      ∃ w : Fin 6, ∃ R : G.Walk a (f w), ∃ g : G.Adj (f w) (f v), ∃ B : G.Walk (f v) b,
        P=R.append (Walk.cons g B) ∧ ¬base.Adj w v := by
    obtain ⟨C,J,hC,hCl,hJ,hJs,he,hCJ,hcover⟩ := mapped_cycle_choice f hf huv
    have hCsub : C.toSubgraph.edgeSet ⊆ Sym2.map f '' base.edgeSet := by
      intro e he
      rw [←hcover]
      exact Or.inl he
    have hJsub : J.toSubgraph.edgeSet ⊆ Sym2.map f '' base.edgeSet := by
      intro e he
      rw [←hcover]
      exact Or.inr he
    have hJP : Disjoint J.toSubgraph.edgeSet P.toSubgraph.edgeSet := hd.mono_left hJsub
    have hnoJ : ¬TwoPathCover (G := G) (J.toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet) := by
      intro htwo
      apply hno
      refine ⟨C,hC,hCl,J.toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet,
        disjoint_sup_right.mpr ⟨hCJ,hd.mono_left hCsub⟩,?_,htwo⟩
      rw [←Set.union_assoc,hcover]
    obtain ⟨w,R,g,B,hform,hwJ⟩ := nonabsorbable_first_predecessor J hJ A D (hPA ▸ hP)
      (fun z hzA hzJ ↦ hA z hzA ((hJs z).mp hzJ))
      (by rw [←hPA]; exact hJP) (by rwa [←hPA]) he
    obtain ⟨w,rfl⟩ := (hJs w).mp hwJ
    refine ⟨w,R,g,B,hPA.trans hform,?_⟩
    intro hwv
    have heP : s(f w,f v) ∈ P.toSubgraph.edgeSet := by rw [hPA,hform]; simp
    exact Set.disjoint_left.mp hd ⟨s(w,v),hwv,rfl⟩ heP
  by_cases hu5 : u=5
  · subst u
    obtain ⟨w,R,g,B,hform,hnw⟩ := hpred 2 (by decide)
    have hw : w=4 := tip_complement_left w (fun he ↦ g.ne (congrArg f he)) hnw
    subst w
    obtain ⟨z,S,h,E,hform',hnz⟩ := hpred 4 (by decide)
    have hz : z=2 := tip_complement_right z (fun he ↦ h.ne (congrArg f he)) hnz
    subst z
    exact path_no_opposite_steps P hP R g B S h E hform hform'
  · obtain ⟨v,z,hvz,huv,huz,hv,hz⟩ := ordinary_neighbor_pair u hu5
    obtain ⟨w,R,g,B,hform,hnw⟩ := hpred v huv
    have hw : w=5 := ordinary_complement v w hv (fun he ↦ g.ne (congrArg f he.symm)) hnw
    subst w
    obtain ⟨w,S,h,E,hform',hnw⟩ := hpred z huz
    have hw : w=5 := ordinary_complement z w hz (fun he ↦ h.ne (congrArg f he.symm)) hnw
    subst w
    exact hvz (hf (path_same_predecessor_same_successor P hP R g B S h E hform hform'))

end Erdos583SubdividedFiveAbsorptionDevelopment
