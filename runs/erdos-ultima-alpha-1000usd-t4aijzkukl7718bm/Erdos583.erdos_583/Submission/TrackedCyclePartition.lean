import Submission.ButterflyPentagon

/-! Tracking one whole cycle while indexing and padding an ordinary path partition. -/
namespace Erdos583TrackedCyclePartitionDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma cycle_and_paths_family {V : Type*} {F G : SimpleGraph V} {m k : ℕ}
    (hFG : F ≤ G) (S : TrailFamily F m) (hS : ∀ i, (S.walk i).IsPath)
    {r : V} (C : G.Walk r r) (hC : C.IsCycle)
    (hdis : Disjoint C.toSubgraph.edgeSet F.edgeSet)
    (hcover : G.edgeSet=C.toSubgraph.edgeSet ∪ F.edgeSet) (hcount : m+1 ≤ k) :
    ∃ T : TrailFamily G k, ∃ i : Fin k, (T.walk i).toSubgraph=C.toSubgraph ∧
      ∀ j, j ≠ i → (T.walk j).IsPath := by
  classical
  let I := Option (Fin m) ⊕ Fin (k-(m+1))
  let a : I → V := fun i ↦ match i with
    | .inl none => r
    | .inl (some j) => S.start j
    | .inr _ => r
  let b : I → V := fun i ↦ match i with
    | .inl none => r
    | .inl (some j) => S.finish j
    | .inr _ => r
  let p : ∀ i : I, G.Walk (a i) (b i) := fun i ↦ match i with
    | .inl none => C
    | .inl (some j) => (S.walk j).mapLe hFG
    | .inr _ => Walk.nil
  have hp : ∀ i, (p i).IsTrail := by
    rintro ((_|j)|j)
    · exact hC.isTrail
    · exact (hS j).isTrail.mapLe hFG
    · exact Walk.IsTrail.nil
  have hpe (j : Fin m) : (p (.inl (some j))).toSubgraph.edgeSet=(S.walk j).toSubgraph.edgeSet := by
    simp only [p,Walk.edgeSet_toSubgraph,Walk.edges_mapLe_eq_edges]
  have hd : Pairwise fun i j ↦ Disjoint (p i).toSubgraph.edgeSet (p j).toSubgraph.edgeSet := by
    rintro ((_|i)|i) ((_|j)|j) hij
    · exact (hij rfl).elim
    · rw [hpe]
      exact hdis.mono_right (S.walk j).toSubgraph.edgeSet_subset
    · simp [p]
    · rw [hpe]
      exact (hdis.mono_right (S.walk i).toSubgraph.edgeSet_subset).symm
    · rw [hpe,hpe]
      exact S.disjoint (fun he ↦ hij (congrArg (fun z : Fin m ↦ Sum.inl (some z)) he))
    · simp [p]
    · simp [p]
    · simp [p]
    · simp [p]
  have hc : ∀ d, d ∈ G.edgeSet ↔ ∃ i, d ∈ (p i).toSubgraph.edgeSet := by
    intro d
    rw [hcover]
    constructor
    · rintro (hd|hd)
      · exact ⟨.inl none,hd⟩
      · obtain ⟨j,hj⟩ := (S.cover d).mp hd
        exact ⟨.inl (some j),by rwa [hpe]⟩
    · rintro ⟨((_|j)|j),hj⟩
      · exact Or.inl hj
      · exact Or.inr ((S.cover d).mpr ⟨j,by rwa [hpe] at hj⟩)
      · simp [p] at hj
  have hI : Fintype.card I=k := by
    simp only [I,Fintype.card_sum,Fintype.card_option,Fintype.card_fin]
    omega
  let e : Fin k ≃ I := (Fintype.equivFinOfCardEq hI).symm
  let T : TrailFamily G k :=
    { start := a ∘ e
      finish := b ∘ e
      walk := fun i ↦ p (e i)
      isTrail := fun i ↦ hp (e i)
      disjoint := fun _ _ hij ↦ hd (fun he ↦ hij (e.injective he))
      cover := by
        intro d
        rw [hc]
        constructor
        · rintro ⟨i,hi⟩
          refine ⟨e.symm i,?_⟩
          change d ∈ (p (e (e.symm i))).toSubgraph.edgeSet
          rw [e.apply_symm_apply]
          exact hi
        · rintro ⟨i,hi⟩; exact ⟨e i,hi⟩ }
  let i : Fin k := e.symm (.inl none)
  refine ⟨T,i,?_,?_⟩
  · change (p (e (e.symm (.inl none)))).toSubgraph=C.toSubgraph
    rw [e.apply_symm_apply]
  · intro j hji
    have hne : e j ≠ Sum.inl none := by
      intro he
      apply hji
      apply e.injective
      change e j=e (e.symm (.inl none))
      rw [he,e.apply_symm_apply]
    change (p (e j)).IsPath
    cases he : e j with
    | inl o =>
      cases o with
      | none => exact (hne he).elim
      | some l => exact (hS l).mapLe hFG
    | inr l => exact Walk.IsPath.nil

lemma one_cycle_family_score {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (i : Fin k) {r : V} (C : G.Walk r r) (hC : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (hother : ∀ j, j ≠ i → (T.walk j).IsPath) :
    T.score+1=G.edgeSet.ncard+k := by
  classical
  have hlen : (T.walk i).length=C.length := by
    rw [←trail_edgeSet_ncard _ (T.isTrail i),hi,trail_edgeSet_ncard C hC.isTrail]
  have hv : (T.walk i).toSubgraph.verts.ncard=C.length := by
    rw [hi,Walk.verts_toSubgraph,cycle_support_ncard hC]
  have hdi : T.defect i=1 := by
    change (T.walk i).length+1-(T.walk i).toSubgraph.verts.ncard=1
    rw [hlen,hv]; omega
  have hsum : ∑ j, T.defect j=1 := by
    rw [Finset.sum_eq_single i,hdi]
    · intro j _ hji; exact (T.defect_eq_zero_iff j).mpr (hother j hji)
    · simp
  have hh := T.sum_defect_add_score
  rw [hsum] at hh
  omega

lemma one_defect_maximal_of_failure {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k) :
    ∀ U : TrailFamily G k, U.score ≤ T.score := by
  intro U
  by_contra hn
  have hb := U.score_le_edges_add
  have he : U.score=G.edgeSet.ncard+k := by omega
  exact hfail (MatchingAppend.path_family_partition U (U.score_eq_edges_add_iff.mp he))

lemma failure_no_pentagon_partition {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {F G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hFG : F ≤ G) {r : Fin n} (C : G.Walk r r) (hC : C.IsCycle) (hl : C.length=5)
    (hdis : Disjoint C.toSubgraph.edgeSet F.edgeSet) (hcover : G.edgeSet=C.toSubgraph.edgeSet ∪ F.edgeSet)
    (D : Finset F.Subgraph) (hD : GoodDecomposition F D)
    (hcount : D.card+1 ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) : False := by
  obtain ⟨S,hS,_⟩ := EdgeDefect.decomposition_path_family D hD
  obtain ⟨T,i,hi,hother⟩ := cycle_and_paths_family hFG S hS C hC hdis hcover hcount
  have hs := one_cycle_family_score T i C hC hi hother
  exact PentagonExclusion.failure_no_whole_pentagon hsmall hG hfail T hs
    (one_defect_maximal_of_failure hfail T hs) i C hC hl hi

end Erdos583TrackedCyclePartitionDevelopment
