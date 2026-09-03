import Submission.SubdividedFiveRestoration

/-! A closed subdivided-K5 core cannot occupy two members of a smallest-failure one-defect family. -/
namespace Erdos583SubdividedFivePairExclusionDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583Work.MemberExpansion
open Erdos583SubdividedFiveFiniteDevelopment Erdos583SubdividedFiveRestorationDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma mapped_core_touches_complement {N : ℕ} {V : Type*} {B : SimpleGraph (Fin N)} {F G : SimpleGraph V}
    (hG : G.Connected) (f : B →g G) (hN : 0 < N)
    (hcover : G.edgeSet=F.edgeSet ∪ (Sym2.map f '' B.edgeSet)) (hF : F.support.Nonempty) :
    ∃ i : Fin N, f i ∈ F.support := by
  by_contra hn
  have hclosed : Set.range f=Set.univ := by
    apply TrailBudget.connected_closed_set hG (Set.range f) ⟨f ⟨0,hN⟩,⟨⟨0,hN⟩,rfl⟩⟩
    intro u v huv hu
    have he : s(u,v) ∈ F.edgeSet ∪ (Sym2.map f '' B.edgeSet) := hcover ▸ huv
    rcases he with he | he
    · obtain ⟨i,rfl⟩ := hu
      exact (hn ⟨i,⟨v,he⟩⟩).elim
    · obtain ⟨e,_,he⟩ := he
      induction e using Sym2.ind with
      | h a b =>
        simp only [Sym2.map_mk] at he
        rcases Sym2.eq_iff.mp he with ⟨ha,hb⟩ | ⟨ha,hb⟩
        · exact ⟨b,hb⟩
        · exact ⟨a,ha⟩
  obtain ⟨v,hv⟩ := hF
  have hh : v ∈ Set.range f := by rw [hclosed]; trivial
  obtain ⟨i,rfl⟩ := hh
  exact hn ⟨i,hv⟩

lemma failure_no_subdivided_five_rooted_pair {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hm : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score ≤ T.score)
    (r : Fin n) (L : RootedCycleRep T r)
    (j : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) (hji : j ≠ L.index)
    (f : base →g G) (hf : Function.Injective f)
    (hcore : (T.walk L.index).toSubgraph.edgeSet ∪ (T.walk j).toSubgraph.edgeSet=
      Sym2.map f '' base.edgeSet) : False := by
  classical
  let A : Finset (Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) := Finset.univ \ {L.index,j}
  let F := selectedGraph T A
  have hiA : L.index ∉ A := by simp [A]
  have hjA : j ∉ A := by simp [A]
  have hAc : A.card+2=⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
    have hh := Finset.card_sdiff_add_card_eq_card (s := {L.index,j})
      (show ({L.index,j} : Finset (Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)) ⊆ Finset.univ from Finset.subset_univ _)
    simpa only [A,Finset.card_pair hji.symm,Finset.card_univ,Fintype.card_fin] using hh
  have hcount : 3 ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
    have hh := Fintype.card_le_of_injective f hf
    simp only [Fintype.card_fin] at hh
    simp only [Fintype.card_fin,BridgeGlue.ceil_half]
    omega
  obtain ⟨l,hlA⟩ := Finset.card_pos.mp (show 0 < A.card by omega)
  have hnone := NilSlot.max_score_nonpath_no_nil T hm ⟨L.index,L.member_not_path⟩
  have hFl : F.Adj (T.start l) (T.walk l).snd := ⟨l,hlA,(T.walk l).toSubgraph_adj_snd (hnone l)⟩
  have hF : F.support.Nonempty := ⟨T.start l,⟨_,hFl⟩⟩
  have hFG : F ≤ G := selectedGraph_le T A
  have hdis : Disjoint (Sym2.map f '' base.edgeSet) F.edgeSet := by
    rw [←hcore]
    exact disjoint_sup_left.mpr ⟨(selected_disjoint T A L.index hiA).symm,(selected_disjoint T A j hjA).symm⟩
  have hcover : G.edgeSet=F.edgeSet ∪ (Sym2.map f '' base.edgeSet) := by
    rw [←hcore]
    ext e
    constructor
    · intro he
      obtain ⟨m,hm⟩ := (T.cover e).mp he
      by_cases hmi : m=L.index
      · subst m; exact Or.inr (Or.inl hm)
      by_cases hmj : m=j
      · subst m; exact Or.inr (Or.inr hm)
      · exact Or.inl ((selected_edge_iff T A e).mpr ⟨m,by simp [A,hmi,hmj],hm⟩)
    · rintro (he|he|he)
      · exact edgeSet_mono hFG he
      · exact (T.walk L.index).toSubgraph.edgeSet_subset he
      · exact (T.walk j).toSubgraph.edgeSet_subset he
  have htouch := mapped_core_touches_complement hG f (by decide) hcover hF
  obtain ⟨D,hD,hDc⟩ := selected_paths_partition T A (by
    intro m hmA
    have hmi : m ≠ L.index := fun hh ↦ hiA (hh ▸ hmA)
    exact (T.one_defect_other_paths hs L.index L.member_not_path).2 m hmi)
  exact failure_no_subdivided_five_partition hsmall hG hfail hFG f hf hdis hcover htouch D hD (by omega)

end Erdos583SubdividedFivePairExclusionDevelopment
