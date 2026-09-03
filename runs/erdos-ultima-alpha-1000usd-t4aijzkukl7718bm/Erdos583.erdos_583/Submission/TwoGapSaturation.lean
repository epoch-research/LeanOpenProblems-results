import Submission.CycleOneCoreGap

/-! The next numerical boundary: at most two full-core deficits force,
away from a triangle, an even complete core with at most one missing edge. -/
namespace Erdos583TwoGapSaturationDevelopment
open SimpleGraph Erdos583Work
open Erdos583PathCoreIntervalsDevelopment Erdos583CycleOneCoreGapDevelopment
open Erdos583SaturatedCycleCoreDevelopment
open scoped Classical
set_option maxHeartbeats 1800000
set_option Elab.async false

lemma two_gap_arithmetic (q t e d : ℕ) (h4 : 4 ≤ q) (hdense : q ≤ 2*t+2)
    (hsum : e+d=t*(q-1)) (hd : d ≤ 2) (hbound : q+e ≤ q.choose 2) :
    q=2*t+2 ∧ 1 ≤ d ∧ q+e+(d-1)=q.choose 2 := by
  have hsub : q-1+1=q := Nat.sub_add_cancel (by omega)
  have hchoose : 2*q.choose 2 ≤ q*(q-1) := by
    rw [Nat.choose_two_right]
    exact Nat.mul_div_le _ _
  have hq : q=2*t+2 := by
    by_contra hn
    have hlt : q ≤ 2*t+1 := by omega
    have hm := Nat.mul_le_mul_right (q-1) (show q-1 ≤ 2*t by omega)
    nlinarith
  have hc : q.choose 2=(t+1)*(q-1) := by
    rw [hq,Nat.choose_two_right]
    have he : 2*t+2=2*(t+1) := by omega
    rw [he]
    simp [Nat.mul_assoc]
  rw [hc] at hbound
  have hd1 : 1 ≤ d := by nlinarith
  have hd' : d-1+1=d := Nat.sub_add_cancel hd1
  exact ⟨hq,hd1,by rw [hc]; nlinarith⟩

lemma missing_one_edge {V : Type*} [Fintype V] (H : SimpleGraph V)
    (hc : H.edgeSet.ncard+1=(Fintype.card V).choose 2) :
    ∃ u v, u ≠ v ∧ H=(⊤ : SimpleGraph V).deleteEdges {s(u,v)} := by
  classical
  have hb := edge_ncard_add_compl H
  have hcomp : Hᶜ.edgeSet.ncard=1 := by omega
  obtain ⟨e,he⟩ := Set.ncard_eq_one.mp hcomp
  induction e using Sym2.ind with
  | h u v =>
    have huv : Hᶜ.Adj u v := by
      change s(u,v) ∈ Hᶜ.edgeSet
      rw [he]; rfl
    refine ⟨u,v,huv.ne,?_⟩
    ext x y
    change s(x,y) ∈ H.edgeSet ↔ _
    have hm : Hᶜ.Adj x y ↔ s(x,y)=s(u,v) := by
      change s(x,y) ∈ Hᶜ.edgeSet ↔ _
      rw [he,Set.mem_singleton_iff]
    simp only [deleteEdges_adj,top_adj,Set.mem_singleton_iff,mem_edgeSet]
    constructor
    · intro hxy
      exact ⟨hxy.ne,fun hh ↦ (hm.mpr hh).2 hxy⟩
    · rintro ⟨hxy,hn⟩
      by_contra hnot
      exact hn (hm.mp ⟨hxy,hnot⟩)

lemma two_core_gaps_force_almost_clique {V : Type*} [Fintype V] {G : SimpleGraph V}
    {t : ℕ} {r : V} (C : G.Walk r r) (hC : C.IsCycle) (h4 : 4 ≤ C.length)
    (a b : Fin t → V) (p : ∀ i, G.Walk (a i) (b i))
    (hp : ∀ i, (p i).IsPath)
    (hS : ∀ i, (coreVerts (p i) C.toSubgraph.verts).Nonempty)
    (hd : Pairwise (fun i j ↦ Disjoint (p i).toSubgraph.edgeSet (p j).toSubgraph.edgeSet))
    (hCp : ∀ i, Disjoint C.toSubgraph.edgeSet (p i).toSubgraph.edgeSet)
    (hc : C.toSubgraph.edgeSet ∪ (⋃ i, (p i).toSubgraph.edgeSet)=G.edgeSet)
    (hdense : C.length ≤ 2*t+2)
    (hgap : (∑ i, (C.length-1-(coreEdges (p i) C.toSubgraph.verts).ncard)) ≤ 2) :
    C.length=2*t+2 ∧
      (G.induce C.toSubgraph.verts=⊤ ∨
        ∃ u v : C.toSubgraph.verts, u ≠ v ∧
          G.induce C.toSubgraph.verts=(⊤ : SimpleGraph C.toSubgraph.verts).deleteEdges {s(u,v)}) := by
  classical
  have hsize : C.toSubgraph.verts.ncard=C.length := by
    rw [Walk.verts_toSubgraph,cycle_support_ncard hC]
  have hv : Fintype.card C.toSubgraph.verts=C.length := by
    rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq,hsize]
  have hupper (i : Fin t) : (coreEdges (p i) C.toSubgraph.verts).ncard ≤ C.length-1 := by
    have hb := core_edge_bound (p i) (hp i) C.toSubgraph.verts (hS i)
    have hh := Set.ncard_mono (show coreVerts (p i) C.toSubgraph.verts ⊆ C.toSubgraph.verts
      from Set.inter_subset_right)
    rw [hsize] at hh
    omega
  have hterm (i : Fin t) : (coreEdges (p i) C.toSubgraph.verts).ncard+
      (C.length-1-(coreEdges (p i) C.toSubgraph.verts).ncard)=C.length-1 :=
    Nat.add_sub_of_le (hupper i)
  have hsum : (∑ i, (coreEdges (p i) C.toSubgraph.verts).ncard)+
      (∑ i, (C.length-1-(coreEdges (p i) C.toSubgraph.verts).ncard))=t*(C.length-1) := by
    rw [←Finset.sum_add_distrib]
    simp only [hterm,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  have hcount := cycle_paths_inside_count C hC a b p hd hCp hc
  have hb := PentagonCarriers.within_edge_bound G C.toSubgraph.verts
  rw [hsize,hcount] at hb
  obtain ⟨hlen,hgap1,hfull⟩ := two_gap_arithmetic C.length t _ _ h4 hdense hsum hgap hb
  refine ⟨hlen,?_⟩
  have he : (G.induce C.toSubgraph.verts).edgeSet.ncard+
      ((∑ i, (C.length-1-(coreEdges (p i) C.toSubgraph.verts).ncard))-1)=
        (Fintype.card C.toSubgraph.verts).choose 2 := by
    rw [←GlobalCritical.within_edge_ncard,hcount,hv]
    exact hfull
  by_cases hg : (∑ i, (C.length-1-(coreEdges (p i) C.toSubgraph.verts).ncard))=1
  · apply Or.inl
    apply full_edge_count_eq_top
    simpa only [hg,Nat.sub_self,Nat.add_zero] using he
  · apply Or.inr
    apply missing_one_edge
    have hg2 : (∑ i, (C.length-1-(coreEdges (p i) C.toSubgraph.verts).ncard))=2 := by omega
    simpa only [hg2,Nat.reduceSub] using he

end Erdos583TwoGapSaturationDevelopment
