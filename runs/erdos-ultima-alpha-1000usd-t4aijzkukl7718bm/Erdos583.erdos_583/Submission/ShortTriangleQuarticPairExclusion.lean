import Submission.ShortTriangleTailChord

/-! Two quartic nonroot vertices are impossible in a degree-five short triangular defect. -/
namespace Erdos583ShortTriangleQuarticPairExclusionDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583ShortTriangleIncidenceDevelopment Erdos583ShortTriangleSingleCarrierDevelopment
open Erdos583ShortTriangleMixedCasesDevelopment Erdos583ShortTriangleBothChordsDevelopment
open Erdos583ShortTriangleTailChordDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma four_neighbors_exhaust {V : Type*} [Fintype V] {G : SimpleGraph V} {x r y a b : V}
    (hxr : G.Adj x r) (hxy : G.Adj x y) (hxa : G.Adj x a) (hxb : G.Adj x b)
    (hry : r ≠ y) (har : a ≠ r) (hbr : b ≠ r) (hay : a ≠ y) (hby : b ≠ y) (hab : a ≠ b)
    (hd : Nat.card (G.neighborSet x)=4) :
    ∀ z, G.Adj x z → z=r ∨ z=y ∨ z=a ∨ z=b := by
  have hsub : ({r,y,a,b} : Set V) ⊆ G.neighborSet x := by
    rintro z (rfl|rfl|rfl|rfl) <;> assumption
  have hc : ({r,y,a,b} : Set V).ncard=4 := by
    simp [Set.ncard_insert_of_notMem,hry,har.symm,hbr.symm,hay.symm,hby.symm,hab]
  have he : G.neighborSet x={r,y,a,b} :=
    (Set.eq_of_subset_of_ncard_le hsub (by simpa only [hc,Nat.card_coe_set_eq] using hd.le)).symm
  intro z hz
  exact (show z ∈ ({r,y,a,b} : Set V) from he ▸ hz)

lemma short_walk_noninitial_edges_eq {V : Type*} {G : SimpleGraph V} {r t : V}
    (S : G.Walk r t) (hl : S.length ≤ 2) {e f : Sym2 V}
    (he : e ∈ S.edges) (hf : f ∈ S.edges) (hre : r ∉ e) (hrf : r ∉ f) : e=f := by
  cases S with
  | nil => simp at he
  | @cons _ u _ h A =>
    have heA : e ∈ A.edges := (List.mem_cons.mp he).resolve_left (fun hh ↦ hre (hh.symm ▸ Sym2.mem_mk_left _ _))
    have hfA : f ∈ A.edges := (List.mem_cons.mp hf).resolve_left (fun hh ↦ hrf (hh.symm ▸ Sym2.mem_mk_left _ _))
    cases A with
    | nil => simp at heA
    | @cons _ v _ g B =>
      have hnB : B.Nil := Walk.nil_iff_length_eq.mpr (by simp only [Walk.length_cons] at hl; omega)
      have he' : e=s(u,v) := by simpa only [Walk.edges_cons,Walk.edges_eq_nil.mpr hnB,List.mem_singleton] using heA
      have hf' : f=s(u,v) := by simpa only [Walk.edges_cons,Walk.edges_eq_nil.mpr hnB,List.mem_singleton] using hfA
      exact he'.trans hf'.symm

lemma failure_no_degree_five_short_triangle_quartic_pair {n : ℕ}
    (hsmall : VertexCritical.SmallerOrders n) {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hm : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score ≤ T.score)
    (r : Fin n) (L : RootedCycleRep T r) {x y : Fin n}
    (hrx : G.Adj r x) (hxy : G.Adj x y) (hry : G.Adj r y)
    (hC : L.cycle=Walk.cons hrx (Walk.cons hxy (Walk.cons hry.symm Walk.nil)))
    (ht : L.tail.length=1 ∨ L.tail.length=2) (hd : Nat.card (G.neighborSet r)=5)
    (hdx : Nat.card (G.neighborSet x)=4) (hdy : Nat.card (G.neighborSet y)=4) : False := by
  classical
  have hc : L.cycle.length=3 := by rw [hC]; rfl
  have hqr := (failure_any_short_triangle_root_degree hsmall hG hfail T hs hm r L hc (by omega)).1
  obtain ⟨j,hji,_,hunique⟩ := short_triangle_degree_five_unique_carrier T hs hm r L hc ht hqr hd
  obtain ⟨_,_,hqx,hqy⟩ := failure_degree_five_short_triangle_nonroot_degrees hsmall hG hfail T hs hm r L
    hrx hxy hry hC ht hd
  have hx0 : T.quota x=0 := by omega
  have hy0 : T.quota y=0 := by omega
  obtain ⟨a,b,c,d,hxa,hxb,hyc,hyd,hab,hcd,har,hbr,hay,hby,hcr,hdr,hcx,hdx',hpairs,habG,hcdG⟩ :=
    failure_degree_five_short_triangle_both_chords hsmall hG hfail T hs hm r L hrx hxy hry hC ht hd hdx hdy
  have hNx := four_neighbors_exhaust hrx.symm hxy hxa hxb hry.ne har hbr hay hby hab hdx
  have hNy := four_neighbors_exhaust hry.symm hxy.symm hyc hyd hrx.ne hcr hdr hcx hdx' hcd hdy
  have habT := short_triangle_external_chord_in_tail T hs hm r L hrx hxy hry hC ht hx0 j hji hunique
    hxa hxb habG har hbr hay hby hNx
  let M : RootedCycleRep T r :=
    ⟨L.index,L.finish,L.start_eq,L.finish_eq,L.cycle.reverse,L.tail,L.isCycle.reverse,L.isPath,
      (fun z hz ht ↦ L.inter z (by simpa only [Walk.support_reverse,List.mem_reverse] using hz) ht),
      L.subgraph.trans (by simp only [Walk.toSubgraph_append,Walk.toSubgraph_reverse])⟩
  have hMC : M.cycle=Walk.cons hry (Walk.cons hxy.symm (Walk.cons hrx.symm Walk.nil)) := by
    change L.cycle.reverse=_
    rw [hC]
    rfl
  have hmUnique : ∀ m, m ≠ M.index → (∃ v ∈ M.cycle.support, v ∈ (T.walk m).support) → m=j := by
    intro m hmi hhit
    apply hunique m hmi
    simpa only [M,Walk.support_reverse,List.mem_reverse] using hhit
  have hcdT := short_triangle_external_chord_in_tail T hs hm r M hry hxy.symm hrx hMC ht hy0 j hji hmUnique
    hyc hyd hcdG hcr hdr hcx hdx' hNy
  exact hpairs (short_walk_noninitial_edges_eq L.tail (by omega) habT hcdT
    (by simp [har.symm,hbr.symm]) (by simp [hcr.symm,hdr.symm]))

end Erdos583ShortTriangleQuarticPairExclusionDevelopment
