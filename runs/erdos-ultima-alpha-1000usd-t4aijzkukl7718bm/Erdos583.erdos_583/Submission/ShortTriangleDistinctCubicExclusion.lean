import Submission.CubicExternalCarrier

/-! Cubic nonroot triangle vertices with distinct external neighbors are excluded at arbitrary roots. -/
namespace Erdos583ShortTriangleDistinctCubicExclusionDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583ShortTriangleIncidenceDevelopment Erdos583ShortTriangleDeletionDevelopment
open Erdos583CubicTriangleDeletionDevelopment Erdos583CubicExternalCarrierDevelopment
open Erdos583CubicTriangleReductionDevelopment Erdos583CubicTriangleEvenAttachmentDevelopment
open Erdos583CubicTriangleOddAttachmentDevelopment Erdos583CubicTrianglePunctureDevelopment
open Erdos583CubicCutReachabilityDevelopment Erdos583ShortTriangleCubicCutDevelopment
open Erdos583PrivateProxyDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma failure_no_short_triangle_distinct_cubic_data {n : ℕ}
    (hsmall : VertexCritical.SmallerOrders n) {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hm : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score ≤ T.score)
    (r : Fin n) (L : RootedCycleRep T r) {x y a b : Fin n}
    (hrx : G.Adj r x) (hxy : G.Adj x y) (hry : G.Adj r y)
    (hC : L.cycle=Walk.cons hrx (Walk.cons hxy (Walk.cons hry.symm Walk.nil)))
    (ht : L.tail.length=1 ∨ L.tail.length=2)
    (hdx : Nat.card (G.neighborSet x)=3) (hdy : Nat.card (G.neighborSet y)=3)
    (hxa : G.Adj x a) (hyb : G.Adj y b)
    (har : a ≠ r) (hay : a ≠ y) (hbr : b ≠ r) (hbx : b ≠ x) (hab : a ≠ b)
    (hNx : ∀ z, G.Adj x z → z=r ∨ z=y ∨ z=a)
    (hNy : ∀ z, G.Adj y z → z=r ∨ z=x ∨ z=b) : False := by
  classical
  have hc : L.cycle.length=3 := by rw [hC]; rfl
  have hrodd := (failure_any_short_triangle_root_degree hsmall hG hfail T hs hm r L hc (by omega)).2.1
  have hJ := short_triangle_delete_connected hG T hs hm r L hrx hxy hry hC ht hxa hyb har hay hbr hbx
  have hCe : L.cycle.toSubgraph.edgeSet=({s(r,x),s(x,y),s(r,y)} : Set (Sym2 (Fin n))) := by
    rw [hC]
    ext e
    simp only [Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_nil,List.mem_cons,
      List.not_mem_nil,or_false,Set.mem_insert_iff,Set.mem_singleton_iff,Sym2.eq_swap (a := y) (b := r)]
  have hx := short_triangle_external_link T hs hm r L hc ht
    (show x ∈ L.cycle.support by rw [hC]; simp) hrx.ne.symm hxa
    (by rw [hCe]; simp [hrx.ne.symm,hxy.ne,har,hay])
  rw [hCe] at hx
  obtain ⟨hK,hra,hrb⟩ := cubic_triangle_deletion_links hrx hry hxy hxa hyb har hay hbr hbx hNx hNy
    hJ (mem_support_of_reachable hrx.ne hx)
  have habG := failure_cubic_triangle_external_adj hsmall hG hfail hrx hry hxy hxa hyb har hay hbr hbx hab
    hNx hNy hra.symm
  by_cases hae : Even (Nat.card (G.neighborSet a))
  · exact hfail (cubic_triangle_even_attachment_reduction hsmall hG hrx hry hxy hxa hyb har hay hbr hbx hab
      hNx hNy hrodd hae hra hrb)
  by_cases hbe : Even (Nat.card (G.neighborSet b))
  · have hswap : ({y,x} : Set (Fin n))={x,y} := Set.pair_comm y x
    exact hfail (cubic_triangle_even_attachment_reduction hsmall hG hry hrx hxy.symm hyb hxa hbr hbx har hay hab.symm
      hNy hNx hrodd hbe (by rwa [hswap]) (by rwa [hswap]))
  have hao := Nat.not_even_iff_odd.mp hae
  have hbo := Nat.not_even_iff_odd.mp hbe
  let K := puncture G ({x,y} : Set (Fin n))
  let K0 := puncture (G.deleteEdges {s(a,b)}) ({x,y} : Set (Fin n))
  have hcomm : K.deleteEdges {s(a,b)}=K0 := by
    ext u v
    simp only [K,K0,puncture_adj,deleteEdges_adj]
    tauto
  have habK : K.Adj a b := ⟨habG,by simp [hxa.ne.symm,hay],by simp [hbx,hyb.ne.symm]⟩
  have hrK : r ∈ K.support := mem_support_of_reachable har.symm hra
  have hsides := deleted_edge_two_sides hK habK hrK
  rw [hcomm] at hsides
  by_cases hra0 : K0.Reachable r a
  · by_cases hrb0 : K0.Reachable r b
    · have hK0 : SupportConnected K0 := cubic_pair_puncture_delete_connected
        (fun u _ v _ ↦ hG.preconnected u v) hrx hry hNx hNy hra0 hrb0
      apply hfail
      apply gallai_private_pair_proxy hsmall G K0 hxy.ne hK0
      · rintro ⟨z,hz⟩; exact hz.2.1 (Or.inl rfl)
      · rintro ⟨z,hz⟩; exact hz.2.1 (Or.inr rfl)
      · intro D hD
        exact cubic_triangle_odd_attachment_lift hrx hry hxy hxa hyb habG har hay hbr hbx hNx hNy hrodd hao D hD
    · obtain ⟨i,hiL,d,P,hP,hPi,hybP⟩ := short_triangle_cubic_external_carrier T hs hm r L hrx hxy hry hC ht hNy hdy
      exact short_triangle_cubic_cut_not_odd T hs hm r L hc ht hrx.ne hry.ne hbx hay
        (by rw [hC]; simp) hyb hNx hNy hra0 hrb0 i hiL P hP hPi hybP hbo
  · have hrb0 : K0.Reachable r b := (hsides.resolve_left (fun h ↦ hra0 h.symm)).symm
    have hswap : puncture (G.deleteEdges {s(b,a)}) ({y,x} : Set (Fin n))=K0 := by
      simp only [K0,Sym2.eq_swap (a := b) (b := a),Set.pair_comm y x]
    obtain ⟨i,hiL,d,P,hP,hPi,hxaP⟩ := cycle_cubic_external_carrier T hs hm r L hc ht
      (show x ∈ L.cycle.support by rw [hC]; simp) hrx.ne.symm
      (show s(x,r) ∈ L.cycle.toSubgraph.edgeSet by rw [hC]; simp [Sym2.eq_swap])
      (show s(x,y) ∈ L.cycle.toSubgraph.edgeSet by rw [hC]; simp) hNx hdx
    exact short_triangle_cubic_cut_not_odd T hs hm r L hc ht hry.ne hrx.ne hay hbx
      (by rw [hC]; simp) hxa hNy hNx (by rwa [hswap]) (by rwa [hswap]) i hiL P hP hPi hxaP hao

end Erdos583ShortTriangleDistinctCubicExclusionDevelopment
