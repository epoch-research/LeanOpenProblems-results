import Submission.ShortTriangleSingleCarrier

/-! External neighbors forced by a cubic-to-cubic carrier through a triangle root. -/
namespace Erdos583CubicTriangleCarrierDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583CubicTriangleReductionDevelopment Erdos583ShortTriangleSingleCarrierDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

lemma three_neighbors_exhaust {V : Type*} [Fintype V] {G : SimpleGraph V}
    {x r y a : V} (hxr : G.Adj x r) (hxy : G.Adj x y) (hxa : G.Adj x a)
    (hry : r ≠ y) (har : a ≠ r) (hay : a ≠ y) (hd : Nat.card (G.neighborSet x)=3) :
    ∀ z, G.Adj x z → z=r ∨ z=y ∨ z=a := by
  have hsub : ({r,y,a} : Set V) ⊆ G.neighborSet x := by
    rintro z (rfl|rfl|rfl) <;> assumption
  have hc : ({r,y,a} : Set V).ncard=3 := Set.ncard_eq_three.mpr ⟨r,y,a,hry,har.symm,hay.symm,rfl⟩
  have he : G.neighborSet x={r,y,a} := (Set.eq_of_subset_of_ncard_le hsub (by simpa only [hc,Nat.card_coe_set_eq] using hd.le)).symm
  intro z hz
  change z ∈ ({r,y,a} : Set V)
  rwa [←he]

lemma path_between_triangle_vertices_external_data {V : Type*} [Fintype V] {G : SimpleGraph V}
    {r x y : V} (hrx : G.Adj r x) (hry : G.Adj r y) (hxy : G.Adj x y)
    (hdx : Nat.card (G.neighborSet x)=3) (hdy : Nat.card (G.neighborSet y)=3)
    (P : G.Walk x y) (hP : P.IsPath) (hrP : r ∈ P.support)
    (hnrx : s(r,x) ∉ P.edges) (hnry : s(r,y) ∉ P.edges) (hnxy : s(x,y) ∉ P.edges) :
    ∃ a b, G.Adj x a ∧ G.Adj y b ∧ a ≠ r ∧ a ≠ y ∧ b ≠ r ∧ b ≠ x ∧ a ≠ b ∧
      (∀ z, G.Adj x z → z=r ∨ z=y ∨ z=a) ∧
      (∀ z, G.Adj y z → z=r ∨ z=x ∨ z=b) ∧
      (puncture G ({x,y} : Set V)).Reachable a r ∧ s(a,b) ∉ P.edges := by
  classical
  cases P with
  | nil => exact (hxy.ne rfl).elim
  | @cons _ a _ hxa Q =>
    have har : a ≠ r := by
      rintro rfl
      exact hnrx (by simp [Sym2.eq_swap])
    have hay : a ≠ y := by
      rintro rfl
      exact hnxy (by simp)
    have hnQ : ¬Q.Nil := Walk.not_nil_of_ne hay
    obtain ⟨b,R,hby,hQR⟩ : ∃ b, ∃ R : G.Walk a b, ∃ hby : G.Adj b y, Q=R.concat hby := by
      cases Q with
      | nil => exact (hnQ Walk.Nil.nil).elim
      | cons h A => exact Walk.exists_cons_eq_concat h A
    subst Q
    have hbr : b ≠ r := by
      rintro rfl
      exact hnry (by simp)
    have hbx : b ≠ x := by
      rintro rfl
      exact hnxy (by simp)
    have hRC := (Walk.cons_isPath_iff hxa (R.concat hby)).mp hP
    have hRR := (Walk.concat_isPath_iff hby).mp hRC.1
    have hrR : r ∈ R.support := by
      simpa only [Walk.support_cons,Walk.support_concat,List.concat_eq_append,List.mem_cons,List.mem_append,
        List.not_mem_nil,hrx.ne,hry.ne,false_or,or_false] using hrP
    have hab : a ≠ b := by
      rintro rfl
      have he := (Walk.isPath_iff_eq_nil R).mp hRR.1
      have hra : r=a := by simpa only [he,Walk.support_nil,List.mem_singleton] using hrR
      exact har hra.symm
    have hxR : x ∉ R.support := fun hx ↦ hRC.2 (by
      simp only [Walk.support_concat,List.concat_eq_append,List.mem_append,List.mem_singleton]
      exact Or.inl hx)
    have hyR : y ∉ R.support := hRR.2
    have hreach : (puncture G ({x,y} : Set V)).Reachable a r := by
      let A := R.takeUntil r hrR
      have htransfer : ∀ e ∈ A.edges, e ∈ (puncture G ({x,y} : Set V)).edgeSet := by
        intro e he
        induction e using Sym2.ind with
        | h u v =>
          refine ⟨A.adj_of_mem_edges he,?_,?_⟩
          · have hu := R.support_takeUntil_subset hrR (A.fst_mem_support_of_mem_edges he)
            rintro (rfl|rfl) <;> contradiction
          · have hv := R.support_takeUntil_subset hrR (A.snd_mem_support_of_mem_edges he)
            rintro (rfl|rfl) <;> contradiction
      exact ⟨A.transfer _ htransfer⟩
    refine ⟨a,b,hxa,hby.symm,har,hay,hbr,hbx,hab,
      three_neighbors_exhaust hrx.symm hxy hxa hry.ne har hay hdx,
      three_neighbors_exhaust hry.symm hxy.symm hby.symm hrx.ne hbr hbx hdy,hreach,?_⟩
    intro he
    have heR : s(a,b) ∈ R.edges := by
      simp only [Walk.edges_cons,Walk.edges_concat,List.concat_eq_append,List.mem_cons,List.mem_append,
        List.not_mem_nil,or_false] at he
      rcases he with he | he | he
      · rcases Sym2.eq_iff.mp he with ⟨ha,_⟩ | ⟨_,hb⟩
        · exact (hxa.ne ha.symm).elim
        · exact (hbx hb).elim
      · exact he
      · rcases Sym2.eq_iff.mp he with ⟨ha,_⟩ | ⟨ha,_⟩
        · exact (hab ha).elim
        · exact (hay ha).elim
    have hlen := PentagonIntersection.endpoint_edge_forces_length_one R hRR.1 heR
    obtain ⟨e,hRe⟩ := ShortLollipop.one_edge_form R hlen
    have hrab : r=a ∨ r=b := by simpa [hRe] using hrR
    exact hrab.elim (fun h ↦ har h.symm) (fun h ↦ hbr h.symm)

lemma failure_cubic_triangle_carrier_external_edge {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {r x y : Fin n} (hrx : G.Adj r x) (hry : G.Adj r y) (hxy : G.Adj x y)
    (hdx : Nat.card (G.neighborSet x)=3) (hdy : Nat.card (G.neighborSet y)=3)
    (P : G.Walk x y) (hP : P.IsPath) (hrP : r ∈ P.support)
    (hnrx : s(r,x) ∉ P.edges) (hnry : s(r,y) ∉ P.edges) (hnxy : s(x,y) ∉ P.edges) :
    ∃ a b, G.Adj x a ∧ G.Adj y b ∧ a ≠ r ∧ a ≠ y ∧ b ≠ r ∧ b ≠ x ∧ a ≠ b ∧
      G.Adj a b ∧ s(a,b) ∉ P.edges := by
  obtain ⟨a,b,hxa,hyb,har,hay,hbr,hbx,hab,hNx,hNy,hreach,hnot⟩ :=
    path_between_triangle_vertices_external_data hrx hry hxy hdx hdy P hP hrP hnrx hnry hnxy
  exact ⟨a,b,hxa,hyb,har,hay,hbr,hbx,hab,
    failure_cubic_triangle_external_adj hsmall hG hfail hrx hry hxy hxa hyb har hay hbr hbx hab hNx hNy hreach,hnot⟩

lemma failure_degree_five_short_triangle_cubic_pair {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hm : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score ≤ T.score)
    (r : Fin n) (L : RootedCycleRep T r) {x y : Fin n}
    (hrx : G.Adj r x) (hxy : G.Adj x y) (hry : G.Adj r y)
    (hC : L.cycle=Walk.cons hrx (Walk.cons hxy (Walk.cons hry.symm Walk.nil)))
    (ht : L.tail.length=1 ∨ L.tail.length=2)
    (hd : Nat.card (G.neighborSet r)=5)
    (hdx : Nat.card (G.neighborSet x)=3) (hdy : Nat.card (G.neighborSet y)=3) :
    ∃ j, j ≠ L.index ∧ ∃ P : G.Walk x y, P.IsPath ∧
      (T.walk j).toSubgraph=P.toSubgraph ∧ r ∈ P.support ∧
      ∃ a b, G.Adj x a ∧ G.Adj y b ∧ a ≠ r ∧ a ≠ y ∧ b ≠ r ∧ b ≠ x ∧ a ≠ b ∧
        G.Adj a b ∧ s(a,b) ∉ P.edges := by
  have hc : L.cycle.length=3 := by rw [hC]; rfl
  have hq := (Erdos583ShortTriangleIncidenceDevelopment.failure_any_short_triangle_root_degree
    hsmall hG hfail T hs hm r L hc (by omega)).1
  have hxC : x ∈ L.cycle.support := by rw [hC]; simp
  have hyC : y ∈ L.cycle.support := by rw [hC]; simp
  obtain ⟨j,hji,P,hP,hPe,hrP,hdis⟩ := degree_five_two_cubic_carrier T hs hm r L hc ht hq hd
    hxC hyC hrx.ne.symm hry.ne.symm hxy.ne hdx hdy
  have hnot {e : Sym2 (Fin n)} (he : e ∈ L.cycle.toSubgraph.edgeSet) : e ∉ P.edges :=
    fun h ↦ Set.disjoint_left.mp hdis he (P.mem_edges_toSubgraph.mpr h)
  have hnr := hnot (show s(r,x) ∈ L.cycle.toSubgraph.edgeSet by rw [hC]; simp)
  have hny := hnot (show s(r,y) ∈ L.cycle.toSubgraph.edgeSet by rw [hC]; simp [Sym2.eq_swap])
  have hnxy := hnot (show s(x,y) ∈ L.cycle.toSubgraph.edgeSet by rw [hC]; simp)
  exact ⟨j,hji,P,hP,hPe,hrP,
    failure_cubic_triangle_carrier_external_edge hsmall hG hfail hrx hry hxy hdx hdy P hP hrP hnr hny hnxy⟩

end Erdos583CubicTriangleCarrierDevelopment
