import Submission.Work
import Submission.EdgeAbsorption

/-! Fixed-cycle optimization with no per-vertex incidence constraint. -/
namespace Erdos583FreeCarrierDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.CarrierCount Erdos583Work.CarrierLength
open Erdos583Work.MemberExpansion Erdos583Work.MemberNormalExpansion Erdos583Work.VertexCritical
open Erdos583Work.QuotaSurgery Erdos583Work.CarrierGroups Erdos583Work.OutsideCarrierBudget
open Erdos583EdgeAbsorptionDevelopment
open scoped Classical
set_option maxHeartbeats 2000000

variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

lemma exists_maximum_carriers (T : TrailFamily G k) (i : Fin k) {r : V}
    (C : G.Walk r r) (hi : (T.walk i).toSubgraph=C.toSubgraph) :
    ∃ U : TrailFamily G k, U.score=T.score ∧ (U.walk i).toSubgraph=C.toSubgraph ∧
      (∀ Z : TrailFamily G k, Z.score=U.score → (Z.walk i).toSubgraph=C.toSubgraph →
        carrierCount Z C.toSubgraph.verts ≤ carrierCount U C.toSubgraph.verts) := by
  let P (m : ℕ) := ∃ U : TrailFamily G k, U.score=T.score ∧
    (U.walk i).toSubgraph=C.toSubgraph ∧ k-carrierCount U C.toSubgraph.verts=m
  have hex : ∃ m, P m := ⟨_,T,rfl,hi,rfl⟩
  obtain ⟨U,hUs,hUi,hUc⟩ := Nat.find_spec hex
  refine ⟨U,hUs,hUi,?_⟩
  intro Z hZs hZi
  have hm := Nat.find_min' hex (show P (k-carrierCount Z C.toSubgraph.verts) from
    ⟨Z,hZs.trans hUs,hZi,rfl⟩)
  have hU := carrierCount_le U C.toSubgraph.verts
  have hZ := carrierCount_le Z C.toSubgraph.verts
  omega

lemma exists_shortest_maximum_carriers (T : TrailFamily G k) (i : Fin k) {r : V}
    (C : G.Walk r r) (hi : (T.walk i).toSubgraph=C.toSubgraph) :
    ∃ U : TrailFamily G k, U.score=T.score ∧ (U.walk i).toSubgraph=C.toSubgraph ∧
      (∀ Z : TrailFamily G k, Z.score=U.score → (Z.walk i).toSubgraph=C.toSubgraph →
        carrierCount Z C.toSubgraph.verts ≤ carrierCount U C.toSubgraph.verts) ∧
      (∀ Z : TrailFamily G k, Z.score=U.score → (Z.walk i).toSubgraph=C.toSubgraph →
        carrierCount Z C.toSubgraph.verts=carrierCount U C.toSubgraph.verts →
        carrierLength U C.toSubgraph.verts ≤ carrierLength Z C.toSubgraph.verts) := by
  obtain ⟨R,hRs,hRi,hRmax⟩ := exists_maximum_carriers T i C hi
  let P (m : ℕ) := ∃ U : TrailFamily G k, U.score=R.score ∧ (U.walk i).toSubgraph=C.toSubgraph ∧
    carrierCount U C.toSubgraph.verts=carrierCount R C.toSubgraph.verts ∧ carrierLength U C.toSubgraph.verts=m
  have hex : ∃ m, P m := ⟨_,R,rfl,hRi,rfl,rfl⟩
  obtain ⟨U,hUs,hUi,hUc,hUl⟩ := Nat.find_spec hex
  refine ⟨U,hUs.trans hRs,hUi,?_,?_⟩
  · intro Z hZs hZi
    rw [hUc]
    exact hRmax Z (hZs.trans hUs) hZi
  · intro Z hZs hZi hZc
    rw [hUl]
    exact Nat.find_min' hex ⟨Z,hZs.trans hUs,hZi,hZc.trans hUc,rfl⟩

lemma carrierCount_strict_of_new (T U : TrailFamily G k) (S : Set V) (m : Fin k)
    (hmT : ¬Touches S (T.walk m).toSubgraph) (hmU : Touches S (U.walk m).toSubgraph)
    (hkeep : ∀ l, Touches S (T.walk l).toSubgraph → Touches S (U.walk l).toSubgraph) :
    carrierCount T S < carrierCount U S := by
  classical
  apply Finset.sum_lt_sum
  · intro l hl
    by_cases h : Touches S (T.walk l).toSubgraph
    · simp only [if_pos h,if_pos (hkeep l h)]
      exact le_refl _
    · simp only [if_neg h]
      exact Nat.zero_le _
  · exact ⟨m,Finset.mem_univ _,by simp only [if_neg hmT,if_pos hmU]; omega⟩

lemma suffix_remains_carrier [Fintype V] (S : Set V) {w x b : V}
    (h : G.Adj w x) (q : G.Walk x b) (hp : (Walk.cons h q).IsPath) (hw : w ∉ S)
    (hbig : 3 ≤ (S ∩ (Walk.cons h q).toSubgraph.verts).ncard)
    (ht : Touches S (Walk.cons h q).toSubgraph) :
    ¬q.Nil ∧ Touches S q.toSubgraph := by
  have hqn : ¬q.Nil := by
    intro hn
    have hbound := Set.ncard_le_ncard (Set.inter_subset_right :
      S ∩ (Walk.cons h q).toSubgraph.verts ⊆ (Walk.cons h q).toSubgraph.verts)
    have hv := walk_vertex_ncard_le (Walk.cons h q)
    have hl := Walk.nil_iff_length_eq.mp hn
    simp only [Walk.length_cons,hl] at hv
    omega
  refine ⟨hqn,?_⟩
  obtain ⟨z,hz,y,hzy⟩ := ht
  have hzq : z ∈ q.support := by
    have hh := Walk.mem_support_of_adj_toSubgraph hzy
    simp only [Walk.support_cons,List.mem_cons] at hh
    exact hh.resolve_left (fun he ↦ hw (he ▸ hz))
  exact touches_of_nonempty_inter q hp.of_cons hqn ⟨z,hz,q.mem_verts_toSubgraph.mpr hzq⟩

lemma tight_group_no_carrier_start_rep {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)}
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (i j : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) (hij : i ≠ j)
    {r : Fin n} (C : G.Walk r r) (hC : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (hmax : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score=T.score →
      (U.walk i).toSubgraph=C.toSubgraph →
      carrierCount U C.toSubgraph.verts ≤ carrierCount T C.toSubgraph.verts)
    (hmin : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score=T.score →
      (U.walk i).toSubgraph=C.toSubgraph →
      carrierCount U C.toSubgraph.verts=carrierCount T C.toSubgraph.verts →
      carrierLength T C.toSubgraph.verts ≤ carrierLength U C.toSubgraph.verts)
    (F : Finset (Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)) (hiF : i ∉ F) (hjF : j ∉ F)
    (hFC : ∀ z ∈ (selectedGraph T F).support, z ∉ C.support)
    (hconn : SupportConnected (selectedGraph T F))
    (htight : 2*F.card=(selectedGraph T F).support.ncard+1)
    {w x b : Fin n} (h : G.Adj w x) (q : G.Walk x b)
    (hp : (Walk.cons h q).IsPath) (hj : (T.walk j).toSubgraph=(Walk.cons h q).toSubgraph)
    (hw : w ∈ (selectedGraph T F).support)
    (hcarrier : Touches C.toSubgraph.verts (T.walk j).toSubgraph) : False := by
  classical
  have hnp := CycleEar.cycle_member_not_path T i C hC hi
  have hm := CyclePrefixRepair.maximum_of_one_defect_failure hfail T hs
  have hbig : 5 ≤ (C.toSubgraph.verts ∩ (T.walk j).toSubgraph.verts).ncard := by
    apply CycleIntersectionBound.single_defect_cycle_intersection_ge_five T hs hm i j hij C hC hi
    obtain ⟨z,hz,y,hzy⟩ := hcarrier
    exact ⟨z,Walk.mem_support_of_adj_toSubgraph hzy,C.mem_verts_toSubgraph.mp hz⟩
  obtain ⟨hqn,hqC⟩ := suffix_remains_carrier C.toSubgraph.verts h q hp
    (fun hz ↦ hFC w hw (C.mem_verts_toSubgraph.mp hz))
    (by rw [hj] at hbig; omega) (hj ▸ hcarrier)
  have hFcard : F.card < ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
    have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ F,fun hh ↦ hiF (hh.symm ▸ Finset.mem_univ i)⟩)
    simpa only [Finset.card_univ,Fintype.card_fin] using hlt
  have horder : (selectedGraph T F).support.ncard+1 < n := by
    simp only [Fintype.card_fin,BridgeGlue.ceil_half] at hFcard
    omega
  obtain ⟨D,hD,hDc⟩ := attach_edge_partition (t := F.card) hsmall (selectedGraph T F) hconn (x := x) hw horder (by omega)
  obtain ⟨U,hUs,hUj,hrest,hUF,hcov⟩ := absorb_first_edge hfail T hs i j hij hnp F hiF hjF
    h q hp hqn hj D hD hDc
  have hUi : (U.walk i).toSubgraph=C.toSubgraph := (hrest i hiF hij).trans hi
  have hUjC : Touches C.toSubgraph.verts (U.walk j).toSubgraph := hUj.symm ▸ hqC
  have hTF (l) (hl : l ∈ F) : ¬Touches C.toSubgraph.verts (T.walk l).toSubgraph := by
    rintro ⟨z,hz,y,hzy⟩
    exact hFC z ⟨y,l,hl,hzy⟩ (C.mem_verts_toSubgraph.mp hz)
  by_cases hx : x ∈ C.support
  · have hedge : s(w,x) ∈ (selectedGraph T F ⊔ edge w x).edgeSet := by
      exact Or.inr ((edge_adj w x w x).mpr ⟨Or.inl ⟨rfl,rfl⟩,h.ne⟩)
    obtain ⟨m,hmF,hmE⟩ := hcov _ hedge
    have hmU : Touches C.toSubgraph.verts (U.walk m).toSubgraph :=
      ⟨x,C.mem_verts_toSubgraph.mpr hx,w,Subgraph.Adj.symm hmE⟩
    have hlt := carrierCount_strict_of_new T U C.toSubgraph.verts m (hTF m hmF) hmU (by
      intro l hl
      by_cases hlj : l=j
      · subst l; exact hUjC
      have hlF : l ∉ F := fun hh ↦ hTF l hh hl
      rw [hrest l hlF hlj]
      exact hl)
    have hle := hmax U hUs hUi
    omega
  · have hnoUF (l) (hl : l ∈ F) : ¬Touches C.toSubgraph.verts (U.walk l).toSubgraph := by
      rintro ⟨z,hz,y,hzy⟩
      have hzyJ : s(z,y) ∈ (selectedGraph T F ⊔ edge w x).edgeSet := hUF l hl hzy
      have hzJ : z ∈ (selectedGraph T F ⊔ edge w x).support := ⟨y,hzyJ⟩
      rcases attach_edge_support (selectedGraph T F) hw hzJ with hzx|hzF
      · exact hx (hzx ▸ C.mem_verts_toSubgraph.mp hz)
      · exact hFC z hzF (C.mem_verts_toSubgraph.mp hz)
    have hUc : carrierCount U C.toSubgraph.verts=carrierCount T C.toSubgraph.verts := by
      apply carrierCount_congr
      intro l
      by_cases hlj : l=j
      · subst l; exact iff_of_true hUjC hcarrier
      by_cases hlF : l ∈ F
      · exact iff_of_false (hnoUF l hlF) (hTF l hlF)
      · rw [hrest l hlF hlj]
    have hUl : carrierLength U C.toSubgraph.verts+1=carrierLength T C.toSubgraph.verts := by
      apply carrierLength_change_one T U C.toSubgraph.verts j 1
      · simp only [if_pos hUjC,if_pos hcarrier]
        rw [trail_length_of_same_subgraph _ _ (U.isTrail j) hp.of_cons.isTrail hUj,
          trail_length_of_same_subgraph _ _ (T.isTrail j) hp.isTrail hj,Walk.length_cons]
      · intro l hlj
        by_cases hlF : l ∈ F
        · simp only [if_neg (hnoUF l hlF),if_neg (hTF l hlF)]
        · exact carrier_weight_of_same_subgraph T U C.toSubgraph.verts l (hrest l hlF hlj)
    have hle := hmin U hUs hUi hUc
    omega

lemma tight_group_avoids_carriers {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)}
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (i j : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) (hij : i ≠ j)
    {r : Fin n} (C : G.Walk r r) (hC : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (hmax : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score=T.score →
      (U.walk i).toSubgraph=C.toSubgraph →
      carrierCount U C.toSubgraph.verts ≤ carrierCount T C.toSubgraph.verts)
    (hmin : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score=T.score →
      (U.walk i).toSubgraph=C.toSubgraph →
      carrierCount U C.toSubgraph.verts=carrierCount T C.toSubgraph.verts →
      carrierLength T C.toSubgraph.verts ≤ carrierLength U C.toSubgraph.verts)
    (F : Finset (Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)) (hiF : i ∉ F) (hjF : j ∉ F)
    (hFC : ∀ z ∈ (selectedGraph T F).support, z ∉ C.support)
    (hconn : SupportConnected (selectedGraph T F))
    (htight : 2*F.card=(selectedGraph T F).support.ncard+1)
    (hcarrier : Touches C.toSubgraph.verts (T.walk j).toSubgraph) :
    ∀ z ∈ (T.walk j).support, z ∉ (selectedGraph T F).support := by
  intro z hz hzF
  have hnp := CycleEar.cycle_member_not_path T i C hC hi
  have hpj := (T.one_defect_other_paths hs i hnp).2 j hij.symm
  have hmark := tight_normal_group_marked hsmall hfail T hs i hnp F hiF hconn htight
  have hend := fully_marked_group_contains_carrier_endpoint T hs i j hij C hC hi
    (fun U hUs hUi _ ↦ hmax U hUs hUi)
    (fun U hUs hUi _ hUc ↦ hmin U hUs hUi hUc)
    F hiF hjF hFC hmark hcarrier ⟨z,hz,hzF⟩
  have hno (w b : Fin n) (P : G.Walk w b) (hP : P.IsPath)
      (hj : (T.walk j).toSubgraph=P.toSubgraph) : w ∉ (selectedGraph T F).support := by
    intro hw
    cases P with
    | nil =>
      rw [hj] at hcarrier
      simp [Touches] at hcarrier
    | @cons w x b h q =>
      exact tight_group_no_carrier_start_rep hsmall hfail T hs i j hij C hC hi hmax hmin
        F hiF hjF hFC hconn htight h q hP hj hw hcarrier
  rcases hend with hstart|hfinish
  · exact hno _ _ (T.walk j) hpj rfl hstart
  · exact hno _ _ (T.walk j).reverse hpj.reverse (by rw [Walk.toSubgraph_reverse]) hfinish

lemma no_tight_outside_components {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (i : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) {r : Fin n}
    (C : G.Walk r r) (hC : C.IsCycle) (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (hmax : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score=T.score →
      (U.walk i).toSubgraph=C.toSubgraph →
      carrierCount U C.toSubgraph.verts ≤ carrierCount T C.toSubgraph.verts)
    (hmin : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score=T.score →
      (U.walk i).toSubgraph=C.toSubgraph →
      carrierCount U C.toSubgraph.verts=carrierCount T C.toSubgraph.verts →
      carrierLength T C.toSubgraph.verts ≤ carrierLength U C.toSubgraph.verts) :
    tightComponents T (outsideIndices T C.toSubgraph.verts)=∅ := by
  classical
  let B := outsideIndices T C.toSubgraph.verts
  have hiB : i ∉ B := fun hh ↦ outside_not_touched T C.toSubgraph.verts hh (cycle_touches T i C hC hi)
  have hnp := CycleEar.cycle_member_not_path T i C hC hi
  have hm := CyclePrefixRepair.maximum_of_one_defect_failure hfail T hs
  have hn := NilSlot.max_score_nonpath_no_nil T hm ⟨i,hnp⟩
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro D hD
  let F := GroupComponents.componentMembers T B D
  have hFB : F ⊆ B := GroupComponents.componentMembers_subset T B D
  have hFC (z : Fin n) (hz : z ∈ (selectedGraph T F).support) : z ∉ C.support := by
    intro hzC
    exact outside_support_avoids T C.toSubgraph.verts
      (SimpleGraph.support_mono (CycleGroupDisjoint.selectedGraph_mono T hFB) hz)
      (C.mem_verts_toSubgraph.mpr hzC)
  obtain ⟨j,hj,x,hxj,hxF⟩ := GroupComponents.component_meets_outside T hG B ⟨i,hiB⟩ hn D
  have hcarrier : Touches C.toSubgraph.verts (T.walk j).toSubgraph := by
    by_contra hh
    exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩)
  have hji : j ≠ i := by
    rintro rfl
    exact hFC x hxF (by rwa [←Walk.mem_verts_toSubgraph,hi,Walk.mem_verts_toSubgraph] at hxj)
  exact tight_group_avoids_carriers hsmall hfail T hs i j hji.symm C hC hi hmax hmin F
    (fun hh ↦ hiB (hFB hh)) (fun hh ↦ hj (hFB hh)) hFC
    (GroupComponents.component_support_connected T B D) (Finset.mem_filter.mp hD).2 hcarrier x hxj hxF

lemma optimized_cycle_carrier_bound {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (i : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) {r : Fin n}
    (C : G.Walk r r) (hC : C.IsCycle) (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (hmax : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score=T.score →
      (U.walk i).toSubgraph=C.toSubgraph →
      carrierCount U C.toSubgraph.verts ≤ carrierCount T C.toSubgraph.verts)
    (hmin : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score=T.score →
      (U.walk i).toSubgraph=C.toSubgraph →
      carrierCount U C.toSubgraph.verts=carrierCount T C.toSubgraph.verts →
      carrierLength T C.toSubgraph.verts ≤ carrierLength U C.toSubgraph.verts) :
    C.length+2*⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ ≤ n+2*(carrierIndices T i C.toSubgraph.verts).card+2 := by
  have hiB : i ∉ outsideIndices T C.toSubgraph.verts := fun hh ↦
    outside_not_touched T C.toSubgraph.verts hh (cycle_touches T i C hC hi)
  have hround := outside_component_rounding hsmall hfail T hs i
    (CycleEar.cycle_member_not_path T i C hC hi) _ hiB
  rw [no_tight_outside_components hsmall hG hfail T hs i C hC hi hmax hmin,Finset.card_empty] at hround
  have hsplit := outside_carrier_partition T i C.toSubgraph.verts (cycle_touches T i C hC hi)
  have hsize := outside_support_cycle_card T C hC
  simp only [Fintype.card_fin] at hsize
  omega

lemma optimized_cycle_length_bound {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (i : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) {r : Fin n}
    (C : G.Walk r r) (hC : C.IsCycle) (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (hmax : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score=T.score →
      (U.walk i).toSubgraph=C.toSubgraph →
      carrierCount U C.toSubgraph.verts ≤ carrierCount T C.toSubgraph.verts)
    (hmin : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score=T.score →
      (U.walk i).toSubgraph=C.toSubgraph →
      carrierCount U C.toSubgraph.verts=carrierCount T C.toSubgraph.verts →
      carrierLength T C.toSubgraph.verts ≤ carrierLength U C.toSubgraph.verts) :
    C.length ≤ 2*(carrierIndices T i C.toSubgraph.verts).card+2 ∧
      (Odd n → C.length ≤ 2*(carrierIndices T i C.toSubgraph.verts).card+1) := by
  have hh := optimized_cycle_carrier_bound hsmall hG hfail T hs i C hC hi hmax hmin
  simp only [Fintype.card_fin,BridgeGlue.ceil_half] at hh
  constructor
  · omega
  · rintro ⟨m,hm⟩
    omega

/-- An optimized fixed-cycle representative, without a quota or incidence
preservation assertion. The carrier lower bounds use the separate exclusion
of whole cycles of length at most seven. -/
lemma exists_optimized_cycle_certificate {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (i : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) {r : Fin n}
    (C : G.Walk r r) (hC : C.IsCycle) (hi : (T.walk i).toSubgraph=C.toSubgraph) :
    ∃ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊,
      U.score=T.score ∧ (U.walk i).toSubgraph=C.toSubgraph ∧
      tightComponents U (outsideIndices U C.toSubgraph.verts)=∅ ∧
      C.length ≤ 2*(carrierIndices U i C.toSubgraph.verts).card+2 ∧
      3 ≤ (carrierIndices U i C.toSubgraph.verts).card ∧
      (Odd n → C.length ≤ 2*(carrierIndices U i C.toSubgraph.verts).card+1 ∧
        4 ≤ (carrierIndices U i C.toSubgraph.verts).card) := by
  obtain ⟨U,hUs,hUi,hUmax,hUmin⟩ := exists_shortest_maximum_carriers T i C hi
  have hUs' : U.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := hUs.symm ▸ hs
  have hlen := optimized_cycle_length_bound hsmall hG hfail U hUs' i C hC hUi hUmax hUmin
  have hlo := HeptagonExclusion.whole_cycle_length_ge_eight hsmall hG hfail U hUs'
    (CyclePrefixRepair.maximum_of_one_defect_failure hfail U hUs') i C hC hUi
  refine ⟨U,hUs,hUi,no_tight_outside_components hsmall hG hfail U hUs' i C hC hUi hUmax hUmin,
    hlen.1,by omega,?_⟩
  intro ho
  have hh := hlen.2 ho
  exact ⟨hh,by omega⟩

end Erdos583FreeCarrierDevelopment
