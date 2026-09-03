import Submission.Work
import Submission.EdgeAbsorption
import Submission.FreeCarrier
import Submission.TightAttachment

/-! Carrier optimization around an arbitrary fixed defective subgraph. -/
namespace Erdos583AnchorCarrierDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.MemberExpansion
open Erdos583Work.MemberNormalExpansion Erdos583Work.MarkedCycleGroups
open Erdos583Work.CarrierCuts Erdos583Work.CarrierCount Erdos583Work.CarrierLength
open Erdos583Work.CarrierGroups Erdos583Work.OutsideCarrierBudget Erdos583Work.VertexCritical
open Erdos583EdgeAbsorptionDevelopment
open Erdos583TightAttachmentDevelopment
open scoped Classical
set_option maxHeartbeats 2200000
variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

lemma member_not_path (T : TrailFamily G k) (i : Fin k) (K : G.Subgraph)
    (hnK : ¬IsPathSubgraph K) (hi : (T.walk i).toSubgraph=K) : ¬(T.walk i).IsPath := by
  intro hp
  exact hnK ⟨_,_,T.walk i,hp,hi.symm⟩

lemma exists_maximum_carriers (T : TrailFamily G k) (i : Fin k) (K : G.Subgraph) (hi : (T.walk i).toSubgraph=K) :
    ∃ U : TrailFamily G k, U.score=T.score ∧ (U.walk i).toSubgraph=K ∧
      (∀ Z : TrailFamily G k, Z.score=U.score → (Z.walk i).toSubgraph=K →
        carrierCount Z K.verts ≤ carrierCount U K.verts) := by
  let P (m : ℕ) := ∃ U : TrailFamily G k, U.score=T.score ∧
    (U.walk i).toSubgraph=K ∧ k-carrierCount U K.verts=m
  have hex : ∃ m, P m := ⟨_,T,rfl,hi,rfl⟩
  obtain ⟨U,hUs,hUi,hUc⟩ := Nat.find_spec hex
  refine ⟨U,hUs,hUi,?_⟩
  intro Z hZs hZi
  have hm := Nat.find_min' hex (show P (k-carrierCount Z K.verts) from
    ⟨Z,hZs.trans hUs,hZi,rfl⟩)
  have hU := carrierCount_le U K.verts
  have hZ := carrierCount_le Z K.verts
  omega

lemma exists_shortest_maximum_carriers (T : TrailFamily G k) (i : Fin k) (K : G.Subgraph) (hi : (T.walk i).toSubgraph=K) :
    ∃ U : TrailFamily G k, U.score=T.score ∧ (U.walk i).toSubgraph=K ∧
      (∀ Z : TrailFamily G k, Z.score=U.score → (Z.walk i).toSubgraph=K →
        carrierCount Z K.verts ≤ carrierCount U K.verts) ∧
      (∀ Z : TrailFamily G k, Z.score=U.score → (Z.walk i).toSubgraph=K →
        carrierCount Z K.verts=carrierCount U K.verts →
        carrierLength U K.verts ≤ carrierLength Z K.verts) := by
  obtain ⟨R,hRs,hRi,hRmax⟩ := exists_maximum_carriers T i K hi
  let P (m : ℕ) := ∃ U : TrailFamily G k, U.score=R.score ∧ (U.walk i).toSubgraph=K ∧
    carrierCount U K.verts=carrierCount R K.verts ∧ carrierLength U K.verts=m
  have hex : ∃ m, P m := ⟨_,R,rfl,hRi,rfl,rfl⟩
  obtain ⟨U,hUs,hUi,hUc,hUl⟩ := Nat.find_spec hex
  refine ⟨U,hUs.trans hRs,hUi,?_,?_⟩
  · intro Z hZs hZi
    rw [hUc]
    exact hRmax Z (hZs.trans hUs) hZi
  · intro Z hZs hZi hZc
    rw [hUl]
    exact Nat.find_min' hex ⟨Z,hZs.trans hUs,hZi,hZc.trans hUc,rfl⟩

lemma marked_internal_cut_increases_carriers [Fintype V]
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (i j : Fin k) (hij : i ≠ j) (K : G.Subgraph) (hnK : ¬IsPathSubgraph K)
    (hi : (T.walk i).toSubgraph=K)
    (F : Finset (Fin k)) (hiF : i ∉ F) (hjF : j ∉ F)
    (hFC : ∀ x ∈ (selectedGraph T F).support, x ∉ K.verts)
    {a z b : V} (A : G.Walk a z) (B : G.Walk z b) (hAB : (A.append B).IsPath)
    (hj : (T.walk j).toSubgraph=(A.append B).toSubgraph)
    (hprefix : ∀ x ∈ A.support, x ∈ (selectedGraph T F).support → x=z)
    (hmark : MarkedPartition (selectedGraph T F) F.card z)
    (hA : (K.verts ∩ A.toSubgraph.verts).Nonempty)
    (hB : (K.verts ∩ B.toSubgraph.verts).Nonempty) :
    ∃ U : TrailFamily G k, U.score=T.score ∧ (U.walk i).toSubgraph=K ∧
      PreservesIncidence T U K.verts ∧
      carrierCount U K.verts=carrierCount T K.verts+1 := by
  classical
  have hnp := member_not_path T i K hnK hi
  obtain ⟨D,d,P,hD,hcard,hP,hnP,hPD⟩ := hmark
  have hzF : z ∈ (selectedGraph T F).support := path_support_subset_graph_support hP hnP z P.start_mem_support
  have hzC := hFC z hzF
  obtain ⟨Z,hZs,hrest,_,hZin,hparts⟩ := GroupActivation.replace_path_group_tracked T F
    (fun l hl ↦ (T.one_defect_other_paths hs i hnp).2 l (fun he ↦ hiF (he ▸ hl))) D hD hcard
  have hTF (l : Fin k) (hl : l ∈ F) : ¬Touches K.verts (T.walk l).toSubgraph := by
    rintro ⟨x,hx,y,hxy⟩
    exact hFC x ⟨y,l,hl,hxy⟩ hx
  have hZF (l : Fin k) (hl : l ∈ F) : ¬Touches K.verts (Z.walk l).toSubgraph := by
    rintro ⟨x,hx,y,hxy⟩
    obtain ⟨K,hK,hKe⟩ := hZin l hl
    have he : s(x,y) ∈ (Z.walk l).toSubgraph.edgeSet := hxy
    rw [hKe,edgeSet_lift] at he
    exact hFC x ⟨y,K.edgeSet_subset he⟩ hx
  have hZc : carrierCount Z K.verts=carrierCount T K.verts := by
    apply carrierCount_congr
    intro l
    by_cases hl : l ∈ F
    · exact iff_of_false (hZF l hl) (hTF l hl)
    · rw [(hrest l hl).2.2]
  obtain ⟨m,hmF,hZm⟩ := hparts P.toSubgraph hPD
  have hjm : j ≠ m := fun he ↦ hjF (he.symm ▸ hmF)
  have him : i ≠ m := fun he ↦ hiF (he.symm ▸ hmF)
  let Q := P.mapLe (selectedGraph_le T F)
  have hQ : Q.IsPath := hP.mapLe _
  have hQe : Q.toSubgraph=P.toSubgraph.map (Hom.ofLE (selectedGraph_le T F)) := by
    simp only [Q,Walk.mapLe,Walk.toSubgraph_map]
  have hQs (x : V) (hx : x ∈ Q.support) : x ∈ (selectedGraph T F).support := by
    apply path_support_subset_graph_support hP hnP x
    simpa only [Q,Walk.support_mapLe_eq_support] using hx
  obtain ⟨U,hUs,hUj,hUm,hUrest⟩ := cut_carrier_at_marked_path Z j m hjm A B Q hAB hQ
    ((hrest j hjF).2.2.trans hj) (hZm.trans hQe.symm)
    (fun x hx hy ↦ hprefix x hx (hQs x hy))
  have hnA : ¬A.Nil := by
    intro hn
    obtain ⟨x,hxC,hxA⟩ := hA
    have hx : x=a := by
      simpa only [Walk.nil_iff_support_eq.mp hn,List.mem_singleton] using A.mem_verts_toSubgraph.mp hxA
    exact hzC ((hx.trans hn.eq) ▸ hxC)
  have hnB : ¬B.Nil := by
    intro hn
    obtain ⟨x,hxC,hxB⟩ := hB
    have hx : x=z := by
      simpa only [Walk.nil_iff_support_eq.mp hn,List.mem_singleton] using B.mem_verts_toSubgraph.mp hxB
    exact hzC (hx ▸ hxC)
  have htA := touches_of_nonempty_inter A hAB.of_append_left hnA hA
  have htB := touches_of_nonempty_inter B hAB.of_append_right hnB hB
  have hcount : carrierCount U K.verts=carrierCount Z K.verts+1 := by
    apply carrierCount_increase Z U K.verts m (hZF m hmF)
    · rw [hUm,touches_append]
      exact Or.inl htA
    · intro l hlm
      by_cases hlj : l=j
      · subst l
        rw [(hrest j hjF).2.2,hj,hUj,touches_append]
        exact iff_of_true (Or.inr htB) htB
      · rw [hUrest l hlj hlm]
  have hZp := untouched_group_preserves T Z K.verts F
    (fun l hl ↦ (hrest l hl).2.2) hTF hZF
  have hUp := carrier_cut_preserves Z U K.verts j m hjm A B Q hAB
    (fun hz ↦ hzC hz)
    (fun ht ↦ hZF m hmF ((hZm.trans hQe.symm).symm ▸ ht))
    ((hrest j hjF).2.2.trans hj) (hZm.trans hQe.symm) hUj hUm hUrest
  exact ⟨U,hUs.trans hZs,(hUrest i hij him).trans ((hrest i hiF).2.2.trans hi),
    preserves_trans hZp hUp,by rw [hcount,hZc]⟩

lemma maximum_carriers_no_marked_internal_cut [Fintype V]
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (i j : Fin k) (hij : i ≠ j) (K : G.Subgraph) (hnK : ¬IsPathSubgraph K)
    (hi : (T.walk i).toSubgraph=K)
    (hmax : ∀ U : TrailFamily G k, U.score=T.score → (U.walk i).toSubgraph=K →
      PreservesIncidence T U K.verts →
      carrierCount U K.verts ≤ carrierCount T K.verts)
    (F : Finset (Fin k)) (hiF : i ∉ F) (hjF : j ∉ F)
    (hFC : ∀ x ∈ (selectedGraph T F).support, x ∉ K.verts)
    {a z b : V} (A : G.Walk a z) (B : G.Walk z b) (hAB : (A.append B).IsPath)
    (hj : (T.walk j).toSubgraph=(A.append B).toSubgraph)
    (hprefix : ∀ x ∈ A.support, x ∈ (selectedGraph T F).support → x=z)
    (hmark : MarkedPartition (selectedGraph T F) F.card z)
    (hA : (K.verts ∩ A.toSubgraph.verts).Nonempty)
    (hB : (K.verts ∩ B.toSubgraph.verts).Nonempty) : False := by
  obtain ⟨U,hUs,hUi,hUp,hUc⟩ := marked_internal_cut_increases_carriers T hs i j hij K hnK hi F hiF hjF
    hFC A B hAB hj hprefix hmark hA hB
  have hh := hmax U hUs hUi hUp
  omega

lemma marked_prefix_shortens_carrier [Fintype V]
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (i j : Fin k) (hij : i ≠ j) (K : G.Subgraph) (hnK : ¬IsPathSubgraph K)
    (hi : (T.walk i).toSubgraph=K)
    (F : Finset (Fin k)) (hiF : i ∉ F) (hjF : j ∉ F)
    (hFC : ∀ x ∈ (selectedGraph T F).support, x ∉ K.verts)
    {a z b : V} (A : G.Walk a z) (B : G.Walk z b) (hAB : (A.append B).IsPath)
    (hj : (T.walk j).toSubgraph=(A.append B).toSubgraph)
    (hprefix : ∀ x ∈ A.support, x ∈ (selectedGraph T F).support → x=z)
    (hmark : MarkedPartition (selectedGraph T F) F.card z)
    (hA : ¬Touches K.verts A.toSubgraph) (hB : Touches K.verts B.toSubgraph) :
    ∃ U : TrailFamily G k, U.score=T.score ∧ (U.walk i).toSubgraph=K ∧
      PreservesIncidence T U K.verts ∧
      carrierCount U K.verts=carrierCount T K.verts ∧
      carrierLength U K.verts+A.length=carrierLength T K.verts := by
  classical
  have hnp := member_not_path T i K hnK hi
  obtain ⟨D,d,P,hD,hcard,hP,hnP,hPD⟩ := hmark
  obtain ⟨Z,hZs,hrest,_,hZin,hparts⟩ := GroupActivation.replace_path_group_tracked T F
    (fun l hl ↦ (T.one_defect_other_paths hs i hnp).2 l (fun he ↦ hiF (he ▸ hl))) D hD hcard
  have hTF (l : Fin k) (hl : l ∈ F) : ¬Touches K.verts (T.walk l).toSubgraph := by
    rintro ⟨x,hx,y,hxy⟩
    exact hFC x ⟨y,l,hl,hxy⟩ hx
  have hZF (l : Fin k) (hl : l ∈ F) : ¬Touches K.verts (Z.walk l).toSubgraph := by
    rintro ⟨x,hx,y,hxy⟩
    obtain ⟨K,hK,hKe⟩ := hZin l hl
    have he : s(x,y) ∈ (Z.walk l).toSubgraph.edgeSet := hxy
    rw [hKe,edgeSet_lift] at he
    exact hFC x ⟨y,K.edgeSet_subset he⟩ hx
  obtain ⟨hZc,hZL⟩ := untouched_group_invariants T Z K.verts F
    (fun l hl ↦ (hrest l hl).2.2) hTF hZF
  obtain ⟨m,hmF,hZm⟩ := hparts P.toSubgraph hPD
  have hjm : j ≠ m := fun he ↦ hjF (he.symm ▸ hmF)
  have him : i ≠ m := fun he ↦ hiF (he.symm ▸ hmF)
  let Q := P.mapLe (selectedGraph_le T F)
  have hQ : Q.IsPath := hP.mapLe _
  have hQe : Q.toSubgraph=P.toSubgraph.map (Hom.ofLE (selectedGraph_le T F)) := by
    simp only [Q,Walk.mapLe,Walk.toSubgraph_map]
  have hQs (x : V) (hx : x ∈ Q.support) : x ∈ (selectedGraph T F).support := by
    apply path_support_subset_graph_support hP hnP x
    simpa only [Q,Walk.support_mapLe_eq_support] using hx
  have htQ : ¬Touches K.verts Q.toSubgraph := by
    rintro ⟨x,hx,y,hxy⟩
    exact hFC x (hQs x (Walk.mem_support_of_adj_toSubgraph hxy)) hx
  obtain ⟨U,hUs,hUj,hUm,hUrest⟩ := cut_carrier_at_marked_path Z j m hjm A B Q hAB hQ
    ((hrest j hjF).2.2.trans hj) (hZm.trans hQe.symm)
    (fun x hx hy ↦ hprefix x hx (hQs x hy))
  have hTj : Touches K.verts (Z.walk j).toSubgraph := by
    rw [(hrest j hjF).2.2,hj,touches_append]
    exact Or.inr hB
  have hUjm : ¬Touches K.verts (U.walk m).toSubgraph := by
    rw [hUm,touches_append]
    exact not_or.mpr ⟨hA,htQ⟩
  have hUjj : Touches K.verts (U.walk j).toSubgraph := hUj.symm ▸ hB
  have hUc : carrierCount U K.verts=carrierCount Z K.verts := by
    apply carrierCount_congr
    intro l
    by_cases hlj : l=j
    · subst l
      exact iff_of_true hUjj hTj
    · by_cases hlm : l=m
      · subst l
        exact iff_of_false hUjm (hZF m hmF)
      · rw [hUrest l hlj hlm]
  have hUl : carrierLength U K.verts+A.length=carrierLength Z K.verts := by
    apply carrierLength_change_one Z U K.verts j A.length
    · simp only [if_pos hUjj,if_pos hTj]
      rw [trail_length_of_same_subgraph _ _ (U.isTrail j) hAB.of_append_right.isTrail hUj,
        trail_length_of_same_subgraph _ _ (Z.isTrail j) hAB.isTrail ((hrest j hjF).2.2.trans hj),Walk.length_append]
      omega
    · intro l hlj
      by_cases hlm : l=m
      · subst l
        simp only [if_neg hUjm,if_neg (hZF m hmF)]
      · exact carrier_weight_of_same_subgraph Z U K.verts l (hUrest l hlj hlm)
  have hZp := untouched_group_preserves T Z K.verts F
    (fun l hl ↦ (hrest l hl).2.2) hTF hZF
  have hz : z ∉ K.verts := fun hh ↦
    hFC z (hQs z Q.start_mem_support) hh
  have hUp := carrier_cut_preserves Z U K.verts j m hjm A B Q hAB hz htQ
    ((hrest j hjF).2.2.trans hj) (hZm.trans hQe.symm) hUj hUm hUrest
  exact ⟨U,hUs.trans hZs,(hUrest i hij him).trans ((hrest i hiF).2.2.trans hi),
    preserves_trans hZp hUp,hUc.trans hZc,hUl.trans hZL⟩

lemma shortest_carrier_marked_prefix_nil [Fintype V]
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (i j : Fin k) (hij : i ≠ j) (K : G.Subgraph) (hnK : ¬IsPathSubgraph K)
    (hi : (T.walk i).toSubgraph=K)
    (hmin : ∀ U : TrailFamily G k, U.score=T.score → (U.walk i).toSubgraph=K →
      PreservesIncidence T U K.verts →
      carrierCount U K.verts=carrierCount T K.verts →
      carrierLength T K.verts ≤ carrierLength U K.verts)
    (F : Finset (Fin k)) (hiF : i ∉ F) (hjF : j ∉ F)
    (hFC : ∀ x ∈ (selectedGraph T F).support, x ∉ K.verts)
    {a z b : V} (A : G.Walk a z) (B : G.Walk z b) (hAB : (A.append B).IsPath)
    (hj : (T.walk j).toSubgraph=(A.append B).toSubgraph)
    (hprefix : ∀ x ∈ A.support, x ∈ (selectedGraph T F).support → x=z)
    (hmark : MarkedPartition (selectedGraph T F) F.card z)
    (hA : ¬Touches K.verts A.toSubgraph) (hB : Touches K.verts B.toSubgraph) :
    A.Nil := by
  obtain ⟨U,hUs,hUi,hUp,hUc,hUl⟩ := marked_prefix_shortens_carrier T hs i j hij K hnK hi F hiF hjF
    hFC A B hAB hj hprefix hmark hA hB
  have hh := hmin U hUs hUi hUp hUc
  exact Walk.nil_iff_length_eq.mpr (by omega)

lemma first_marked_hit_start_or_free_suffix [Fintype V]
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (i j : Fin k) (hij : i ≠ j) (K : G.Subgraph) (hnK : ¬IsPathSubgraph K)
    (hi : (T.walk i).toSubgraph=K)
    (hmax : ∀ U : TrailFamily G k, U.score=T.score → (U.walk i).toSubgraph=K →
      PreservesIncidence T U K.verts →
      carrierCount U K.verts ≤ carrierCount T K.verts)
    (hmin : ∀ U : TrailFamily G k, U.score=T.score → (U.walk i).toSubgraph=K →
      PreservesIncidence T U K.verts →
      carrierCount U K.verts=carrierCount T K.verts →
      carrierLength T K.verts ≤ carrierLength U K.verts)
    (F : Finset (Fin k)) (hiF : i ∉ F) (hjF : j ∉ F)
    (hFC : ∀ x ∈ (selectedGraph T F).support, x ∉ K.verts)
    {a z b : V} (A : G.Walk a z) (B : G.Walk z b) (hAB : (A.append B).IsPath)
    (hj : (T.walk j).toSubgraph=(A.append B).toSubgraph)
    (hprefix : ∀ x ∈ A.support, x ∈ (selectedGraph T F).support → x=z)
    (hmark : MarkedPartition (selectedGraph T F) F.card z) :
    A.Nil ∨ ¬Touches K.verts B.toSubgraph := by
  classical
  by_cases hB : Touches K.verts B.toSubgraph
  · by_cases hA : Touches K.verts A.toSubgraph
    · have hA' : (K.verts ∩ A.toSubgraph.verts).Nonempty := by
        obtain ⟨x,hx,y,hxy⟩ := hA
        exact ⟨x,hx,A.toSubgraph.edge_vert hxy⟩
      have hB' : (K.verts ∩ B.toSubgraph.verts).Nonempty := by
        obtain ⟨x,hx,y,hxy⟩ := hB
        exact ⟨x,hx,B.toSubgraph.edge_vert hxy⟩
      exact (maximum_carriers_no_marked_internal_cut T hs i j hij K hnK hi hmax F hiF hjF
        hFC A B hAB hj hprefix hmark hA' hB').elim
    · exact Or.inl (shortest_carrier_marked_prefix_nil T hs i j hij K hnK hi hmin F hiF hjF
        hFC A B hAB hj hprefix hmark hA hB)
  · exact Or.inr hB

lemma fully_marked_group_contains_carrier_endpoint [Fintype V]
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (i j : Fin k) (hij : i ≠ j) (K : G.Subgraph) (hnK : ¬IsPathSubgraph K)
    (hi : (T.walk i).toSubgraph=K)
    (hmax : ∀ U : TrailFamily G k, U.score=T.score → (U.walk i).toSubgraph=K →
      PreservesIncidence T U K.verts →
      carrierCount U K.verts ≤ carrierCount T K.verts)
    (hmin : ∀ U : TrailFamily G k, U.score=T.score → (U.walk i).toSubgraph=K →
      PreservesIncidence T U K.verts →
      carrierCount U K.verts=carrierCount T K.verts →
      carrierLength T K.verts ≤ carrierLength U K.verts)
    (F : Finset (Fin k)) (hiF : i ∉ F) (hjF : j ∉ F)
    (hFC : ∀ x ∈ (selectedGraph T F).support, x ∉ K.verts)
    (hmark : ∀ x ∈ (selectedGraph T F).support, MarkedPartition (selectedGraph T F) F.card x)
    (hcarrier : Touches K.verts (T.walk j).toSubgraph)
    (hhit : ∃ x ∈ (T.walk j).support, x ∈ (selectedGraph T F).support) :
    T.start j ∈ (selectedGraph T F).support ∨ T.finish j ∈ (selectedGraph T F).support := by
  classical
  have hnp := member_not_path T i K hnK hi
  have hpj := (T.one_defect_other_paths hs i hnp).2 j hij.symm
  obtain ⟨x,hx,A,B,hform,hprefix⟩ := QuadrilateralAbsorption.first_hit_split (T.walk j)
    (selectedGraph T F).support hhit
  have hAB : (A.append B).IsPath := hform ▸ hpj
  have hj := congrArg Walk.toSubgraph hform
  rcases first_marked_hit_start_or_free_suffix T hs i j hij K hnK hi hmax hmin F hiF hjF
    hFC A B hAB hj hprefix (hmark x hx) with hnA|hBfree
  · exact Or.inl (hnA.eq.symm ▸ hx)
  · obtain ⟨y,hy,D,E,hB,hE⟩ := CycleDefect.last_hit_split B (selectedGraph T F).support
      ⟨x,B.start_mem_support,hx⟩
    have hrev : (T.walk j).reverse=E.reverse.append (A.append D).reverse := by
      simp only [hform,hB,Walk.reverse_append,Walk.append_assoc]
    have hrevEq : (T.walk j).toSubgraph=(E.reverse.append (A.append D).reverse).toSubgraph := by
      rw [←hrev,Walk.toSubgraph_reverse]
    have hrevP : (E.reverse.append (A.append D).reverse).IsPath := hrev ▸ hpj.reverse
    have hEfree : ¬Touches K.verts E.reverse.toSubgraph := by
      rw [Walk.toSubgraph_reverse]
      intro he
      apply hBfree
      rw [hB,touches_append]
      exact Or.inr he
    have htail : Touches K.verts (A.append D).reverse.toSubgraph := by
      rw [hrevEq,touches_append] at hcarrier
      exact hcarrier.resolve_left hEfree
    have hprefixE : ∀ z ∈ E.reverse.support, z ∈ (selectedGraph T F).support → z=y := by
      intro z hz hzF
      exact hE z (by simpa only [Walk.support_reverse,List.mem_reverse] using hz) hzF
    have hnErev := shortest_carrier_marked_prefix_nil T hs i j hij K hnK hi hmin F hiF hjF hFC
      E.reverse (A.append D).reverse hrevP hrevEq hprefixE (hmark y hy) hEfree htail
    have hnE : E.Nil := by simpa using hnErev
    exact Or.inr (hnE.eq ▸ hy)

lemma anchor_touches (T : TrailFamily G k) (i : Fin k) (K : G.Subgraph)
    (hnK : ¬IsPathSubgraph K) (hi : (T.walk i).toSubgraph=K) : Touches K.verts (T.walk i).toSubgraph := by
  have hn : ¬(T.walk i).Nil := by
    intro hh
    apply member_not_path T i K hnK hi
    apply Walk.IsPath.mk'
    rw [Walk.nil_iff_support_eq.mp hh]
    simp
  obtain ⟨y,hy⟩ := VertexTracking.walk_vertex_has_subgraph_neighbor (T.walk i) hn (T.walk i).start_mem_verts_toSubgraph
  exact ⟨T.start i,hi ▸ (T.walk i).start_mem_verts_toSubgraph,y,hy⟩

lemma outside_support_anchor_card [Fintype V] (T : TrailFamily G k) (K : G.Subgraph) :
    (selectedGraph T (outsideIndices T K.verts)).support.ncard+K.verts.ncard ≤ Fintype.card V := by
  have hh := Set.ncard_mono (outside_support_avoids T K.verts)
  have hs := K.verts.ncard_add_ncard_compl
  rw [Nat.card_eq_fintype_card] at hs
  omega

lemma tight_group_no_carrier_start_rep {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)}
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (i j : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) (hij : i ≠ j)
    (K : G.Subgraph) (hnK : ¬IsPathSubgraph K)
    (hi : (T.walk i).toSubgraph=K)
    (hmax : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score=T.score →
      (U.walk i).toSubgraph=K →
      carrierCount U K.verts ≤ carrierCount T K.verts)
    (hmin : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score=T.score →
      (U.walk i).toSubgraph=K →
      carrierCount U K.verts=carrierCount T K.verts →
      carrierLength T K.verts ≤ carrierLength U K.verts)
    (F : Finset (Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)) (hiF : i ∉ F) (hjF : j ∉ F)
    (hFC : ∀ z ∈ (selectedGraph T F).support, z ∉ K.verts)
    (hconn : SupportConnected (selectedGraph T F))
    (htight : 2*F.card=(selectedGraph T F).support.ncard+1)
    {w x b : Fin n} (h : G.Adj w x) (q : G.Walk x b)
    (hp : (Walk.cons h q).IsPath) (hj : (T.walk j).toSubgraph=(Walk.cons h q).toSubgraph)
    (hw : w ∈ (selectedGraph T F).support)
    (hcarrier : Touches K.verts (T.walk j).toSubgraph) : False := by
  classical
  have hnp := member_not_path T i K hnK hi
  have hqn := suffix_nonempty_at_tight_group hsmall hfail T hs i j hij hnp F hiF hjF hconn htight h q hj hw
  have hqC : Touches K.verts q.toSubgraph := by
    obtain ⟨z,hz,y,hzy⟩ := hcarrier
    have hzw : z ≠ w := fun hh ↦ hFC w hw (hh ▸ hz)
    have hzq : z ∈ q.support := by
      have hh := Walk.mem_support_of_adj_toSubgraph hzy
      rw [←Walk.mem_verts_toSubgraph,hj,Walk.mem_verts_toSubgraph,Walk.support_cons,List.mem_cons] at hh
      exact hh.resolve_left hzw
    exact touches_of_nonempty_inter q hp.of_cons hqn ⟨z,hz,q.mem_verts_toSubgraph.mpr hzq⟩
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
  have hUi : (U.walk i).toSubgraph=K := (hrest i hiF hij).trans hi
  have hUjC : Touches K.verts (U.walk j).toSubgraph := hUj.symm ▸ hqC
  have hTF (l) (hl : l ∈ F) : ¬Touches K.verts (T.walk l).toSubgraph := by
    rintro ⟨z,hz,y,hzy⟩
    exact hFC z ⟨y,l,hl,hzy⟩ hz
  by_cases hx : x ∈ K.verts
  · have hedge : s(w,x) ∈ (selectedGraph T F ⊔ edge w x).edgeSet := by
      exact Or.inr ((edge_adj w x w x).mpr ⟨Or.inl ⟨rfl,rfl⟩,h.ne⟩)
    obtain ⟨m,hmF,hmE⟩ := hcov _ hedge
    have hmU : Touches K.verts (U.walk m).toSubgraph :=
      ⟨x,hx,w,Subgraph.Adj.symm hmE⟩
    have hlt := Erdos583FreeCarrierDevelopment.carrierCount_strict_of_new T U K.verts m (hTF m hmF) hmU (by
      intro l hl
      by_cases hlj : l=j
      · subst l; exact hUjC
      have hlF : l ∉ F := fun hh ↦ hTF l hh hl
      rw [hrest l hlF hlj]
      exact hl)
    have hle := hmax U hUs hUi
    omega
  · have hnoUF (l) (hl : l ∈ F) : ¬Touches K.verts (U.walk l).toSubgraph := by
      rintro ⟨z,hz,y,hzy⟩
      have hzyJ : s(z,y) ∈ (selectedGraph T F ⊔ edge w x).edgeSet := hUF l hl hzy
      have hzJ : z ∈ (selectedGraph T F ⊔ edge w x).support := ⟨y,hzyJ⟩
      rcases attach_edge_support (selectedGraph T F) hw hzJ with hzx|hzF
      · exact hx (hzx ▸ hz)
      · exact hFC z hzF hz
    have hUc : carrierCount U K.verts=carrierCount T K.verts := by
      apply carrierCount_congr
      intro l
      by_cases hlj : l=j
      · subst l; exact iff_of_true hUjC hcarrier
      by_cases hlF : l ∈ F
      · exact iff_of_false (hnoUF l hlF) (hTF l hlF)
      · rw [hrest l hlF hlj]
    have hUl : carrierLength U K.verts+1=carrierLength T K.verts := by
      apply carrierLength_change_one T U K.verts j 1
      · simp only [if_pos hUjC,if_pos hcarrier]
        rw [trail_length_of_same_subgraph _ _ (U.isTrail j) hp.of_cons.isTrail hUj,
          trail_length_of_same_subgraph _ _ (T.isTrail j) hp.isTrail hj,Walk.length_cons]
      · intro l hlj
        by_cases hlF : l ∈ F
        · simp only [if_neg (hnoUF l hlF),if_neg (hTF l hlF)]
        · exact carrier_weight_of_same_subgraph T U K.verts l (hrest l hlF hlj)
    have hle := hmin U hUs hUi hUc
    omega

lemma tight_group_avoids_carriers {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)}
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (i j : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) (hij : i ≠ j)
    (K : G.Subgraph) (hnK : ¬IsPathSubgraph K)
    (hi : (T.walk i).toSubgraph=K)
    (hmax : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score=T.score →
      (U.walk i).toSubgraph=K →
      carrierCount U K.verts ≤ carrierCount T K.verts)
    (hmin : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score=T.score →
      (U.walk i).toSubgraph=K →
      carrierCount U K.verts=carrierCount T K.verts →
      carrierLength T K.verts ≤ carrierLength U K.verts)
    (F : Finset (Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)) (hiF : i ∉ F) (hjF : j ∉ F)
    (hFC : ∀ z ∈ (selectedGraph T F).support, z ∉ K.verts)
    (hconn : SupportConnected (selectedGraph T F))
    (htight : 2*F.card=(selectedGraph T F).support.ncard+1)
    (hcarrier : Touches K.verts (T.walk j).toSubgraph) :
    ∀ z ∈ (T.walk j).support, z ∉ (selectedGraph T F).support := by
  intro z hz hzF
  have hnp := member_not_path T i K hnK hi
  have hpj := (T.one_defect_other_paths hs i hnp).2 j hij.symm
  have hmark := tight_normal_group_marked hsmall hfail T hs i hnp F hiF hconn htight
  have hend := fully_marked_group_contains_carrier_endpoint T hs i j hij K hnK hi
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
      exact tight_group_no_carrier_start_rep hsmall hfail T hs i j hij K hnK hi hmax hmin
        F hiF hjF hFC hconn htight h q hP hj hw hcarrier
  rcases hend with hstart|hfinish
  · exact hno _ _ (T.walk j) hpj rfl hstart
  · exact hno _ _ (T.walk j).reverse hpj.reverse (by rw [Walk.toSubgraph_reverse]) hfinish

lemma no_tight_outside_components {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (i : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) (K : G.Subgraph) (hnK : ¬IsPathSubgraph K) (hi : (T.walk i).toSubgraph=K)
    (hmax : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score=T.score →
      (U.walk i).toSubgraph=K →
      carrierCount U K.verts ≤ carrierCount T K.verts)
    (hmin : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score=T.score →
      (U.walk i).toSubgraph=K →
      carrierCount U K.verts=carrierCount T K.verts →
      carrierLength T K.verts ≤ carrierLength U K.verts) :
    tightComponents T (outsideIndices T K.verts)=∅ := by
  classical
  let B := outsideIndices T K.verts
  have hiB : i ∉ B := fun hh ↦ outside_not_touched T K.verts hh (anchor_touches T i K hnK hi)
  have hnp := member_not_path T i K hnK hi
  have hm := CyclePrefixRepair.maximum_of_one_defect_failure hfail T hs
  have hn := NilSlot.max_score_nonpath_no_nil T hm ⟨i,hnp⟩
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro D hD
  let F := GroupComponents.componentMembers T B D
  have hFB : F ⊆ B := GroupComponents.componentMembers_subset T B D
  have hFC (z : Fin n) (hz : z ∈ (selectedGraph T F).support) : z ∉ K.verts := by
    intro hzC
    exact outside_support_avoids T K.verts
      (SimpleGraph.support_mono (CycleGroupDisjoint.selectedGraph_mono T hFB) hz)
      (hzC)
  obtain ⟨j,hj,x,hxj,hxF⟩ := GroupComponents.component_meets_outside T hG B ⟨i,hiB⟩ hn D
  have hcarrier : Touches K.verts (T.walk j).toSubgraph := by
    by_contra hh
    exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩)
  have hji : j ≠ i := by
    rintro rfl
    exact hFC x hxF (by rwa [←Walk.mem_verts_toSubgraph,hi] at hxj)
  exact tight_group_avoids_carriers hsmall hfail T hs i j hji.symm K hnK hi hmax hmin F
    (fun hh ↦ hiB (hFB hh)) (fun hh ↦ hj (hFB hh)) hFC
    (GroupComponents.component_support_connected T B D) (Finset.mem_filter.mp hD).2 hcarrier x hxj hxF

lemma optimized_anchor_carrier_bound {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (i : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) (K : G.Subgraph) (hnK : ¬IsPathSubgraph K) (hi : (T.walk i).toSubgraph=K)
    (hmax : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score=T.score →
      (U.walk i).toSubgraph=K →
      carrierCount U K.verts ≤ carrierCount T K.verts)
    (hmin : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score=T.score →
      (U.walk i).toSubgraph=K →
      carrierCount U K.verts=carrierCount T K.verts →
      carrierLength T K.verts ≤ carrierLength U K.verts) :
    K.verts.ncard+2*⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ ≤ n+2*(carrierIndices T i K.verts).card+2 := by
  have hiB : i ∉ outsideIndices T K.verts := fun hh ↦
    outside_not_touched T K.verts hh (anchor_touches T i K hnK hi)
  have hround := outside_component_rounding hsmall hfail T hs i
    (member_not_path T i K hnK hi) _ hiB
  rw [no_tight_outside_components hsmall hG hfail T hs i K hnK hi hmax hmin,Finset.card_empty] at hround
  have hsplit := outside_carrier_partition T i K.verts (anchor_touches T i K hnK hi)
  have hsize := outside_support_anchor_card T K
  simp only [Fintype.card_fin] at hsize
  omega

lemma optimized_anchor_size_bound {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (i : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) (K : G.Subgraph) (hnK : ¬IsPathSubgraph K) (hi : (T.walk i).toSubgraph=K)
    (hmax : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score=T.score →
      (U.walk i).toSubgraph=K →
      carrierCount U K.verts ≤ carrierCount T K.verts)
    (hmin : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score=T.score →
      (U.walk i).toSubgraph=K →
      carrierCount U K.verts=carrierCount T K.verts →
      carrierLength T K.verts ≤ carrierLength U K.verts) :
    K.verts.ncard ≤ 2*(carrierIndices T i K.verts).card+2 ∧
      (Odd n → K.verts.ncard ≤ 2*(carrierIndices T i K.verts).card+1) := by
  have hh := optimized_anchor_carrier_bound hsmall hG hfail T hs i K hnK hi hmax hmin
  simp only [Fintype.card_fin,BridgeGlue.ceil_half] at hh
  constructor
  · omega
  · rintro ⟨m,hm⟩
    omega


lemma exists_optimized_anchor_certificate {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (i : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) (K : G.Subgraph)
    (hnK : ¬IsPathSubgraph K) (hi : (T.walk i).toSubgraph=K) :
    ∃ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊,
      U.score=T.score ∧ (U.walk i).toSubgraph=K ∧
      tightComponents U (outsideIndices U K.verts)=∅ ∧
      K.verts.ncard ≤ 2*(carrierIndices U i K.verts).card+2 ∧
      (Odd n → K.verts.ncard ≤ 2*(carrierIndices U i K.verts).card+1) := by
  obtain ⟨U,hUs,hUi,hUmax,hUmin⟩ := exists_shortest_maximum_carriers T i K hi
  have hUs' : U.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := hUs.symm ▸ hs
  have hb := optimized_anchor_size_bound hsmall hG hfail U hUs' i K hnK hUi hUmax hUmin
  exact ⟨U,hUs,hUi,no_tight_outside_components hsmall hG hfail U hUs' i K hnK hUi hUmax hUmin,hb⟩

/-- This version covers open lollipops too. It fixes the entire defective
subgraph; it makes no assertion of preserved quota energy or shortest-tail
properties for the new family. -/
lemma exists_optimized_lollipop_certificate {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (r : Fin n) (L : LollipopEar.RootedCycleRep T r) :
    ∃ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊,
      U.score=T.score ∧ (U.walk L.index).toSubgraph=(T.walk L.index).toSubgraph ∧
      tightComponents U (outsideIndices U (T.walk L.index).toSubgraph.verts)=∅ ∧
      L.cycle.length+L.tail.length ≤ 2*(carrierIndices U L.index (T.walk L.index).toSubgraph.verts).card+2 ∧
      (Odd n → L.cycle.length+L.tail.length ≤ 2*(carrierIndices U L.index (T.walk L.index).toSubgraph.verts).card+1) := by
  have hnK : ¬IsPathSubgraph (T.walk L.index).toSubgraph := by
    rintro ⟨a,b,P,hP,hPe⟩
    exact L.member_not_path (ProtectedEdge.trail_isPath_of_subgraph_eq _ _ (T.isTrail L.index) hP hPe)
  obtain ⟨U,hUs,hUi,ht,hb,ho⟩ := exists_optimized_anchor_certificate hsmall hG hfail T hs L.index
    (T.walk L.index).toSubgraph hnK rfl
  have hv : (T.walk L.index).toSubgraph.verts.ncard=L.cycle.length+L.tail.length := by
    rw [L.subgraph,LollipopEar.lollipop_vertex_card L.cycle L.isCycle L.tail L.isPath L.inter,Walk.length_append]
  exact ⟨U,hUs,hUi,ht,by rwa [hv] at hb,fun h ↦ by have hh := ho h; rwa [hv] at hh⟩

end Erdos583AnchorCarrierDevelopment
