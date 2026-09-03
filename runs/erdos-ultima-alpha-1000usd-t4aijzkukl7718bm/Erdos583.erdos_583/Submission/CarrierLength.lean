import Submission.Work
import Submission.CarrierCuts
import Submission.CarrierCount

/-! Length minimization after maximizing the number of cycle carriers. -/
namespace Erdos583CarrierLengthDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open Erdos583Work.MemberExpansion Erdos583Work.MemberNormalExpansion Erdos583Work.MarkedCycleGroups
open Erdos583CarrierCutsDevelopment Erdos583CarrierCountDevelopment
open scoped Classical
set_option maxHeartbeats 2000000

variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

noncomputable def carrierLength (T : TrailFamily G k) (S : Set V) : ℕ :=
  ∑ j, if Touches S (T.walk j).toSubgraph then (T.walk j).length else 0

lemma trail_length_of_same_subgraph {a b c d : V} (P : G.Walk a b) (Q : G.Walk c d)
    (hP : P.IsTrail) (hQ : Q.IsTrail) (he : P.toSubgraph=Q.toSubgraph) : P.length=Q.length := by
  rw [←trail_edgeSet_ncard P hP,he,trail_edgeSet_ncard Q hQ]

lemma carrier_weight_of_same_subgraph (T U : TrailFamily G k) (S : Set V) (j : Fin k)
    (he : (U.walk j).toSubgraph=(T.walk j).toSubgraph) :
    (if Touches S (U.walk j).toSubgraph then (U.walk j).length else 0) =
      (if Touches S (T.walk j).toSubgraph then (T.walk j).length else 0) := by
  rw [he,trail_length_of_same_subgraph (U.walk j) (T.walk j) (U.isTrail j) (T.isTrail j) he]

lemma untouched_group_invariants (T Z : TrailFamily G k) (S : Set V) (F : Finset (Fin k))
    (hrest : ∀ l, l ∉ F → (Z.walk l).toSubgraph=(T.walk l).toSubgraph)
    (hTF : ∀ l ∈ F, ¬Touches S (T.walk l).toSubgraph)
    (hZF : ∀ l ∈ F, ¬Touches S (Z.walk l).toSubgraph) :
    carrierCount Z S=carrierCount T S ∧ carrierLength Z S=carrierLength T S := by
  classical
  constructor
  · apply carrierCount_congr
    intro l
    by_cases hl : l ∈ F
    · exact iff_of_false (hZF l hl) (hTF l hl)
    · rw [hrest l hl]
  · unfold carrierLength
    apply Finset.sum_congr rfl
    intro l hl
    by_cases hlF : l ∈ F
    · simp only [if_neg (hZF l hlF),if_neg (hTF l hlF)]
    · exact carrier_weight_of_same_subgraph T Z S l (hrest l hlF)

lemma carrierLength_change_one (T U : TrailFamily G k) (S : Set V) (j : Fin k) (d : ℕ)
    (hj : (if Touches S (U.walk j).toSubgraph then (U.walk j).length else 0)+d =
      (if Touches S (T.walk j).toSubgraph then (T.walk j).length else 0))
    (hrest : ∀ l, l ≠ j →
      (if Touches S (U.walk l).toSubgraph then (U.walk l).length else 0) =
        (if Touches S (T.walk l).toSubgraph then (T.walk l).length else 0)) :
    carrierLength U S+d=carrierLength T S := by
  classical
  have he : ∑ l ∈ Finset.univ.erase j, (if Touches S (U.walk l).toSubgraph then (U.walk l).length else 0) =
      ∑ l ∈ Finset.univ.erase j, (if Touches S (T.walk l).toSubgraph then (T.walk l).length else 0) := by
    apply Finset.sum_congr rfl
    intro l hl
    exact hrest l (Finset.mem_erase.mp hl).1
  have hT := Finset.sum_erase_add (s := Finset.univ)
    (fun l : Fin k ↦ if Touches S (T.walk l).toSubgraph then (T.walk l).length else 0) (Finset.mem_univ j)
  have hU := Finset.sum_erase_add (s := Finset.univ)
    (fun l : Fin k ↦ if Touches S (U.walk l).toSubgraph then (U.walk l).length else 0) (Finset.mem_univ j)
  dsimp only at hT hU
  change _=carrierLength T S at hT
  change _=carrierLength U S at hU
  omega

lemma exists_shortest_maximum_carriers (T : TrailFamily G k) (i : Fin k) {r : V}
    (C : G.Walk r r) (hi : (T.walk i).toSubgraph=C.toSubgraph) :
    ∃ U : TrailFamily G k, U.score=T.score ∧ (U.walk i).toSubgraph=C.toSubgraph ∧
      PreservesIncidence T U C.toSubgraph.verts ∧
      (∀ Z : TrailFamily G k, Z.score=U.score → (Z.walk i).toSubgraph=C.toSubgraph →
        PreservesIncidence U Z C.toSubgraph.verts →
        carrierCount Z C.toSubgraph.verts ≤ carrierCount U C.toSubgraph.verts) ∧
      (∀ Z : TrailFamily G k, Z.score=U.score → (Z.walk i).toSubgraph=C.toSubgraph →
        PreservesIncidence U Z C.toSubgraph.verts →
        carrierCount Z C.toSubgraph.verts=carrierCount U C.toSubgraph.verts →
        carrierLength U C.toSubgraph.verts ≤ carrierLength Z C.toSubgraph.verts) := by
  obtain ⟨R,hRs,hRi,hRp,hRmax⟩ := exists_maximum_carriers T i C hi
  let P (m : ℕ) := ∃ U : TrailFamily G k, U.score=R.score ∧ (U.walk i).toSubgraph=C.toSubgraph ∧
    PreservesIncidence R U C.toSubgraph.verts ∧
    carrierCount U C.toSubgraph.verts=carrierCount R C.toSubgraph.verts ∧ carrierLength U C.toSubgraph.verts=m
  have hex : ∃ m, P m := ⟨_,R,rfl,hRi,preserves_refl R _,rfl,rfl⟩
  obtain ⟨U,hUs,hUi,hUp,hUc,hUl⟩ := Nat.find_spec hex
  refine ⟨U,hUs.trans hRs,hUi,preserves_trans hRp hUp,?_,?_⟩
  · intro Z hZs hZi hZp
    rw [hUc]
    exact hRmax Z (hZs.trans hUs) hZi (preserves_trans hUp hZp)
  · intro Z hZs hZi hZp hZc
    rw [hUl]
    exact Nat.find_min' hex ⟨Z,hZs.trans hUs,hZi,preserves_trans hUp hZp,hZc.trans hUc,rfl⟩

lemma marked_prefix_shortens_carrier [Fintype V]
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (i j : Fin k) (hij : i ≠ j) {r : V} (C : G.Walk r r) (hC : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (F : Finset (Fin k)) (hiF : i ∉ F) (hjF : j ∉ F)
    (hFC : ∀ x ∈ (selectedGraph T F).support, x ∉ C.support)
    {a z b : V} (A : G.Walk a z) (B : G.Walk z b) (hAB : (A.append B).IsPath)
    (hj : (T.walk j).toSubgraph=(A.append B).toSubgraph)
    (hprefix : ∀ x ∈ A.support, x ∈ (selectedGraph T F).support → x=z)
    (hmark : MarkedPartition (selectedGraph T F) F.card z)
    (hA : ¬Touches C.toSubgraph.verts A.toSubgraph) (hB : Touches C.toSubgraph.verts B.toSubgraph) :
    ∃ U : TrailFamily G k, U.score=T.score ∧ (U.walk i).toSubgraph=C.toSubgraph ∧
      PreservesIncidence T U C.toSubgraph.verts ∧
      carrierCount U C.toSubgraph.verts=carrierCount T C.toSubgraph.verts ∧
      carrierLength U C.toSubgraph.verts+A.length=carrierLength T C.toSubgraph.verts := by
  classical
  have hnp := CycleEar.cycle_member_not_path T i C hC hi
  obtain ⟨D,d,P,hD,hcard,hP,hnP,hPD⟩ := hmark
  obtain ⟨Z,hZs,hrest,_,hZin,hparts⟩ := GroupActivation.replace_path_group_tracked T F
    (fun l hl ↦ (T.one_defect_other_paths hs i hnp).2 l (fun he ↦ hiF (he ▸ hl))) D hD hcard
  have hTF (l : Fin k) (hl : l ∈ F) : ¬Touches C.toSubgraph.verts (T.walk l).toSubgraph := by
    rintro ⟨x,hx,y,hxy⟩
    exact hFC x ⟨y,l,hl,hxy⟩ (C.mem_verts_toSubgraph.mp hx)
  have hZF (l : Fin k) (hl : l ∈ F) : ¬Touches C.toSubgraph.verts (Z.walk l).toSubgraph := by
    rintro ⟨x,hx,y,hxy⟩
    obtain ⟨K,hK,hKe⟩ := hZin l hl
    have he : s(x,y) ∈ (Z.walk l).toSubgraph.edgeSet := hxy
    rw [hKe,edgeSet_lift] at he
    exact hFC x ⟨y,K.edgeSet_subset he⟩ (C.mem_verts_toSubgraph.mp hx)
  obtain ⟨hZc,hZL⟩ := untouched_group_invariants T Z C.toSubgraph.verts F
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
  have htQ : ¬Touches C.toSubgraph.verts Q.toSubgraph := by
    rintro ⟨x,hx,y,hxy⟩
    exact hFC x (hQs x (Walk.mem_support_of_adj_toSubgraph hxy)) (C.mem_verts_toSubgraph.mp hx)
  obtain ⟨U,hUs,hUj,hUm,hUrest⟩ := cut_carrier_at_marked_path Z j m hjm A B Q hAB hQ
    ((hrest j hjF).2.2.trans hj) (hZm.trans hQe.symm)
    (fun x hx hy ↦ hprefix x hx (hQs x hy))
  have hTj : Touches C.toSubgraph.verts (Z.walk j).toSubgraph := by
    rw [(hrest j hjF).2.2,hj,touches_append]
    exact Or.inr hB
  have hUjm : ¬Touches C.toSubgraph.verts (U.walk m).toSubgraph := by
    rw [hUm,touches_append]
    exact not_or.mpr ⟨hA,htQ⟩
  have hUjj : Touches C.toSubgraph.verts (U.walk j).toSubgraph := hUj.symm ▸ hB
  have hUc : carrierCount U C.toSubgraph.verts=carrierCount Z C.toSubgraph.verts := by
    apply carrierCount_congr
    intro l
    by_cases hlj : l=j
    · subst l
      exact iff_of_true hUjj hTj
    · by_cases hlm : l=m
      · subst l
        exact iff_of_false hUjm (hZF m hmF)
      · rw [hUrest l hlj hlm]
  have hUl : carrierLength U C.toSubgraph.verts+A.length=carrierLength Z C.toSubgraph.verts := by
    apply carrierLength_change_one Z U C.toSubgraph.verts j A.length
    · simp only [if_pos hUjj,if_pos hTj]
      rw [trail_length_of_same_subgraph _ _ (U.isTrail j) hAB.of_append_right.isTrail hUj,
        trail_length_of_same_subgraph _ _ (Z.isTrail j) hAB.isTrail ((hrest j hjF).2.2.trans hj),Walk.length_append]
      omega
    · intro l hlj
      by_cases hlm : l=m
      · subst l
        simp only [if_neg hUjm,if_neg (hZF m hmF)]
      · exact carrier_weight_of_same_subgraph Z U C.toSubgraph.verts l (hUrest l hlj hlm)
  have hZp := untouched_group_preserves T Z C.toSubgraph.verts F
    (fun l hl ↦ (hrest l hl).2.2) hTF hZF
  have hz : z ∉ C.toSubgraph.verts := fun hh ↦
    hFC z (hQs z Q.start_mem_support) (C.mem_verts_toSubgraph.mp hh)
  have hUp := carrier_cut_preserves Z U C.toSubgraph.verts j m hjm A B Q hAB hz htQ
    ((hrest j hjF).2.2.trans hj) (hZm.trans hQe.symm) hUj hUm hUrest
  exact ⟨U,hUs.trans hZs,(hUrest i hij him).trans ((hrest i hiF).2.2.trans hi),
    preserves_trans hZp hUp,hUc.trans hZc,hUl.trans hZL⟩

lemma shortest_carrier_marked_prefix_nil [Fintype V]
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (i j : Fin k) (hij : i ≠ j) {r : V} (C : G.Walk r r) (hC : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (hmin : ∀ U : TrailFamily G k, U.score=T.score → (U.walk i).toSubgraph=C.toSubgraph →
      PreservesIncidence T U C.toSubgraph.verts →
      carrierCount U C.toSubgraph.verts=carrierCount T C.toSubgraph.verts →
      carrierLength T C.toSubgraph.verts ≤ carrierLength U C.toSubgraph.verts)
    (F : Finset (Fin k)) (hiF : i ∉ F) (hjF : j ∉ F)
    (hFC : ∀ x ∈ (selectedGraph T F).support, x ∉ C.support)
    {a z b : V} (A : G.Walk a z) (B : G.Walk z b) (hAB : (A.append B).IsPath)
    (hj : (T.walk j).toSubgraph=(A.append B).toSubgraph)
    (hprefix : ∀ x ∈ A.support, x ∈ (selectedGraph T F).support → x=z)
    (hmark : MarkedPartition (selectedGraph T F) F.card z)
    (hA : ¬Touches C.toSubgraph.verts A.toSubgraph) (hB : Touches C.toSubgraph.verts B.toSubgraph) :
    A.Nil := by
  obtain ⟨U,hUs,hUi,hUp,hUc,hUl⟩ := marked_prefix_shortens_carrier T hs i j hij C hC hi F hiF hjF
    hFC A B hAB hj hprefix hmark hA hB
  have hh := hmin U hUs hUi hUp hUc
  exact Walk.nil_iff_length_eq.mpr (by omega)

lemma first_marked_hit_start_or_free_suffix [Fintype V]
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (i j : Fin k) (hij : i ≠ j) {r : V} (C : G.Walk r r) (hC : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (hmax : ∀ U : TrailFamily G k, U.score=T.score → (U.walk i).toSubgraph=C.toSubgraph →
      PreservesIncidence T U C.toSubgraph.verts →
      carrierCount U C.toSubgraph.verts ≤ carrierCount T C.toSubgraph.verts)
    (hmin : ∀ U : TrailFamily G k, U.score=T.score → (U.walk i).toSubgraph=C.toSubgraph →
      PreservesIncidence T U C.toSubgraph.verts →
      carrierCount U C.toSubgraph.verts=carrierCount T C.toSubgraph.verts →
      carrierLength T C.toSubgraph.verts ≤ carrierLength U C.toSubgraph.verts)
    (F : Finset (Fin k)) (hiF : i ∉ F) (hjF : j ∉ F)
    (hFC : ∀ x ∈ (selectedGraph T F).support, x ∉ C.support)
    {a z b : V} (A : G.Walk a z) (B : G.Walk z b) (hAB : (A.append B).IsPath)
    (hj : (T.walk j).toSubgraph=(A.append B).toSubgraph)
    (hprefix : ∀ x ∈ A.support, x ∈ (selectedGraph T F).support → x=z)
    (hmark : MarkedPartition (selectedGraph T F) F.card z) :
    A.Nil ∨ ¬Touches C.toSubgraph.verts B.toSubgraph := by
  classical
  by_cases hB : Touches C.toSubgraph.verts B.toSubgraph
  · by_cases hA : Touches C.toSubgraph.verts A.toSubgraph
    · have hA' : (C.toSubgraph.verts ∩ A.toSubgraph.verts).Nonempty := by
        obtain ⟨x,hx,y,hxy⟩ := hA
        exact ⟨x,hx,A.toSubgraph.edge_vert hxy⟩
      have hB' : (C.toSubgraph.verts ∩ B.toSubgraph.verts).Nonempty := by
        obtain ⟨x,hx,y,hxy⟩ := hB
        exact ⟨x,hx,B.toSubgraph.edge_vert hxy⟩
      exact (maximum_carriers_no_marked_internal_cut T hs i j hij C hC hi hmax F hiF hjF
        hFC A B hAB hj hprefix hmark hA' hB').elim
    · exact Or.inl (shortest_carrier_marked_prefix_nil T hs i j hij C hC hi hmin F hiF hjF
        hFC A B hAB hj hprefix hmark hA hB)
  · exact Or.inr hB

lemma fully_marked_group_contains_carrier_endpoint [Fintype V]
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (i j : Fin k) (hij : i ≠ j) {r : V} (C : G.Walk r r) (hC : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (hmax : ∀ U : TrailFamily G k, U.score=T.score → (U.walk i).toSubgraph=C.toSubgraph →
      PreservesIncidence T U C.toSubgraph.verts →
      carrierCount U C.toSubgraph.verts ≤ carrierCount T C.toSubgraph.verts)
    (hmin : ∀ U : TrailFamily G k, U.score=T.score → (U.walk i).toSubgraph=C.toSubgraph →
      PreservesIncidence T U C.toSubgraph.verts →
      carrierCount U C.toSubgraph.verts=carrierCount T C.toSubgraph.verts →
      carrierLength T C.toSubgraph.verts ≤ carrierLength U C.toSubgraph.verts)
    (F : Finset (Fin k)) (hiF : i ∉ F) (hjF : j ∉ F)
    (hFC : ∀ x ∈ (selectedGraph T F).support, x ∉ C.support)
    (hmark : ∀ x ∈ (selectedGraph T F).support, MarkedPartition (selectedGraph T F) F.card x)
    (hcarrier : Touches C.toSubgraph.verts (T.walk j).toSubgraph)
    (hhit : ∃ x ∈ (T.walk j).support, x ∈ (selectedGraph T F).support) :
    T.start j ∈ (selectedGraph T F).support ∨ T.finish j ∈ (selectedGraph T F).support := by
  classical
  have hnp := CycleEar.cycle_member_not_path T i C hC hi
  have hpj := (T.one_defect_other_paths hs i hnp).2 j hij.symm
  obtain ⟨x,hx,A,B,hform,hprefix⟩ := QuadrilateralAbsorption.first_hit_split (T.walk j)
    (selectedGraph T F).support hhit
  have hAB : (A.append B).IsPath := hform ▸ hpj
  have hj := congrArg Walk.toSubgraph hform
  rcases first_marked_hit_start_or_free_suffix T hs i j hij C hC hi hmax hmin F hiF hjF
    hFC A B hAB hj hprefix (hmark x hx) with hnA|hBfree
  · exact Or.inl (hnA.eq.symm ▸ hx)
  · obtain ⟨y,hy,D,E,hB,hE⟩ := CycleDefect.last_hit_split B (selectedGraph T F).support
      ⟨x,B.start_mem_support,hx⟩
    have hrev : (T.walk j).reverse=E.reverse.append (A.append D).reverse := by
      simp only [hform,hB,Walk.reverse_append,Walk.append_assoc]
    have hrevEq : (T.walk j).toSubgraph=(E.reverse.append (A.append D).reverse).toSubgraph := by
      rw [←hrev,Walk.toSubgraph_reverse]
    have hrevP : (E.reverse.append (A.append D).reverse).IsPath := hrev ▸ hpj.reverse
    have hEfree : ¬Touches C.toSubgraph.verts E.reverse.toSubgraph := by
      rw [Walk.toSubgraph_reverse]
      intro he
      apply hBfree
      rw [hB,touches_append]
      exact Or.inr he
    have htail : Touches C.toSubgraph.verts (A.append D).reverse.toSubgraph := by
      rw [hrevEq,touches_append] at hcarrier
      exact hcarrier.resolve_left hEfree
    have hprefixE : ∀ z ∈ E.reverse.support, z ∈ (selectedGraph T F).support → z=y := by
      intro z hz hzF
      exact hE z (by simpa only [Walk.support_reverse,List.mem_reverse] using hz) hzF
    have hnErev := shortest_carrier_marked_prefix_nil T hs i j hij C hC hi hmin F hiF hjF hFC
      E.reverse (A.append D).reverse hrevP hrevEq hprefixE (hmark y hy) hEfree htail
    have hnE : E.Nil := by simpa using hnErev
    exact Or.inr (hnE.eq ▸ hy)

end Erdos583CarrierLengthDevelopment
