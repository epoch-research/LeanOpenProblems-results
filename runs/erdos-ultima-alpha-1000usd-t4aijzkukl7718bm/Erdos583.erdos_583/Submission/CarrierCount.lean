import Submission.Work
import Submission.CarrierCuts

/-! Maximum carrier-count optimization for one fixed whole-cycle member. -/
namespace Erdos583CarrierCountDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open Erdos583Work.MemberExpansion Erdos583Work.MemberNormalExpansion Erdos583Work.MarkedCycleGroups
open Erdos583CarrierCutsDevelopment
open scoped Classical
set_option maxHeartbeats 1800000

variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

def Touches (S : Set V) (H : G.Subgraph) : Prop := ∃ x ∈ S, ∃ y, H.Adj x y

noncomputable def carrierCount (T : TrailFamily G k) (S : Set V) : ℕ :=
  ∑ j, if Touches S (T.walk j).toSubgraph then 1 else 0

lemma carrierCount_le (T : TrailFamily G k) (S : Set V) : carrierCount T S ≤ k := by
  classical
  calc
    carrierCount T S ≤ ∑ _j : Fin k, (1 : ℕ) := Finset.sum_le_sum (by intro j hj; split_ifs <;> omega)
    _ = k := by simp

lemma touches_append (S : Set V) {a b c : V} (A : G.Walk a b) (B : G.Walk b c) :
    Touches S (A.append B).toSubgraph ↔ Touches S A.toSubgraph ∨ Touches S B.toSubgraph := by
  simp only [Touches,Walk.toSubgraph_append,Subgraph.sup_adj]
  aesop

lemma touches_of_nonempty_inter [Fintype V] {S : Set V} {a b : V} (P : G.Walk a b) (hp : P.IsPath)
    (hn : ¬P.Nil) (hhit : (S ∩ P.toSubgraph.verts).Nonempty) : Touches S P.toSubgraph := by
  obtain ⟨x,hxS,hxP⟩ := hhit
  have hpos := path_neighbor_ncard_pos hp hn (P.mem_verts_toSubgraph.mp hxP)
  obtain ⟨y,hy⟩ := (Set.ncard_pos (Set.toFinite _)).mp hpos
  exact ⟨x,hxS,y,hy⟩

lemma carrierCount_congr (T U : TrailFamily G k) (S : Set V)
    (h : ∀ j, Touches S (T.walk j).toSubgraph ↔ Touches S (U.walk j).toSubgraph) :
    carrierCount T S=carrierCount U S := by
  classical
  unfold carrierCount
  apply Finset.sum_congr rfl
  intro j hj
  rw [h j]

lemma carrierCount_increase (T U : TrailFamily G k) (S : Set V) (m : Fin k)
    (hmT : ¬Touches S (T.walk m).toSubgraph) (hmU : Touches S (U.walk m).toSubgraph)
    (hrest : ∀ l, l ≠ m → (Touches S (T.walk l).toSubgraph ↔ Touches S (U.walk l).toSubgraph)) :
    carrierCount U S=carrierCount T S+1 := by
  classical
  have hsum : ∑ l ∈ Finset.univ.erase m, (if Touches S (U.walk l).toSubgraph then 1 else 0 : ℕ) =
      ∑ l ∈ Finset.univ.erase m, (if Touches S (T.walk l).toSubgraph then 1 else 0 : ℕ) := by
    apply Finset.sum_congr rfl
    intro l hl
    rw [hrest l (Finset.mem_erase.mp hl).1]
  have hT := Finset.sum_erase_add (s := Finset.univ) (fun l : Fin k ↦ if Touches S (T.walk l).toSubgraph then (1:ℕ) else 0)
    (Finset.mem_univ m)
  have hU := Finset.sum_erase_add (s := Finset.univ) (fun l : Fin k ↦ if Touches S (U.walk l).toSubgraph then (1:ℕ) else 0)
    (Finset.mem_univ m)
  simp only [if_pos hmU,if_neg hmT,add_zero] at hT hU
  change _=carrierCount T S at hT
  change _=carrierCount U S at hU
  omega

def PreservesIncidence (T U : TrailFamily G k) (S : Set V) : Prop :=
  ∀ x ∈ S, carrierCount U {x}=carrierCount T {x}

lemma preserves_refl (T : TrailFamily G k) (S : Set V) : PreservesIncidence T T S := fun _ _ ↦ rfl

lemma preserves_trans {T U Z : TrailFamily G k} {S : Set V}
    (hTU : PreservesIncidence T U S) (hUZ : PreservesIncidence U Z S) : PreservesIncidence T Z S :=
  fun x hx ↦ (hUZ x hx).trans (hTU x hx)

lemma touches_mono {S R : Set V} {H : G.Subgraph} (hSR : S ⊆ R) (h : Touches S H) : Touches R H := by
  obtain ⟨x,hx,y,hxy⟩ := h
  exact ⟨x,hSR hx,y,hxy⟩

lemma untouched_group_preserves (T U : TrailFamily G k) (S : Set V) (F : Finset (Fin k))
    (hrest : ∀ l, l ∉ F → (U.walk l).toSubgraph=(T.walk l).toSubgraph)
    (hTF : ∀ l ∈ F, ¬Touches S (T.walk l).toSubgraph)
    (hUF : ∀ l ∈ F, ¬Touches S (U.walk l).toSubgraph) : PreservesIncidence T U S := by
  intro x hx
  apply carrierCount_congr
  intro l
  by_cases hl : l ∈ F
  · have hsub : ({x} : Set V) ⊆ S := Set.singleton_subset_iff.mpr hx
    exact iff_of_false (fun hh ↦ hUF l hl (touches_mono hsub hh)) (fun hh ↦ hTF l hl (touches_mono hsub hh))
  · rw [hrest l hl]

lemma carrierCount_two_balance (T U : TrailFamily G k) (S : Set V) (j m : Fin k) (hjm : j ≠ m)
    (hpair : (if Touches S (U.walk j).toSubgraph then 1 else 0)+(if Touches S (U.walk m).toSubgraph then 1 else 0) =
      (if Touches S (T.walk j).toSubgraph then 1 else 0)+(if Touches S (T.walk m).toSubgraph then 1 else 0))
    (hrest : ∀ l, l ≠ j → l ≠ m → (Touches S (U.walk l).toSubgraph ↔ Touches S (T.walk l).toSubgraph)) :
    carrierCount U S=carrierCount T S := by
  classical
  have hsum : ∑ l ∈ (Finset.univ.erase j).erase m, (if Touches S (U.walk l).toSubgraph then 1 else 0 : ℕ) =
      ∑ l ∈ (Finset.univ.erase j).erase m, (if Touches S (T.walk l).toSubgraph then 1 else 0 : ℕ) := by
    apply Finset.sum_congr rfl
    intro l hl
    obtain ⟨hlm,hlj⟩ := Finset.mem_erase.mp hl
    rw [hrest l (Finset.mem_erase.mp hlj).1 hlm]
  unfold carrierCount
  rw [NormalTrailSystem.sum_extract_two (fun l ↦ if Touches S (U.walk l).toSubgraph then 1 else 0) j m hjm,
    NormalTrailSystem.sum_extract_two (fun l ↦ if Touches S (T.walk l).toSubgraph then 1 else 0) j m hjm,hsum]
  omega

lemma carrier_cut_preserves (T U : TrailFamily G k) (S : Set V) (j m : Fin k) (hjm : j ≠ m)
    {a z b d : V} (A : G.Walk a z) (B : G.Walk z b) (Q : G.Walk z d)
    (hAB : (A.append B).IsPath) (hz : z ∉ S) (hQ : ¬Touches S Q.toSubgraph)
    (hTj : (T.walk j).toSubgraph=(A.append B).toSubgraph) (hTm : (T.walk m).toSubgraph=Q.toSubgraph)
    (hUj : (U.walk j).toSubgraph=B.toSubgraph) (hUm : (U.walk m).toSubgraph=(A.append Q).toSubgraph)
    (hrest : ∀ l, l ≠ j → l ≠ m → (U.walk l).toSubgraph=(T.walk l).toSubgraph) :
    PreservesIncidence T U S := by
  classical
  intro x hx
  apply carrierCount_two_balance T U {x} j m hjm
  · have hQx : ¬Touches ({x} : Set V) Q.toSubgraph := fun hh ↦
      hQ (touches_mono (Set.singleton_subset_iff.mpr hx) hh)
    have hboth : ¬(Touches ({x} : Set V) A.toSubgraph ∧ Touches ({x} : Set V) B.toSubgraph) := by
      rintro ⟨⟨y,hy,w,hyw⟩,⟨z',hz',v,hzv⟩⟩
      have hyx : y=x := hy
      have hzx : z'=x := hz'
      subst y z'
      have hxz : x ≠ z := fun he ↦ hz (he ▸ hx)
      exact hAB.ne_of_mem_support_of_append hxz (Walk.mem_support_of_adj_toSubgraph hyw)
        (Walk.mem_support_of_adj_toSubgraph hzv) rfl
    rw [hUj,hUm,hTj,hTm,touches_append,touches_append]
    by_cases ha : Touches ({x} : Set V) A.toSubgraph <;> by_cases hb : Touches ({x} : Set V) B.toSubgraph
    · exact (hboth ⟨ha,hb⟩).elim
    all_goals simp [ha,hb,hQx]
  · intro l hlj hlm
    rw [hrest l hlj hlm]

lemma exists_maximum_carriers (T : TrailFamily G k) (i : Fin k) {r : V}
    (C : G.Walk r r) (hi : (T.walk i).toSubgraph=C.toSubgraph) :
    ∃ U : TrailFamily G k, U.score=T.score ∧ (U.walk i).toSubgraph=C.toSubgraph ∧
      PreservesIncidence T U C.toSubgraph.verts ∧
      ∀ Z : TrailFamily G k, Z.score=U.score → (Z.walk i).toSubgraph=C.toSubgraph →
        PreservesIncidence U Z C.toSubgraph.verts →
        carrierCount Z C.toSubgraph.verts ≤ carrierCount U C.toSubgraph.verts := by
  classical
  let P (m : ℕ) := ∃ U : TrailFamily G k, U.score=T.score ∧
    (U.walk i).toSubgraph=C.toSubgraph ∧ PreservesIncidence T U C.toSubgraph.verts ∧
    k-carrierCount U C.toSubgraph.verts=m
  have hex : ∃ m, P m := ⟨_,T,rfl,hi,preserves_refl T _,rfl⟩
  obtain ⟨U,hUs,hUi,hUp,hUc⟩ := Nat.find_spec hex
  refine ⟨U,hUs,hUi,hUp,?_⟩
  intro Z hZs hZi hZp
  have hm := Nat.find_min' hex (show P (k-carrierCount Z C.toSubgraph.verts) from
    ⟨Z,hZs.trans hUs,hZi,preserves_trans hUp hZp,rfl⟩)
  have hU := carrierCount_le U C.toSubgraph.verts
  have hZ := carrierCount_le Z C.toSubgraph.verts
  omega

lemma marked_internal_cut_increases_carriers [Fintype V]
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (i j : Fin k) (hij : i ≠ j) {r : V} (C : G.Walk r r) (hC : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (F : Finset (Fin k)) (hiF : i ∉ F) (hjF : j ∉ F)
    (hFC : ∀ x ∈ (selectedGraph T F).support, x ∉ C.support)
    {a z b : V} (A : G.Walk a z) (B : G.Walk z b) (hAB : (A.append B).IsPath)
    (hj : (T.walk j).toSubgraph=(A.append B).toSubgraph)
    (hprefix : ∀ x ∈ A.support, x ∈ (selectedGraph T F).support → x=z)
    (hmark : MarkedPartition (selectedGraph T F) F.card z)
    (hA : (C.toSubgraph.verts ∩ A.toSubgraph.verts).Nonempty)
    (hB : (C.toSubgraph.verts ∩ B.toSubgraph.verts).Nonempty) :
    ∃ U : TrailFamily G k, U.score=T.score ∧ (U.walk i).toSubgraph=C.toSubgraph ∧
      PreservesIncidence T U C.toSubgraph.verts ∧
      carrierCount U C.toSubgraph.verts=carrierCount T C.toSubgraph.verts+1 := by
  classical
  have hnp := CycleEar.cycle_member_not_path T i C hC hi
  obtain ⟨D,d,P,hD,hcard,hP,hnP,hPD⟩ := hmark
  have hzF : z ∈ (selectedGraph T F).support := path_support_subset_graph_support hP hnP z P.start_mem_support
  have hzC := hFC z hzF
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
  have hZc : carrierCount Z C.toSubgraph.verts=carrierCount T C.toSubgraph.verts := by
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
    exact hzC ((hx.trans hn.eq) ▸ C.mem_verts_toSubgraph.mp hxC)
  have hnB : ¬B.Nil := by
    intro hn
    obtain ⟨x,hxC,hxB⟩ := hB
    have hx : x=z := by
      simpa only [Walk.nil_iff_support_eq.mp hn,List.mem_singleton] using B.mem_verts_toSubgraph.mp hxB
    exact hzC (hx ▸ C.mem_verts_toSubgraph.mp hxC)
  have htA := touches_of_nonempty_inter A hAB.of_append_left hnA hA
  have htB := touches_of_nonempty_inter B hAB.of_append_right hnB hB
  have hcount : carrierCount U C.toSubgraph.verts=carrierCount Z C.toSubgraph.verts+1 := by
    apply carrierCount_increase Z U C.toSubgraph.verts m (hZF m hmF)
    · rw [hUm,touches_append]
      exact Or.inl htA
    · intro l hlm
      by_cases hlj : l=j
      · subst l
        rw [(hrest j hjF).2.2,hj,hUj,touches_append]
        exact iff_of_true (Or.inr htB) htB
      · rw [hUrest l hlj hlm]
  have hZp := untouched_group_preserves T Z C.toSubgraph.verts F
    (fun l hl ↦ (hrest l hl).2.2) hTF hZF
  have hUp := carrier_cut_preserves Z U C.toSubgraph.verts j m hjm A B Q hAB
    (fun hz ↦ hzC (C.mem_verts_toSubgraph.mp hz))
    (fun ht ↦ hZF m hmF ((hZm.trans hQe.symm).symm ▸ ht))
    ((hrest j hjF).2.2.trans hj) (hZm.trans hQe.symm) hUj hUm hUrest
  exact ⟨U,hUs.trans hZs,(hUrest i hij him).trans ((hrest i hiF).2.2.trans hi),
    preserves_trans hZp hUp,by rw [hcount,hZc]⟩

lemma maximum_carriers_no_marked_internal_cut [Fintype V]
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (i j : Fin k) (hij : i ≠ j) {r : V} (C : G.Walk r r) (hC : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (hmax : ∀ U : TrailFamily G k, U.score=T.score → (U.walk i).toSubgraph=C.toSubgraph →
      PreservesIncidence T U C.toSubgraph.verts →
      carrierCount U C.toSubgraph.verts ≤ carrierCount T C.toSubgraph.verts)
    (F : Finset (Fin k)) (hiF : i ∉ F) (hjF : j ∉ F)
    (hFC : ∀ x ∈ (selectedGraph T F).support, x ∉ C.support)
    {a z b : V} (A : G.Walk a z) (B : G.Walk z b) (hAB : (A.append B).IsPath)
    (hj : (T.walk j).toSubgraph=(A.append B).toSubgraph)
    (hprefix : ∀ x ∈ A.support, x ∈ (selectedGraph T F).support → x=z)
    (hmark : MarkedPartition (selectedGraph T F) F.card z)
    (hA : (C.toSubgraph.verts ∩ A.toSubgraph.verts).Nonempty)
    (hB : (C.toSubgraph.verts ∩ B.toSubgraph.verts).Nonempty) : False := by
  obtain ⟨U,hUs,hUi,hUp,hUc⟩ := marked_internal_cut_increases_carriers T hs i j hij C hC hi F hiF hjF
    hFC A B hAB hj hprefix hmark hA hB
  have hh := hmax U hUs hUi hUp
  omega

end Erdos583CarrierCountDevelopment
