import Submission.Work
import Submission.OddContiguousRegion

/-! The one-port obstruction for contiguous carriers does not require odd cycle order. -/
namespace Erdos583ContiguousRegionDevelopment
open SimpleGraph Erdos583Work Erdos583Work.VertexCritical
open Erdos583OddContiguousRegionDevelopment
open scoped Classical
set_option maxHeartbeats 1800000

lemma unique_crossing_bridge {V : Type*} {G : SimpleGraph V} (S : Set V) {u v : V}
    (h : G.Adj u v) (hu : u ∈ S) (hv : v ∉ S)
    (hcross : ∀ x ∈ S, ∀ y ∉ S, G.Adj x y → x=u ∧ y=v) : G.IsBridge s(u,v) := by
  have crosses {a b : V} (P : G.Walk a b) (ha : a ∈ S) (hb : b ∉ S) : s(u,v) ∈ P.edges := by
    induction P with
    | nil => exact (hb ha).elim
    | @cons a c b hac P ih =>
      simp only [Walk.edges_cons,List.mem_cons]
      by_cases hc : c ∈ S
      · exact Or.inr (ih hc hb)
      · obtain ⟨rfl,rfl⟩ := hcross a ha c hc hac
        exact Or.inl rfl
  exact isBridge_iff_adj_and_forall_walk_mem_edges.mpr ⟨h,fun P ↦ crosses P hu hv⟩

lemma path_ends_ne {V : Type*} {G : SimpleGraph V} {a b : V} (P : G.Walk a b)
    (hp : P.IsPath) (hn : ¬P.Nil) : a ≠ b := by
  rintro rfl
  exact hn (Walk.nil_iff_eq_nil.mpr ((Walk.isPath_iff_eq_nil P).mp hp))

lemma single_tail_port_degree {V : Type*} [Fintype V] {G : SimpleGraph V} {r a b t : V}
    (C : G.Walk r r) (hC : C.IsCycle) (P : G.Walk a b) (B : G.Walk b t)
    (hp : (P.append B).IsPath) (hnP : ¬P.Nil) (hnB : ¬B.Nil)
    (hb : b ∈ C.support)
    (hd : Disjoint C.toSubgraph.edgeSet (P.append B).toSubgraph.edgeSet)
    (hcarrier : ∀ y, G.Adj b y → C.toSubgraph.Adj b y ∨ (P.append B).toSubgraph.Adj b y) :
    Nat.card (G.neighborSet b)=4 := by
  classical
  have hba := (path_ends_ne P hp.of_append_left hnP).symm
  have hbt := path_ends_ne B hp.of_append_right hnB
  have hn : ¬(P.append B).Nil := fun hh ↦ hnP (Walk.nil_append_iff.mp hh).1
  have hbW : b ∈ (P.append B).support := by
    rw [Walk.mem_support_append_iff]; exact Or.inl P.end_mem_support
  have hW : ((P.append B).toSubgraph.neighborSet b).ncard=2 := by
    simpa only [hba,hbt,false_or,if_false,hbW,if_true] using path_neighbor_ncard_formula hp hn b
  have hN : G.neighborSet b=C.toSubgraph.neighborSet b ∪ (P.append B).toSubgraph.neighborSet b := by
    ext y
    exact ⟨hcarrier y,fun hh ↦ hh.elim C.toSubgraph.adj_sub (P.append B).toSubgraph.adj_sub⟩
  have hdis : Disjoint (C.toSubgraph.neighborSet b) ((P.append B).toSubgraph.neighborSet b) := by
    apply Set.disjoint_left.mpr
    intro y hy hy'
    exact Set.disjoint_left.mp hd (show s(b,y) ∈ C.toSubgraph.edgeSet from hy)
      (show s(b,y) ∈ (P.append B).toSubgraph.edgeSet from hy')
  rw [Nat.card_coe_set_eq,hN,Set.ncard_union_eq hdis,hC.ncard_neighborSet_toSubgraph_eq_two hb,hW]

lemma failure_no_single_tail {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {r a b t : Fin n} (C : G.Walk r r) (hC : C.IsCycle)
    (hsize : C.length < n)
    (P : G.Walk a b) (B : G.Walk b t) (hp : (P.append B).IsPath) (hnP : ¬P.Nil)
    (hP : ∀ x ∈ P.support, x ∈ C.support)
    (hB : ∀ x ∈ B.support, x ∈ C.support → x=b)
    (hd : Disjoint C.toSubgraph.edgeSet (P.append B).toSubgraph.edgeSet)
    (hcarrier : ∀ x ∈ C.support, ∀ y, G.Adj x y →
      C.toSubgraph.Adj x y ∨ (P.append B).toSubgraph.Adj x y) : False := by
  let S : Set (Fin n) := {x | x ∈ C.support}
  have hSc : S.ncard=C.length := cycle_support_ncard hC
  cases B with
  | nil =>
    have hclosed : S=Set.univ := by
      apply TrailBudget.connected_closed_set hG S ⟨r,C.start_mem_support⟩
      intro x y hxy hx
      rcases hcarrier x hx y hxy with he|he
      · exact Walk.mem_support_of_adj_toSubgraph (C.toSubgraph.symm he)
      · simp only [Walk.append_nil] at he
        exact hP y (Walk.mem_support_of_adj_toSubgraph (P.toSubgraph.symm he))
    rw [hclosed] at hSc
    simp only [Set.ncard_univ,Nat.card_fin] at hSc
    omega
  | @cons _ v _ h R =>
    have hR : ∀ x ∈ R.support, x ∉ C.support := by
      intro x hx hxC
      have he := hB x (List.mem_cons_of_mem _ hx) hxC
      exact (Walk.cons_isPath_iff h R).mp hp.of_append_right |>.2 (he ▸ hx)
    have hcross : ∀ x ∈ S, ∀ y ∉ S, G.Adj x y → x=b ∧ y=v := by
      intro x hx y hy hxy
      rcases hcarrier x hx y hxy with hc|hc
      · exact (hy (Walk.mem_support_of_adj_toSubgraph (C.toSubgraph.symm hc))).elim
      · change s(x,y) ∈ (P.append (Walk.cons h R)).toSubgraph.edgeSet at hc
        have hh : s(x,y) ∈ P.toSubgraph.edgeSet ∨ s(x,y)=s(b,v) ∨
            s(x,y) ∈ R.toSubgraph.edgeSet := by
          simpa only [Walk.edgeSet_toSubgraph,Set.mem_setOf_eq,Walk.edges_append,
            Walk.edges_cons,List.mem_append,List.mem_cons] using hc
        rcases hh with hh|hh|hh
        · exact (hy (hP y (Walk.mem_support_of_adj_toSubgraph (P.toSubgraph.symm hh)))).elim
        · rcases Sym2.eq_iff.mp hh with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
          · exact ⟨rfl,rfl⟩
          · exact (hR _ R.start_mem_support hx).elim
        · exact (hR x (Walk.mem_support_of_adj_toSubgraph hh) hx).elim
    have hbr := unique_crossing_bridge S h (hP b P.end_mem_support) (hR v R.start_mem_support) hcross
    have hdeg := single_tail_port_degree C hC P (Walk.cons h R) hp hnP (by simp)
      (hP b P.end_mem_support) hd (hcarrier b (hP b P.end_mem_support))
    have ho := (BridgeParityReduction.bridge_endpoints_odd_of_failure hsmall hG hfail hbr).1
    rw [hdeg] at ho
    exact (by decide : ¬Odd (4 : ℕ)) ho

lemma failure_no_contiguous_region {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {r s a b t : Fin n} (C : G.Walk r r) (hC : C.IsCycle)
    (hlen : 5 ≤ C.length) (hsize : C.length < n)
    (A : G.Walk s a) (P : G.Walk a b) (B : G.Walk b t)
    (hp : (A.append (P.append B)).IsPath) (hnP : ¬P.Nil)
    (hA : ∀ x ∈ A.support, x ∈ C.support → x=a)
    (hB : ∀ x ∈ B.support, x ∈ C.support → x=b)
    (hP : ∀ x ∈ P.support, x ∈ C.support)
    (hd : Disjoint (A.append (P.append B)).toSubgraph.edgeSet C.toSubgraph.edgeSet)
    (hcarrier : ∀ x ∈ C.support, ∀ y, G.Adj x y →
      C.toSubgraph.Adj x y ∨ (A.append (P.append B)).toSubgraph.Adj x y) : False := by
  by_cases hnA : A.Nil
  · cases A with
    | nil =>
      exact failure_no_single_tail hsmall hG hfail C hC hsize P B
        hp.of_append_right hnP hP hB (by simpa using hd.symm)
        (by simpa only [Walk.nil_append] using hcarrier)
    | cons h R => exact (Walk.not_nil_cons hnA).elim
  by_cases hnB : B.Nil
  · cases B with
    | nil =>
      have hr : (P.reverse.append A.reverse).IsPath := by
        simpa only [Walk.append_nil,Walk.reverse_append] using hp.reverse
      apply failure_no_single_tail hsmall hG hfail C hC hsize P.reverse A.reverse hr
        (by simpa only [Walk.nil_reverse] using hnP)
      · simpa only [Walk.support_reverse,List.mem_reverse] using hP
      · simpa only [Walk.support_reverse,List.mem_reverse] using hA
      · simpa only [Walk.append_nil,←Walk.reverse_append,Walk.toSubgraph_reverse] using hd.symm
      · intro x hx y hxy
        simpa only [Walk.append_nil,←Walk.reverse_append,Walk.toSubgraph_reverse] using hcarrier x hx y hxy
    | cons h R => exact (Walk.not_nil_cons hnB).elim
  obtain ⟨u,L,hua,heA,hL⟩ := remove_last_tail C A hp.of_append_left hnA hA
  obtain ⟨v,hbv,R,heB,hR⟩ := remove_first_tail C B hp.of_append_right.of_append_right hnB hB
  have he : A.append (P.append B)=L.append (Walk.cons hua (P.append (Walk.cons hbv R))) := by
    rw [heA,heB,Walk.concat_eq_append,←Walk.append_assoc,Walk.cons_append,Walk.nil_append]
  apply hfail
  apply CorridorReduction.single_carrier_cycle_region hsmall hG C hC hlen L P R hua hbv
    (he ▸ hp) hL hR hP (he ▸ hd)
  simpa only [←he] using hcarrier

lemma failure_no_single_contiguous_member {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : QuotaTrails.TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hm : ∀ U : QuotaTrails.TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score ≤ T.score)
    (i j : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) (hij : i ≠ j)
    {r a b : Fin n} (C : G.Walk r r) (hC : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (A : G.Walk (T.start j) a) (P : G.Walk a b) (B : G.Walk b (T.finish j))
    (hj : T.walk j=A.append (P.append B)) (hnP : ¬P.Nil)
    (hA : ∀ x ∈ A.support, x ∈ C.support → x=a)
    (hB : ∀ x ∈ B.support, x ∈ C.support → x=b)
    (hP : ∀ x ∈ P.support, x ∈ C.support)
    (hother : ∀ l, l ≠ i → l ≠ j → ∀ x ∈ (T.walk l).support, x ∉ C.support) : False := by
  have hb : Fintype.card (Fin n) ≤ 2*⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
    simp only [Fintype.card_fin,BridgeGlue.ceil_half]; omega
  have hlen := QuadrilateralAbsorption.whole_cycle_length_ge_five T hG hs hm hb i C hC hi
  have hcard := Set.ncard_le_card {x | x ∈ C.support}
  rw [cycle_support_ncard hC,Nat.card_fin] at hcard
  have hk : 2 < ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
    simp only [Fintype.card_fin,BridgeGlue.ceil_half]; omega
  obtain ⟨l,hli,hlj⟩ := Fin.exists_ne_and_ne_of_two_lt i j hk
  have havoid := hother l hli hlj (T.start l) (T.walk l).start_mem_support
  have hS : {x | x ∈ C.support} ≠ Set.univ := by
    intro he
    apply havoid
    have hh : T.start l ∈ {x | x ∈ C.support} := by rw [he]; trivial
    exact hh
  have hsize := Set.ncard_lt_card hS
  rw [cycle_support_ncard hC,Nat.card_fin] at hsize
  have hp := (T.one_defect_other_paths hs i (CycleEar.cycle_member_not_path T i C hC hi)).2 j hij.symm
  apply failure_no_contiguous_region hsmall hG hfail C hC hlen hsize A P B (hj ▸ hp) hnP hA hB hP
  · rw [←hj,←hi]; exact T.disjoint hij.symm
  · intro x hx y hxy
    obtain ⟨l,hl⟩ := (T.cover s(x,y)).mp hxy
    by_cases hli : l=i
    · subst l; exact Or.inl (hi ▸ hl)
    · by_cases hlj : l=j
      · subst l; exact Or.inr ((congrArg Walk.toSubgraph hj) ▸ hl)
      · exact (hother l hli hlj x (Walk.mem_support_of_adj_toSubgraph hl) hx).elim

end Erdos583ContiguousRegionDevelopment
