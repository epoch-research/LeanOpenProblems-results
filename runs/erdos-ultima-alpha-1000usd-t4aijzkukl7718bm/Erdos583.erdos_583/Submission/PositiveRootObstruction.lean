import Submission.RootLocality

/-! Positive endpoint quota at the internally repeated vertex does not ensure
rootification at the same quotas, even for a globally maximum-score family.
This is NOT a counterexample to Gallai's conjecture. -/
namespace Erdos583PositiveRootObstructionDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaRooted Erdos583Work.QuotaSurgery
open Erdos583Work.RootCapacity Erdos583RootLocalityDevelopment
open scoped Classical
set_option maxHeartbeats 1600000

abbrev edges : Finset (Sym2 (Fin 11)) :=
  {s(0,2),s(0,3),s(0,4),s(0,5),s(0,7),s(1,2),s(1,4),s(1,9),s(2,5),
   s(2,9),s(3,4),s(3,7),s(3,8),s(4,8),s(5,6),s(5,10),s(6,10)}
def G : SimpleGraph (Fin 11) := fromEdgeSet (edges : Set (Sym2 (Fin 11)))
instance : DecidableRel G.Adj :=
  inferInstanceAs (DecidableRel (fromEdgeSet (edges : Set (Sym2 (Fin 11)))).Adj)

def p : G.Walk 1 6 := (.cons (by decide : G.Adj 1 2) (.cons (by decide : G.Adj 2 0) (.cons (by decide : G.Adj 0 3) (.cons (by decide : G.Adj 3 4) (.cons (by decide : G.Adj 4 0) (.cons (by decide : G.Adj 0 5) (.cons (by decide : G.Adj 5 6) .nil)))))))

def q : G.Walk 0 6 := (.cons (by decide : G.Adj 0 7) (.cons (by decide : G.Adj 7 3) (.cons (by decide : G.Adj 3 8) (.cons (by decide : G.Adj 8 4) (.cons (by decide : G.Adj 4 1) (.cons (by decide : G.Adj 1 9) (.cons (by decide : G.Adj 9 2) (.cons (by decide : G.Adj 2 5) (.cons (by decide : G.Adj 5 10) (.cons (by decide : G.Adj 10 6) .nil))))))))))

def c129 : G.Walk 1 1 := (.cons (by decide : G.Adj 1 2) (.cons (by decide : G.Adj 2 9) (.cons (by decide : G.Adj 9 1) .nil)))

def c348 : G.Walk 3 3 := (.cons (by decide : G.Adj 3 4) (.cons (by decide : G.Adj 4 8) (.cons (by decide : G.Adj 8 3) .nil)))

def c034 : G.Walk 0 0 := (.cons (by decide : G.Adj 0 3) (.cons (by decide : G.Adj 3 4) (.cons (by decide : G.Adj 4 0) .nil)))

def c0384 : G.Walk 0 0 := (.cons (by decide : G.Adj 0 3) (.cons (by decide : G.Adj 3 8) (.cons (by decide : G.Adj 8 4) (.cons (by decide : G.Adj 4 0) .nil))))

def c0734 : G.Walk 0 0 := (.cons (by decide : G.Adj 0 7) (.cons (by decide : G.Adj 7 3) (.cons (by decide : G.Adj 3 4) (.cons (by decide : G.Adj 4 0) .nil))))

def c07384 : G.Walk 0 0 := (.cons (by decide : G.Adj 0 7) (.cons (by decide : G.Adj 7 3) (.cons (by decide : G.Adj 3 8) (.cons (by decide : G.Adj 8 4) (.cons (by decide : G.Adj 4 0) .nil)))))

abbrev starts : Fin 2 → Fin 11 := ![1,0]
abbrev finishes : Fin 2 → Fin 11 := ![6,6]
def walks : ∀ i, G.Walk (starts i) (finishes i) :=
  Fin.cases p (Fin.cases q (fun i ↦ Fin.elim0 i))
def T : TrailFamily G 2 where
  start := starts
  finish := finishes
  walk := walks
  isTrail := by intro i; simp only [Walk.isTrail_def]; revert i; decide
  disjoint := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro e he hf
    simp only [Walk.mem_edges_toSubgraph] at he hf
    have hd : ∀ i j : Fin 2, i ≠ j → ∀ e : Sym2 (Fin 11),
        e ∈ (walks i).edges → e ∉ (walks j).edges := by decide
    exact hd i j hij e he hf
  cover := by
    intro e
    induction e using Sym2.ind with
    | h a b =>
      simp only [mem_edgeSet,Walk.mem_edges_toSubgraph]
      revert a b
      decide

abbrev quota : Fin 11 → ℕ := ![1,1,0,0,0,0,2,0,0,0,0]
lemma quota_table (v : Fin 11) : T.quota v=quota v := by
  rw [TrailFamily.quota,Nat.card_eq_fintype_card]
  revert v
  decide
lemma connected : G.Connected := by
  classical
  have hm (v : Fin 11) : v ∈ q.support := by revert v; decide
  exact ⟨fun u v ↦ (q.takeUntil u (hm u)).reachable.symm.trans (q.takeUntil v (hm v)).reachable⟩
lemma edge_card : G.edgeSet.ncard=17 := by
  rw [←Nat.card_coe_set_eq,Nat.card_eq_fintype_card]
  decide
lemma one_defect : T.score+1=G.edgeSet.ncard+2 := by
  rw [edge_card]
  simp [TrailFamily.score,T,walks,p,q,Fin.sum_univ_succ,Walk.verts_toSubgraph]
  simp only [Set.ncard_eq_toFinset_card',Set.toFinset_setOf]
  decide
lemma degrees (v : Fin 11) : Nat.card (G.neighborSet v)= (![5,3,4,4,4,4,2,2,2,2,2] : Fin 11 → ℕ) v := by
  rw [Nat.card_eq_fintype_card,card_neighborSet_eq_degree]
  revert v
  decide

lemma neighbor_sum (K : G.Subgraph) (v : Fin 11) :
    (K.neighborSet v).ncard=∑ w ∈ G.neighborFinset v, if K.Adj v w then 1 else 0 := by
  classical
  rw [Set.ncard_eq_toFinset_card',←Finset.card_filter]
  congr 1
  ext w
  simp only [Set.mem_toFinset,Subgraph.mem_neighborSet,Finset.mem_filter,mem_neighborFinset]
  exact ⟨fun h ↦ ⟨K.adj_sub h,h⟩,fun h ↦ h.2⟩

lemma path_no_cycle {a b c : Fin 11} (P : G.Walk a b) (hp : P.IsPath)
    (C : G.Walk c c) (hc : C.IsCycle)
    (he : C.toSubgraph.edgeSet ⊆ P.toSubgraph.edgeSet) : False := by
  let H := P.toSubgraph.spanningCoe
  have hE : ∀ e ∈ C.edges, e ∈ H.edgeSet := fun e heC ↦ he (C.mem_edges_toSubgraph.mpr heC)
  exact (MatchingTrim.path_spanningCoe_isAcyclic P hp) (C.transfer H hE) (hc.transfer hE)

lemma even_pair_iff (P Q : Prop) [Decidable P] [Decidable Q]
    (he : Even ((if P then 1 else 0)+(if Q then 1 else 0) : ℕ)) : P ↔ Q := by
  obtain ⟨m,hm⟩ := he
  by_cases hP : P <;> by_cases hQ : Q <;> simp_all <;> omega

lemma c129_cycle : c129.IsCycle := by
  simp [c129,Walk.cons_isCycle_iff,Walk.isPath_def]

lemma c348_cycle : c348.IsCycle := by
  simp [c348,Walk.cons_isCycle_iff,Walk.isPath_def]

lemma c034_cycle : c034.IsCycle := by
  simp [c034,Walk.cons_isCycle_iff,Walk.isPath_def]

lemma c0384_cycle : c0384.IsCycle := by
  simp [c0384,Walk.cons_isCycle_iff,Walk.isPath_def]

lemma c0734_cycle : c0734.IsCycle := by
  simp [c0734,Walk.cons_isCycle_iff,Walk.isPath_def]

lemma c07384_cycle : c07384.IsCycle := by
  simp [c07384,Walk.cons_isCycle_iff,Walk.isPath_def]


lemma no_path_pattern {a b : Fin 11} (P : G.Walk a b) (hp : P.IsPath)
    (h1 : (P.toSubgraph.neighborSet 1).ncard=1)
    (h3 : (P.toSubgraph.neighborSet 3).ncard=2)
    (h4 : (P.toSubgraph.neighborSet 4).ncard=2)
    (h7 : Even (P.toSubgraph.neighborSet 7).ncard)
    (h8 : Even (P.toSubgraph.neighborSet 8).ncard)
    (h9 : Even (P.toSubgraph.neighborSet 9).ncard)
    (h129 : P.toSubgraph.Adj 1 2 ∨ P.toSubgraph.Adj 1 9 ∨ P.toSubgraph.Adj 2 9)
    (h348 : P.toSubgraph.Adj 3 4 ∨ P.toSubgraph.Adj 3 8 ∨ P.toSubgraph.Adj 4 8) : False := by
  classical
  let K := P.toSubgraph
  have n348 : ¬(K.Adj 3 4 ∧ K.Adj 4 8 ∧ K.Adj 3 8) := by
    rintro ⟨h0,h1,h2⟩
    apply path_no_cycle P hp c348 c348_cycle
    intro e he
    simp only [Walk.mem_edges_toSubgraph,c348,Walk.edges_cons,Walk.edges_nil,
      List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl|rfl
    · exact h0
    · exact h1
    · exact h2.symm
  have n034 : ¬(K.Adj 0 3 ∧ K.Adj 3 4 ∧ K.Adj 0 4) := by
    rintro ⟨h0,h1,h2⟩
    apply path_no_cycle P hp c034 c034_cycle
    intro e he
    simp only [Walk.mem_edges_toSubgraph,c034,Walk.edges_cons,Walk.edges_nil,
      List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl|rfl
    · exact h0
    · exact h1
    · exact h2.symm
  have n0384 : ¬(K.Adj 0 3 ∧ K.Adj 3 8 ∧ K.Adj 4 8 ∧ K.Adj 0 4) := by
    rintro ⟨h0,h1,h2,h3⟩
    apply path_no_cycle P hp c0384 c0384_cycle
    intro e he
    simp only [Walk.mem_edges_toSubgraph,c0384,Walk.edges_cons,Walk.edges_nil,
      List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl|rfl|rfl
    · exact h0
    · exact h1
    · exact h2.symm
    · exact h3.symm
  have n0734 : ¬(K.Adj 0 7 ∧ K.Adj 3 7 ∧ K.Adj 3 4 ∧ K.Adj 0 4) := by
    rintro ⟨h0,h1,h2,h3⟩
    apply path_no_cycle P hp c0734 c0734_cycle
    intro e he
    simp only [Walk.mem_edges_toSubgraph,c0734,Walk.edges_cons,Walk.edges_nil,
      List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl|rfl|rfl
    · exact h0
    · exact h1.symm
    · exact h2
    · exact h3.symm
  have n07384 : ¬(K.Adj 0 7 ∧ K.Adj 3 7 ∧ K.Adj 3 8 ∧ K.Adj 4 8 ∧ K.Adj 0 4) := by
    rintro ⟨h0,h1,h2,h3,h4⟩
    apply path_no_cycle P hp c07384 c07384_cycle
    intro e he
    simp only [Walk.mem_edges_toSubgraph,c07384,Walk.edges_cons,Walk.edges_nil,
      List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl|rfl|rfl|rfl
    · exact h0
    · exact h1.symm
    · exact h2
    · exact h3.symm
    · exact h4.symm
  have hn1 : G.neighborFinset 1={2,4,9} := by decide
  have hn3 : G.neighborFinset 3={0,4,7,8} := by decide
  have hn4 : G.neighborFinset 4={0,1,3,8} := by decide
  have hn7 : G.neighborFinset 7={0,3} := by decide
  have hn8 : G.neighborFinset 8={3,4} := by decide
  have hn9 : G.neighborFinset 9={1,2} := by decide
  have hsym (x y : Fin 11) : K.Adj x y ↔ K.Adj y x := ⟨fun h ↦ h.symm,fun h ↦ h.symm⟩
  change (K.neighborSet 1).ncard=1 at h1
  change (K.neighborSet 3).ncard=2 at h3
  change (K.neighborSet 4).ncard=2 at h4
  change Even (K.neighborSet 7).ncard at h7
  change Even (K.neighborSet 8).ncard at h8
  change Even (K.neighborSet 9).ncard at h9
  rw [neighbor_sum,hn1] at h1
  rw [Finset.sum_insert (by decide),Finset.sum_insert (by decide),Finset.sum_singleton] at h1
  rw [neighbor_sum,hn3] at h3
  rw [Finset.sum_insert (by decide),Finset.sum_insert (by decide),Finset.sum_insert (by decide),Finset.sum_singleton] at h3
  rw [neighbor_sum,hn4] at h4
  rw [Finset.sum_insert (by decide),Finset.sum_insert (by decide),Finset.sum_insert (by decide),Finset.sum_singleton] at h4
  rw [neighbor_sum,hn7] at h7
  rw [Finset.sum_insert (by decide),Finset.sum_singleton] at h7
  rw [neighbor_sum,hn8] at h8
  rw [Finset.sum_insert (by decide),Finset.sum_singleton] at h8
  rw [neighbor_sum,hn9] at h9
  rw [Finset.sum_insert (by decide),Finset.sum_singleton] at h9
  simp only [hsym 3 0] at h3
  simp only [hsym 4 0,hsym 4 1,hsym 4 3] at h4
  simp only [hsym 7 0,hsym 7 3] at h7
  simp only [hsym 8 3,hsym 8 4] at h8
  simp only [hsym 9 1,hsym 9 2] at h9
  have p7 := even_pair_iff _ _ h7
  have p8 := even_pair_iff _ _ h8
  have p9 := even_pair_iff _ _ h9
  change K.Adj 1 2 ∨ K.Adj 1 9 ∨ K.Adj 2 9 at h129
  change K.Adj 3 4 ∨ K.Adj 3 8 ∨ K.Adj 4 8 at h348
  have hx : K.Adj 1 2 ∨ K.Adj 1 9 := h129.elim Or.inl (fun hh ↦ Or.inr (hh.elim id p9.mpr))
  have hn14 : ¬K.Adj 1 4 := by
    intro h
    rcases hx with hx|hx <;> simp [hx,h] at h1
  have hy : K.Adj 3 4 ∨ K.Adj 3 8 := h348.elim Or.inl (fun hh ↦ Or.inr (hh.elim id p8.mpr))
  have hsum : (if K.Adj 3 4 then 1 else 0)+(if K.Adj 3 8 then 1 else 0)= (1 : ℕ) := by
    by_cases h : K.Adj 3 4
    · have hn : ¬K.Adj 3 8 := fun hh ↦ n348 ⟨h,p8.mp hh,hh⟩
      simp [h,hn]
    · have hm : K.Adj 3 8 := hy.resolve_left h
      simp [h,hm]
  rw [←propext p7] at h3
  rw [←propext p8] at h4
  have h03 : K.Adj 0 3 ∨ K.Adj 0 7 := by
    by_contra! hn
    simp only [if_neg hn.1,if_neg hn.2,zero_add] at h3
    omega
  have h04 : K.Adj 0 4 := by
    by_contra hn
    simp only [if_neg hn,if_neg hn14,zero_add] at h4
    omega
  rcases h03 with h03|h07 <;> rcases hy with h34|h38
  · exact n034 ⟨h03,h34,h04⟩
  · exact n0384 ⟨h03,h38,p8.mp h38,h04⟩
  · exact n0734 ⟨h07,p7.mp h07,h34,h04⟩
  · exact n07384 ⟨h07,p7.mp h07,h38,p8.mp h38,h04⟩


lemma quota_one_separates (S : TrailFamily G 2) {i j : Fin 2} (hij : i ≠ j)
    {v : Fin 11} (hq : S.quota v=1)
    (hi : v=S.start i ∨ v=S.finish i) (hj : v=S.start j ∨ v=S.finish j) : False := by
  letI : Subsingleton {x : Fin 2 × Bool // S.endpoint x=v} :=
    (Nat.card_eq_one_iff_unique.mp hq).1
  obtain ⟨bi,hbi⟩ : ∃ bi : Bool, S.endpoint (i,bi)=v := by
    rcases hi with hi|hi
    · exact ⟨true,hi.symm⟩
    · exact ⟨false,hi.symm⟩
  obtain ⟨bj,hbj⟩ : ∃ bj : Bool, S.endpoint (j,bj)=v := by
    rcases hj with hj|hj
    · exact ⟨true,hj.symm⟩
    · exact ⟨false,hj.symm⟩
  exact hij (congrArg (fun z : {x : Fin 2 × Bool // S.endpoint x=v} ↦ z.val.1)
    (Subsingleton.elim ⟨(i,bi),hbi⟩ ⟨(j,bj),hbj⟩))

lemma all_members_contain (S : TrailFamily G 2) (hs : S.score+1=G.edgeSet.ncard+2)
    (hr : HasRoot S 0) {v : Fin 11} (hv : v ≠ 0)
    (hd : Nat.card (G.neighborSet v)+S.quota v=4) (i : Fin 2) : v ∈ (S.walk i).support := by
  classical
  letI : DecidableEq (Fin 11) := Classical.decEq _
  have h := rooted_incidence S 0 hs hr v
  rw [if_neg hv.symm,mul_zero,add_zero,hd] at h
  have hc := Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2)
    (show _ = 2*2 from h.symm)
  have hu := Finset.eq_univ_of_card _ hc
  have hm := Finset.mem_univ i
  rw [←hu] at hm
  exact (Finset.mem_filter.mp hm).2

lemma off_root_cycle_hits_each (S : TrailFamily G 2) (hs : S.score+1=G.edgeSet.ncard+2)
    (hr : HasRoot S 0) {a : Fin 11} (C : G.Walk a a) (hc : C.IsCycle)
    (hz : (0 : Fin 11) ∉ C.support) (j : Fin 2) :
    (C.toSubgraph.edgeSet ∩ (S.walk j).toSubgraph.edgeSet).Nonempty := by
  classical
  by_contra hn
  obtain ⟨i,hij⟩ := exists_ne j
  have hinds (l : Fin 2) : l=j ∨ l=i := by fin_cases i <;> fin_cases j <;> fin_cases l <;> simp_all
  apply hz
  apply member_cycle_contains_root S 0 hs hr i C hc
  intro e he
  obtain ⟨l,hl⟩ := (S.cover e).mp (C.toSubgraph.edgeSet_subset he)
  rcases hinds l with rfl|rfl
  · exact (hn ⟨e,he,hl⟩).elim
  · exact hl

lemma no_rooted_same_quotas :
    ¬∃ (S : TrailFamily G 2) (r : Fin 11), (∀ v, S.quota v=T.quota v) ∧
      S.score+1=G.edgeSet.ncard+2 ∧ HasRoot S r := by
  classical
  rintro ⟨S,r,hq,hs,hr⟩
  have hquota (v) : S.quota v=quota v := (hq v).trans (quota_table v)
  have hr0 : r=0 := root_eq_of_over_capacity S r hs hr 0 (by rw [hquota,degrees]; decide)
  subst r
  obtain ⟨A,R,ρ,hρ,hn⟩ := hr
  have hx : (R.tail ρ).toSubgraph.Adj 0 (R.tail ρ).snd := by
    simpa only [hρ] using (R.tail ρ).toSubgraph_adj_snd hn
  obtain ⟨i,b,h,p,_,hends,ht,he,hrep⟩ := rooted_exposed_rep R ρ hρ hx
  obtain ⟨_,_,hothers⟩ := simple_tail_of_one_defect_rep S hs i h p ht he hrep
  have hroot : HasRoot S 0 := ⟨A,R,ρ,hρ,hn⟩
  obtain ⟨j,hji⟩ := exists_ne i
  have hp := hothers j hji
  have hi0 : (0 : Fin 11)=S.start i ∨ (0 : Fin 11)=S.finish i :=
    hends.elim (fun hh ↦ Or.inl hh.1.symm) (fun hh ↦ Or.inr hh.1.symm)
  have hj0 : ¬((0 : Fin 11)=S.start j ∨ (0 : Fin 11)=S.finish j) :=
    fun hh ↦ quota_one_separates S hji.symm (hquota 0) hi0 hh
  have allowed (v : Fin 11) (hv : v=S.start j ∨ v=S.finish j) : v=0 ∨ v=1 ∨ v=6 := by
    have hpos := DeletionEndpoint.quota_pos_of_endpoint S j hv
    rw [hquota] at hpos
    have hf : ∀ v : Fin 11, 0 < quota v → v=0 ∨ v=1 ∨ v=6 := by decide
    exact hf v hpos
  have ha : S.start j=1 ∨ S.start j=6 :=
    (allowed _ (Or.inl rfl)).resolve_left (fun h ↦ hj0 (Or.inl h.symm))
  have hb : S.finish j=1 ∨ S.finish j=6 :=
    (allowed _ (Or.inr rfl)).resolve_left (fun h ↦ hj0 (Or.inr h.symm))
  have hm3 := all_members_contain S hs hroot (v := 3) (by decide) (by rw [hquota,degrees]; decide) j
  have hm4 := all_members_contain S hs hroot (v := 4) (by decide) (by rw [hquota,degrees]; decide) j
  have hnot (v : Fin 11) (hv : quota v=0) : v ≠ S.start j ∧ v ≠ S.finish j := by
    constructor <;> intro hh
    · have hh' := DeletionEndpoint.quota_pos_of_endpoint S j (Or.inl hh)
      rw [hquota,hv] at hh'; omega
    · have hh' := DeletionEndpoint.quota_pos_of_endpoint S j (Or.inr hh)
      rw [hquota,hv] at hh'; omega
  have hnP : ¬(S.walk j).Nil := by
    intro hh
    rw [Walk.nil_iff_support_eq.mp hh] at hm3
    exact (hnot 3 (by decide)).1 (List.mem_singleton.mp hm3)
  have hne : S.start j ≠ S.finish j := path_endpoints_ne hp
    ⟨s(S.start j,(S.walk j).snd),(S.walk j).toSubgraph_adj_snd hnP⟩
  have hj1 : (1 : Fin 11)=S.start j ∨ (1 : Fin 11)=S.finish j := by
    rcases ha with ha|ha
    · exact Or.inl ha.symm
    rcases hb with hb|hb
    · exact Or.inr hb.symm
    · exact (hne (ha.trans hb.symm)).elim
  apply no_path_pattern (S.walk j) hp
  · simpa only [if_pos hj1] using path_neighbor_ncard_formula hp hnP (1 : Fin 11)
  · simpa only [if_neg (not_or.mpr (hnot 3 (by decide))),if_pos hm3] using
      path_neighbor_ncard_formula hp hnP (3 : Fin 11)
  · simpa only [if_neg (not_or.mpr (hnot 4 (by decide))),if_pos hm4] using
      path_neighbor_ncard_formula hp hnP (4 : Fin 11)
  · exact path_neighbor_ncard_even hp (hnot 7 (by decide)).1 (hnot 7 (by decide)).2
  · exact path_neighbor_ncard_even hp (hnot 8 (by decide)).1 (hnot 8 (by decide)).2
  · exact path_neighbor_ncard_even hp (hnot 9 (by decide)).1 (hnot 9 (by decide)).2
  · obtain ⟨e,heC,heP⟩ := off_root_cycle_hits_each S hs hroot c129 c129_cycle (by decide) j
    simp only [Walk.mem_edges_toSubgraph,c129,Walk.edges_cons,Walk.edges_nil,List.mem_cons,
      List.not_mem_nil,or_false] at heC
    rcases heC with rfl|rfl|rfl
    · exact Or.inl heP
    · exact Or.inr (Or.inr heP)
    · exact Or.inr (Or.inl (Subgraph.Adj.symm heP))
  · obtain ⟨e,heC,heP⟩ := off_root_cycle_hits_each S hs hroot c348 c348_cycle (by decide) j
    simp only [Walk.mem_edges_toSubgraph,c348,Walk.edges_cons,Walk.edges_nil,List.mem_cons,
      List.not_mem_nil,or_false] at heC
    rcases heC with rfl|rfl|rfl
    · exact Or.inl heP
    · exact Or.inr (Or.inr heP)
    · exact Or.inr (Or.inl (Subgraph.Adj.symm heP))


lemma no_two_paths (S : TrailFamily G 2) : ¬∀ i, (S.walk i).IsPath := by
  intro hp
  have hd := QuotaParity.degree_sum S (0 : Fin 11)
  rw [degrees,Fin.sum_univ_two] at hd
  have h0 := path_neighbor_ncard_le_two ⟨_,_,S.walk 0,hp 0,rfl⟩ (0 : Fin 11)
  have h1 := path_neighbor_ncard_le_two ⟨_,_,S.walk 1,hp 1,rfl⟩ (0 : Fin 11)
  norm_num at hd
  omega

lemma global_maximum (S : TrailFamily G 2) : S.score ≤ T.score := by
  have hb := S.score_le_edges_add
  have hn : S.score ≠ G.edgeSet.ncard+2 := fun hh ↦
    no_two_paths S (S.score_eq_edges_add_iff.mp hh)
  have ht := one_defect
  omega

lemma positive_repetition : 0 < T.quota 0 ∧ (T.walk 0).support.count 0=2 := by
  rw [quota_table]
  decide

def goodA : G.Walk 1 3 := (.cons (by decide : G.Adj 1 2) (.cons (by decide : G.Adj 2 0) (.cons (by decide : G.Adj 0 3) .nil)))

def goodB : G.Walk 3 6 := (.cons (by decide : G.Adj 3 4) (.cons (by decide : G.Adj 4 0) (.cons (by decide : G.Adj 0 5) (.cons (by decide : G.Adj 5 6) .nil))))

abbrev goodStarts : Fin 3 → Fin 11 := ![1,3,0]
abbrev goodFinishes : Fin 3 → Fin 11 := ![3,6,6]
def goodWalks : ∀ i, G.Walk (goodStarts i) (goodFinishes i) :=
  Fin.cases goodA (Fin.cases goodB (Fin.cases q (fun i ↦ Fin.elim0 i)))
def good : TrailFamily G 3 where
  start := goodStarts
  finish := goodFinishes
  walk := goodWalks
  isTrail := by intro i; simp only [Walk.isTrail_def]; revert i; decide
  disjoint := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro e he hf
    simp only [Walk.mem_edges_toSubgraph] at he hf
    have hd : ∀ i j : Fin 3, i ≠ j → ∀ e : Sym2 (Fin 11),
        e ∈ (goodWalks i).edges → e ∉ (goodWalks j).edges := by decide
    exact hd i j hij e he hf
  cover := by
    intro e
    induction e using Sym2.ind with
    | h a b =>
      simp only [mem_edgeSet,Walk.mem_edges_toSubgraph]
      revert a b
      decide

lemma three_paths : ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ 3 :=
  MatchingAppend.path_family_partition good (by intro i; simp only [Walk.isPath_def]; revert i; decide)

/-- A globally maximum single internal defect with positive quota at its
repeated vertex need not have ANY rooted realization at the same quotas.
There are eleven vertices and only two slots; this is below the Gallai budget. -/
lemma witness : G.Connected ∧ T.score+1=G.edgeSet.ncard+2 ∧
    (∀ S : TrailFamily G 2, S.score ≤ T.score) ∧
    0 < T.quota 0 ∧ (T.walk 0).support.count 0=2 ∧
    (¬∃ (S : TrailFamily G 2) (r : Fin 11), (∀ v, S.quota v=T.quota v) ∧
      S.score+1=G.edgeSet.ncard+2 ∧ HasRoot S r) ∧
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ 3 :=
  ⟨connected,one_defect,global_maximum,positive_repetition.1,positive_repetition.2,
    no_rooted_same_quotas,three_paths⟩

end Erdos583PositiveRootObstructionDevelopment
