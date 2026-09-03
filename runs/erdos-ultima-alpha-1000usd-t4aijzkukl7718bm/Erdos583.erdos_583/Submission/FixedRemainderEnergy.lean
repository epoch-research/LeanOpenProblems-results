import Submission.UniversalNormalEndpoints

/-! Energy minimization among path partitions of the fixed normal remainder.
This does not add a global quota-energy minimum to the optimized defect.
The lollipop is kept fixed, and only its ordinary remainder is optimized. -/
namespace Erdos583FixedRemainderEnergyDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.RootEnergy
open Erdos583UnifiedMinimalDefectDevelopment Erdos583NormalRemainderCriticalDevelopment
open Erdos583UniversalNormalEndpointsDevelopment Erdos583TailEdgeAbsorptionDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}

def PathEnergyMinimum (T : TrailFamily G k) : Prop :=
  ∀ U : TrailFamily G k, (∀ i, (U.walk i).IsPath) → quotaEnergy T ≤ quotaEnergy U

lemma exists_path_energy_minimum (T : TrailFamily G k) (hp : ∀ i, (T.walk i).IsPath) :
    ∃ U : TrailFamily G k, (∀ i, (U.walk i).IsPath) ∧ PathEnergyMinimum U := by
  let P (m : ℕ) := ∃ U : TrailFamily G k, (∀ i, (U.walk i).IsPath) ∧ quotaEnergy U=m
  have hex : ∃ m, P m := ⟨quotaEnergy T,T,hp,rfl⟩
  obtain ⟨U,hU,he⟩ := Nat.find_spec hex
  refine ⟨U,hU,?_⟩
  intro W hW
  rw [he]
  exact Nat.find_min' hex ⟨W,hW,rfl⟩

lemma pair_energy_balance_general (q Q : V → ℕ) (r x : V) (hrx : r ≠ x)
    (hbal : ∀ v, Q v+2*(if r=v then 1 else 0)=q v+2*(if x=v then 1 else 0)) :
    (∑ v, (Q v)^2)+4*q r=(∑ v, (q v)^2)+4*q x+8 := by
  have hQr : Q r+2=q r := by
    simpa only [if_pos rfl,if_neg hrx.symm,mul_one,mul_zero,add_zero] using hbal r
  have hQx : Q x=q x+2 := by
    simpa only [if_neg hrx,if_pos rfl,mul_zero,mul_one,add_zero] using hbal x
  have hrest : ∑ v ∈ (Finset.univ.erase r).erase x, (Q v)^2 =
      ∑ v ∈ (Finset.univ.erase r).erase x, (q v)^2 := by
    apply Finset.sum_congr rfl
    intro v hv
    have hvx := (Finset.mem_erase.mp hv).1
    have hvr := (Finset.mem_erase.mp (Finset.mem_erase.mp hv).2).1
    have hh : Q v=q v := by
      simpa only [if_neg hvr.symm,if_neg hvx.symm,mul_zero,add_zero] using hbal v
    rw [hh]
  rw [NormalTrailSystem.sum_extract_two (fun v ↦ (Q v)^2) r x hrx,
    NormalTrailSystem.sum_extract_two (fun v ↦ (q v)^2) r x hrx,hrest,hQx,←hQr]
  ring

omit [Fintype V] in
lemma path_pair_slide (T : TrailFamily G k) (hp : ∀ i, (T.walk i).IsPath)
    (i j : Fin k) (hij : i ≠ j) {x : V} (h : G.Adj (T.start i) x)
    (P : G.Walk x (T.finish i)) (hP : (Walk.cons h P).IsPath)
    (he : (T.walk i).toSubgraph=(Walk.cons h P).toSubgraph)
    (hstart : T.start j=T.start i) (havoid : x ∉ (T.walk j).support) :
    ∃ U : TrailFamily G k, (∀ l, (U.walk l).IsPath) ∧
      (∀ l, l ≠ i → l ≠ j → (U.walk l).toSubgraph=(T.walk l).toSubgraph) ∧
      ∀ v, U.quota v+2*(if T.start i=v then 1 else 0)=T.quota v+2*(if x=v then 1 else 0) := by
  let h' : G.Adj x (T.start j) := hstart.symm ▸ h.symm
  let Q := Walk.cons h' (T.walk j)
  have hp' : P.IsPath := (Walk.cons_isPath_iff h P).mp hP |>.1
  have hQ : Q.IsPath := (Walk.cons_isPath_iff h' (T.walk j)).mpr ⟨hp j,havoid⟩
  have hnot : s(T.start i,x) ∉ P.edges := (Walk.isTrail_cons h P).mp hP.isTrail |>.2
  have hd : Disjoint P.toSubgraph.edgeSet Q.toSubgraph.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e heP heQ
    have heP' := P.mem_edges_toSubgraph.mp heP
    have heQ' := Q.mem_edges_toSubgraph.mp heQ
    simp only [Q,Walk.edges_cons,List.mem_cons,hstart,Sym2.eq_swap (a := x)] at heQ'
    rcases heQ' with rfl|heQ'
    · exact hnot heP'
    · exact Set.disjoint_left.mp (T.disjoint hij)
        (he.symm ▸ (Walk.cons h P).mem_edges_toSubgraph.mpr (by simp [heP']))
        ((T.walk j).mem_edges_toSubgraph.mpr heQ')
  have hc : P.toSubgraph.edgeSet ∪ Q.toSubgraph.edgeSet=
      (T.walk i).toSubgraph.edgeSet ∪ (T.walk j).toSubgraph.edgeSet := by
    rw [he]
    ext e
    simp only [Set.mem_union,Walk.mem_edges_toSubgraph,Q,Walk.edges_cons,List.mem_cons,
      hstart,Sym2.eq_swap (a := x)]
    tauto
  obtain ⟨U,hUi,hUj,hrest,_,_,_,hUq⟩ := replace_two_starts_general T i j hij x x P Q hp'.isTrail hQ.isTrail hd hc
  refine ⟨U,?_,hrest,?_⟩
  · intro l
    by_cases hli : l=i
    · subst l
      exact ProtectedEdge.trail_isPath_of_subgraph_eq _ _ (U.isTrail i) hp' hUi
    by_cases hlj : l=j
    · subst l
      exact ProtectedEdge.trail_isPath_of_subgraph_eq _ _ (U.isTrail j) hQ hUj
    exact ProtectedEdge.trail_isPath_of_subgraph_eq _ _ (U.isTrail l) (hp l) (hrest l hli hlj)
  · intro v
    have hh := hUq v
    rw [hstart] at hh
    omega

lemma PathEnergyMinimum.slide_quota_bound (T : TrailFamily G k) (hp : ∀ i, (T.walk i).IsPath)
    (hmin : PathEnergyMinimum T) (i j : Fin k) (hij : i ≠ j) {x : V}
    (h : G.Adj (T.start i) x) (P : G.Walk x (T.finish i))
    (hP : (Walk.cons h P).IsPath) (he : (T.walk i).toSubgraph=(Walk.cons h P).toSubgraph)
    (hstart : T.start j=T.start i) (havoid : x ∉ (T.walk j).support) :
    T.quota (T.start i) ≤ T.quota x+2 := by
  obtain ⟨U,hU,_,hUq⟩ := path_pair_slide T hp i j hij h P hP he hstart havoid
  have he := pair_energy_balance_general T.quota U.quota (T.start i) x h.ne hUq
  change quotaEnergy U+4*T.quota (T.start i)=quotaEnergy T+4*T.quota x+8 at he
  have hm := hmin U hU
  omega

lemma PathEnergyMinimum.endpoint_neighbors_blocked (T : TrailFamily G k) (hp : ∀ i, (T.walk i).IsPath)
    (hmin : PathEnergyMinimum T) (i j : Fin k) (hij : i ≠ j) {x : V}
    (h : G.Adj (T.start i) x) (P : G.Walk x (T.finish i))
    (hP : (Walk.cons h P).IsPath) (he : (T.walk i).toSubgraph=(Walk.cons h P).toSubgraph)
    (hstart : T.start j=T.start i) (hlarge : T.quota x+3 ≤ T.quota (T.start i)) :
    x ∈ (T.walk j).support := by
  by_contra hn
  have hh := PathEnergyMinimum.slide_quota_bound T hp hmin i j hij h P hP he hstart hn
  omega

lemma PathEnergyMinimum.of_quota_eq (T U : TrailFamily G k) (hmin : PathEnergyMinimum T)
    (hq : ∀ v, U.quota v=T.quota v) : PathEnergyMinimum U := by
  intro W hW
  have he : quotaEnergy U=quotaEnergy T := by simp only [quotaEnergy,hq]
  rw [he]
  exact hmin W hW

lemma endpoint_edge_slide_bound (T : TrailFamily G k) (hp : ∀ i, (T.walk i).IsPath)
    (hmin : PathEnergyMinimum T) (i j : Fin k) (hij : i ≠ j) {a x : V}
    (hi : a=T.start i ∨ a=T.finish i) (hj : a=T.start j ∨ a=T.finish j)
    (hax : (T.walk i).toSubgraph.Adj a x) (havoid : x ∉ (T.walk j).support) :
    T.quota a ≤ T.quota x+2 := by
  obtain ⟨U,_,hUq,hU⟩ := orient T (fun l ↦ decide (a=T.finish l))
  have hUp (l) : (U.walk l).IsPath := ProtectedEdge.trail_isPath_of_subgraph_eq _ _
    (U.isTrail l) (hp l) (hU l).2.2
  have hUs (l) (hl : a=T.start l ∨ a=T.finish l) : U.start l=a := by
    rw [(hU l).1]
    by_cases h : a=T.finish l
    · simp [h]
    · have hh := hl.resolve_right h
      simpa only [decide_eq_true_eq,if_neg h] using hh.symm
  have hia := hUs i hi
  have hja := hUs j hj
  have hadj : (U.walk i).toSubgraph.Adj (U.start i) x := by rw [(hU i).2.2,hia]; exact hax
  have hnil : ¬(U.walk i).Nil := Walk.not_nil_of_adj_toSubgraph hadj
  have hxs : x=(U.walk i).snd := by
    have hh : x ∈ (U.walk i).toSubgraph.neighborSet (U.start i) := hadj
    rwa [(hUp i).neighborSet_toSubgraph_startpoint hnil] at hh
  have hnav : x ∉ (U.walk j).support := by
    rw [←Walk.mem_verts_toSubgraph,(hU j).2.2,Walk.mem_verts_toSubgraph]
    exact havoid
  subst x
  have hminU := PathEnergyMinimum.of_quota_eq T U hmin hUq
  have hb := PathEnergyMinimum.slide_quota_bound U hUp hminU i j hij
    ((U.walk i).adj_snd hnil) (U.walk i).tail
    (by rw [(U.walk i).cons_tail_eq hnil]; exact hUp i) (by rw [(U.walk i).cons_tail_eq hnil])
    (hja.trans hia.symm) hnav
  simpa only [hUq,hia] using hb

lemma low_quota_neighbor_contains_endpoints (T : TrailFamily G k) (hp : ∀ i, (T.walk i).IsPath)
    (hmin : PathEnergyMinimum T) (i : Fin k) {a x : V}
    (hi : a=T.start i ∨ a=T.finish i) (hax : (T.walk i).toSubgraph.Adj a x)
    (hlarge : T.quota x+3 ≤ T.quota a) :
    ∀ j, a=T.start j ∨ a=T.finish j → x ∈ (T.walk j).support := by
  intro j hj
  by_cases hji : j=i
  · subst j
    exact Walk.mem_support_of_adj_toSubgraph hax.symm
  by_contra hn
  have hb := endpoint_edge_slide_bound T hp hmin i j (fun he ↦ hji he.symm) hi hj hax hn
  omega

lemma quota_bound_of_endpoint_containment (T : TrailFamily G k) (hp : ∀ i, (T.walk i).IsPath)
    (hn : ∀ i, ¬(T.walk i).Nil) (a x : V)
    (hcontain : ∀ j, a=T.start j ∨ a=T.finish j → x ∈ (T.walk j).support) :
    2*T.quota a ≤ Nat.card (G.neighborSet x)+T.quota x := by
  have hlocal (j : Fin k) :
      2*((if T.start j=a then 1 else 0)+(if T.finish j=a then 1 else 0)) ≤
        ((T.walk j).toSubgraph.neighborSet x).ncard+
          (if T.start j=x then 1 else 0)+(if T.finish j=x then 1 else 0) := by
    have hne := ContiguousRegion.path_ends_ne (T.walk j) (hp j) (hn j)
    have hinc := RootCapacity.path_incidence (T.walk j) (hp j) x
    by_cases hsa : T.start j=a
    · have hfa : T.finish j ≠ a := fun h ↦ hne (hsa.trans h.symm)
      have hx := hcontain j (Or.inl hsa.symm)
      simp only [if_pos hsa,if_neg hfa,if_pos hx] at hinc ⊢
      omega
    by_cases hfa : T.finish j=a
    · have hx := hcontain j (Or.inr hfa.symm)
      simp only [if_neg hsa,if_pos hfa,if_pos hx] at hinc ⊢
      omega
    simp only [if_neg hsa,if_neg hfa,add_zero,mul_zero,Nat.zero_le]
  have hh := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin k))) ↦ hlocal j)
  rw [←Finset.mul_sum,←quota_eq_sum_endpoints,Finset.sum_add_distrib,Finset.sum_add_distrib,
    ←QuotaParity.degree_sum] at hh
  have hq := quota_eq_sum_endpoints T x
  rw [Finset.sum_add_distrib] at hq
  omega

lemma endpoint_neighbor_degree_bound (T : TrailFamily G k) (hp : ∀ i, (T.walk i).IsPath)
    (hn : ∀ i, ¬(T.walk i).Nil) (hmin : PathEnergyMinimum T)
    (i : Fin k) {a x : V} (hi : a=T.start i ∨ a=T.finish i)
    (hax : (T.walk i).toSubgraph.Adj a x) (hlarge : T.quota x+3 ≤ T.quota a) :
    2*T.quota a ≤ Nat.card (G.neighborSet x)+T.quota x ∧ T.quota x+6 ≤ Nat.card (G.neighborSet x) := by
  have hb := quota_bound_of_endpoint_containment T hp hn a x
    (low_quota_neighbor_contains_endpoints T hp hmin i hi hax hlarge)
  exact ⟨hb,by omega⟩

lemma normal_remainder_energy_optimum (F : MinimalFailure) (D : OptimizedDefect F.graph) :
    ∃ U : TrailFamily (remainder F D) (normalBudget F D),
      (∀ i, (U.walk i).IsPath) ∧ PathEnergyMinimum U := by
  obtain ⟨E,hE,hEc,_⟩ := normal_partition_exact F D
  obtain ⟨T,hT⟩ := padded_path_family D.root E hE hEc.le
  exact exists_path_energy_minimum T hT

lemma zero_neighbor_small_degree_endpoint_quota (T : TrailFamily G k) (hp : ∀ i, (T.walk i).IsPath)
    (hn : ∀ i, ¬(T.walk i).Nil) (hmin : PathEnergyMinimum T)
    (i : Fin k) {a x : V} (hi : a=T.start i ∨ a=T.finish i)
    (hax : (T.walk i).toSubgraph.Adj a x) (hzero : T.quota x=0)
    (hd : Nat.card (G.neighborSet x) ≤ 5) : T.quota a ≤ 2 := by
  by_contra hh
  have hb := (endpoint_neighbor_degree_bound T hp hn hmin i hi hax (by omega)).2
  omega

lemma odd_short_tail_energy_witness (F : MinimalFailure) (D : OptimizedDefect F.graph)
    (ho : Odd F.order) (hl : D.rep.tail.length ≤ 1) :
    ∃ U : TrailFamily (remainder F D) (normalBudget F D),
      (∀ i, (U.walk i).IsPath) ∧ PathEnergyMinimum U ∧
      (∀ i, ¬(U.walk i).Nil) ∧ U.quota D.root=0 ∧
      2 ≤ Fintype.card (StarPathPieces.AvoidIndex U D.root) := by
  obtain ⟨U,hU,hmin⟩ := normal_remainder_energy_optimum F D
  exact ⟨U,hU,hmin,optimal_normal_family_nonnil F D U hU,
    short_tail_normal_family_quota_zero F D hl U hU,
    odd_short_tail_two_root_avoiders F D ho hl U hU⟩

end Erdos583FixedRemainderEnergyDevelopment
