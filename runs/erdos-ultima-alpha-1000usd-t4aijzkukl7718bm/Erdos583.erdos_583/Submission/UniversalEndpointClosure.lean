import Submission.FixedRemainderEnergy

/-! Endpoint containment at a vertex that has quota zero in every fixed-slot
path family. No energy minimization or endpoint-flexibility premise is used. -/
namespace Erdos583UniversalEndpointClosureDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open Erdos583FixedRemainderEnergyDevelopment
open Erdos583UnifiedMinimalDefectDevelopment Erdos583NormalRemainderCriticalDevelopment
open Erdos583UniversalNormalEndpointsDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}

omit [Fintype V] in
lemma endpoint_pair_slide (T : TrailFamily G k) (hp : ∀ i, (T.walk i).IsPath)
    (i j : Fin k) (hij : i ≠ j) {a x : V}
    (hi : a=T.start i ∨ a=T.finish i) (hj : a=T.start j ∨ a=T.finish j)
    (hax : (T.walk i).toSubgraph.Adj a x) (havoid : x ∉ (T.walk j).support) :
    ∃ U : TrailFamily G k, (∀ l, (U.walk l).IsPath) ∧
      (∀ l, l ≠ i → l ≠ j → (U.walk l).toSubgraph=(T.walk l).toSubgraph) ∧
      ∀ v, U.quota v+2*(if a=v then 1 else 0)=T.quota v+2*(if x=v then 1 else 0) := by
  obtain ⟨S,_,hSq,hS⟩ := orient T (fun l ↦ decide (a=T.finish l))
  have hSp (l) : (S.walk l).IsPath := ProtectedEdge.trail_isPath_of_subgraph_eq _ _
    (S.isTrail l) (hp l) (hS l).2.2
  have hSs (l) (hl : a=T.start l ∨ a=T.finish l) : S.start l=a := by
    rw [(hS l).1]
    by_cases h : a=T.finish l
    · simp [h]
    · have hh := hl.resolve_right h
      simpa only [decide_eq_true_eq,if_neg h] using hh.symm
  have hia := hSs i hi
  have hja := hSs j hj
  have hadj : (S.walk i).toSubgraph.Adj (S.start i) x := by rw [(hS i).2.2,hia]; exact hax
  have hnil : ¬(S.walk i).Nil := Walk.not_nil_of_adj_toSubgraph hadj
  have hxs : x=(S.walk i).snd := by
    have hh : x ∈ (S.walk i).toSubgraph.neighborSet (S.start i) := hadj
    rwa [(hSp i).neighborSet_toSubgraph_startpoint hnil] at hh
  have hnav : x ∉ (S.walk j).support := by
    rw [←Walk.mem_verts_toSubgraph,(hS j).2.2,Walk.mem_verts_toSubgraph]
    exact havoid
  subst x
  obtain ⟨U,hU,hrest,hUq⟩ := path_pair_slide S hSp i j hij
    ((S.walk i).adj_snd hnil) (S.walk i).tail
    (by rw [(S.walk i).cons_tail_eq hnil]; exact hSp i) (by rw [(S.walk i).cons_tail_eq hnil])
    (hja.trans hia.symm) hnav
  refine ⟨U,hU,?_,?_⟩
  · intro l hli hlj
    exact (hrest l hli hlj).trans (hS l).2.2
  · simpa only [hSq,hia] using hUq

omit [Fintype V] in
lemma universally_zero_terminal_contains (T : TrailFamily G k)
    (hp : ∀ i, (T.walk i).IsPath) {x : V}
    (hzero : ∀ U : TrailFamily G k, (∀ i, (U.walk i).IsPath) → U.quota x=0)
    (i : Fin k) {a : V} (hi : a=T.start i ∨ a=T.finish i)
    (hax : (T.walk i).toSubgraph.Adj a x) :
    ∀ j, a=T.start j ∨ a=T.finish j → x ∈ (T.walk j).support := by
  intro j hj
  by_cases hji : j=i
  · subst j
    exact Walk.mem_support_of_adj_toSubgraph hax.symm
  by_contra havoid
  obtain ⟨U,hU,_,hUq⟩ := endpoint_pair_slide T hp i j
    (fun he ↦ hji he.symm) hi hj hax havoid
  have hh := hUq x
  have hne : a ≠ x := hax.adj_sub.ne
  simp [hne,hzero U hU,hzero T hp] at hh

lemma universally_zero_neighbor_quota_bound (T : TrailFamily G k)
    (hp : ∀ i, (T.walk i).IsPath) (hn : ∀ i, ¬(T.walk i).Nil) {x : V}
    (hzero : ∀ U : TrailFamily G k, (∀ i, (U.walk i).IsPath) → U.quota x=0)
    (i : Fin k) {a : V} (hi : a=T.start i ∨ a=T.finish i)
    (hax : (T.walk i).toSubgraph.Adj a x) :
    2*T.quota a ≤ Nat.card (G.neighborSet x) := by
  have hh := quota_bound_of_endpoint_containment T hp hn a x
    (universally_zero_terminal_contains T hp hzero i hi hax)
  simpa only [hzero T hp,add_zero] using hh

lemma short_tail_terminal_root_contains (F : MinimalFailure) (D : OptimizedDefect F.graph)
    (hl : D.rep.tail.length ≤ 1)
    (T : TrailFamily (remainder F D) (normalBudget F D)) (hp : ∀ i, (T.walk i).IsPath)
    (i : Fin (normalBudget F D)) {a : Fin F.order}
    (hi : a=T.start i ∨ a=T.finish i) (har : (T.walk i).toSubgraph.Adj a D.root) :
    ∀ j, a=T.start j ∨ a=T.finish j → D.root ∈ (T.walk j).support :=
  universally_zero_terminal_contains T hp
    (short_tail_normal_family_quota_zero F D hl) i hi har

lemma short_tail_terminal_neighbor_quota_bound (F : MinimalFailure) (D : OptimizedDefect F.graph)
    (hl : D.rep.tail.length ≤ 1)
    (T : TrailFamily (remainder F D) (normalBudget F D)) (hp : ∀ i, (T.walk i).IsPath)
    (i : Fin (normalBudget F D)) {a : Fin F.order}
    (hi : a=T.start i ∨ a=T.finish i) (har : (T.walk i).toSubgraph.Adj a D.root) :
    2*T.quota a+3 ≤ Nat.card (F.graph.neighborSet D.root) := by
  have hh := universally_zero_neighbor_quota_bound T hp (optimal_normal_family_nonnil F D T hp)
    (short_tail_normal_family_quota_zero F D hl) i hi har
  have hr := normal_root_degree F D
  omega

end Erdos583UniversalEndpointClosureDevelopment
