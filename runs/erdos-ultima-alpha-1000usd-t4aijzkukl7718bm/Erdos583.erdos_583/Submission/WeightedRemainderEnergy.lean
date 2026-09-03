import Submission.FixedRemainderEnergy

/-! Secondary endpoint potentials on a fixed path remainder. These optima
are not imposed on the global optimized defect. -/
namespace Erdos583WeightedRemainderEnergyDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.RootEnergy
open Erdos583FixedRemainderEnergyDevelopment
open Erdos583UnifiedMinimalDefectDevelopment Erdos583NormalRemainderCriticalDevelopment
open Erdos583UniversalNormalEndpointsDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}

noncomputable def endpointWeight (w : V → ℕ) (T : TrailFamily G k) : ℕ :=
  ∑ v, w v*T.quota v

def WeightedPathMinimum (w : V → ℕ) (T : TrailFamily G k) : Prop :=
  PathEnergyMinimum T ∧ ∀ U : TrailFamily G k, (∀ i, (U.walk i).IsPath) →
    quotaEnergy U=quotaEnergy T → endpointWeight w T ≤ endpointWeight w U

lemma exists_weighted_path_minimum (w : V → ℕ) (T : TrailFamily G k)
    (hp : ∀ i, (T.walk i).IsPath) :
    ∃ U : TrailFamily G k, (∀ i, (U.walk i).IsPath) ∧ WeightedPathMinimum w U := by
  obtain ⟨S,hS,hmin⟩ := exists_path_energy_minimum T hp
  let P (m : ℕ) := ∃ U : TrailFamily G k, (∀ i, (U.walk i).IsPath) ∧
    quotaEnergy U=quotaEnergy S ∧ endpointWeight w U=m
  have hex : ∃ m, P m := ⟨endpointWeight w S,S,hS,rfl,rfl⟩
  obtain ⟨U,hU,hUe,hUw⟩ := Nat.find_spec hex
  refine ⟨U,hU,?_,?_⟩
  · intro W hW
    rw [hUe]
    exact hmin W hW
  · intro W hW he
    rw [hUw]
    exact Nat.find_min' hex ⟨W,hW,he.trans hUe,rfl⟩

lemma pair_weight_balance (w q Q : V → ℕ) (a x : V) (hax : a ≠ x)
    (hbal : ∀ v, Q v+2*(if a=v then 1 else 0)=q v+2*(if x=v then 1 else 0)) :
    (∑ v, w v*Q v)+2*w a=(∑ v, w v*q v)+2*w x := by
  have hQa : Q a+2=q a := by
    simpa only [if_pos rfl,if_neg hax.symm,mul_one,mul_zero,add_zero] using hbal a
  have hQx : Q x=q x+2 := by
    simpa only [if_neg hax,if_pos rfl,mul_zero,mul_one,add_zero] using hbal x
  have hrest : ∑ v ∈ (Finset.univ.erase a).erase x, w v*Q v =
      ∑ v ∈ (Finset.univ.erase a).erase x, w v*q v := by
    apply Finset.sum_congr rfl
    intro v hv
    have hvx := (Finset.mem_erase.mp hv).1
    have hva := (Finset.mem_erase.mp (Finset.mem_erase.mp hv).2).1
    have hh : Q v=q v := by
      simpa only [if_neg hva.symm,if_neg hvx.symm,mul_zero,add_zero] using hbal v
    rw [hh]
  rw [NormalTrailSystem.sum_extract_two (fun v ↦ w v*Q v) a x hax,
    NormalTrailSystem.sum_extract_two (fun v ↦ w v*q v) a x hax,hrest,hQx,←hQa]
  ring

lemma WeightedPathMinimum.of_quota_eq (w : V → ℕ) (T U : TrailFamily G k)
    (hmin : WeightedPathMinimum w T) (hq : ∀ v, U.quota v=T.quota v) :
    WeightedPathMinimum w U := by
  have he : quotaEnergy U=quotaEnergy T := by simp only [quotaEnergy,hq]
  have hw : endpointWeight w U=endpointWeight w T := by simp only [endpointWeight,hq]
  refine ⟨PathEnergyMinimum.of_quota_eq T U hmin.1 hq,?_⟩
  intro W hW hWe
  rw [hw]
  exact hmin.2 W hW (hWe.trans he)

lemma weighted_slide_bound (w : V → ℕ) (T : TrailFamily G k)
    (hp : ∀ i, (T.walk i).IsPath) (hmin : WeightedPathMinimum w T)
    (i j : Fin k) (hij : i ≠ j) {x : V} (h : G.Adj (T.start i) x)
    (P : G.Walk x (T.finish i)) (hP : (Walk.cons h P).IsPath)
    (he : (T.walk i).toSubgraph=(Walk.cons h P).toSubgraph)
    (hstart : T.start j=T.start i) (havoid : x ∉ (T.walk j).support) :
    T.quota (T.start i) ≤ T.quota x+2 ∧
      (T.quota (T.start i)=T.quota x+2 → w (T.start i) ≤ w x) := by
  obtain ⟨U,hU,_,hUq⟩ := path_pair_slide T hp i j hij h P hP he hstart havoid
  have he := pair_energy_balance_general T.quota U.quota (T.start i) x h.ne hUq
  change quotaEnergy U+4*T.quota (T.start i)=quotaEnergy T+4*T.quota x+8 at he
  have hm := hmin.1 U hU
  refine ⟨by omega,?_⟩
  intro hq
  have hE : quotaEnergy U=quotaEnergy T := by omega
  have hmW := hmin.2 U hU hE
  have hw := pair_weight_balance w T.quota U.quota (T.start i) x h.ne hUq
  change endpointWeight w U+2*w (T.start i)=endpointWeight w T+2*w x at hw
  omega

lemma weighted_endpoint_edge_bound (w : V → ℕ) (T : TrailFamily G k)
    (hp : ∀ i, (T.walk i).IsPath) (hmin : WeightedPathMinimum w T)
    (i j : Fin k) (hij : i ≠ j) {a x : V}
    (hi : a=T.start i ∨ a=T.finish i) (hj : a=T.start j ∨ a=T.finish j)
    (hax : (T.walk i).toSubgraph.Adj a x) (havoid : x ∉ (T.walk j).support) :
    T.quota a ≤ T.quota x+2 ∧ (T.quota a=T.quota x+2 → w a ≤ w x) := by
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
  have hminU := WeightedPathMinimum.of_quota_eq w T U hmin hUq
  have hb := weighted_slide_bound w U hUp hminU i j hij
    ((U.walk i).adj_snd hnil) (U.walk i).tail
    (by rw [(U.walk i).cons_tail_eq hnil]; exact hUp i) (by rw [(U.walk i).cons_tail_eq hnil])
    (hja.trans hia.symm) hnav
  simpa only [hUq,hia] using hb

lemma descending_neighbor_contains_endpoints (w : V → ℕ) (T : TrailFamily G k)
    (hp : ∀ i, (T.walk i).IsPath) (hmin : WeightedPathMinimum w T)
    (i : Fin k) {a x : V} (hi : a=T.start i ∨ a=T.finish i)
    (hax : (T.walk i).toSubgraph.Adj a x) (hq : T.quota x+2 ≤ T.quota a)
    (hw : w x < w a) :
    ∀ j, a=T.start j ∨ a=T.finish j → x ∈ (T.walk j).support := by
  intro j hj
  by_cases hji : j=i
  · subst j
    exact Walk.mem_support_of_adj_toSubgraph hax.symm
  by_contra hn
  obtain ⟨hb,he⟩ := weighted_endpoint_edge_bound w T hp hmin i j
    (fun h ↦ hji h.symm) hi hj hax hn
  have hh := he (by omega)
  omega

lemma descending_endpoint_degree_bound (w : V → ℕ) (T : TrailFamily G k)
    (hp : ∀ i, (T.walk i).IsPath) (hn : ∀ i, ¬(T.walk i).Nil)
    (hmin : WeightedPathMinimum w T) (i : Fin k) {a x : V}
    (hi : a=T.start i ∨ a=T.finish i) (hax : (T.walk i).toSubgraph.Adj a x)
    (hq : T.quota x+2 ≤ T.quota a) (hw : w x < w a) :
    2*T.quota a ≤ Nat.card (G.neighborSet x)+T.quota x ∧
      T.quota x+4 ≤ Nat.card (G.neighborSet x) := by
  have hb := quota_bound_of_endpoint_containment T hp hn a x
    (descending_neighbor_contains_endpoints w T hp hmin i hi hax hq hw)
  exact ⟨hb,by omega⟩

lemma normal_remainder_weighted_optimum (F : MinimalFailure) (D : OptimizedDefect F.graph)
    (w : Fin F.order → ℕ) :
    ∃ U : TrailFamily (remainder F D) (normalBudget F D),
      (∀ i, (U.walk i).IsPath) ∧ WeightedPathMinimum w U := by
  obtain ⟨T,hT,_⟩ := normal_remainder_energy_optimum F D
  exact exists_weighted_path_minimum w T hT

lemma odd_short_tail_distance_witness (F : MinimalFailure) (D : OptimizedDefect F.graph)
    (ho : Odd F.order) (hl : D.rep.tail.length ≤ 1) :
    ∃ U : TrailFamily (remainder F D) (normalBudget F D),
      (∀ i, (U.walk i).IsPath) ∧
      WeightedPathMinimum (fun v ↦ (remainder F D).dist D.root v) U ∧
      (∀ i, ¬(U.walk i).Nil) ∧ U.quota D.root=0 ∧
      2 ≤ Fintype.card (StarPathPieces.AvoidIndex U D.root) := by
  obtain ⟨U,hU,hmin⟩ := normal_remainder_weighted_optimum F D
    (fun v ↦ (remainder F D).dist D.root v)
  exact ⟨U,hU,hmin,optimal_normal_family_nonnil F D U hU,
    short_tail_normal_family_quota_zero F D hl U hU,
    odd_short_tail_two_root_avoiders F D ho hl U hU⟩

end Erdos583WeightedRemainderEnergyDevelopment
