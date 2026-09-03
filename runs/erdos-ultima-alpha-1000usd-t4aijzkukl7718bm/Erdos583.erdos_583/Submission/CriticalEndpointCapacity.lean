import Submission.NormalRemainderCritical

/-! Endpoint capacity at a star of path-budget-critical missing edges.
The conclusions hold for every path partition at the indicated budget. -/
namespace Erdos583CriticalEndpointCapacityDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open Erdos583UnifiedMinimalDefectDevelopment Erdos583NormalRemainderCriticalDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

variable {V : Type*} [Fintype V] {H : SimpleGraph V} {p : ℕ}

/-- Adding this edge exceeds the given path budget. -/
def EdgeCritical (H : SimpleGraph V) (p : ℕ) (r x : V) : Prop :=
  ¬∃ E : Finset (H ⊔ edge r x).Subgraph,
    GoodDecomposition (H ⊔ edge r x) E ∧ E.card ≤ p

omit [Fintype V] in
lemma EdgeCritical.symm {r x : V} (hc : EdgeCritical H p r x) : EdgeCritical H p x r := by
  unfold EdgeCritical at *
  rwa [edge_comm x r]

omit [Fintype V] in
lemma critical_edge_missing (T : TrailFamily H p) (hp : ∀ j, (T.walk j).IsPath)
    {r x : V} (hc : EdgeCritical H p r x) : ¬H.Adj r x := by
  intro h
  have he : H ⊔ edge r x=H := sup_eq_left.mpr ((edge_le_iff _).mpr (Or.inr h))
  unfold EdgeCritical at hc
  rw [he] at hc
  exact hc (MatchingAppend.path_family_partition T hp)


lemma critical_endpoint_contains (T : TrailFamily H p) (hp : ∀ j, (T.walk j).IsPath)
    {r x : V} (hrx : r ≠ x) (hmiss : ¬H.Adj r x) (hc : EdgeCritical H p r x)
    (j : Fin p) (hx : x=T.start j ∨ x=T.finish j) : r ∈ (T.walk j).support := by
  by_contra hr
  have ha : (H ⊔ edge r x).Adj r x := Or.inr ((edge_adj r x r x).mpr ⟨Or.inl ⟨rfl,rfl⟩,hrx⟩)
  have hcover : (H ⊔ edge r x).edgeSet=insert s(r,x) H.edgeSet := by
    rw [edgeSet_sup,edge_edgeSet_of_ne hrx]
    ext e
    simp only [Set.mem_union,Set.mem_singleton_iff,Set.mem_insert_iff]
    tauto
  obtain ⟨U,_,_,hU,_⟩ := DeletionEndpoint.append_new_edge_tracked le_sup_left T hp j hx ha hmiss hcover
  exact hc (MatchingAppend.path_family_partition U (hU hr))

lemma critical_neighbor_quota_bound (T : TrailFamily H p) (hp : ∀ j, (T.walk j).IsPath)
    (r : V) (X : Finset V) (hr : r ∉ X)
    (hmiss : ∀ x ∈ X, ¬H.Adj r x) (hc : ∀ x ∈ X, EdgeCritical H p r x) :
    (∑ x ∈ X, T.quota x) ≤ Nat.card (H.neighborSet r) := by
  have hlocal (j : Fin p) :
      (if T.start j ∈ X then 1 else 0)+(if T.finish j ∈ X then 1 else 0) ≤
        ((T.walk j).toSubgraph.neighborSet r).ncard := by
    have ha : T.start j ∈ X → r ∈ (T.walk j).support := by
      intro hj
      exact critical_endpoint_contains T hp (r := r) (x := T.start j) (fun h ↦ hr (h.symm ▸ hj)) (hmiss _ hj) (hc _ hj) j (Or.inl rfl)
    have hb : T.finish j ∈ X → r ∈ (T.walk j).support := by
      intro hj
      exact critical_endpoint_contains T hp (r := r) (x := T.finish j) (fun h ↦ hr (h.symm ▸ hj)) (hmiss _ hj) (hc _ hj) j (Or.inr rfl)
    have hinc := RootCapacity.path_incidence (T.walk j) (hp j) r
    have has : (if T.start j ∈ X then 1 else 0)+(if T.start j=r then 1 else 0) ≤ (1 : ℕ) := by
      by_cases h : T.start j=r
      · simp [h,hr]
      · simp only [if_neg h,add_zero]
        split_ifs <;> omega
    have hbs : (if T.finish j ∈ X then 1 else 0)+(if T.finish j=r then 1 else 0) ≤ (1 : ℕ) := by
      by_cases h : T.finish j=r
      · simp [h,hr]
      · simp only [if_neg h,add_zero]
        split_ifs <;> omega
    by_cases hmem : r ∈ (T.walk j).support
    · rw [if_pos hmem] at hinc
      omega
    · simp only [if_neg hmem] at hinc
      have han : T.start j ∉ X := fun h ↦ hmem (ha h)
      have hbn : T.finish j ∉ X := fun h ↦ hmem (hb h)
      simp only [if_neg han,if_neg hbn,add_zero,Nat.zero_le]
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin p))) ↦ hlocal j)
  rw [←QuotaParity.degree_sum T r] at hsum
  have heq : (∑ x ∈ X, T.quota x)=
      ∑ j : Fin p, ((if T.start j ∈ X then 1 else 0)+(if T.finish j ∈ X then 1 else 0)) := by
    simp only [quota_eq_sum_endpoints]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_add_distrib]
    simp
  rwa [heq]

lemma critical_odd_neighbors_bound (T : TrailFamily H p) (hp : ∀ j, (T.walk j).IsPath)
    (r : V) (X : Finset V) (hr : r ∉ X)
    (hmiss : ∀ x ∈ X, ¬H.Adj r x) (hc : ∀ x ∈ X, EdgeCritical H p r x)
    (ho : ∀ x ∈ X, Odd (Nat.card (H.neighborSet x))) : X.card ≤ Nat.card (H.neighborSet r) := by
  have hq (x : V) (hx : x ∈ X) : 1 ≤ T.quota x :=
    ((QuotaParity.quota_odd_iff T x).mpr (ho x hx)).pos
  calc
    X.card = ∑ _x ∈ X, (1 : ℕ) := by simp
    _ ≤ ∑ x ∈ X, T.quota x := Finset.sum_le_sum hq
    _ ≤ _ := critical_neighbor_quota_bound T hp r X hr hmiss hc

lemma remainder_root_cycle_endpoint_contains (F : MinimalFailure) (D : OptimizedDefect F.graph)
    (T : TrailFamily (remainder F D) (normalBudget F D)) (hp : ∀ j, (T.walk j).IsPath)
    {x : Fin F.order} (hx : D.rep.cycle.toSubgraph.Adj D.root x)
    (j : Fin (normalBudget F D)) (hj : x=T.start j ∨ x=T.finish j) :
    D.root ∈ (T.walk j).support :=
  critical_endpoint_contains T hp hx.ne (root_cycle_edge_missing F D hx)
    (root_cycle_edge_critical F D hx) j hj

lemma remainder_last_tail_endpoint_contains (F : MinimalFailure) (D : OptimizedDefect F.graph)
    (T : TrailFamily (remainder F D) (normalBudget F D)) (hp : ∀ j, (T.walk j).IsPath)
    (j : Fin (normalBudget F D)) (hj : D.rep.tail.penultimate=T.start j ∨ D.rep.tail.penultimate=T.finish j) :
    D.rep.finish ∈ (T.walk j).support :=
  critical_endpoint_contains T hp (D.rep.tail.adj_penultimate (tail_not_nil F D)).ne.symm
    (last_tail_edge_missing F D) (last_tail_edge_critical F D) j hj

end Erdos583CriticalEndpointCapacityDevelopment
