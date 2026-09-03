import Submission.DoubleStarCone

/-!
Arbitrarily long prescribed sequences of cycle deletions can preserve full
support and count-criticality. This does not exclude a favorable choice of
cycles and does not settle Erdős 184.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.CriticalDeletionPlateau
open CountCritical DoubleStarCone
set_option maxHeartbeats 1000000

abbrev Old (r : ℕ) := Fin r × Base 2
abbrev Vert (r : ℕ) := Option (Old r)

def forest (r : ℕ) : SimpleGraph (Old r) where
  Adj x y := x.1 = y.1 ∧ (base 2).Adj x.2 y.2
  symm := by intro x y h; exact ⟨h.1.symm,h.2.symm⟩
  loopless := by intro x h; exact (base 2).loopless x.2 h.2

lemma forest_degree (r : ℕ) (i : Fin r) (x : Base 2) :
    (forest r).degree (i,x) = (base 2).degree x := by
  have hn : (forest r).neighborFinset (i,x) =
      ((base 2).neighborFinset x).image (fun y => (i,y)) := by
    ext y
    rcases y with ⟨j,y⟩
    simp [mem_neighborFinset,forest,eq_comm]
    tauto
  rw [← card_neighborFinset_eq_degree,hn,Finset.card_image_of_injective _]
  · exact card_neighborFinset_eq_degree _ _
  · intro y z h
    exact congrArg Prod.snd h

lemma forest_acyclic (r : ℕ) : (forest r).IsAcyclic := by
  intro v p hp
  have hc := cycle_subgraph_regular (forest r) hp
  have hleaf : ∀ i b j, (i,b,some j) ∉ p.toSubgraph.verts := by
    intro i b j hv
    have hd := hc.2 ⟨(i,b,some j),hv⟩
    rw [Subgraph.coe_degree] at hd
    have hl := p.toSubgraph.degree_le (i,b,some j)
    have hg : (forest r).degree (i,b,some j) = 1 := by rw [forest_degree,leaf_degree]
    simp only [Subgraph.degree,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      at hd hl hg
    omega
  obtain ⟨i,b,x⟩ := v
  have hv := p.mem_verts_toSubgraph.mpr p.start_mem_support
  cases x with
  | some j => exact hleaf i b j hv
  | none =>
    have hsub : p.toSubgraph.neighborSet (i,b,none) ⊆ {(i,!b,none)} := by
      rintro ⟨j,c,y⟩ hy
      have hadj := p.toSubgraph.adj_sub hy
      have hji : j = i := hadj.1.symm
      subst j
      cases y with
      | some k => exact (hleaf i c k (p.toSubgraph.edge_vert hy.symm)).elim
      | none =>
        have hbc : b ≠ c := hadj.2
        cases b <;> cases c <;> simp_all
    have hh := Set.ncard_le_ncard hsub
    have hd := hp.ncard_neighborSet_toSubgraph_eq_two p.start_mem_support
    simp only [Set.ncard_singleton] at hh
    omega

def active {r : ℕ} (S : Finset (Fin r)) : Set (Old r) :=
  {x | x.2.2 ≠ none ∨ x.1 ∉ S}

def core {r : ℕ} (S : Finset (Fin r)) : SimpleGraph (Old r) where
  Adj x y := (forest r).Adj x y ∧ (x.2.2 ≠ none ∨ y.2.2 ≠ none ∨ x.1 ∉ S)
  symm := by
    intro x y h
    refine ⟨h.1.symm,?_⟩
    rw [← h.1.1]
    tauto
  loopless := by intro x h; exact (forest r).loopless x h.1

def graph {r : ℕ} (S : Finset (Fin r)) : SimpleGraph (Vert r) :=
  FanPaths.cone (core S) (active S)

lemma leaf_degree {r : ℕ} (S : Finset (Fin r)) (i : Fin r) (b : Bool) (j : Fin 2) :
    (graph S).degree (some (i,b,some j)) = 2 := by
  have hn : (graph S).neighborFinset (some (i,b,some j)) = {none,some (i,b,none)} := by
    ext x
    cases x with
    | none => simp [mem_neighborFinset,graph,FanPaths.cone,active]
    | some x =>
      obtain ⟨k,c,y⟩ := x
      cases y <;> simp [mem_neighborFinset,graph,FanPaths.cone,core,forest,base,eq_comm]
  rw [← card_neighborFinset_eq_degree,hn]
  simp

lemma center_degree {r : ℕ} (S : Finset (Fin r)) (i : Fin r) (b : Bool) :
    (graph S).degree (some (i,b,none)) = if i ∈ S then 2 else 4 := by
  let L : Finset (Vert r) := Finset.univ.image (fun j : Fin 2 => some (i,b,some j))
  have hL : L.card = 2 := by
    rw [Finset.card_image_of_injective _ (by
      intro j k h
      exact Option.some.inj (congrArg (fun x : Old r => x.2.2) (Option.some.inj h)))]
    simp
  by_cases hi : i ∈ S
  · have hn : (graph S).neighborFinset (some (i,b,none)) = L := by
      ext x
      cases x with
      | none => simp [mem_neighborFinset,graph,FanPaths.cone,active,hi,L]
      | some x =>
        obtain ⟨k,c,y⟩ := x
        cases y <;> simp [mem_neighborFinset,graph,FanPaths.cone,core,forest,base,L,hi,eq_comm]
    rw [if_pos hi,← card_neighborFinset_eq_degree,hn,hL]
  · have hn : (graph S).neighborFinset (some (i,b,none)) = insert none (insert (some (i,!b,none)) L) := by
      ext x
      cases x with
      | none => simp [mem_neighborFinset,graph,FanPaths.cone,active,hi,L]
      | some x =>
        obtain ⟨k,c,y⟩ := x
        cases b <;> cases c <;> cases y <;>
          simp [mem_neighborFinset,graph,FanPaths.cone,core,forest,base,L,hi,eq_comm]
    rw [if_neg hi,← card_neighborFinset_eq_degree,hn,
      Finset.card_insert_of_notMem (by simp [L]),
      Finset.card_insert_of_notMem (by simp [L]),hL]

lemma active_card {r : ℕ} (S : Finset (Fin r)) :
    (active S).ncard + 2*S.card = 6*r := by
  have hbad : Finset.univ.filter (fun x : Old r => x ∉ active S) =
      (S.product (Finset.univ : Finset Bool)).image (fun x => (x.1,x.2,none)) := by
    ext x
    obtain ⟨i,b,x⟩ := x
    cases x <;> simp [active]
  have hi : Function.Injective (fun x : Fin r × Bool => (x.1,x.2,(none : Option (Fin 2)))) := by
    intro x y h
    exact Prod.ext (congrArg (fun z : Old r => z.1) h) (congrArg (fun z : Old r => z.2.1) h)
  have hbc : (Finset.univ.filter (fun x : Old r => x ∉ active S)).card = 2*S.card := by
    rw [hbad,Finset.card_image_of_injective _ hi,Finset.product_eq_sprod,Finset.card_product]
    simp [Nat.mul_comm]
  have hh := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Old r)))
    (fun x => x ∈ active S)
  have hgood : Finset.univ.filter (fun x : Old r => x ∈ active S) = (active S).toFinset := by
    ext x; simp
  rw [hgood,hbc,← Set.ncard_eq_toFinset_card'] at hh
  simpa [Old,Base,Nat.mul_assoc,Nat.mul_comm] using hh

lemma apex_degree {r : ℕ} (S : Finset (Fin r)) :
    (graph S).degree none = 2*(3*r-S.card) := by
  have hn : (graph S).neighborFinset none = (active S).toFinset.image Option.some := by
    ext x
    cases x <;> simp [mem_neighborFinset,graph,FanPaths.cone]
  rw [← card_neighborFinset_eq_degree,hn,
    Finset.card_image_of_injective _ (Option.some_injective _),← Set.ncard_eq_toFinset_card']
  have hc := active_card S
  have hle := S.card_le_univ
  simp only [Fintype.card_fin] at hle
  omega

lemma graph_even {r : ℕ} (S : Finset (Fin r)) : ∀ v, Even ((graph S).degree v) := by
  intro v
  cases v with
  | none => rw [apex_degree]; exact even_two_mul _
  | some v =>
    obtain ⟨i,b,x⟩ := v
    cases x with
    | none => rw [center_degree]; split_ifs <;> decide
    | some j => rw [leaf_degree]; decide

lemma graph_le_full {r : ℕ} (S : Finset (Fin r)) :
    graph S ≤ ConeEnvelopeLoss.fullCone (forest r) := by
  intro x y h
  cases x <;> cases y
  · exact h
  · trivial
  · trivial
  · exact h.1

lemma feedback {r : ℕ} (hr : 0 < r) (S : Finset (Fin r)) :
    ((graph S).deleteIncidenceSet none).IsAcyclic := by
  have hdel : (graph S).deleteIncidenceSet none ≤
      (ConeEnvelopeLoss.fullCone (forest r)).deleteIncidenceSet none := by
    intro x y h
    obtain ⟨hxy,hx,hy⟩ := deleteIncidenceSet_adj.mp h
    exact deleteIncidenceSet_adj.mpr ⟨graph_le_full S hxy,hx,hy⟩
  exact (deleted_cone_acyclic (forest r) (⟨0,hr⟩,false,none) (forest_acyclic r)).comap
    (Hom.ofLE hdel) Function.injective_id

lemma graph_critical {r : ℕ} (hr : 0 < r) (S : Finset (Fin r)) :
    IsCountCritical (3*r-S.card) (graph S) :=
  FeedbackKernels.critical_of_feedback (graph_even S) none (feedback hr S) _ (apex_degree S)

lemma graph_invariant {r : ℕ} (hr : 0 < r) (S : Finset (Fin r)) :
    InvariantPartitions.HasInvariantCount (graph S) :=
  FeedbackKernels.invariant_of_feedback none (feedback hr S)

lemma graph_support {r : ℕ} (hr : 0 < r) (S : Finset (Fin r)) :
    (graph S).support = Set.univ := by
  apply Set.eq_univ_of_forall
  intro v
  apply ((graph S).degree_pos_iff_mem_support v).mp
  cases v with
  | none =>
    rw [apex_degree]
    have hh := S.card_le_univ
    simp only [Fintype.card_fin] at hh
    omega
  | some v =>
    obtain ⟨i,b,x⟩ := v
    cases x with
    | none => rw [center_degree]; split_ifs <;> decide
    | some j => rw [leaf_degree]; decide

lemma graph_connected {r : ℕ} (S : Finset (Fin r)) : (graph S).Connected := by
  have hn (x : Vert r) : (graph S).Reachable x none := by
    cases x with
    | none => exact .rfl
    | some x =>
      obtain ⟨i,b,x⟩ := x
      cases x with
      | some j =>
        have h : (graph S).Adj (some (i,b,some j)) none := by
          change (i,b,some j) ∈ active S
          simp [active]
        exact h.reachable
      | none =>
        have h₁ : (graph S).Adj (some (i,b,none)) (some (i,b,some 0)) := by
          change (forest r).Adj (i,b,none) (i,b,some 0) ∧ _
          simp [forest,base]
        have h₂ : (graph S).Adj (some (i,b,some 0)) none := by
          change (i,b,some 0) ∈ active S
          simp [active]
        exact h₁.reachable.trans h₂.reachable
  exact ⟨fun x y => (hn x).trans (hn y).symm⟩

lemma graph_order (r : ℕ) : Fintype.card (Vert r) = 6*r+1 := by
  simp [Vert,Old,Base,Nat.mul_comm]

def triangle {r : ℕ} (S : Finset (Fin r)) (i : Fin r) (hi : i ∉ S) :
    (graph S).Walk none none :=
  .cons (show (graph S).Adj none (some (i,false,none)) from by
    change (i,false,none) ∈ active S; simp [active,hi]) <|
  .cons (show (graph S).Adj (some (i,false,none)) (some (i,true,none)) from by
    change (forest r).Adj (i,false,none) (i,true,none) ∧ _
    simp [forest,base,hi]) <|
  .cons (show (graph S).Adj (some (i,true,none)) none from by
    change (i,true,none) ∈ active S; simp [active,hi]) .nil

lemma triangle_cycle {r : ℕ} (S : Finset (Fin r)) (i : Fin r) (hi : i ∉ S) :
    (triangle S i hi).IsCycle := by
  apply (Walk.cons_isCycle_iff _ _).mpr
  constructor
  · rw [Walk.isPath_def]
    change [some (i,false,none),some (i,true,none),(none : Vert r)].Nodup
    simp
  · simp

lemma triangle_adj {r : ℕ} (S : Finset (Fin r)) (i : Fin r) (hi : i ∉ S)
    (x y : Vert r) :
    (triangle S i hi).toSubgraph.Adj x y ↔
      s(x,y) = s(none,some (i,false,none)) ∨
      s(x,y) = s(some (i,false,none),some (i,true,none)) ∨
      s(x,y) = s(some (i,true,none),none) := by
  change s(x,y) ∈ (triangle S i hi).toSubgraph.edgeSet ↔ _
  rw [Walk.mem_edges_toSubgraph]
  simp [triangle]

lemma triangle_edge_card {r : ℕ} (S : Finset (Fin r)) (i : Fin r) (hi : i ∉ S) :
    (triangle S i hi).toSubgraph.edgeSet.ncard = 3 := by
  have hh := trail_spanning_edge_card (triangle S i hi) (triangle_cycle S i hi).isTrail
  simpa only [edgeFinset_card,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq,
    triangle,Walk.length_cons,Walk.length_nil] using hh

/-- Deleting exactly the displayed triangle produces the next member of the
family. No additional extraction or deletion is hidden in this identity. -/
lemma delete_triangle {r : ℕ} (S : Finset (Fin r)) (i : Fin r) (hi : i ∉ S) :
    graph S \ (triangle S i hi).toSubgraph.spanningCoe = graph (insert i S) := by
  ext x y
  change ((graph S).Adj x y ∧ ¬(triangle S i hi).toSubgraph.Adj x y) ↔ _
  rw [triangle_adj]
  cases x with
  | none =>
    cases y with
    | none => simp [graph,FanPaths.cone]
    | some y =>
      obtain ⟨j,b,y⟩ := y
      cases b <;> cases y <;>
        simp [graph,FanPaths.cone,active,eq_comm] <;> tauto
  | some x =>
    obtain ⟨j,b,x⟩ := x
    cases y with
    | none =>
      cases b <;> cases x <;>
        simp [graph,FanPaths.cone,active,eq_comm] <;> tauto
    | some y =>
      obtain ⟨k,c,y⟩ := y
      by_cases hjk : j = k
      · subst k
        by_cases hji : j = i
        · subst j
          cases b <;> cases c <;> cases x <;> cases y <;>
            simp [graph,FanPaths.cone,core,forest,base,hi]
        · cases b <;> cases c <;> cases x <;> cases y <;>
            simp [graph,FanPaths.cone,core,forest,base,hji]
      · cases b <;> cases c <;> cases x <;> cases y <;>
          simp [graph,FanPaths.cone,core,forest,base,hjk]

/-- At every step of this prescribed deletion, both graphs have full support,
are count-critical, and their minimum counts differ by exactly one. -/
theorem critical_full_support_step {r : ℕ} (hr : 0 < r)
    (S : Finset (Fin r)) (i : Fin r) (hi : i ∉ S) :
    IsCountCritical (3*r-S.card) (graph S) ∧
    IsCountCritical (3*r-(S.card+1))
      (graph S \ (triangle S i hi).toSubgraph.spanningCoe) ∧
    (graph S).support = Set.univ ∧
    (graph S \ (triangle S i hi).toSubgraph.spanningCoe).support = Set.univ := by
  rw [delete_triangle]
  refine ⟨graph_critical hr S,?_,graph_support hr S,graph_support hr (insert i S)⟩
  simpa only [Finset.card_insert_of_notMem hi] using graph_critical hr (insert i S)

noncomputable def initialBlocks (r t : ℕ) : Finset (Fin r) :=
  Finset.univ.filter (fun i => i.val < t)

lemma prefix_card {r t : ℕ} (ht : t ≤ r) : (initialBlocks r t).card = t := by
  have hh := Fintype.card_fin_lt_of_le ht
  simpa only [Fintype.card_subtype,initialBlocks] using hh

lemma prefix_step {r t : ℕ} (ht : t < r) :
    initialBlocks r (t+1) = insert ⟨t,ht⟩ (initialBlocks r t) := by
  ext i
  simp only [initialBlocks,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert]
  rw [Fin.ext_iff]
  change (i.val < t+1) ↔ (i.val = t ∨ i.val < t)
  omega

/-- An explicit r-step chain, with no support loss at ANY stage, even though
all stages are critical and each step deletes just one simple cycle. -/
theorem arbitrary_length_plateau (r : ℕ) (hr : 0 < r) :
    ∃ G : ℕ → SimpleGraph (Vert r),
      (∀ t ≤ r, IsCountCritical (3*r-t) (G t) ∧ (G t).support = Set.univ ∧ (G t).Connected) ∧
      (∀ t < r, ∃ C : (G t).Subgraph,
        (C.coe.Connected ∧ C.coe.IsRegularOfDegree 2) ∧ C.edgeSet.ncard = 3 ∧
        G (t+1) = G t \ C.spanningCoe) := by
  refine ⟨fun t => graph (initialBlocks r t),?_,?_⟩
  · intro t ht
    exact ⟨by simpa only [prefix_card ht] using graph_critical hr (initialBlocks r t),
      graph_support hr (initialBlocks r t),graph_connected (initialBlocks r t)⟩
  · intro t ht
    have hi : (⟨t,ht⟩ : Fin r) ∉ initialBlocks r t := by simp [initialBlocks]
    refine ⟨(triangle (initialBlocks r t) ⟨t,ht⟩ hi).toSubgraph,?_,
      triangle_edge_card (initialBlocks r t) ⟨t,ht⟩ hi,?_⟩
    · have hc := cycle_subgraph_regular _ (triangle_cycle (initialBlocks r t) ⟨t,ht⟩ hi)
      refine ⟨hc.1,?_⟩
      intro v
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hc.2 v
    · dsimp only
      rw [delete_triangle,prefix_step ht]

end Erdos184.CriticalDeletionPlateau
