import Submission.GatewayPacking
import Submission.LongCyclePacking

/-! A dense even graph where every long-cycle packing retains full support.
This obstructs an immediate-support charging argument, not Erdős 184. -/
open SimpleGraph
namespace Erdos184.GatewayObstruction

abbrev V := Fin 31 × Fin 5

def localAdj (u v : V) : Prop :=
  u.1 = v.1 ∧ u.2 ≠ v.2 ∧ ¬((u.2 = 0 ∧ v.2 = 1) ∨ (u.2 = 1 ∧ v.2 = 0))

def G : SimpleGraph V where
  Adj u v := (u.2 = 0 ∧ v.2 = 0 ∧ u.1 ≠ v.1) ∨ localAdj u v ∨
    (u.2 = 1 ∧ v.2 = 0 ∧ v.1 = u.1 + 1) ∨
    (u.2 = 0 ∧ v.2 = 1 ∧ u.1 = v.1 + 1)
  symm := by
    intro u v h
    simp only [localAdj] at *
    aesop
  loopless := by
    intro u h
    simp only [localAdj] at h
    rcases h with h | h | h | h
    · exact h.2.2 rfl
    · exact h.2.1 rfl
    · have := h.1.symm.trans h.2.1
      norm_num at this
    · have := h.1.symm.trans h.2.1
      norm_num at this

instance : DecidableRel G.Adj := by
  intro u v
  change Decidable ((u.2 = 0 ∧ v.2 = 0 ∧ u.1 ≠ v.1) ∨ localAdj u v ∨
    (u.2 = 1 ∧ v.2 = 0 ∧ v.1 = u.1 + 1) ∨
    (u.2 = 0 ∧ v.2 = 1 ∧ u.1 = v.1 + 1))
  unfold localAdj
  infer_instance

def A (i : Fin 31) : SimpleGraph V where
  Adj u v := u.1 = i ∧ v.1 = i ∧ u.2 ≠ v.2 ∧
    ¬((u.2 = 0 ∧ v.2 = 1) ∨ (u.2 = 1 ∧ v.2 = 0))
  symm := by intro u v h; aesop
  loopless := by intro u h; exact h.2.2.1 rfl

instance (i : Fin 31) : DecidableRel (A i).Adj := by
  intro u v
  change Decidable (u.1 = i ∧ v.1 = i ∧ u.2 ≠ v.2 ∧
    ¬((u.2 = 0 ∧ v.2 = 1) ∨ (u.2 = 1 ∧ v.2 = 0)))
  infer_instance

def gateway (i : Fin 31) : Sym2 V := s((i,1), (i+1,0))
def B (i : Fin 31) : SimpleGraph V := (G.deleteEdges {gateway i}) \ A i

lemma A_le_G (i : Fin 31) : A i ≤ G := by
  intro u v h
  exact Or.inr (Or.inl ⟨h.1.trans h.2.1.symm, h.2.2⟩)

lemma gateway_not_A (i : Fin 31) : gateway i ∉ (A i).edgeSet := by
  change ¬(A i).Adj (i,1) (i+1,0)
  simp [A]

lemma A_le_delete (i : Fin 31) : A i ≤ G.deleteEdges {gateway i} := by
  intro u v h
  apply SimpleGraph.deleteEdges_adj.mpr
  refine ⟨A_le_G i h, ?_⟩
  intro hh
  have hh' := Set.mem_singleton_iff.mp hh
  exact gateway_not_A i (hh' ▸ (show s(u,v) ∈ (A i).edgeSet from h))

lemma side_cover (i : Fin 31) :
    (A i).edgeSet ∪ (B i).edgeSet = (G.deleteEdges {gateway i}).edgeSet := by
  change (A i).edgeSet ∪ ((G.deleteEdges {gateway i}) \ A i).edgeSet = _
  rw [SimpleGraph.edgeSet_sdiff]
  exact Set.union_diff_cancel (SimpleGraph.edgeSet_mono (A_le_delete i))

lemma side_disjoint (i : Fin 31) : Disjoint (A i).edgeSet (B i).edgeSet := by
  change Disjoint (A i).edgeSet ((G.deleteEdges {gateway i}) \ A i).edgeSet
  rw [SimpleGraph.edgeSet_sdiff]
  exact Set.disjoint_sdiff_right

lemma side_support_first {i : Fin 31} {u : V} (h : u ∈ (A i).support) : u.1 = i := by
  obtain ⟨v, hv⟩ := h
  exact hv.1

lemma internal_adj {i : Fin 31} {u v : V} (hi : u.1 = i) (hn : u.2 ≠ 0)
    (h : G.Adj u v) : (A i).Adj u v ∨ s(u,v) = gateway i := by
  rcases h with h | h | h | h
  · exact (hn h.1).elim
  · left
    exact ⟨hi, h.1.symm.trans hi, h.2⟩
  · right
    have hu : u = (i,1) := Prod.ext hi h.1
    have hv : v = (i+1,0) := Prod.ext (h.2.2.trans (congrArg (· + 1) hi)) h.2.1
    rw [hu, hv]
    rfl
  · exact (hn h.1).elim

open scoped Classical
lemma side_overlap (i : Fin 31) : ((A i).support ∩ (B i).support).ncard ≤ 1 := by
  have hsingle : ∀ u ∈ (A i).support ∩ (B i).support, u = (i,0) := by
    intro u hu
    have hi := side_support_first hu.1
    apply Prod.ext hi
    by_contra hn
    obtain ⟨v, hv⟩ := hu.2
    change (G.deleteEdges {gateway i}).Adj u v ∧ ¬(A i).Adj u v at hv
    obtain ⟨hG, hne⟩ := SimpleGraph.deleteEdges_adj.mp hv.1
    rcases internal_adj hi hn hG with hA | he
    · exact hv.2 hA
    · exact hne (Set.mem_singleton_iff.mpr he)
  apply Set.ncard_le_one_iff_subsingleton.mpr
  intro u hu v hv
  exact (hsingle u hu).trans (hsingle v hv).symm

lemma side_support_card (i : Fin 31) : (A i).support.ncard ≤ 5 := by
  let S : Finset V := ({i} : Finset (Fin 31)) ×ˢ (Finset.univ : Finset (Fin 5))
  have hsub : (A i).support ⊆ (S : Set V) := by
    intro u hu
    simp only [S, Finset.mem_coe, Finset.mem_product, Finset.mem_singleton,
      Finset.mem_univ, and_true]
    exact side_support_first hu
  have hh := Set.ncard_le_ncard hsub
  rw [Set.ncard_coe_finset] at hh
  simpa only [S, Finset.card_product, Finset.card_singleton, Finset.card_univ,
    Fintype.card_fin, one_mul] using hh

lemma degree_ge_three_of_neighbors {W : Type*} [Fintype W] (K : SimpleGraph W)
    (v a b c : W) (ha : K.Adj v a) (hb : K.Adj v b) (hc : K.Adj v c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : 3 ≤ Nat.card (K.neighborSet v) := by
  have hsub : ({a,b,c} : Finset W) ⊆ K.neighborFinset v := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · simpa using ha
    · simpa using hb
    · simpa using hc
  have hh := Finset.card_le_card hsub
  have hdeg : 3 ≤ K.degree v := by simpa [hab, hac, hbc] using hh
  simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hdeg

lemma side_degree_lower (i : Fin 31) (j : Fin 5) : 3 ≤ (A i).degree (i,j) := by
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
  fin_cases j
  · exact degree_ge_three_of_neighbors (A i) (i,0) (i,2) (i,3) (i,4)
      (by simp [A]) (by simp [A]) (by simp [A]) (by simp) (by simp) (by simp)
  · exact degree_ge_three_of_neighbors (A i) (i,1) (i,2) (i,3) (i,4)
      (by simp [A]) (by simp [A]) (by simp [A]) (by simp) (by simp) (by simp)
  · exact degree_ge_three_of_neighbors (A i) (i,2) (i,0) (i,3) (i,4)
      (by simp [A]) (by simp [A]) (by simp [A]) (by simp) (by simp) (by simp)
  · exact degree_ge_three_of_neighbors (A i) (i,3) (i,0) (i,2) (i,4)
      (by simp [A]) (by simp [A]) (by simp [A]) (by simp) (by simp) (by simp)
  · exact degree_ge_three_of_neighbors (A i) (i,4) (i,0) (i,2) (i,3)
      (by simp [A]) (by simp [A]) (by simp [A]) (by simp) (by simp) (by simp)

lemma long_packing_residual_full_support (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet))
    (hlong : ∀ H ∈ D, 5 < H.edgeSet.ncard) :
    (G \ unionPieces G D).support = Set.univ := by
  apply Set.eq_univ_of_forall
  intro v
  have hh := gateway_packing_degree_lower (A_le_G v.1) (gateway v.1)
    (side_cover v.1) (side_disjoint v.1) (side_overlap v.1) D (by
      intro H hH
      refine ⟨(hc H hH).1, ?_⟩
      intro w
      simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using (hc H hH).2 w) hd
    (fun H hH => (side_support_card v.1).trans_lt (hlong H hH)) v
  have hv := side_degree_lower v.1 v.2
  apply (G \ unionPieces G D).degree_pos_iff_mem_support v |>.mp
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hh hv ⊢
  simp only [Prod.mk.eta] at hv
  omega

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
lemma graph_degrees : ∀ v : V, G.degree v = if v.2 = 0 then 34 else 4 := by
  decide

lemma graph_even : ∀ v, Even (G.degree v) := by
  intro v
  rw [graph_degrees]
  split <;> decide

lemma graph_order : Fintype.card V = 155 := by simp [V]

set_option maxRecDepth 4096 in
lemma graph_size : G.edgeFinset.card = 775 := by
  have hh := G.sum_degrees_eq_twice_card_edges
  have hs : (∑ v : V, G.degree v) = 1550 := by
    simp_rw [graph_degrees]
    decide
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hh ⊢
  omega

lemma graph_support : G.support = Set.univ := by
  apply Set.eq_univ_of_forall
  intro v
  apply (G.degree_pos_iff_mem_support v).mp
  rw [graph_degrees]
  split <;> omega

lemma exists_nonempty_maximal_packing :
    ∃ D : Finset G.Subgraph, D.Nonempty ∧
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 ∧ 5 < H.edgeSet.ncard) ∧
      Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet) ∧
      (∀ u (p : (G \ unionPieces G D).Walk u u), p.IsCycle → p.length ≤ 5) ∧
      (G \ unionPieces G D).support = G.support ∧
      (G \ unionPieces G D).edgeFinset.card ≤ 620 := by
  obtain ⟨D, hc, hd, hmax⟩ := exists_maximal_long_cycle_packing G 5
  have hsmall := edge_card_le_of_cycle_length_bound (G \ unionPieces G D) 5 (by omega) hmax
  rw [graph_order] at hsmall
  have hne : D.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro h0
    have hpart := cycle_packing_edge_card_partition G D hd
    have hsum : (∑ H ∈ D, H.edgeSet.ncard) = 0 := by rw [h0]; simp
    rw [hsum, zero_add] at hpart
    have hsize := graph_size
    simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hpart hsmall hsize
    omega
  have hs := long_packing_residual_full_support D (by
    intro H hH
    refine ⟨(hc H hH).1, ?_⟩
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using (hc H hH).2.1 v) hd (fun H hH => (hc H hH).2.2)
  refine ⟨D, hne, ?_, hd, hmax, hs.trans graph_support.symm, ?_⟩
  · intro H hH
    refine ⟨(hc H hH).1, ?_, (hc H hH).2.2⟩
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using (hc H hH).2.1 v
  · simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using hsmall

/-- No fixed charge per immediately lost support vertex can bound even an
optimally chosen nonempty long-cycle phase in this graph. -/
lemma support_drop_charge_impossible :
    ¬ ∃ C : ℕ, ∃ D : Finset G.Subgraph, D.Nonempty ∧
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 ∧ 5 < H.edgeSet.ncard) ∧
      Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet) ∧
      D.card ≤ C * (G.support.ncard - (G \ unionPieces G D).support.ncard) := by
  rintro ⟨C, D, hne, hc, hd, hb⟩
  have hs := long_packing_residual_full_support D (by
    intro H hH
    refine ⟨(hc H hH).1, ?_⟩
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using (hc H hH).2.1 v) hd (fun H hH => (hc H hH).2.2)
  rw [hs, graph_support, Nat.sub_self, mul_zero] at hb
  have hh := Finset.card_pos.mpr hne
  omega

lemma core_successor_ne : ∀ i : Fin 31, i + 1 ≠ i := by decide

lemma core_reachable (z : V) (i j : Fin 31) (hi : (i,0) ≠ z) (hj : (j,0) ≠ z) :
    (G.induce {x | x ≠ z}).Reachable ⟨(i,0), hi⟩ ⟨(j,0), hj⟩ := by
  by_cases h : i = j
  · subst j
    exact Reachable.rfl
  · apply SimpleGraph.Adj.reachable
    exact Or.inl ⟨rfl, rfl, h⟩

lemma reachable_core_avoiding (z u : V) (hu : u ≠ z) :
    ∃ (i : Fin 31) (hi : (i,0) ≠ z),
      (G.induce {x | x ≠ z}).Reachable ⟨u, hu⟩ ⟨(i,0), hi⟩ := by
  rcases u with ⟨i,j⟩
  by_cases hj : j = 0
  · subst j
    exact ⟨i, hu, Reachable.rfl⟩
  by_cases ha : (i,0) = z
  · subst z
    have hb : (i+1, (0 : Fin 5)) ≠ (i,0) := by
      intro h
      exact core_successor_ne i (congrArg Prod.fst h)
    refine ⟨i+1, hb, ?_⟩
    have h1 : (i, (1 : Fin 5)) ≠ (i,0) := by simp
    have hgate : (G.induce {x | x ≠ (i,0)}).Adj ⟨(i,1),h1⟩ ⟨(i+1,0),hb⟩ :=
      Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
    by_cases hj1 : j = 1
    · subst j
      exact hgate.reachable
    · have hx : (G.induce {x | x ≠ (i,0)}).Adj ⟨(i,j),hu⟩ ⟨(i,1),h1⟩ := by
        change G.Adj (i,j) (i,1)
        simp [G, localAdj, hj, hj1]
      exact hx.reachable.trans hgate.reachable
  · refine ⟨i, ha, ?_⟩
    by_cases hj1 : j = 1
    · subst j
      have hex : ∃ k : Fin 5, (k = 2 ∨ k = 3) ∧ (i,k) ≠ z := by
        by_cases h2 : (i,(2 : Fin 5)) = z
        · refine ⟨3, Or.inr rfl, ?_⟩
          intro h3
          have hh := congrArg Prod.snd (h2.trans h3.symm)
          exact (by decide : (2 : Fin 5) ≠ 3) hh
        · exact ⟨2, Or.inl rfl, h2⟩
      obtain ⟨k, hk, hkz⟩ := hex
      have hx : (G.induce {x | x ≠ z}).Adj ⟨(i,1),hu⟩ ⟨(i,k),hkz⟩ := by
        change G.Adj (i,1) (i,k)
        rcases hk with rfl | rfl <;> simp [G, localAdj]
      have hy : (G.induce {x | x ≠ z}).Adj ⟨(i,k),hkz⟩ ⟨(i,0),ha⟩ := by
        change G.Adj (i,k) (i,0)
        rcases hk with rfl | rfl <;> simp [G, localAdj]
      exact hx.reachable.trans hy.reachable
    · apply SimpleGraph.Adj.reachable
      change G.Adj (i,j) (i,0)
      simp [G, localAdj, hj, hj1]

/-- Deleting any vertex leaves the graph connected; in particular the
support obstruction is not caused by an articulation vertex. -/
lemma connected_after_vertex_deletion (z : V) : (G.induce {x | x ≠ z}).Connected := by
  have hex : ∃ a : Fin 31, (a,(0 : Fin 5)) ≠ z := by
    by_cases h : z.1 = 0
    · refine ⟨1, ?_⟩
      intro hh
      have h1 := (congrArg Prod.fst hh).trans h
      norm_num at h1
    · refine ⟨0, ?_⟩
      intro hh
      exact h (congrArg Prod.fst hh).symm
  obtain ⟨a, ha⟩ := hex
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨⟨(a,0),ha⟩, ?_⟩
  intro u
  obtain ⟨i, hi, hp⟩ := reachable_core_avoiding z u.val u.property
  exact (core_reachable z a i ha hi).trans hp.symm

lemma graph_connected : G.Connected := by
  let z : V := (0,4)
  have ha : ((0,0) : V) ≠ z := by decide
  let K := G.induce {x | x ≠ z}
  have hK := connected_after_vertex_deletion z
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨(0,0), ?_⟩
  intro u
  by_cases hu : u = z
  · subst u
    apply SimpleGraph.Adj.reachable
    decide
  · exact (hK ⟨(0,0),ha⟩ ⟨u,hu⟩).map (SimpleGraph.Embedding.induce {x | x ≠ z}).toHom

end Erdos184.GatewayObstruction
