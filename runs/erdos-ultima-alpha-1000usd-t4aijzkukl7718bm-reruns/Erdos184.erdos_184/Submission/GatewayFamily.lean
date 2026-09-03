import Submission.GatewayPacking
import Submission.LongCyclePacking
import Submission.DegreePotential

/-! A parameterized gateway graph, with degree counts and restrictions on
long-cycle packings. These lemmas do not settle Erdős 184. -/
open SimpleGraph
namespace Erdos184.GatewayFamily

variable {r d : ℕ}

abbrev V (r d : ℕ) := Fin (r + 2) × Fin (d + 2)

def localAdj (u v : V r d) : Prop :=
  u.1 = v.1 ∧ u.2 ≠ v.2 ∧ ¬((u.2 = 0 ∧ v.2 = 1) ∨ (u.2 = 1 ∧ v.2 = 0))

def graph : SimpleGraph (V r d) where
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

local notation "G" => (graph (r := r) (d := d))

instance : DecidableRel (G).Adj := by
  intro u v
  change Decidable ((u.2 = 0 ∧ v.2 = 0 ∧ u.1 ≠ v.1) ∨ localAdj u v ∨
    (u.2 = 1 ∧ v.2 = 0 ∧ v.1 = u.1 + 1) ∨
    (u.2 = 0 ∧ v.2 = 1 ∧ u.1 = v.1 + 1))
  unfold localAdj
  infer_instance

def side (i : Fin (r + 2)) : SimpleGraph (V r d) where
  Adj u v := u.1 = i ∧ v.1 = i ∧ u.2 ≠ v.2 ∧
    ¬((u.2 = 0 ∧ v.2 = 1) ∨ (u.2 = 1 ∧ v.2 = 0))
  symm := by intro u v h; aesop
  loopless := by intro u h; exact h.2.2.1 rfl

local notation "A" => (side (r := r) (d := d))

instance (i : Fin (r + 2)) : DecidableRel (A i).Adj := by
  intro u v
  change Decidable (u.1 = i ∧ v.1 = i ∧ u.2 ≠ v.2 ∧
    ¬((u.2 = 0 ∧ v.2 = 1) ∨ (u.2 = 1 ∧ v.2 = 0)))
  infer_instance

def gatewayEdge (i : Fin (r + 2)) : Sym2 (V r d) := s((i,1), (i+1,0))
local notation "gateway" => (gatewayEdge (r := r) (d := d))

def otherSide (i : Fin (r + 2)) : SimpleGraph (V r d) := ((G).deleteEdges {gateway i}) \ A i

local notation "B" => (otherSide (r := r) (d := d))

lemma A_le_G (i : Fin (r + 2)) : A i ≤ G := by
  intro u v h
  exact Or.inr (Or.inl ⟨h.1.trans h.2.1.symm, h.2.2⟩)

lemma gateway_not_A (i : Fin (r + 2)) : gateway i ∉ (A i).edgeSet := by
  change ¬(A i).Adj (i,1) (i+1,0)
  simp [side]

lemma A_le_delete (i : Fin (r + 2)) : A i ≤ (G).deleteEdges {gateway i} := by
  intro u v h
  apply SimpleGraph.deleteEdges_adj.mpr
  refine ⟨A_le_G i h, ?_⟩
  intro hh
  have hh' := Set.mem_singleton_iff.mp hh
  exact gateway_not_A i (hh' ▸ (show s(u,v) ∈ (A i).edgeSet from h))

lemma side_cover (i : Fin (r + 2)) :
    (A i).edgeSet ∪ (B i).edgeSet = ((G).deleteEdges {gateway i}).edgeSet := by
  change (A i).edgeSet ∪ (((G).deleteEdges {gateway i}) \ A i).edgeSet = _
  rw [SimpleGraph.edgeSet_sdiff]
  exact Set.union_diff_cancel (SimpleGraph.edgeSet_mono (A_le_delete i))

lemma side_disjoint (i : Fin (r + 2)) : Disjoint (A i).edgeSet (B i).edgeSet := by
  change Disjoint (A i).edgeSet (((G).deleteEdges {gateway i}) \ A i).edgeSet
  rw [SimpleGraph.edgeSet_sdiff]
  exact Set.disjoint_sdiff_right

lemma side_support_first {i : Fin (r + 2)} {u : V r d} (h : u ∈ (A i).support) : u.1 = i := by
  obtain ⟨v, hv⟩ := h
  exact hv.1

lemma internal_adj {i : Fin (r + 2)} {u v : V r d} (hi : u.1 = i) (hn : u.2 ≠ 0)
    (h : (G).Adj u v) : (A i).Adj u v ∨ s(u,v) = gateway i := by
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
lemma side_overlap (i : Fin (r + 2)) : ((A i).support ∩ (B i).support).ncard ≤ 1 := by
  have hsingle : ∀ u ∈ (A i).support ∩ (B i).support, u = (i,0) := by
    intro u hu
    have hi := side_support_first hu.1
    apply Prod.ext hi
    by_contra hn
    obtain ⟨v, hv⟩ := hu.2
    change ((G).deleteEdges {gateway i}).Adj u v ∧ ¬(A i).Adj u v at hv
    obtain ⟨hG, hne⟩ := SimpleGraph.deleteEdges_adj.mp hv.1
    rcases internal_adj hi hn hG with hA | he
    · exact hv.2 hA
    · exact hne (Set.mem_singleton_iff.mpr he)
  apply Set.ncard_le_one_iff_subsingleton.mpr
  intro u hu v hv
  exact (hsingle u hu).trans (hsingle v hv).symm

lemma side_support_card (i : Fin (r + 2)) : (A i).support.ncard ≤ d + 2 := by
  let S : Finset (V r d) := ({i} : Finset (Fin (r + 2))) ×ˢ (Finset.univ : Finset (Fin (d + 2)))
  have hsub : (A i).support ⊆ (S : Set (V r d)) := by
    intro u hu
    simp only [S, Finset.mem_coe, Finset.mem_product, Finset.mem_singleton,
      Finset.mem_univ, and_true]
    exact side_support_first hu
  have hh := Set.ncard_le_ncard hsub
  rw [Set.ncard_coe_finset] at hh
  simpa only [S, Finset.card_product, Finset.card_singleton, Finset.card_univ,
    Fintype.card_fin, one_mul] using hh



lemma side_degree (i : Fin (r + 2)) (j : Fin (d + 2)) :
    (A i).degree (i,j) = if j = 0 ∨ j = 1 then d else d + 1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hinj : Function.Injective (fun l : Fin (d + 2) => (i,l)) :=
    fun _ _ h => (Prod.mk.inj h).2
  by_cases hj : j = 0 ∨ j = 1
  · have hset : (A i).neighborFinset (i,j) =
        ((Finset.univ.erase 0).erase 1).image (fun l : Fin (d + 2) => (i,l)) := by
      ext ⟨k,l⟩
      simp only [SimpleGraph.mem_neighborFinset, side, Finset.mem_image,
        Finset.mem_erase, Finset.mem_univ, and_true, Prod.mk.injEq]
      rcases hj with rfl | rfl <;> simp <;> aesop
    rw [hset, Finset.card_image_of_injective _ hinj, if_pos hj]
    rw [Finset.card_erase_of_mem (by simp), Finset.card_erase_of_mem (by simp)]
    simp
  · have hset : (A i).neighborFinset (i,j) =
        (Finset.univ.erase j).image (fun l : Fin (d + 2) => (i,l)) := by
      ext ⟨k,l⟩
      simp only [SimpleGraph.mem_neighborFinset, side, Finset.mem_image,
        Finset.mem_erase, Finset.mem_univ, and_true, Prod.mk.injEq]
      simp only [not_or] at hj
      simp [hj.1, hj.2, eq_comm, and_comm]
    rw [hset, Finset.card_image_of_injective _ hinj, if_neg hj]
    rw [Finset.card_erase_of_mem (by simp)]
    simp

lemma side_degree_lower (i : Fin (r + 2)) (j : Fin (d + 2)) :
    d ≤ (A i).degree (i,j) := by
  rw [side_degree]
  split <;> omega

lemma core_degree (i : Fin (r + 2)) : (G).degree (i,0) = r + d + 2 := by
  let C : Finset (V r d) := (Finset.univ.erase i).image (fun k => (k,0))
  let L : Finset (V r d) := ((Finset.univ.erase 0).erase 1).image (fun l => (i,l))
  have hset : (G).neighborFinset (i,0) = insert (i-1,1) (C ∪ L) := by
    ext ⟨k,l⟩
    simp only [SimpleGraph.mem_neighborFinset, graph, localAdj, C, L, Finset.mem_insert,
      Finset.mem_union, Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true,
      Prod.mk.injEq]
    have hk : i = k + 1 ↔ k = i - 1 := by
      constructor
      · intro h; rw [h, add_sub_cancel_right]
      · rintro rfl; simp
    simp only [Fin.zero_ne_one, false_and, or_false, true_and, false_or]
    rw [hk]
    aesop
  have hnot : (i-1,1) ∉ C ∪ L := by simp [C, L]
  have hdis : Disjoint C L := by
    apply Finset.disjoint_left.mpr
    intro v hvC hvL
    simp only [C, L, Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true] at *
    obtain ⟨k, hk, rfl⟩ := hvC
    obtain ⟨l, hl, heq⟩ := hvL
    exact hl.2 ((Prod.mk.inj heq).2)
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hset,
    Finset.card_insert_of_notMem hnot, Finset.card_union_of_disjoint hdis]
  have hinj1 : Function.Injective (fun k : Fin (r + 2) => (k, (0 : Fin (d + 2)))) :=
    fun _ _ h => (Prod.mk.inj h).1
  have hinj2 : Function.Injective (fun l : Fin (d + 2) => (i,l)) :=
    fun _ _ h => (Prod.mk.inj h).2
  simp only [C, L, Finset.card_image_of_injective _ hinj1,
    Finset.card_image_of_injective _ hinj2]
  rw [Finset.card_erase_of_mem (by simp), Finset.card_erase_of_mem (by simp),
    Finset.card_erase_of_mem (by simp)]
  simp
  omega

lemma internal_degree (i : Fin (r + 2)) (j : Fin (d + 2)) (hj : j ≠ 0) :
    (G).degree (i,j) = d + 1 := by
  by_cases hj1 : j = 1
  · subst j
    have hset : (G).neighborFinset (i,1) = insert (i+1,0) ((A i).neighborFinset (i,1)) := by
      ext ⟨k,l⟩
      simp only [SimpleGraph.mem_neighborFinset, graph, localAdj, side, Finset.mem_insert,
        Prod.mk.injEq]
      simp only [Ne.symm Fin.zero_ne_one, false_and, false_or, true_and]
      aesop
    have hnot : (i+1,0) ∉ (A i).neighborFinset (i,1) := by
      simp [SimpleGraph.mem_neighborFinset, side]
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hset, Finset.card_insert_of_notMem hnot,
      SimpleGraph.card_neighborFinset_eq_degree, side_degree]
    simp
  · have hset : (G).neighborFinset (i,j) = (A i).neighborFinset (i,j) := by
      ext ⟨k,l⟩
      simp only [SimpleGraph.mem_neighborFinset, graph, localAdj, side, hj, hj1,
        false_and, false_or, true_and]
      aesop
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hset,
      SimpleGraph.card_neighborFinset_eq_degree, side_degree, if_neg (not_or.mpr ⟨hj,hj1⟩)]

lemma graph_degrees (v : V r d) :
    (G).degree v = if v.2 = 0 then r + d + 2 else d + 1 := by
  rcases v with ⟨i,j⟩
  by_cases hj : j = 0
  · subst j; simpa using core_degree (d := d) i
  · simpa [hj] using internal_degree i j hj

lemma graph_order : Fintype.card (V r d) = (r + 2) * (d + 2) := by simp [V]

lemma twice_graph_size : 2 * (G).edgeFinset.card = (r + 2) * (r + d + 2 + (d + 1)^2) := by
  rw [← SimpleGraph.sum_degrees_eq_twice_card_edges]
  simp_rw [graph_degrees, Fintype.sum_prod_type]
  have hsum : (∑ j : Fin (d + 2), if j = 0 then r + d + 2 else d + 1) =
      r + d + 2 + (d + 1)^2 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Fin (d + 2)))]
    simp only [ite_true]
    rw [Finset.sum_congr rfl (fun j hj => if_neg (Finset.ne_of_mem_erase hj))]
    simp [Finset.card_erase_of_mem, pow_two]
    ring
  simp only [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]


lemma graph_even (hr : Odd r) (hd : Odd d) : ∀ v : V r d, Even ((G).degree v) := by
  intro v
  rw [graph_degrees]
  obtain ⟨a, ha⟩ := hr
  obtain ⟨b, hb⟩ := hd
  split
  · exact ⟨a + b + 2, by omega⟩
  · exact ⟨b + 1, by omega⟩

lemma residual_degree_lower (hr : Odd r) (hd : Odd d) (D : Finset (G).Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdis : Set.PairwiseDisjoint (D : Set (G).Subgraph) (fun H => H.edgeSet))
    (hlong : ∀ H ∈ D, d + 2 < H.edgeSet.ncard) (v : V r d) :
    d - 1 ≤ ((G) \ unionPieces (G) D).degree v := by
  have hside := side_degree_lower v.1 v.2
  have hh := gateway_packing_degree_lower (A_le_G (d := d) v.1) (gateway v.1)
    (side_cover v.1) (side_disjoint v.1) (side_overlap v.1) D (by
      intro H hH
      refine ⟨(hc H hH).1, ?_⟩
      intro w
      simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using (hc H hH).2 w) hdis
    (fun H hH => (side_support_card v.1).trans_lt (hlong H hH)) v
  have he := even_residual_of_cycle_packing (G) (by
    intro w
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using graph_even hr hd w) D (by
      intro H hH
      refine ⟨(hc H hH).1, ?_⟩
      intro w
      simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using (hc H hH).2 w) hdis v
  obtain ⟨a, ha⟩ := hd
  obtain ⟨b, hb⟩ := he
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card,
    Prod.mk.eta] at hside hh hb ⊢
  omega

lemma packing_internal_degree_upper (hr : Odd r) (hd : Odd d)
    (D : Finset (G).Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdis : Set.PairwiseDisjoint (D : Set (G).Subgraph) (fun H => H.edgeSet))
    (hlong : ∀ H ∈ D, d + 2 < H.edgeSet.ncard) (v : V r d) (hv : v.2 ≠ 0) :
    (unionPieces (G) D).degree v ≤ 2 := by
  have hR := residual_degree_lower hr hd D hc hdis hlong v
  have hG := internal_degree v.1 v.2 hv
  have hU := degree_sdiff_of_le (unionPieces_le (G) D) v
  have hle : (unionPieces (G) D).degree v ≤ (G).degree v :=
    SimpleGraph.degree_le_of_le (unionPieces_le (G) D)
  obtain ⟨a, ha⟩ := hd
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card,
    Prod.mk.eta] at hR hG hU hle ⊢
  omega

lemma packing_degree_upper (D : Finset (G).Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdis : Set.PairwiseDisjoint (D : Set (G).Subgraph) (fun H => H.edgeSet)) (v : V r d) :
    (unionPieces (G) D).degree v ≤ 2 * D.card := by
  have heq := unionPieces_degree (G) D hdis v
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card,
    Subgraph.degree] at heq ⊢
  rw [heq]
  calc
    ∑ H ∈ D, Nat.card (H.neighborSet v) ≤ ∑ H ∈ D, (2 : ℕ) := by
      apply Finset.sum_le_sum
      intro H hH
      have hh := regular_two_spanning_degree_le H (by
        intro w
        simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
          using (hc H hH).2 w) v
      rw [Subgraph.degree_spanningCoe] at hh
      simpa only [Subgraph.degree, ← Nat.card_eq_fintype_card] using hh
    _ = _ := by simp [mul_comm]

lemma sum_two_values {S : Type*} [Semiring S] (a b : S) :
    (∑ v : V r d, if v.2 = 0 then a else b) =
      (r + 2 : ℕ) * (a + (d + 1 : ℕ) * b) := by
  rw [Fintype.sum_prod_type]
  have hs : (∑ j : Fin (d + 2), if j = 0 then a else b) = a + (d + 1 : ℕ) * b := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Fin (d + 2)))]
    simp only [ite_true]
    rw [Finset.sum_congr rfl (fun j hj => if_neg (Finset.ne_of_mem_erase hj))]
    simp [Finset.card_erase_of_mem, add_comm]
  simp only [hs, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

lemma packing_edge_upper (hr : Odd r) (hd : Odd d) (D : Finset (G).Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdis : Set.PairwiseDisjoint (D : Set (G).Subgraph) (fun H => H.edgeSet))
    (hlong : ∀ H ∈ D, d + 2 < H.edgeSet.ncard) :
    (unionPieces (G) D).edgeFinset.card ≤ (r + 2) * (D.card + d + 1) := by
  have hh : ∑ v : V r d, (unionPieces (G) D).degree v ≤
      ∑ v : V r d, if v.2 = 0 then 2 * D.card else 2 := by
    apply Finset.sum_le_sum
    intro v _
    split_ifs with hv
    · exact packing_degree_upper D hc hdis v
    · exact packing_internal_degree_upper hr hd D hc hdis hlong v hv
  rw [sum_two_values, SimpleGraph.sum_degrees_eq_twice_card_edges] at hh
  nlinarith

lemma potential_drop_upper (hr : Odd r) (hd : Odd d) (D : Finset (G).Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdis : Set.PairwiseDisjoint (D : Set (G).Subgraph) (fun H => H.edgeSet))
    (hlong : ∀ H ∈ D, d + 2 < H.edgeSet.ncard)
    (φ : ℕ → ℝ) (hm : Monotone φ) (hb : BddAbove (Set.range φ)) :
    (∑ v : V r d, (φ ((G).degree v) - φ (((G) \ unionPieces (G) D).degree v))) ≤
      (r + 2 : ℕ) * ((⨆ i, φ i) - φ (d - 1) +
        (d + 1 : ℕ) * (φ (d + 1) - φ (d - 1))) := by
  rw [← sum_two_values]
  apply Finset.sum_le_sum
  intro v _
  have hR := hm (residual_degree_lower hr hd D hc hdis hlong v)
  rw [graph_degrees]
  split_ifs with hv
  · exact sub_le_sub (le_ciSup hb _) hR
  · exact sub_le_sub_left hR _

end Erdos184.GatewayFamily
