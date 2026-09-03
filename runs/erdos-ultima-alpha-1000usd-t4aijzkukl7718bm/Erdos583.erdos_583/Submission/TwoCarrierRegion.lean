import Submission.CyclePortCover

/-! Any sufficiently large cycle region with two contiguous carriers is
reducible, with no restrictions on intersections of its exterior tails. -/
namespace Erdos583TwoCarrierRegionDevelopment
open SimpleGraph Erdos583Work Erdos583Work.BridgeGlue Erdos583Work.QuotaTrails
open Erdos583Work.PentagonCarriers Erdos583CyclePortCoverDevelopment
open scoped Classical
set_option maxHeartbeats 2000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

omit [Fintype V] in
lemma tail_neighbor_card_le {s a : V} (A : G.Walk s a) (hA : A.IsPath)
    (S : Set V) (hAS : ∀ x ∈ A.support, x ∈ S → x=a) {v : V} (hv : v ∈ S) :
    (A.toSubgraph.neighborSet v).ncard ≤ if v=a then 1 else 0 := by
  classical
  by_cases hva : v=a
  · subst v
    by_cases hn : A.Nil
    · cases hn
      simp
    · rw [path_neighbor_ncard_formula hA hn]
      simp
  · have hem : A.toSubgraph.neighborSet v=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      exact hva (hAS v (Walk.mem_support_of_adj_toSubgraph hy) hv)
    rw [hem]
    simp [hva]

omit [Fintype V] in
lemma four_label_fiber (a b c d v : V) :
    Fintype.card {i : Fin 4 // ![a,c,b,d] i=v}=
      ((if v=a then 1 else 0)+(if v=b then 1 else 0))+
      ((if v=c then 1 else 0)+(if v=d then 1 else 0)) := by
  classical
  simp only [Fintype.card_subtype,Finset.card_filter,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,
    Matrix.cons_val_zero,Matrix.cons_val_succ]
  simp only [eq_comm]
  omega

lemma two_carrier_boundary_capacity {r s a b t u c d w : V}
    (C : G.Walk r r) (A : G.Walk s a) (P : G.Walk a b) (B : G.Walk b t)
    (D : G.Walk u c) (Q : G.Walk c d) (E : G.Walk d w)
    (hP : (A.append (P.append B)).IsPath) (hQ : (D.append (Q.append E)).IsPath)
    (S : Set V) (hCS : ∀ x ∈ C.support, x ∈ S)
    (hPS : ∀ x ∈ P.support, x ∈ S) (hQS : ∀ x ∈ Q.support, x ∈ S)
    (hA : ∀ x ∈ A.support, x ∈ S → x=a) (hB : ∀ x ∈ B.support, x ∈ S → x=b)
    (hD : ∀ x ∈ D.support, x ∈ S → x=c) (hE : ∀ x ∈ E.support, x ∈ S → x=d)
    (hcarrier : ∀ x ∈ S, ∀ y, G.Adj x y → C.toSubgraph.Adj x y ∨
      (A.append (P.append B)).toSubgraph.Adj x y ∨ (D.append (Q.append E)).toSubgraph.Adj x y) :
    ∀ v ∈ S, Nat.card (G.neighborSet v) ≤ (G.neighborSet v ∩ S).ncard+
      Fintype.card {i : Fin 4 // ![a,c,b,d] i=v} := by
  intro v hv
  have hAr := tail_neighbor_card_le A hP.of_append_left S hA hv
  have hBr := tail_neighbor_card_le B.reverse hP.of_append_right.of_append_right.reverse S
    (by simpa only [Walk.support_reverse,List.mem_reverse] using hB) hv
  have hDr := tail_neighbor_card_le D hQ.of_append_left S hD hv
  have hEr := tail_neighbor_card_le E.reverse hQ.of_append_right.of_append_right.reverse S
    (by simpa only [Walk.support_reverse,List.mem_reverse] using hE) hv
  simp only [Walk.toSubgraph_reverse] at hBr hEr
  have hsub : G.neighborSet v ∩ Sᶜ ⊆
      (A.toSubgraph.neighborSet v ∪ B.toSubgraph.neighborSet v) ∪
      (D.toSubgraph.neighborSet v ∪ E.toSubgraph.neighborSet v) := by
    intro y hy
    rcases hcarrier v hv y hy.1 with hc | hp | hq
    · exact (hy.2 (hCS y (Walk.mem_support_of_adj_toSubgraph hc.symm))).elim
    · simp only [Walk.toSubgraph_append,Subgraph.sup_adj] at hp
      rcases hp with ha | hp | hb
      · exact Or.inl (Or.inl ha)
      · exact (hy.2 (hPS y (Walk.mem_support_of_adj_toSubgraph hp.symm))).elim
      · exact Or.inl (Or.inr hb)
    · simp only [Walk.toSubgraph_append,Subgraph.sup_adj] at hq
      rcases hq with hd | hq | he
      · exact Or.inr (Or.inl hd)
      · exact (hy.2 (hQS y (Walk.mem_support_of_adj_toSubgraph hq.symm))).elim
      · exact Or.inr (Or.inr he)
  have hcount := Set.ncard_mono hsub
  have hAB := Set.ncard_union_le (A.toSubgraph.neighborSet v) (B.toSubgraph.neighborSet v)
  have hDE := Set.ncard_union_le (D.toSubgraph.neighborSet v) (E.toSubgraph.neighborSet v)
  have hall := Set.ncard_union_le (A.toSubgraph.neighborSet v ∪ B.toSubgraph.neighborSet v)
    (D.toSubgraph.neighborSet v ∪ E.toSubgraph.neighborSet v)
  have hsplit := BoundaryPorts.split_degree G S v
  rw [four_label_fiber]
  omega

omit [Fintype V] in
lemma two_carrier_core_cover {r s a b t u c d w : V}
    (C : G.Walk r r) (A : G.Walk s a) (P : G.Walk a b) (B : G.Walk b t)
    (D : G.Walk u c) (Q : G.Walk c d) (E : G.Walk d w)
    (S : Set V) (hCS : ∀ x ∈ C.support, x ∈ S)
    (hPS : ∀ x ∈ P.support, x ∈ S) (hQS : ∀ x ∈ Q.support, x ∈ S)
    (hA : ∀ x ∈ A.support, x ∈ S → x=a) (hB : ∀ x ∈ B.support, x ∈ S → x=b)
    (hD : ∀ x ∈ D.support, x ∈ S → x=c) (hE : ∀ x ∈ E.support, x ∈ S → x=d)
    (hcarrier : ∀ x ∈ S, ∀ y, G.Adj x y → C.toSubgraph.Adj x y ∨
      (A.append (P.append B)).toSubgraph.Adj x y ∨ (D.append (Q.append E)).toSubgraph.Adj x y) :
    (within G S).edgeSet=C.toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet ∪ Q.toSubgraph.edgeSet := by
  apply Set.Subset.antisymm
  · intro e he
    induction e using Sym2.ind with
    | h x y =>
      obtain ⟨hxy,hx,hy⟩ := he
      rcases hcarrier x hx y hxy with hc | hp | hq
      · exact Or.inl (Or.inl hc)
      · exact Or.inl (Or.inr (HeptagonCore.middle_adj_of_inside A P B S hA hB hx hy hp))
      · exact Or.inr (HeptagonCore.middle_adj_of_inside D Q E S hD hE hx hy hq)
  · apply Set.union_subset
    · apply Set.union_subset
      · exact subgraph_edges_within C.toSubgraph S (by intro x hx; exact hCS x (C.mem_verts_toSubgraph.mp hx))
      · exact subgraph_edges_within P.toSubgraph S (by intro x hx; exact hPS x (P.mem_verts_toSubgraph.mp hx))
    · exact subgraph_edges_within Q.toSubgraph S (by intro x hx; exact hQS x (Q.mem_verts_toSubgraph.mp hx))

lemma two_contiguous_carrier_region {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    (hn : Fintype.card V=n) (hG : G.Connected) {r s a b t u c d w : V}
    (C : G.Walk r r) (hC : C.IsCycle) (hsize : 7 ≤ C.length)
    (A : G.Walk s a) (P : G.Walk a b) (B : G.Walk b t)
    (D : G.Walk u c) (Q : G.Walk c d) (E : G.Walk d w)
    (hP : (A.append (P.append B)).IsPath) (hQ : (D.append (Q.append E)).IsPath)
    (hPS : ∀ x ∈ P.support, x ∈ C.support) (hQS : ∀ x ∈ Q.support, x ∈ C.support)
    (hA : ∀ x ∈ A.support, x ∈ C.support → x=a) (hB : ∀ x ∈ B.support, x ∈ C.support → x=b)
    (hD : ∀ x ∈ D.support, x ∈ C.support → x=c) (hE : ∀ x ∈ E.support, x ∈ C.support → x=d)
    (hCP : Disjoint C.toSubgraph.edgeSet (A.append (P.append B)).toSubgraph.edgeSet)
    (hCQ : Disjoint C.toSubgraph.edgeSet (D.append (Q.append E)).toSubgraph.edgeSet)
    (hPQ : Disjoint (A.append (P.append B)).toSubgraph.edgeSet (D.append (Q.append E)).toSubgraph.edgeSet)
    (hcarrier : ∀ x ∈ C.support, ∀ y, G.Adj x y → C.toSubgraph.Adj x y ∨
      (A.append (P.append B)).toSubgraph.Adj x y ∨ (D.append (Q.append E)).toSubgraph.Adj x y) :
    ∃ F : Finset G.Subgraph, GoodDecomposition G F ∧ F.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ := by
  let S : Set V := {x | x ∈ C.support}
  have hcov := two_carrier_core_cover C A P B D Q E S (fun _ hx ↦ hx) hPS hQS hA hB hD hE hcarrier
  have hcap := two_carrier_boundary_capacity C A P B D Q E hP hQ S (fun _ hx ↦ hx)
    hPS hQS hA hB hD hE hcarrier
  have hs : 7 ≤ S.ncard := by
    change 7 ≤ ({x | x ∈ C.support} : Set V).ncard
    rw [cycle_support_ncard hC]
    exact hsize
  apply cycle_two_carrier_reduction hsmall hn hG C hC P Q
    hP.of_append_right.of_append_left hQ.of_append_right.of_append_left
    (hPS b P.end_mem_support) (hQS d Q.end_mem_support)
    (hCP.mono_right (middle_edges_subset A P B))
    (hCQ.mono_right (middle_edges_subset D Q E))
    (hPQ.mono (middle_edges_subset A P B) (middle_edges_subset D Q E)) S
    (fun _ hx ↦ hx) hPS hQS hcov hs hcap

lemma failure_no_two_contiguous_members {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    (hn : Fintype.card V=n) (hG : G.Connected)
    (hfail : ¬∃ F : Finset G.Subgraph, GoodDecomposition G F ∧ F.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊)
    {k : ℕ} (T : TrailFamily G k) (i j l : Fin k) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    {r a b c d : V} (C : G.Walk r r) (hC : C.IsCycle) (hsize : 7 ≤ C.length)
    (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (A : G.Walk (T.start j) a) (P : G.Walk a b) (B : G.Walk b (T.finish j))
    (D : G.Walk (T.start l) c) (Q : G.Walk c d) (E : G.Walk d (T.finish l))
    (hj : T.walk j=A.append (P.append B)) (hl : T.walk l=D.append (Q.append E))
    (hpj : (T.walk j).IsPath) (hpl : (T.walk l).IsPath)
    (hPS : ∀ x ∈ P.support, x ∈ C.support) (hQS : ∀ x ∈ Q.support, x ∈ C.support)
    (hA : ∀ x ∈ A.support, x ∈ C.support → x=a) (hB : ∀ x ∈ B.support, x ∈ C.support → x=b)
    (hD : ∀ x ∈ D.support, x ∈ C.support → x=c) (hE : ∀ x ∈ E.support, x ∈ C.support → x=d)
    (hother : ∀ q, q ≠ i → q ≠ j → q ≠ l → ∀ x ∈ (T.walk q).support, x ∉ C.support) : False := by
  apply hfail
  apply two_contiguous_carrier_region hsmall hn hG C hC hsize A P B D Q E
    (hj ▸ hpj) (hl ▸ hpl) hPS hQS hA hB hD hE
  · rw [←hi,←hj]
    exact T.disjoint hij
  · rw [←hi,←hl]
    exact T.disjoint hil
  · rw [←hj,←hl]
    exact T.disjoint hjl
  · intro x hx y hxy
    obtain ⟨q,hq⟩ := (T.cover s(x,y)).mp hxy
    by_cases hqi : q=i
    · subst q
      exact Or.inl (hi ▸ hq)
    by_cases hqj : q=j
    · subst q
      exact Or.inr (Or.inl (hj ▸ hq))
    by_cases hql : q=l
    · subst q
      exact Or.inr (Or.inr (hl ▸ hq))
    exact (hother q hqi hqj hql x (Walk.mem_support_of_adj_toSubgraph hq) hx).elim

end Erdos583TwoCarrierRegionDevelopment
