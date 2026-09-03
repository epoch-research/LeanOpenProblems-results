import Submission.Work

/-! Odd cycle regions with a single contiguous carrier. -/
namespace Erdos583OddContiguousRegionDevelopment
open SimpleGraph Erdos583Work Erdos583Work.VertexCritical
open scoped Classical
set_option maxHeartbeats 1800000

variable {V : Type*} {G : SimpleGraph V}

lemma remove_first_tail {a b r : V} (C : G.Walk r r) (B : G.Walk a b)
    (hp : B.IsPath) (hn : ¬B.Nil)
    (hB : ∀ x ∈ B.support, x ∈ C.support → x=a) :
    ∃ v, ∃ h : G.Adj a v, ∃ R : G.Walk v b,
      B=Walk.cons h R ∧ ∀ x ∈ R.support, x ∉ C.support := by
  cases B with
  | nil => exact (hn Walk.Nil.nil).elim
  | @cons _ v _ h R =>
    refine ⟨v,h,R,rfl,?_⟩
    intro x hx hxC
    have he := hB x (List.mem_cons_of_mem _ hx) hxC
    exact (Walk.cons_isPath_iff h R).mp hp |>.2 (he ▸ hx)

lemma remove_last_tail {a b r : V} (C : G.Walk r r) (A : G.Walk a b)
    (hp : A.IsPath) (hn : ¬A.Nil)
    (hA : ∀ x ∈ A.support, x ∈ C.support → x=b) :
    ∃ u, ∃ L : G.Walk a u, ∃ h : G.Adj u b,
      A=L.concat h ∧ ∀ x ∈ L.support, x ∉ C.support := by
  let h := A.adj_penultimate hn
  have he := A.concat_dropLast h
  have hnend := (Walk.concat_isPath_iff h).mp (he.symm ▸ hp) |>.2
  refine ⟨A.penultimate,A.dropLast,h,he.symm,?_⟩
  intro x hx hxC
  have hxA : x ∈ A.support := by
    rw [←he,Walk.support_concat,List.concat_eq_append,List.mem_append]
    exact Or.inl hx
  have hxb := hA x hxA hxC
  exact hnend (hxb ▸ hx)

lemma failure_no_single_tail {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {r a b t : Fin n} (C : G.Walk r r) (hC : C.IsCycle)
    (hodd : Odd C.length) (hsize : C.length+2 ≤ n)
    (P : G.Walk a b) (B : G.Walk b t) (hB : B.IsPath)
    (hP : ∀ x ∈ P.support, x ∈ C.support)
    (hBon : ∀ x ∈ B.support, x ∈ C.support → x=b)
    (hcarrier : ∀ x ∈ C.support, ∀ y, G.Adj x y →
      C.toSubgraph.Adj x y ∨ (P.append B).toSubgraph.Adj x y) : False := by
  let S : Set (Fin n) := {x | x ∈ C.support}
  have hSc : S.ncard=C.length := cycle_support_ncard hC
  have hsum : S.ncard+Sᶜ.ncard=n := by simpa using S.ncard_add_ncard_compl
  have hcs : 2 ≤ Sᶜ.ncard := by omega
  cases B with
  | nil =>
    have hclosed : S=Set.univ := by
      apply TrailBudget.connected_closed_set hG S ⟨r,C.start_mem_support⟩
      intro x y hxy hx
      rcases hcarrier x hx y hxy with he|he
      · exact Walk.mem_support_of_adj_toSubgraph (C.toSubgraph.symm he)
      · simp only [Walk.append_nil] at he
        exact hP y (Walk.mem_support_of_adj_toSubgraph (P.toSubgraph.symm he))
    simp [hclosed] at hcs
  | @cons _ v _ h R =>
    have hR : ∀ x ∈ R.support, x ∉ C.support := by
      intro x hx hxC
      have he := hBon x (List.mem_cons_of_mem _ hx) hxC
      exact (Walk.cons_isPath_iff h R).mp hB |>.2 (he ▸ hx)
    have heven := hsmall.bridge_cut_even hG hfail S h (hP b P.end_mem_support)
      (hR v R.start_mem_support) (fun x hx y hy hxy ↦ ?_)
      (by rw [hSc]; have hh := hC.three_le_length; omega) hcs
    · rw [hSc] at heven
      exact (Nat.not_even_iff_odd.mpr hodd) heven.1
    · rcases hcarrier x hx y hxy with hc|hc
      · exact (hy (Walk.mem_support_of_adj_toSubgraph (C.toSubgraph.symm hc))).elim
      · have hh : s(x,y) ∈ P.toSubgraph.edgeSet ∨ s(x,y)=s(b,v) ∨
            s(x,y) ∈ R.toSubgraph.edgeSet := by
          change s(x,y) ∈ (P.append (Walk.cons h R)).toSubgraph.edgeSet at hc
          simpa only [Walk.edgeSet_toSubgraph,Set.mem_setOf_eq,Walk.edges_append,
            Walk.edges_cons,List.mem_append,List.mem_cons] using hc
        rcases hh with hh|hh|hh
        · exact (hy (hP y (Walk.mem_support_of_adj_toSubgraph (P.toSubgraph.symm hh)))).elim
        · rcases Sym2.eq_iff.mp hh with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
          · exact ⟨rfl,rfl⟩
          · exact (hR _ R.start_mem_support hx).elim
        · exact (hR x (Walk.mem_support_of_adj_toSubgraph hh) hx).elim

lemma failure_no_contiguous_region {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {r s a b t : Fin n} (C : G.Walk r r) (hC : C.IsCycle)
    (hlen : 5 ≤ C.length) (hodd : Odd C.length) (hsize : C.length+2 ≤ n)
    (A : G.Walk s a) (P : G.Walk a b) (B : G.Walk b t)
    (hp : (A.append (P.append B)).IsPath)
    (hA : ∀ x ∈ A.support, x ∈ C.support → x=a)
    (hB : ∀ x ∈ B.support, x ∈ C.support → x=b)
    (hP : ∀ x ∈ P.support, x ∈ C.support)
    (hd : Disjoint (A.append (P.append B)).toSubgraph.edgeSet C.toSubgraph.edgeSet)
    (hcarrier : ∀ x ∈ C.support, ∀ y, G.Adj x y →
      C.toSubgraph.Adj x y ∨ (A.append (P.append B)).toSubgraph.Adj x y) : False := by
  by_cases hnA : A.Nil
  · cases A with
    | nil =>
      exact failure_no_single_tail hsmall hG hfail C hC hodd hsize P B
        hp.of_append_right.of_append_right hP hB (by simpa only [Walk.nil_append] using hcarrier)
    | cons h R => exact (Walk.not_nil_cons hnA).elim
  by_cases hnB : B.Nil
  · cases B with
    | nil =>
      apply failure_no_single_tail hsmall hG hfail C hC hodd hsize P.reverse A.reverse
        hp.of_append_left.reverse
      · simpa only [Walk.support_reverse,List.mem_reverse] using hP
      · simpa only [Walk.support_reverse,List.mem_reverse] using hA
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

end Erdos583OddContiguousRegionDevelopment
