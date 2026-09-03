import Submission.ShortCycles

/-! Elementary sparsity bounds from an upper bound on cycle lengths. -/
open SimpleGraph
open scoped Classical
namespace Erdos184

lemma path_endpoint_edge_notMem {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hp : p.IsPath) (hl : 2 ≤ p.length) : s(u,v) ∉ p.edges := by
  cases p with
  | nil => simp at hl
  | @cons u a v h q =>
    have hq := (Walk.cons_isPath_iff h q).mp hp
    intro he
    simp only [Walk.edges_cons, List.mem_cons] at he
    rcases he with he | he
    · have hav : a = v := by
        rcases Sym2.eq_iff.mp he.symm with hh | hh
        · exact hh.2
        · exact hh.2.trans hh.1
      subst a
      have hnil := (Walk.isPath_iff_eq_nil q).mp hq.1
      subst q
      simp at hl
    · exact hq.2 (q.fst_mem_support_of_mem_edges he)

lemma path_close_isCycle {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hp : p.IsPath) (hl : 2 ≤ p.length) (h : G.Adj v u) :
    (p.cons h).IsCycle := by
  apply (Walk.cons_isCycle_iff p h).mpr
  exact ⟨hp, by simpa only [Sym2.eq_swap] using path_endpoint_edge_notMem p hp hl⟩

lemma longest_path_start_neighbors {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hp : p.IsPath)
    (hm : ∀ x y (q : G.Walk x y), q.IsPath → q.length ≤ p.length) :
    ∀ x, G.Adj u x → x ∈ p.support := by
  intro x hx
  by_contra hn
  have hh := hm x v (p.cons hx.symm) (hp.cons hn)
  simp only [Walk.length_cons] at hh
  omega

lemma exists_degree_le_of_cycle_length_bound {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (k : ℕ) (hk : 2 ≤ k)
    (hc : ∀ u (p : G.Walk u u), p.IsCycle → p.length ≤ k) :
    ∃ u, G.degree u ≤ k - 1 := by
  obtain ⟨u, v, p, hp, hm⟩ := Walk.exists_isPath_forall_isPath_length_le_length G
  have hs := longest_path_start_neighbors p hp hm
  have hindex : ∀ x : G.neighborSet u, ∃ i : ℕ, 1 ≤ i ∧ i < k ∧ p.getVert i = x.val := by
    intro x
    have hx := hs x.val x.property
    let q := p.takeUntil x.val hx
    have hq : q.IsPath := hp.takeUntil hx
    have hpos : 1 ≤ q.length := by
      have hne : u ≠ x.val := x.property.ne
      have hn : ¬q.Nil := Walk.not_nil_of_ne hne
      have := Walk.not_nil_iff_lt_length.mp hn
      omega
    have hlt : q.length < k := by
      by_cases h2 : 2 ≤ q.length
      · have hcy := path_close_isCycle q hq h2 x.property.symm
        have hh := hc x.val (q.cons x.property.symm) hcy
        simp only [Walk.length_cons] at hh
        omega
      · omega
    exact ⟨q.length, hpos, hlt, p.getVert_length_takeUntil hx⟩
  choose f hf using hindex
  let g : G.neighborSet u → {i // i ∈ Finset.Ico 1 k} := fun x =>
    ⟨f x, Finset.mem_Ico.mpr ⟨(hf x).1, (hf x).2.1⟩⟩
  have hg : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    have hh : f x = f y := congrArg Subtype.val hxy
    exact (hf x).2.2.symm.trans (hh ▸ (hf y).2.2)
  refine ⟨u, ?_⟩
  have hh := Fintype.card_le_of_injective g hg
  simpa only [Fintype.card_coe, Nat.card_Ico, SimpleGraph.card_neighborSet_eq_degree] using hh

/-- The elementary degeneracy bound for graphs of bounded circumference. -/
lemma edge_card_le_of_cycle_length_bound {V : Type*} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) (hk : 2 ≤ k)
    (hc : ∀ u (p : G.Walk u u), p.IsCycle → p.length ≤ k) :
    G.edgeFinset.card ≤ (k - 1) * Fintype.card V := by
  classical
  generalize hn : Fintype.card V = n
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
    cases isEmpty_or_nonempty V with
    | inl he =>
      haveI := he
      have hg : G = ⊥ := by ext u v; exact isEmptyElim u
      simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]
      simp [hg]
    | inr he =>
      haveI := he
      obtain ⟨v, hv⟩ := exists_degree_le_of_cycle_length_bound G k hk hc
      let A := G.induce ({v}ᶜ : Set V)
      have hnA : Fintype.card ({v}ᶜ : Set V) < n := by
        rw [← hn]
        exact Fintype.card_subtype_lt (x := v) (by simp)
      have hcA : ∀ u (p : A.Walk u u), p.IsCycle → p.length ≤ k := by
        intro u p hp
        let f : A →g G := (SimpleGraph.Embedding.induce ({v}ᶜ : Set V)).toHom
        have hh := hc u.val (p.map f) (hp.map Subtype.val_injective)
        simpa only [Walk.length_map] using hh
      have hb := ih _ hnA A hcA rfl
      have hcard : A.edgeFinset.card + G.degree v = G.edgeFinset.card := by
        change (G.induce {v}ᶜ).edgeFinset.card + G.degree v = _
        rw [SimpleGraph.card_edgeFinset_induce_compl_singleton,
          SimpleGraph.card_edgeFinset_deleteIncidenceSet,
          Nat.sub_add_cancel (G.degree_le_card_edgeFinset v)]
      have hn' : Fintype.card ({v}ᶜ : Set V) + 1 ≤ n := by omega
      calc
        G.edgeFinset.card = A.edgeFinset.card + G.degree v := hcard.symm
        _ ≤ (k - 1) * Fintype.card ({v}ᶜ : Set V) + (k - 1) := Nat.add_le_add hb hv
        _ = (k - 1) * (Fintype.card ({v}ᶜ : Set V) + 1) := by ring
        _ ≤ (k - 1) * n := Nat.mul_le_mul_left _ hn'

/-- Triangle pieces in a minimum pure-cycle decomposition satisfy a linear bound. -/
lemma minimum_triangle_subfamily_card_bound {V : Type*} [Fintype V]
    (G : SimpleGraph V) (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D)
    (hm : ∀ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      IsDecomposition G E → D.card ≤ E.card)
    (S : Finset G.Subgraph) (hs : S ⊆ D)
    (htri : ∀ H ∈ S, H.edgeSet.ncard = 3) :
    3 * S.card ≤ 2 * Fintype.card V := by
  have hbound := edge_card_le_of_cycle_length_bound (unionPieces G S) 3 (by omega)
    (fun _ p hp => (minimum_triangle_subfamily_cycles G D hc hd hm S hs htri p hp).le)
  have hdis : Set.PairwiseDisjoint (S : Set G.Subgraph) (fun H => H.edgeSet) :=
    fun _ hH _ hK hHK => hd.1 (hs hH) (hs hK) hHK
  have hsum := unionPieces_edge_card G S hdis
  have heq : (∑ H ∈ S, H.edgeSet.ncard) = 3 * S.card := by
    simp only [Finset.sum_congr rfl htri, Finset.sum_const, smul_eq_mul, mul_comm]
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hsum hbound ⊢
  rw [hsum, heq] at hbound
  exact hbound

end Erdos184
