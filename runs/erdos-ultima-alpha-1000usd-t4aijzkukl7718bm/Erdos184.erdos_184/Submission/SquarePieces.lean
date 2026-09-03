import Submission.ShortCycles

/-! Square pieces in minimum decompositions. This is an auxiliary counting
estimate, not a uniform decomposition theorem. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.SquarePieces
open Critical Rigidity MaximumCycles ShortCycles
set_option maxHeartbeats 2000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma cycle_piece_four_le_of_coloring (c : V → Bool)
    (hc : ∀ ⦃x y⦄, G.Adj x y → c x ≠ c y)
    (H : G.Subgraph) (hH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) :
    4 ≤ H.coe.edgeFinset.card := by
  have h3 := cycle_piece_three_le_edges H hH
  by_contra! h4
  have he : H.coe.edgeFinset.card = 3 := by omega
  obtain ⟨v⟩ := hH.1.nonempty
  have hd : (H.coe.neighborFinset v).card = 2 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using hH.2 v
  obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp (show 1 < (H.coe.neighborFinset v).card by omega)
  have hvx : H.Adj v.val x.val := (H.coe.mem_neighborFinset v x).mp hx
  have hvy : H.Adj v.val y.val := (H.coe.mem_neighborFinset v y).mp hy
  have hxy' : H.Adj x.val y.val := triangle_piece_adj H (by
    simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hH.2) he x.property y.property
    (fun h => hxy (Subtype.ext h))
  have h1 := hc (H.adj_sub hvx)
  have h2 := hc (H.adj_sub hvy)
  have h3 := hc (H.adj_sub hxy')
  cases hv : c v.val <;> cases hx : c x.val <;> cases hy : c y.val <;> simp_all

lemma rigid_of_edges_eq_four_mul_number (c : V → Bool)
    (hc : ∀ ⦃x y⦄, G.Adj x y → c x ≠ c y)
    (he : G.edgeFinset.card = 4 * number G) : CycleRigid G := by
  intro D hD hdec
  have hb : 4 * D.card ≤ (subfamilyGraph D).edgeFinset.card := by
    rw [subfamilyGraph_card_edges D hdec.1]
    calc
      _ = ∑ _H ∈ D, 4 := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun H hH => cycle_piece_four_le_of_coloring c hc H (hD H hH))
  have hg : subfamilyGraph D = G :=
    SimpleGraph.edgeSet_injective ((subfamilyGraph_edges D).trans hdec.2)
  rw [hg,he] at hb
  have hn := number_le D (fun H hH => Or.inl (by
    simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hD H hH)) hdec
  omega

lemma square_subfamily_colored_card_le (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdec : IsDecomposition G D) (hcD : D.card = number G)
    (A : Finset G.Subgraph) (hAD : A ⊆ D)
    (hsq : ∀ H ∈ A, H.coe.edgeFinset.card = 4)
    (c : V → Bool) (hcolor : ∀ H ∈ A, ∀ ⦃x y⦄, H.Adj x y → c x ≠ c y) :
    A.card ≤ Fintype.card V := by
  have hD' : ∀ H ∈ D, IsCycleOrEdge H.coe := fun H hH => Or.inl (by
    simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hD H hH)
  have hn := Subfamilies.minimal_subfamily_number D hD' hdec hcD A hAD
  have hd : Set.PairwiseDisjoint (A : Set G.Subgraph) (fun H => H.edgeSet) :=
    fun _ hH _ hK hne => hdec.1 (hAD hH) (hAD hK) hne
  have hc : ∀ ⦃x y⦄, (subfamilyGraph A).Adj x y → c x ≠ c y := by
    intro x y hxy
    change s(x,y) ∈ (subfamilyGraph A).edgeSet at hxy
    rw [subfamilyGraph_edges] at hxy
    obtain ⟨H,hH,hxy⟩ := Set.mem_iUnion₂.mp hxy
    exact hcolor H hH hxy
  have hr : CycleRigid (subfamilyGraph A) := by
    apply rigid_of_edges_eq_four_mul_number c hc
    rw [hn,subfamilyGraph_card_edges A hd]
    calc
      _ = ∑ _H ∈ A, 4 := Finset.sum_congr rfl hsq
      _ = _ := by simp [Nat.mul_comm]
  have he := cycle_subfamily_even A (fun H hH => hD H (hAD hH)) hd
  have hb := CycleRings.rigid_number_le_support hr (by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using he)
  rw [hn] at hb
  exact hb.trans (by simpa only [Nat.card_eq_fintype_card] using Set.ncard_le_card (subfamilyGraph A).support)

noncomputable def fixedColoringEquiv (S : Set V) (c : V → Bool) :
    {f : V → Bool // ∀ v ∈ S, f v = c v} ≃ ({v : V // v ∉ S} → Bool) where
  toFun f v := f.val v.val
  invFun g := ⟨fun v => if h : v ∈ S then c v else g ⟨v,h⟩, by
    intro v hv
    simp [hv]⟩
  left_inv f := by
    apply Subtype.ext
    funext v
    by_cases hv : v ∈ S
    · simp [hv,f.property v hv]
    · simp [hv]
  right_inv g := by
    funext v
    simp [v.property]

lemma fixed_colorings_card (S : Set V) (c : V → Bool) :
    (Finset.univ.filter (fun f : V → Bool => ∀ v ∈ S, f v = c v)).card =
      2 ^ Fintype.card {v : V // v ∉ S} := by
  rw [← Fintype.card_subtype]
  have h := Fintype.card_congr (fixedColoringEquiv S c)
  simpa only [Fintype.card_fun,Fintype.card_bool] using h

omit [Fintype V] in
lemma four_cycle_coloring {u : V} (p : G.Walk u u) (hp : p.IsCycle)
    (hlen : p.length = 4) :
    ∃ c : V → Bool, ∀ ⦃x y⦄, p.toSubgraph.Adj x y → c x ≠ c y := by
  cases p with
  | nil => simp at hlen
  | @cons a b _ hab p =>
    cases p with
    | nil => simp at hlen
    | @cons _ c _ hbc p =>
      cases p with
      | nil => simp at hlen
      | @cons _ d _ hcd p =>
        cases p with
        | nil => simp at hlen
        | @cons _ e _ hde p =>
          have hz : p.length = 0 := by simpa using hlen
          have hea : e = u := p.eq_of_length_eq_zero hz
          subst e
          have hn := Walk.length_eq_zero_iff.mp hz
          cases hn
          have hnod := hp.support_nodup
          simp only [Walk.support_cons,Walk.support_nil,List.tail_cons,List.nodup_cons,
            List.mem_cons,not_or] at hnod
          refine ⟨fun x => decide (x = u ∨ x = c),?_⟩
          intro x y hxy
          change s(x,y) ∈ (Walk.cons hab (.cons hbc (.cons hcd (.cons hde .nil)))).toSubgraph.edgeSet at hxy
          rw [Walk.mem_edges_toSubgraph] at hxy
          simp only [Walk.edges_cons,Walk.edges_nil,List.mem_cons,List.not_mem_nil,or_false,
            Sym2.eq_iff] at hxy
          rcases hxy with (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) | (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) |
            (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) | (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
          all_goals simp_all [Ne.symm]

lemma square_piece_coloring (H : G.Subgraph)
    (hH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hsq : H.coe.edgeFinset.card = 4) :
    ∃ c : V → Bool, ∀ ⦃x y⦄, H.Adj x y → c x ≠ c y := by
  obtain ⟨v⟩ := hH.1.nonempty
  obtain ⟨p,hp,hpH⟩ := LongRing.regular_cycle_walk_at H hH.1 (by
    simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hH.2) v.val v.property
  have hl := cycle_edge_count G hp
  rw [hpH,subgraph_edge_card,hsq] at hl
  obtain ⟨c,hc⟩ := four_cycle_coloring p hp hl.symm
  refine ⟨c,?_⟩
  intro x y hxy
  exact hc (hpH.symm ▸ hxy)

lemma square_subfamily_card_le (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdec : IsDecomposition G D) (hcD : D.card = number G)
    (A : Finset G.Subgraph) (hAD : A ⊆ D)
    (hsq : ∀ H ∈ A, H.coe.edgeFinset.card = 4) :
    A.card ≤ 8 * Fintype.card V := by
  by_cases hA : A = ∅
  · simp [hA]
  have hfour (H : G.Subgraph) (hH : H ∈ A) : Fintype.card H.verts = 4 := by
    have he := regular_two_card_edges H (hD H (hAD hH)).2
    rw [subgraph_edge_card] at he
    change H.coe.edgeFinset.card = Nat.card H.verts at he
    rw [← Nat.card_eq_fintype_card,← he,hsq H hH]
  have hn : 4 ≤ Fintype.card V := by
    obtain ⟨H,hH⟩ := Finset.nonempty_iff_ne_empty.mpr hA
    simpa only [hfour H hH] using Fintype.card_subtype_le (fun v => v ∈ H.verts)
  let good (c : V → Bool) := A.filter (fun H => ∀ ⦃x y⦄, H.Adj x y → c x ≠ c y)
  have hbound (c : V → Bool) : (good c).card ≤ Fintype.card V := by
    apply square_subfamily_colored_card_le D hD hdec hcD (good c)
      ((Finset.filter_subset _ _).trans hAD)
      (fun H hH => hsq H (Finset.mem_filter.mp hH).1) c
    exact fun H hH => (Finset.mem_filter.mp hH).2
  have hcount (H : G.Subgraph) (hH : H ∈ A) :
      2 * 2 ^ (Fintype.card V - 4) ≤
        (Finset.univ.filter (fun c : V → Bool => ∀ ⦃x y⦄, H.Adj x y → c x ≠ c y)).card := by
    obtain ⟨c,hc⟩ := square_piece_coloring H (hD H (hAD hH)) (hsq H hH)
    let B (d : V → Bool) := Finset.univ.filter (fun f : V → Bool => ∀ v ∈ H.verts, f v = d v)
    have hsub (d : V → Bool) (hd : ∀ ⦃x y⦄, H.Adj x y → d x ≠ d y) : B d ⊆
        Finset.univ.filter (fun f : V → Bool => ∀ ⦃x y⦄, H.Adj x y → f x ≠ f y) := by
      intro f hf
      have hf' := (Finset.mem_filter.mp hf).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
      intro x y hxy
      rw [hf' x (H.edge_vert hxy),hf' y (H.edge_vert hxy.symm)]
      exact hd hxy
    have hneg : ∀ ⦃x y⦄, H.Adj x y → (!c x) ≠ (!c y) := by
      intro x y hxy heq
      exact hc hxy (by simpa only [Bool.not_not] using congrArg Bool.not heq)
    have hdis : Disjoint (B c) (B (fun v => !c v)) := by
      apply Finset.disjoint_left.mpr
      intro f hf hg
      obtain ⟨v⟩ := (hD H (hAD hH)).1.nonempty
      have h1 := (Finset.mem_filter.mp hf).2 v.val v.property
      have h2 := (Finset.mem_filter.mp hg).2 v.val v.property
      have h3 : c v.val = !c v.val := h1.symm.trans h2
      exact (show ∀ b : Bool, b ≠ !b by decide) (c v.val) h3
    have hb := Finset.card_le_card (Finset.union_subset (hsub c hc) (hsub (fun v => !c v) hneg))
    rw [Finset.card_union_of_disjoint hdis] at hb
    simp only [B,fixed_colorings_card,Fintype.card_subtype_compl,hfour H hH] at hb
    omega
  have hl : A.card * (2 * 2 ^ (Fintype.card V - 4)) ≤
      ∑ c : V → Bool, (good c).card := by
    calc
      _ = ∑ H ∈ A, 2 * 2 ^ (Fintype.card V - 4) := by simp
      _ ≤ ∑ H ∈ A, (Finset.univ.filter (fun c : V → Bool =>
          ∀ ⦃x y⦄, H.Adj x y → c x ≠ c y)).card := Finset.sum_le_sum hcount
      _ = _ := by
        simp only [good,Finset.card_filter]
        rw [Finset.sum_comm]
  have hu : (∑ c : V → Bool, (good c).card) ≤ 2 ^ Fintype.card V * Fintype.card V := by
    calc
      _ ≤ ∑ _c : V → Bool, Fintype.card V := Finset.sum_le_sum (fun c _ => hbound c)
      _ = _ := by simp
  have hp : 2 ^ Fintype.card V = 16 * 2 ^ (Fintype.card V - 4) := by
    conv_lhs => rw [← Nat.sub_add_cancel hn,pow_add]
    norm_num
    omega
  rw [hp] at hu
  have hpos : 0 < 2 ^ (Fintype.card V - 4) := by positivity
  nlinarith

lemma five_mul_number_le_edges_add_nine_card (heven : ∀ v, Even (G.degree v)) :
    5 * number G ≤ G.edgeFinset.card + 9 * Fintype.card V := by
  obtain ⟨D,hD,hdec,hcard⟩ := minimum_cycles heven
  let A := D.filter (fun H => H.coe.edgeFinset.card = 3)
  let B := D.filter (fun H => H.coe.edgeFinset.card = 4)
  have ht := triangle_subfamily_twice_card_le D hD hdec hcard A
    (Finset.filter_subset _ _) (fun H hH => (Finset.mem_filter.mp hH).2)
  have hs := square_subfamily_card_le D hD hdec hcard B
    (Finset.filter_subset _ _) (fun H hH => (Finset.mem_filter.mp hH).2)
  have he : G.edgeFinset.card = ∑ H ∈ D, H.coe.edgeFinset.card := by
    have hg : subfamilyGraph D = G :=
      SimpleGraph.edgeSet_injective ((subfamilyGraph_edges D).trans hdec.2)
    have h := subfamilyGraph_card_edges D hdec.1
    rw [hg] at h
    exact h
  have hfive : 5 * D.card ≤ G.edgeFinset.card + 2 * A.card + B.card := by
    calc
      _ = ∑ _H ∈ D, 5 := by simp [Nat.mul_comm]
      _ ≤ ∑ H ∈ D, (H.coe.edgeFinset.card +
          (if H.coe.edgeFinset.card = 3 then 2 else 0) +
          (if H.coe.edgeFinset.card = 4 then 1 else 0)) := by
        apply Finset.sum_le_sum
        intro H hH
        have h3 := cycle_piece_three_le_edges H (hD H hH)
        split_ifs <;> omega
      _ = _ := by
        rw [Finset.sum_add_distrib,Finset.sum_add_distrib,← he]
        simp [A,B,Finset.sum_ite,Nat.mul_comm]
  omega

#print axioms square_subfamily_card_le
#print axioms five_mul_number_le_edges_add_nine_card
end Erdos184Work.SquarePieces
