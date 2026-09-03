import FormalConjecturesUtil

/-! The extremal exponent of the complete bipartite graph `K₃,₃` with one edge removed. -/

open SimpleGraph Filter Asymptotics Finset

namespace Erdos713Minus

def D33 : SimpleGraph (Fin 3 ⊕ Fin 3) where
  Adj u v := match u, v with
    | Sum.inl i, Sum.inr j => i ≠ 2 ∨ j ≠ 2
    | Sum.inr j, Sum.inl i => i ≠ 2 ∨ j ≠ 2
    | _, _ => False
  symm := by intro u v; cases u <;> cases v <;> simp
  loopless := by intro v; cases v <;> simp

theorem contained_of_maps {V : Type*} (G : SimpleGraph V) (a b : Fin 3 → V)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hab : ∀ i j, a i ≠ b j)
    (hAdj : ∀ i j, i ≠ 2 ∨ j ≠ 2 → G.Adj (a i) (b j)) : D33 ⊑ G := by
  refine ⟨⟨⟨Sum.elim a b, ?_⟩, ?_⟩⟩
  · intro u v huv
    cases u with
    | inl i =>
      cases v with
      | inl j => exact huv.elim
      | inr j => exact hAdj i j huv
    | inr j =>
      cases v with
      | inl i => exact (hAdj i j huv).symm
      | inr i => exact huv.elim
  · intro u v huv
    change Sum.elim a b u = Sum.elim a b v at huv
    cases u with
    | inl i =>
      cases v with
      | inl j => exact congrArg Sum.inl (ha huv)
      | inr j => exact (hab i j huv).elim
    | inr j =>
      cases v with
      | inl i => exact (hab i j huv.symm).elim
      | inr i => exact congrArg Sum.inr (hb huv)

theorem triple_injective {V : Type*} {u v w : V} (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    Function.Injective ![u, v, w] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

open scoped Classical in
theorem third_common_neighbor {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v x y : V} (hc : 3 ≤ Fintype.card (G.commonNeighbors u v)) :
    ∃ z, G.Adj u z ∧ G.Adj v z ∧ z ≠ x ∧ z ≠ y := by
  classical
  have hsmall : ({x, y} : Finset V).card < (G.commonNeighbors u v).toFinset.card := by
    rw [Set.toFinset_card]
    have hh : ({x, y} : Finset V).card ≤ 2 := by simpa using card_insert_le x ({y} : Finset V)
    omega
  obtain ⟨z, hz, hzne⟩ := exists_mem_notMem_of_card_lt_card hsmall
  have hz' : z ∈ G.commonNeighbors u v := by simpa using hz
  have hneq : z ≠ x ∧ z ≠ y := by simpa using hzne
  exact ⟨z, hz'.1, hz'.2, hneq.1, hneq.2⟩

open scoped Classical in
theorem rectangle_has_light_pair {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hBip : G.IsBipartite) (hfree : D33.Free G)
    {u v x y : V} (huv : u ≠ v) (hxy : x ≠ y)
    (hux : G.Adj u x) (hvx : G.Adj v x) (huy : G.Adj u y) (hvy : G.Adj v y) :
    Fintype.card (G.commonNeighbors u v) ≤ 2 ∨ Fintype.card (G.commonNeighbors x y) ≤ 2 := by
  classical
  by_contra hh
  push_neg at hh
  obtain ⟨z, huz, hvz, hzx, hzy⟩ := third_common_neighbor G (x := x) (y := y) hh.1
  obtain ⟨w, hxw, hyw, hwu, hwv⟩ := third_common_neighbor G (x := u) (y := v) hh.2
  obtain ⟨χ⟩ := hBip
  have hcolv : χ v = χ u := by have h1 := χ.valid hux; have h2 := χ.valid hvx; omega
  have hcolw : χ w = χ u := by have h1 := χ.valid hux; have h2 := χ.valid hxw; omega
  have hcolx : χ x ≠ χ u := (χ.valid hux).symm
  have hcoly : χ y ≠ χ u := (χ.valid huy).symm
  have hcolz : χ z ≠ χ u := (χ.valid huz).symm
  apply hfree
  apply contained_of_maps G ![u, v, w] ![x, y, z]
    (triple_injective huv hwu.symm hwv.symm) (triple_injective hxy hzx.symm hzy.symm)
  · intro i j he
    have hci : χ (![u, v, w] i) = χ u := by fin_cases i <;> first | rfl | assumption
    have hcj : χ (![x, y, z] j) ≠ χ u := by fin_cases j <;> assumption
    exact hcj (he ▸ hci)
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [adj_comm]

abbrev Pair (V : Type*) := {p : V × V // p.1 ≠ p.2}

def Rectangle {V : Type*} (G : SimpleGraph V) (p q : Pair V) : Prop :=
  G.Adj p.val.1 q.val.1 ∧ G.Adj p.val.2 q.val.1 ∧
    G.Adj p.val.1 q.val.2 ∧ G.Adj p.val.2 q.val.2

theorem rectangle_symm {V : Type*} {G : SimpleGraph V} {p q : Pair V}
    (h : Rectangle G p q) : Rectangle G q p :=
  ⟨h.1.symm, h.2.2.1.symm, h.2.1.symm, h.2.2.2.symm⟩

open scoped Classical in
theorem row_card {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (p : Pair V) :
    ((univ : Finset (Pair V)).bipartiteAbove (Rectangle G) p).card =
      (Fintype.card (G.commonNeighbors p.val.1 p.val.2)).descFactorial 2 := by
  classical
  let e : ↥((univ : Finset (Pair V)).bipartiteAbove (Rectangle G) p) ≃
      (Fin 2 ↪ G.commonNeighbors p.val.1 p.val.2) :=
    { toFun := fun q =>
        ⟨![⟨q.val.val.1, ((mem_bipartiteAbove _).mp q.prop).2.1,
            ((mem_bipartiteAbove _).mp q.prop).2.2.1⟩,
          ⟨q.val.val.2, ((mem_bipartiteAbove _).mp q.prop).2.2.2.1,
            ((mem_bipartiteAbove _).mp q.prop).2.2.2.2⟩], by
          intro i j hij
          fin_cases i <;> fin_cases j
          · rfl
          · exact (q.val.prop (congrArg Subtype.val hij)).elim
          · exact (q.val.prop (congrArg Subtype.val hij).symm).elim
          · rfl⟩
      invFun := fun f =>
        ⟨⟨((f 0).val, (f 1).val), fun he =>
          (show (0 : Fin 2) ≠ 1 by decide) (f.injective (Subtype.ext he))⟩,
          (mem_bipartiteAbove _).mpr ⟨mem_univ _, (f 0).prop.1, (f 0).prop.2,
            (f 1).prop.1, (f 1).prop.2⟩⟩
      left_inv := by intro q; rfl
      right_inv := by intro f; ext i; fin_cases i <;> rfl }
  rw [← Fintype.card_coe, Fintype.card_congr e, Fintype.card_embedding_eq, Fintype.card_fin]

open scoped Classical in
theorem sum_rows_le_of_light {I : Type*} [Fintype I] (r : I → I → Prop)
    (P : I → Prop) (k : ℕ) (hsymm : ∀ i j, r i j → r j i)
    (hlight : ∀ i j, r i j → P i ∨ P j)
    (hrow : ∀ i, P i → ((univ : Finset I).bipartiteAbove r i).card ≤ k) :
    ∑ i, ((univ : Finset I).bipartiteAbove r i).card ≤ 2 * k * Fintype.card I := by
  classical
  let r₁ : I → I → Prop := fun i j => r i j ∧ P i
  let r₂ : I → I → Prop := fun i j => r i j ∧ P j
  have hcov (i : I) : ((univ : Finset I).bipartiteAbove r i).card ≤
      ((univ : Finset I).bipartiteAbove r₁ i).card +
      ((univ : Finset I).bipartiteAbove r₂ i).card := by
    apply (card_le_card ?_).trans (card_union_le _ _)
    intro j hj
    have hr : r i j := ((mem_bipartiteAbove r).mp hj).2
    rcases hlight i j hr with hi | hj'
    · exact mem_union_left _ ((mem_bipartiteAbove r₁).mpr ⟨mem_univ _, hr, hi⟩)
    · exact mem_union_right _ ((mem_bipartiteAbove r₂).mpr ⟨mem_univ _, hr, hj'⟩)
  have hrow₁ (i : I) : ((univ : Finset I).bipartiteAbove r₁ i).card ≤ k := by
    by_cases hi : P i
    · apply (card_le_card ?_).trans (hrow i hi)
      intro j hj
      exact (mem_bipartiteAbove r).mpr ⟨mem_univ _, ((mem_bipartiteAbove r₁).mp hj).2.1⟩
    · have he : (univ : Finset I).bipartiteAbove r₁ i = ∅ := by
        ext j
        simp [r₁, bipartiteAbove, hi]
      simp [he]
  have hcol₂ (j : I) : ((univ : Finset I).bipartiteBelow r₂ j).card ≤ k := by
    by_cases hj : P j
    · apply (card_le_card ?_).trans (hrow j hj)
      intro i hi
      exact (mem_bipartiteAbove r).mpr ⟨mem_univ _,
        hsymm i j ((mem_bipartiteBelow r₂).mp hi).2.1⟩
    · have he : (univ : Finset I).bipartiteBelow r₂ j = ∅ := by
        ext i
        simp [r₂, bipartiteBelow, hj]
      simp [he]
  calc
    ∑ i, ((univ : Finset I).bipartiteAbove r i).card ≤
        ∑ i, (((univ : Finset I).bipartiteAbove r₁ i).card +
          ((univ : Finset I).bipartiteAbove r₂ i).card) := sum_le_sum fun i _ => hcov i
    _ = (∑ i, ((univ : Finset I).bipartiteAbove r₁ i).card) +
        (∑ j, ((univ : Finset I).bipartiteBelow r₂ j).card) := by
      rw [sum_add_distrib, sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow r₂]
    _ ≤ (∑ _ : I, k) + (∑ _ : I, k) :=
      Nat.add_le_add (sum_le_sum fun i _ => hrow₁ i) (sum_le_sum fun j _ => hcol₂ j)
    _ = 2 * k * Fintype.card I := by simp only [sum_const, card_univ, Nat.nsmul_eq_mul]; ring

open scoped Classical in
theorem sum_rectangles_le {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hBip : G.IsBipartite) (hfree : D33.Free G) :
    ∑ p : Pair V, ((univ : Finset (Pair V)).bipartiteAbove (Rectangle G) p).card ≤
      4 * Fintype.card (Pair V) := by
  apply sum_rows_le_of_light (Rectangle G)
    (fun p => Fintype.card (G.commonNeighbors p.val.1 p.val.2) ≤ 2) 2
    (fun _ _ h => rectangle_symm h)
  · intro p q h
    exact rectangle_has_light_pair G hBip hfree p.prop q.prop h.1 h.2.1 h.2.2.1 h.2.2.2
  · intro p hp
    rw [row_card]
    exact (Nat.descFactorial_le 2 hp).trans (by decide)

theorem le_descFactorial_two_add_one (n : ℕ) : n ≤ n.descFactorial 2 + 1 := by
  by_cases hn : n ≤ 1
  · omega
  · have hpos : 0 < n - 1 := by omega
    have hh := Nat.le_mul_of_pos_left n hpos
    simpa [Nat.descFactorial_succ] using hh.trans (Nat.le_succ _)

open scoped Classical in
theorem sum_common_le {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hBip : G.IsBipartite) (hfree : D33.Free G) :
    ∑ p : Pair V, Fintype.card (G.commonNeighbors p.val.1 p.val.2) ≤ 5 * Fintype.card V ^ 2 := by
  have hh : (∑ p : Pair V, Fintype.card (G.commonNeighbors p.val.1 p.val.2)) ≤
      (∑ p : Pair V, ((univ : Finset (Pair V)).bipartiteAbove (Rectangle G) p).card) +
        Fintype.card (Pair V) := by
    calc
      _ ≤ ∑ p : Pair V, (((univ : Finset (Pair V)).bipartiteAbove (Rectangle G) p).card + 1) := by
        apply sum_le_sum
        intro p _
        rw [row_card]
        exact le_descFactorial_two_add_one _
      _ = _ := by simp [sum_add_distrib]
  have hsum := sum_rectangles_le G hBip hfree
  have hc : Fintype.card (Pair V) ≤ Fintype.card V ^ 2 := by
    simpa only [Fintype.card_prod, pow_two] using Fintype.card_subtype_le
      (fun p : V × V => p.1 ≠ p.2)
  omega

open scoped Classical in
theorem sum_degree_sq_le {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hBip : G.IsBipartite) (hfree : D33.Free G) :
    ∑ v, G.degree v ^ 2 ≤ 6 * Fintype.card V ^ 2 := by
  classical
  let r : V → V × V → Prop := fun x p => G.Adj x p.1 ∧ G.Adj x p.2
  have hAbove (x : V) : ((univ : Finset (V × V)).bipartiteAbove r x).card = G.degree x ^ 2 := by
    have hs : (univ : Finset (V × V)).bipartiteAbove r x =
        G.neighborFinset x ×ˢ G.neighborFinset x := by
      ext p
      simp [r, bipartiteAbove]
    rw [hs, card_product, card_neighborFinset_eq_degree, pow_two]
  have hBelow (p : V × V) : ((univ : Finset V).bipartiteBelow r p).card =
      Fintype.card (G.commonNeighbors p.1 p.2) := by
    have hs : (univ : Finset V).bipartiteBelow r p = (G.commonNeighbors p.1 p.2).toFinset := by
      ext x
      simp [r, bipartiteBelow, mem_commonNeighbors, adj_comm]
    rw [hs, Set.toFinset_card]
  have hsum := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (r := r) (s := (univ : Finset V)) (t := (univ : Finset (V × V)))
  simp_rw [hAbove, hBelow] at hsum
  rw [hsum]
  have hdiag : Fintype.card {p : V × V // ¬p.1 ≠ p.2} = Fintype.card V := by
    apply Fintype.card_congr
    refine ⟨fun p => p.val.1, fun v => ⟨(v, v), by simp⟩, ?_, ?_⟩
    · intro p
      apply Subtype.ext
      exact Prod.ext rfl (not_not.mp p.prop)
    · intro v; rfl
  have hdiagSum : (∑ p : {p : V × V // ¬p.1 ≠ p.2},
      Fintype.card (G.commonNeighbors p.val.1 p.val.2)) ≤ Fintype.card V ^ 2 := by
    calc
      _ ≤ ∑ _ : {p : V × V // ¬p.1 ≠ p.2}, Fintype.card V :=
        sum_le_sum fun p _ => Fintype.card_subtype_le _
      _ = _ := by simp only [sum_const, card_univ, hdiag, Nat.nsmul_eq_mul, pow_two]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun p : V × V => p.1 ≠ p.2)]
  have hh := sum_common_le G hBip hfree
  calc
    _ ≤ 5 * Fintype.card V ^ 2 + Fintype.card V ^ 2 := by
      apply Nat.add_le_add
      · convert hh using 1 <;> congr! 2
      · exact hdiagSum
    _ = _ := by omega

open scoped Classical in
theorem bipartite_edge_sq_le {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hBip : G.IsBipartite) (hfree : D33.Free G) :
    G.edgeFinset.card ^ 2 ≤ 6 * Fintype.card V ^ 3 := by
  have hc := sq_sum_le_card_mul_sum_sq (s := univ) (f := fun v => G.degree v)
  rw [card_univ, sum_degrees_eq_twice_card_edges] at hc
  have hb := Nat.mul_le_mul_left (Fintype.card V) (sum_degree_sq_le G hBip hfree)
  nlinarith

end Erdos713Minus

#print axioms Erdos713Minus.rectangle_has_light_pair
#print axioms Erdos713Minus.row_card

#print axioms Erdos713Minus.bipartite_edge_sq_le
