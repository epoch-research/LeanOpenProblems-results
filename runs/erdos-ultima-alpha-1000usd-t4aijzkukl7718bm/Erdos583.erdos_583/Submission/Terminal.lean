import Submission.Work

/-! Restricting path decompositions when only terminal edges can be removed. -/

open SimpleGraph Erdos583Work
namespace Erdos583TerminalDevelopment

lemma dropLast_subset_cons {α : Type*} (a : α) (l : List α) :
    l.dropLast ⊆ (a::l).dropLast := by
  cases l with
  | nil => simp
  | cons b l =>
    rw [List.dropLast_cons₂]
    intro x hx
    exact List.mem_cons_of_mem _ hx

lemma exists_trim_last {V : Type*} {G J : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (hp : p.IsPath)
    (hgood : ∀ e ∈ p.edges.dropLast, e ∈ J.edgeSet) :
    ∃ c, ∃ q : J.Walk a c, q.IsPath ∧ q.support ⊆ p.support ∧
      q.toSubgraph.edgeSet = p.toSubgraph.edgeSet ∩ J.edgeSet := by
  classical
  induction p with
  | @nil a => exact ⟨a, .nil, Walk.IsPath.nil, by simp, by simp⟩
  | @cons a x b h p ih =>
    have hg : ∀ e ∈ p.edges.dropLast, e ∈ J.edgeSet := by
      intro e he
      exact hgood e (dropLast_subset_cons s(a,x) p.edges he)
    by_cases hJ : J.Adj a x
    · obtain ⟨c, q, hq, hsub, heq⟩ := ih hp.of_cons hg
      have ha : a ∉ p.support := (List.nodup_cons.mp hp.support_nodup).1
      refine ⟨c, .cons hJ q, hq.cons (fun he ↦ ha (hsub he)), ?_, ?_⟩
      · simpa only [Walk.support_cons] using List.cons_subset_cons a hsub
      · ext e
        have heq' : e ∈ q.edges ↔ e ∈ p.edges ∧ e ∈ J.edgeSet := by
          simpa only [Walk.edgeSet_toSubgraph, Set.mem_inter_iff, Set.mem_setOf_eq]
            using Set.ext_iff.mp heq e
        have hJe : s(a,x) ∈ J.edgeSet := hJ
        simp only [Walk.edgeSet_toSubgraph, Set.mem_inter_iff, Set.mem_setOf_eq,
          Walk.edges_cons, List.mem_cons]
        aesop
    · have hn : p.Nil := by
        by_contra hn
        have hne : p.edges ≠ [] := fun he ↦ hn (Walk.edges_eq_nil.mp he)
        have hm : s(a,x) ∈ (Walk.cons h p).edges.dropLast := by
          simp [Walk.edges_cons, List.dropLast_cons_of_ne_nil hne]
        exact hJ (hgood _ hm)
      cases hn
      refine ⟨a, .nil, Walk.IsPath.nil, by simp, ?_⟩
      ext e
      simp only [Walk.edgeSet_toSubgraph, Walk.edges_nil, Walk.edges_cons, List.mem_cons,
        List.not_mem_nil, or_false, Set.mem_inter_iff, Set.mem_setOf_eq, false_iff]
      rintro ⟨rfl, he⟩
      exact hJ he

lemma exists_trim_ends {V : Type*} {G J : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (hp : p.IsPath)
    (hgood : ∀ e ∈ p.edges.tail.dropLast, e ∈ J.edgeSet) :
    ∃ c d, ∃ q : J.Walk c d, q.IsPath ∧
      q.toSubgraph.edgeSet = p.toSubgraph.edgeSet ∩ J.edgeSet := by
  classical
  cases p with
  | nil => exact ⟨a, a, .nil, Walk.IsPath.nil, by simp⟩
  | @cons a x b h p =>
    obtain ⟨c, q, hq, hsub, heq⟩ := exists_trim_last p hp.of_cons hgood
    by_cases hJ : J.Adj a x
    · have ha : a ∉ p.support := (List.nodup_cons.mp hp.support_nodup).1
      refine ⟨a, c, .cons hJ q, hq.cons (fun he ↦ ha (hsub he)), ?_⟩
      ext e
      have heq' : e ∈ q.edges ↔ e ∈ p.edges ∧ e ∈ J.edgeSet := by
          simpa only [Walk.edgeSet_toSubgraph, Set.mem_inter_iff, Set.mem_setOf_eq]
            using Set.ext_iff.mp heq e
      have hJe : s(a,x) ∈ J.edgeSet := hJ
      simp only [Walk.edgeSet_toSubgraph, Set.mem_inter_iff, Set.mem_setOf_eq,
        Walk.edges_cons, List.mem_cons]
      aesop
    · refine ⟨x, c, q, hq, ?_⟩
      ext e
      have heq' : e ∈ q.edges ↔ e ∈ p.edges ∧ e ∈ J.edgeSet := by
          simpa only [Walk.edgeSet_toSubgraph, Set.mem_inter_iff, Set.mem_setOf_eq]
            using Set.ext_iff.mp heq e
      have hJe : s(a,x) ∉ J.edgeSet := hJ
      simp only [Walk.edgeSet_toSubgraph, Set.mem_inter_iff, Set.mem_setOf_eq,
        Walk.edges_cons, List.mem_cons]
      aesop

lemma GoodDecomposition.restrict_terminal_edges {V : Type*} {G J : SimpleGraph V}
    (hJG : J ≤ G) {D : Finset G.Subgraph} (hD : GoodDecomposition G D)
    (hcompat : ∀ H ∈ D, ∃ a b, ∃ p : G.Walk a b,
      p.IsPath ∧ H = p.toSubgraph ∧ ∀ e ∈ p.edges.tail.dropLast, e ∈ J.edgeSet) :
    ∃ E : Finset J.Subgraph, GoodDecomposition J E ∧ E.card ≤ D.card := by
  classical
  have hx (H : D) : ∃ K : J.Subgraph, IsPathSubgraph K ∧ K.edgeSet = H.val.edgeSet ∩ J.edgeSet := by
    obtain ⟨a, b, p, hp, heq, hgood⟩ := hcompat H.val H.property
    obtain ⟨c, d, q, hq, hqeq⟩ := exists_trim_ends p hp hgood
    exact ⟨q.toSubgraph, ⟨c, d, q, hq, rfl⟩, by simpa [heq] using hqeq⟩
  choose f hf hfe using hx
  obtain ⟨E, hE, hn⟩ := refine_decomposition hJG hD (fun H ↦ {f H})
    (by intro H L hL; simpa only [Finset.mem_singleton.mp hL] using hf H)
    (by intro H; simp) (by intro H; simpa using hfe H)
  exact ⟨E, hE, by simpa using hn⟩

lemma edge_getElem {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (j : ℕ) (hj : j < p.length) :
    p.edges[j]'(by simpa using hj) = s(p.getVert j, p.getVert (j+1)) := by
  induction p generalizing j with
  | nil => simp at hj
  | cons h p ih =>
    cases j with
    | zero => simp
    | succ j => simpa using ih j (by simpa using hj)

lemma mem_inner_edges_index {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) {e : Sym2 V} (he : e ∈ p.edges.tail.dropLast) :
    ∃ j, 0 < j ∧ j+1 < p.length ∧ e = s(p.getVert j, p.getVert (j+1)) := by
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp he
  have hi' : i+2 < p.length := by
    simp only [List.length_dropLast, List.length_tail, Walk.length_edges] at hi
    omega
  have heq' : p.edges[i+1]'(by simpa using (by omega : i+1 < p.length)) = e := by
    simpa only [List.getElem_dropLast, List.getElem_tail] using heq
  refine ⟨i+1, by omega, by omega, ?_⟩
  exact heq'.symm.trans (edge_getElem p (i+1) (by omega))

open scoped Classical in
lemma goodDecomposition_of_family_of_card {V I : Type*} [Fintype V] [Fintype I]
    (G : SimpleGraph V) (f : I → G.Subgraph)
    (hf : ∀ i, IsPathSubgraph (f i))
    (hd : Pairwise (fun i j ↦ Disjoint (f i).edgeSet (f j).edgeSet))
    (hc : ∑ i, (f i).edgeSet.ncard = G.edgeSet.ncard) :
    GoodDecomposition G (Finset.univ.image f) := by
  classical
  let U := ⋃ i, (f i).edgeSet
  have hsub : U ⊆ G.edgeSet := by
    rintro e ⟨_, ⟨i, rfl⟩, he⟩
    exact (f i).edgeSet_subset he
  have hcard : U.ncard = G.edgeSet.ncard := by
    have hU : U = ⋃ i ∈ ((Finset.univ : Finset I) : Set I), (f i).edgeSet := by simp [U]
    rw [hU]
    rw [(Finset.univ : Finset I).finite_toSet.ncard_biUnion
      (fun _ _ ↦ Set.toFinite _) (fun i _ j _ hij ↦ hd hij), finsum_mem_coe_finset]
    exact hc
  have hcover : U = G.edgeSet := Set.eq_of_subset_of_ncard_le hsub hcard.ge
  let D := Finset.univ.image f
  change GoodDecomposition G D
  refine ⟨?_, ?_, ?_⟩
  · intro K hK
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hK
    exact hf i
  · intro K hK L hL hKL
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hK
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hL
    exact hd (fun hij ↦ hKL (congrArg f hij))
  · simpa [D, U] using hcover

namespace WaleckiTerminal
open Erdos583Work.Walecki

lemma zig_succ_difference {k j : ℕ} (hj : j+1 < 2*k) :
    (zig (2*k) (j+1) : ZMod (2*k)) - (zig (2*k) j : ZMod (2*k)) =
      if j%2=0 then -((j+1 : ℕ) : ZMod (2*k)) else ((j+1 : ℕ) : ZMod (2*k)) := by
  by_cases hp : j%2=0
  · rw [if_pos hp]
    have hn : zig (2*k) (j+1) + (j+1) = 2*k + zig (2*k) j := by
      unfold zig
      split_ifs <;> omega
    have hc := congrArg (fun n : ℕ ↦ (n : ZMod (2*k))) hn
    simp only [Nat.cast_add, ZMod.natCast_self, zero_add] at hc
    push_cast
    linear_combination hc
  · rw [if_neg hp]
    have hn : zig (2*k) (j+1) + 2*k = zig (2*k) j + (j+1) := by
      unfold zig
      split_ifs <;> omega
    have hc := congrArg (fun n : ℕ ↦ (n : ZMod (2*k))) hn
    simp only [Nat.cast_add, ZMod.natCast_self, add_zero] at hc
    push_cast
    linear_combination hc

lemma cast_eq_unit_cases {n a : ℕ} (hn : 1 < n) (ha : a < n)
    (h : (a : ZMod n) = 1 ∨ (a : ZMod n) = -1) : a = 1 ∨ a = n-1 := by
  have hm : ((n-1 : ℕ) : ZMod n) = -1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), ZMod.natCast_self, Nat.cast_one, zero_sub]
  rcases h with h | h
  · left
    have hv := congrArg ZMod.val h
    have hone : (1 : ZMod n).val = 1 := by simpa only [Nat.cast_one] using ZMod.val_natCast_of_lt hn
    simpa only [ZMod.val_natCast_of_lt ha, hone] using hv
  · right
    rw [← hm] at h
    have hv := congrArg ZMod.val h
    simpa only [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt (by omega : n-1 < n)] using hv

lemma cyclic_adj_vertex_indices {k : ℕ} (i : Fin k) {j : ℕ} (hj : j+1 < 2*k)
    (h : vertex i ⟨j+1, hj⟩ = vertex i ⟨j, by omega⟩ + 1 ∨
      vertex i ⟨j, by omega⟩ = vertex i ⟨j+1, hj⟩ + 1) : j = 0 ∨ j+2 = 2*k := by
  have hd := zig_succ_difference hj
  have hd' : vertex i ⟨j+1, hj⟩ - vertex i ⟨j, by omega⟩ =
      if j%2=0 then -((j+1 : ℕ) : ZMod (2*k)) else ((j+1 : ℕ) : ZMod (2*k)) := by
    simpa only [vertex, add_sub_add_left_eq_sub] using hd
  have hc : ((j+1 : ℕ) : ZMod (2*k)) = 1 ∨ ((j+1 : ℕ) : ZMod (2*k)) = -1 := by
    split_ifs at hd' with hp
    · rcases h with h | h
      · right; linear_combination hd' - h
      · left; linear_combination hd' + h
    · rcases h with h | h
      · left; linear_combination -hd' + h
      · right; linear_combination -hd' - h
  have hn : 1 < 2*k := by have := i.isLt; omega
  have ht := cast_eq_unit_cases hn hj hc
  omega

lemma inner_edges_avoid_cycle {k : ℕ} (i : Fin k) {a b : ZMod (2*k)}
    (p : (⊤ : SimpleGraph (ZMod (2*k))).Walk a b)
    (hs : p.support = List.ofFn (vertex i)) {x y : ZMod (2*k)}
    (he : s(x,y) ∈ p.edges.tail.dropLast) : ¬(y = x+1 ∨ x = y+1) := by
  obtain ⟨j, hj0, hj, heq⟩ := mem_inner_edges_index p he
  have hl : p.length + 1 = 2*k := by simpa using congrArg List.length hs
  rw [getVert_of_support_eq_ofFn p hs j (by omega),
    getVert_of_support_eq_ofFn p hs (j+1) (by omega)] at heq
  intro hxy
  have hh : vertex i ⟨j+1, by omega⟩ = vertex i ⟨j, by omega⟩ + 1 ∨
      vertex i ⟨j, by omega⟩ = vertex i ⟨j+1, by omega⟩ + 1 := by
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hxy
    · exact hxy.symm
  have := cyclic_adj_vertex_indices i (by omega) hh
  omega

/-- A complete graph of even order with any subset of a fixed spanning cycle
removed still meets Gallai's bound. -/
lemma complete_even_cycle_deletion (k : ℕ) (hk : 0 < k)
    (G : SimpleGraph (ZMod (2*k)))
    (hG : ∀ x y, x ≠ y → ¬(y = x+1 ∨ x = y+1) → G.Adj x y) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ k := by
  classical
  letI : NeZero (2*k) := ⟨by omega⟩
  choose a b p hp hs using exists_path_vertex (k := k)
  have hd : Pairwise (fun i j ↦ Disjoint (p i).toSubgraph.edgeSet (p j).toSubgraph.edgeSet) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro e hei hej
    induction e using Sym2.ind with
    | h x y =>
      have hci := path_vertex_color i (p i) (hs i) ((p i).mem_edges_toSubgraph.mp hei)
      have hcj := path_vertex_color j (p j) (hs j) ((p j).mem_edges_toSubgraph.mp hej)
      exact hij (Fin.ext (hci.symm.trans hcj))
  have hc (i : Fin k) : (p i).toSubgraph.edgeSet.ncard = 2*k-1 := by
    rw [path_edgeSet_ncard (hp i)]
    have hl := congrArg List.length (hs i)
    simp only [Walk.length_support, List.length_ofFn] at hl
    omega
  have ht : (⊤ : SimpleGraph (ZMod (2*k))).edgeSet.ncard = k*(2*k-1) := by
    rw [Set.ncard_eq_toFinset_card']
    change (⊤ : SimpleGraph (ZMod (2*k))).edgeFinset.card = _
    rw [card_edgeFinset_top_eq_card_choose_two, ZMod.card, Nat.choose_two_right]
    simp [Nat.mul_assoc]
  let D := Finset.univ.image (fun i ↦ (p i).toSubgraph)
  have hD : GoodDecomposition (⊤ : SimpleGraph (ZMod (2*k))) D :=
    goodDecomposition_of_family_of_card _ (fun i ↦ (p i).toSubgraph)
      (fun i ↦ ⟨a i, b i, p i, hp i, rfl⟩) hd (by
        simp only [hc, ht, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, Nat.cast_id])
  have hcompat : ∀ H ∈ D, ∃ u v, ∃ p' : (⊤ : SimpleGraph (ZMod (2*k))).Walk u v,
      p'.IsPath ∧ H = p'.toSubgraph ∧ ∀ e ∈ p'.edges.tail.dropLast, e ∈ G.edgeSet := by
    intro H hH
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hH
    refine ⟨a i, b i, p i, hp i, rfl, ?_⟩
    intro e he
    induction e using Sym2.ind with
    | h x y =>
      have he' : s(x,y) ∈ (p i).edges := List.mem_of_mem_tail (List.mem_of_mem_dropLast he)
      exact hG x y ((p i).adj_of_mem_edges he') (inner_edges_avoid_cycle i (p i) (hs i) he)
  obtain ⟨E, hE, hn⟩ := GoodDecomposition.restrict_terminal_edges le_top hD hcompat
  have hDc : D.card ≤ k := Finset.card_image_le.trans (by simp)
  exact ⟨E, hE, hn.trans hDc⟩

end WaleckiTerminal

universe u

lemma matching_vertex_order_aux (n : ℕ) :
    ∀ {V : Type u} [Fintype V], Fintype.card V = n →
      ∀ F : SimpleGraph V, (∀ x, (F.neighborSet x).Subsingleton) →
      ∃ l : List V, l.Nodup ∧ (∀ x, x ∈ l) ∧
        ∀ x y, F.Adj x y → [x,y] <:+: l ∨ [y,x] <:+: l := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V inst hn F hm
    by_cases he : ∃ x y, F.Adj x y
    · obtain ⟨x, y, hxy⟩ := he
      let S : Set V := {v | v ≠ x ∧ v ≠ y}
      let R := S
      let F' : SimpleGraph R := F.induce S
      have hm' : ∀ v, (F'.neighborSet v).Subsingleton := by
        intro v a ha b hb
        exact Subtype.ext (hm v.val ha hb)
      have hlt : Fintype.card R < n := by
        rw [← hn]
        exact Fintype.card_subtype_lt (p := fun v : V ↦ v ≠ x ∧ v ≠ y) (x := x)
          (fun hx ↦ hx.1 rfl)
      obtain ⟨l, hl, hall, hedge⟩ := ih (Fintype.card R) hlt (V := R) rfl F' hm'
      let m := l.map (Subtype.val : R → V)
      have hmx : x ∉ m := by
        rintro hx
        obtain ⟨v, _, hv⟩ := List.mem_map.mp hx
        exact v.property.1 hv
      have hmy : y ∉ m := by
        rintro hy
        obtain ⟨v, _, hv⟩ := List.mem_map.mp hy
        exact v.property.2 hv
      have hmn : m.Nodup := List.Nodup.map Subtype.val_injective hl
      refine ⟨x::y::m, ?_, ?_, ?_⟩
      · simp [hxy.ne, hmx, hmy, hmn]
      · intro v
        by_cases hvx : v = x
        · simp [hvx]
        by_cases hvy : v = y
        · simp [hvy]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_map.mpr ⟨⟨v, hvx, hvy⟩, hall _, rfl⟩))
      · intro a b hab
        have hpref : [x,y] <:+: x::y::m := ⟨[], m, rfl⟩
        by_cases hax : a = x
        · subst a
          have hby : b = y := hm x hab hxy
          subst b
          exact Or.inl hpref
        by_cases hay : a = y
        · subst a
          have hbx : b = x := hm y hab hxy.symm
          subst b
          exact Or.inr hpref
        by_cases hbx : b = x
        · subst b
          have hay : a = y := hm x hab.symm hxy
          subst a
          exact Or.inr hpref
        by_cases hby : b = y
        · subst b
          have hax : a = x := hm y hab.symm hxy.symm
          subst a
          exact Or.inl hpref
        let a' : R := ⟨a, hax, hay⟩
        let b' : R := ⟨b, hbx, hby⟩
        have ht : m <:+: x::y::m := ⟨[x,y], [], by simp⟩
        rcases hedge a' b' hab with h | h
        · left
          apply List.IsInfix.trans _ ht
          simpa only [List.map_cons, List.map_nil] using h.map (Subtype.val : R → V)
        · right
          apply List.IsInfix.trans _ ht
          simpa only [List.map_cons, List.map_nil] using h.map (Subtype.val : R → V)
    · refine ⟨Finset.univ.toList, Finset.nodup_toList _, by simp, ?_⟩
      intro x y hxy
      exact (he ⟨x, y, hxy⟩).elim

lemma matching_vertex_order {V : Type*} [Fintype V] (F : SimpleGraph V)
    (hm : ∀ x, (F.neighborSet x).Subsingleton) :
    ∃ l : List V, l.Nodup ∧ (∀ x, x ∈ l) ∧
      ∀ x y, F.Adj x y → [x,y] <:+: l ∨ [y,x] <:+: l :=
  matching_vertex_order_aux (Fintype.card V) rfl F hm

lemma infix_pair_indices {V : Type*} {a b : V} {l : List V} (h : [a,b] <:+: l) :
    ∃ j, ∃ hj : j+1 < l.length, l[j]'(by omega) = a ∧ l[j+1]'hj = b := by
  obtain ⟨s, t, rfl⟩ := h
  refine ⟨s.length, by simp, ?_, ?_⟩
  · simp [List.getElem_append_right]
  · simp [List.getElem_append_right]

lemma matching_cyclic_order {V : Type*} [Fintype V] (F : SimpleGraph V)
    (hm : ∀ x, (F.neighborSet x).Subsingleton) (n : ℕ) (hn : 0 < n)
    (hcard : Fintype.card V = n) :
    ∃ e : ZMod n ≃ V, ∀ x y, F.Adj (e x) (e y) → y = x+1 ∨ x = y+1 := by
  classical
  letI : NeZero n := ⟨by omega⟩
  obtain ⟨l, hl, hall, hedge⟩ := matching_vertex_order F hm
  have hinj : Function.Injective l.get := List.nodup_iff_injective_get.mp hl
  have hsurj : Function.Surjective l.get := fun v ↦ List.mem_iff_get.mp (hall v)
  have hlen : l.length = n := by
    have hc := Fintype.card_congr (Equiv.ofBijective l.get ⟨hinj, hsurj⟩)
    simpa only [Fintype.card_fin, hcard] using hc
  let f (z : ZMod n) := l.get ⟨z.val, by rw [hlen]; exact z.val_lt⟩
  have hfi : Function.Injective f := by
    intro x y he
    have hv := congrArg Fin.val (hinj he)
    exact ZMod.val_injective n hv
  have hfs : Function.Surjective f := by
    intro v
    obtain ⟨i, hi⟩ := hsurj v
    refine ⟨(i.val : ZMod n), ?_⟩
    dsimp only [f]
    have hiLt : i.val < n := hlen ▸ i.isLt
    simpa only [ZMod.val_natCast_of_lt hiLt] using hi
  let e := Equiv.ofBijective f ⟨hfi, hfs⟩
  have hstep {x y : ZMod n} (h : [e x, e y] <:+: l) : y = x+1 := by
    obtain ⟨j, hj, hx, hy⟩ := infix_pair_indices h
    have hx' : x.val = j := congrArg Fin.val (hinj (show
      l.get ⟨x.val, by rw [hlen]; exact x.val_lt⟩ = l.get ⟨j, by omega⟩ from
      by simpa only [e, Equiv.ofBijective_apply, f, List.get_eq_getElem] using hx.symm))
    have hy' : y.val = j+1 := congrArg Fin.val (hinj (show
      l.get ⟨y.val, by rw [hlen]; exact y.val_lt⟩ = l.get ⟨j+1, hj⟩ from
      by simpa only [e, Equiv.ofBijective_apply, f, List.get_eq_getElem] using hy.symm))
    have hx'' : x = (j : ZMod n) := by rw [← ZMod.natCast_zmod_val x, hx']
    have hy'' : y = ((j+1 : ℕ) : ZMod n) := by rw [← ZMod.natCast_zmod_val y, hy']
    rw [hx'', hy'', Nat.cast_add, Nat.cast_one]
  refine ⟨e, ?_⟩
  intro x y hxy
  exact (hedge (e x) (e y) hxy).imp hstep hstep

lemma GoodDecomposition.map_comap_equiv {V W : Type*} {G : SimpleGraph V} (e : W ≃ V)
    {D : Finset (G.comap e).Subgraph} (hD : GoodDecomposition (G.comap e) D) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ D.card := by
  apply hD.map_of_edge_surjective (Hom.comap e G) e.injective
  ext d
  induction d using Sym2.ind with
  | h a b =>
    constructor
    · intro hab
      refine ⟨s(e.symm a, e.symm b), ?_, ?_⟩
      · simpa using hab
      · simp
    · rintro ⟨d, hd, he⟩
      induction d using Sym2.ind with
      | h x y => exact (G.adj_congr_of_sym2 he).mp hd

/-- A coordinate-free version of the spanning-cycle deletion construction. -/
lemma cyclic_complement_decomposition {V : Type*} [Fintype V] (G : SimpleGraph V)
    (k : ℕ) (hk : 0 < k) (e : ZMod (2*k) ≃ V)
    (hcomp : ∀ x y, (Gᶜ).Adj (e x) (e y) → y=x+1 ∨ x=y+1) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ 2*D.card ≤ Fintype.card V := by
  classical
  letI : NeZero (2*k) := ⟨by omega⟩
  have hcard : 2*k = Fintype.card V := by simpa only [ZMod.card] using Fintype.card_congr e
  let J := G.comap e
  have hJ : ∀ x y, x ≠ y → ¬(y=x+1 ∨ x=y+1) → J.Adj x y := by
    intro x y hxy hcyc
    by_contra hnxy
    exact hcyc (hcomp x y ⟨fun he ↦ hxy (e.injective he), hnxy⟩)
  obtain ⟨D, hD, hnD⟩ := WaleckiTerminal.complete_even_cycle_deletion k hk J hJ
  obtain ⟨E, hE, hnE⟩ := GoodDecomposition.map_comap_equiv e hD
  exact ⟨E, hE, by omega⟩

lemma erdos_583_of_cyclic_complement {V : Type*} [Fintype V] (G : SimpleGraph V)
    (k : ℕ) (hk : 0 < k) (e : ZMod (2*k) ≃ V)
    (hcomp : ∀ x y, (Gᶜ).Adj (e x) (e y) → y=x+1 ∨ x=y+1) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ) / 2⌉₊ := by
  obtain ⟨D, hD, hn⟩ := cyclic_complement_decomposition G k hk e hcomp
  have hq : 2 * (D.card : ℚ) ≤ (Fintype.card V : ℚ) := by exact_mod_cast hn
  have hr := Nat.le_ceil ((Fintype.card V : ℚ) / 2)
  refine ⟨D, hD, ?_⟩
  exact_mod_cast (show (D.card : ℚ) ≤ (⌈(Fintype.card V : ℚ) / 2⌉₊ : ℚ) by linarith)

/-- Gallai's bound after deleting an arbitrary matching from an even-order
complete graph. No connectivity hypothesis is needed. -/
lemma complete_even_matching_deletion {V : Type*} [Fintype V] (G : SimpleGraph V)
    (heven : Even (Fintype.card V))
    (hm : ∀ x, ((Gᶜ).neighborSet x).Subsingleton) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ 2*D.card ≤ Fintype.card V := by
  classical
  by_cases hn : Fintype.card V = 0
  · letI : IsEmpty V := Fintype.card_eq_zero_iff.mp hn
    have ht : G.edgeSet = ∅ := by ext e; induction e using Sym2.ind with | h a b => exact isEmptyElim a
    refine ⟨∅, ⟨by simp, by simp, ?_⟩, by simp⟩
    simp [ht]
  · obtain ⟨k, hk⟩ := heven
    have hcard : Fintype.card V = 2*k := by omega
    have hkpos : 0 < k := by omega
    obtain ⟨e, hedge⟩ := matching_cyclic_order Gᶜ hm (2*k) (by omega) hcard
    exact cyclic_complement_decomposition G k hkpos e hedge

lemma erdos_583_of_even_complement_matching {V : Type*} [Fintype V] (G : SimpleGraph V)
    (heven : Even (Fintype.card V))
    (hm : ∀ x, ((Gᶜ).neighborSet x).Subsingleton) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ) / 2⌉₊ := by
  obtain ⟨D, hD, hn⟩ := complete_even_matching_deletion G heven hm
  have hq : 2 * (D.card : ℚ) ≤ (Fintype.card V : ℚ) := by exact_mod_cast hn
  have hr := Nat.le_ceil ((Fintype.card V : ℚ) / 2)
  refine ⟨D, hD, ?_⟩
  exact_mod_cast (show (D.card : ℚ) ≤ (⌈(Fintype.card V : ℚ) / 2⌉₊ : ℚ) by linarith)

end Erdos583TerminalDevelopment
