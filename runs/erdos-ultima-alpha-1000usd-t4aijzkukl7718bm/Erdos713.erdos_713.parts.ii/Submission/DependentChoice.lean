import FormalConjecturesUtil
import Submission.Verified

open Filter SimpleGraph Asymptotics Finset

namespace Erdos713DRC

open scoped Classical in
theorem clean_set {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (k : ℕ) :
    ∃ S : Finset V, S ⊆ U ∧
      U.card ≤ S.card + ((U ×ˢ U).filter
        (fun p => Fintype.card (G.commonNeighbors p.1 p.2) < k)).card ∧
      ∀ x ∈ S, ∀ y ∈ S, k ≤ Fintype.card (G.commonNeighbors x y) := by
  classical
  let B := (U ×ˢ U).filter (fun p => Fintype.card (G.commonNeighbors p.1 p.2) < k)
  let S := U \ B.image Prod.fst
  refine ⟨S, sdiff_subset, ?_, ?_⟩
  · have hh := card_le_card_sdiff_add_card (s := U) (t := B.image Prod.fst)
    exact hh.trans (Nat.add_le_add_left (card_image_le) _)
  · intro x hx y hy
    by_contra hh
    have hB : (x, y) ∈ B := mem_filter.mpr
      ⟨mem_product.mpr ⟨(mem_sdiff.mp hx).1, (mem_sdiff.mp hy).1⟩, lt_of_not_ge hh⟩
    exact (mem_sdiff.mp hx).2 (mem_image_of_mem Prod.fst hB)

open scoped Classical in
theorem sum_common_eq_sum_degree_sq {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    ∑ p : V × V, Fintype.card (G.commonNeighbors p.1 p.2) = ∑ v, G.degree v ^ 2 := by
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
  simpa only [hAbove, hBelow] using hsum.symm

open scoped Classical in
theorem sum_bad_pairs_le {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ) :
    ∑ p : V × V, (((G.commonNeighbors p.1 p.2).toFinset ×ˢ
      (G.commonNeighbors p.1 p.2).toFinset).filter
        (fun q => Fintype.card (G.commonNeighbors q.1 q.2) < k)).card ≤
      k ^ 2 * Fintype.card V ^ 2 := by
  classical
  let r : (V × V) → (V × V) → Prop := fun p q =>
    G.Adj p.1 q.1 ∧ G.Adj p.2 q.1 ∧ G.Adj p.1 q.2 ∧ G.Adj p.2 q.2 ∧
      Fintype.card (G.commonNeighbors q.1 q.2) < k
  have hAbove (p : V × V) : ((univ : Finset (V × V)).bipartiteAbove r p) =
      (((G.commonNeighbors p.1 p.2).toFinset ×ˢ
      (G.commonNeighbors p.1 p.2).toFinset).filter
        (fun q => Fintype.card (G.commonNeighbors q.1 q.2) < k)) := by
    ext q
    simp [r, bipartiteAbove, mem_commonNeighbors, and_assoc]
  have hBelow (q : V × V) : ((univ : Finset (V × V)).bipartiteBelow r q).card ≤ k ^ 2 := by
    by_cases hq : Fintype.card (G.commonNeighbors q.1 q.2) < k
    · have he : ((univ : Finset (V × V)).bipartiteBelow r q) =
          (G.commonNeighbors q.1 q.2).toFinset ×ˢ (G.commonNeighbors q.1 q.2).toFinset := by
        ext p
        simp only [mem_bipartiteBelow, mem_univ, true_and, r, mem_product,
          Set.mem_toFinset, mem_commonNeighbors, hq, and_true]
        constructor
        · rintro ⟨h1, h2, h3, h4⟩
          exact ⟨⟨h1.symm, h3.symm⟩, h2.symm, h4.symm⟩
        · rintro ⟨⟨h1, h2⟩, h3, h4⟩
          exact ⟨h1.symm, h3.symm, h2.symm, h4.symm⟩
      rw [he, card_product, Set.toFinset_card, ← pow_two]
      exact Nat.pow_le_pow_left hq.le 2
    · have he : ((univ : Finset (V × V)).bipartiteBelow r q) = ∅ := by
        ext p
        simp only [mem_bipartiteBelow, mem_univ, true_and, r, hq, and_false, not_false_eq_true,
          notMem_empty, iff_self]
      simp [he]
  have hsum := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (r := r) (s := (univ : Finset (V × V))) (t := (univ : Finset (V × V)))
  simp_rw [hAbove] at hsum
  rw [hsum]
  calc
    _ ≤ ∑ _ : V × V, k ^ 2 := sum_le_sum fun q _ => hBelow q
    _ = _ := by simp [Fintype.card_prod, pow_two, mul_comm]

open scoped Classical in
theorem degree_sq_le_of_no_heavy_set {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (s k : ℕ)
    (h : ∀ S : Finset V, (∀ x ∈ S, ∀ y ∈ S,
      k ≤ Fintype.card (G.commonNeighbors x y)) → S.card ≤ s) :
    ∑ v, G.degree v ^ 2 ≤ (s + k ^ 2) * Fintype.card V ^ 2 := by
  classical
  have hrow (p : V × V) : Fintype.card (G.commonNeighbors p.1 p.2) ≤
      s + (((G.commonNeighbors p.1 p.2).toFinset ×ˢ
      (G.commonNeighbors p.1 p.2).toFinset).filter
        (fun q => Fintype.card (G.commonNeighbors q.1 q.2) < k)).card := by
    obtain ⟨S, _, hcard, hgood⟩ := clean_set G (G.commonNeighbors p.1 p.2).toFinset k
    rw [Set.toFinset_card] at hcard
    exact hcard.trans (Nat.add_le_add_right (h S hgood) _)
  rw [← sum_common_eq_sum_degree_sq]
  calc
    _ ≤ ∑ p : V × V, (s + (((G.commonNeighbors p.1 p.2).toFinset ×ˢ
        (G.commonNeighbors p.1 p.2).toFinset).filter
          (fun q => Fintype.card (G.commonNeighbors q.1 q.2) < k)).card) :=
      sum_le_sum fun p _ => hrow p
    _ ≤ s * Fintype.card V ^ 2 + k ^ 2 * Fintype.card V ^ 2 := by
      rw [sum_add_distrib]
      have hc : (∑ _ : V × V, s) = s * Fintype.card V ^ 2 := by
        simp [Fintype.card_prod, pow_two, mul_comm]
      rw [hc]
      exact Nat.add_le_add_left (sum_bad_pairs_le G k) _
    _ = _ := by ring

end Erdos713DRC

namespace Erdos713DRC

open Erdos713C6

open scoped Classical in
theorem contained_of_heavy_set {A B V : Type*} [Fintype A] [Fintype B] [Fintype V]
    (R : A → B → Prop) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hR : ∀ b, ∃ u v, ∀ a, R a b → a = u ∨ a = v)
    (S : Finset V) (hS : Fintype.card A ≤ S.card)
    (hgood : ∀ x ∈ S, ∀ y ∈ S,
      Fintype.card A + Fintype.card B ≤ Fintype.card (G.commonNeighbors x y)) :
    bipGraph R ⊑ G := by
  classical
  obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset hS
  choose u v huv using hR
  let L := (univ : Finset A).image f
  let t : B → Finset V := fun b => (G.commonNeighbors (f (u b)) (f (v b))).toFinset \ L
  have hL : L.card ≤ Fintype.card A := by
    exact (card_image_le).trans (by simp)
  have ht (b : B) : Fintype.card B ≤ (t b).card := by
    have hg := hgood (f (u b)) (hf ⟨u b, rfl⟩) (f (v b)) (hf ⟨v b, rfl⟩)
    have hh := card_le_card_sdiff_add_card (s := (G.commonNeighbors (f (u b)) (f (v b))).toFinset)
      (t := L)
    rw [Set.toFinset_card] at hh
    dsimp only [t]
    omega
  have hHall (U : Finset B) : U.card ≤ (U.biUnion t).card := by
    rcases U.eq_empty_or_nonempty with rfl | hU
    · simp
    obtain ⟨b, hb⟩ := hU
    exact (card_le_univ U).trans ((ht b).trans (card_le_card (subset_biUnion_of_mem t hb)))
  obtain ⟨g, hginj, hg⟩ := (all_card_le_biUnion_card_iff_exists_injective t).mp hHall
  have hdis (a : A) (b : B) : f a ≠ g b := by
    intro hab
    have hh := (mem_sdiff.mp (hg b)).2
    exact hh (hab ▸ mem_image_of_mem f (mem_univ a))
  have hAdj (a : A) (b : B) (hab : R a b) : G.Adj (f a) (g b) := by
    have hh : g b ∈ G.commonNeighbors (f (u b)) (f (v b)) := by
      simpa only [Set.mem_toFinset] using (mem_sdiff.mp (hg b)).1
    rcases huv b a hab with rfl | rfl
    · exact hh.1
    · exact hh.2
  refine ⟨⟨⟨Sum.elim f g, ?_⟩, ?_⟩⟩
  · intro x y hxy
    cases x with
    | inl a =>
      cases y with
      | inl a' => exact hxy.elim
      | inr b => exact hAdj a b hxy
    | inr b =>
      cases y with
      | inl a => exact (hAdj a b hxy).symm
      | inr b' => exact hxy.elim
  · intro x y hxy
    change Sum.elim f g x = Sum.elim f g y at hxy
    cases x with
    | inl a =>
      cases y with
      | inl a' => exact congrArg Sum.inl (f.injective hxy)
      | inr b => exact (hdis a b hxy).elim
    | inr b =>
      cases y with
      | inl a => exact (hdis a b hxy.symm).elim
      | inr b' => exact congrArg Sum.inr (hginj hxy)

open scoped Classical in
theorem degree_two_edge_sq_le {A B V : Type*} [Fintype A] [Fintype B] [Fintype V]
    (R : A → B → Prop) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hR : ∀ b, ∃ u v, ∀ a, R a b → a = u ∨ a = v)
    (hfree : (bipGraph R).Free G) :
    G.edgeFinset.card ^ 2 ≤
      (Fintype.card A + (Fintype.card A + Fintype.card B) ^ 2) * Fintype.card V ^ 3 := by
  classical
  have hb := degree_sq_le_of_no_heavy_set G (Fintype.card A) (Fintype.card A + Fintype.card B)
    (fun S hg => by
      by_contra hcard
      exact hfree (contained_of_heavy_set R G hR S (by omega) hg))
  have hc := sq_sum_le_card_mul_sum_sq (s := univ) (f := fun v => G.degree v)
  rw [card_univ, sum_degrees_eq_twice_card_edges] at hc
  have hm := Nat.mul_le_mul_left (Fintype.card V) hb
  nlinarith

end Erdos713DRC

#print axioms Erdos713DRC.degree_two_edge_sq_le

namespace Erdos713DRC
open Erdos713C6

theorem pair_cover_of_card_le_two {A : Type*} [Nonempty A] (U : Finset A) (hU : U.card ≤ 2) :
    ∃ u v, ∀ a ∈ U, a = u ∨ a = v := by
  classical
  by_cases h0 : U.card = 0
  · refine ⟨Classical.arbitrary A, Classical.arbitrary A, ?_⟩
    simp [card_eq_zero.mp h0]
  by_cases h1 : U.card = 1
  · obtain ⟨u, rfl⟩ := card_eq_one.mp h1
    exact ⟨u, u, by simp⟩
  obtain ⟨u, v, _, rfl⟩ := card_eq_two.mp (show U.card = 2 by omega)
  exact ⟨u, v, by simp⟩

open scoped Classical in
theorem pair_cover_of_degree_two {A B : Type*} [Fintype A] [Nonempty A]
    (R : A → B → Prop) (hR : ∀ b, Fintype.card {a // R a b} ≤ 2) :
    ∀ b, ∃ u v, ∀ a, R a b → a = u ∨ a = v := by
  classical
  intro b
  obtain ⟨u, v, h⟩ := pair_cover_of_card_le_two (univ.filter (R · b))
    (by simpa only [Fintype.card_subtype] using hR b)
  exact ⟨u, v, fun a ha => h a (mem_filter.mpr ⟨mem_univ _, ha⟩)⟩

theorem extremal_sq_le {A B : Type*} [Fintype A] [Fintype B]
    (R : A → B → Prop) (hR : ∀ b, ∃ u v, ∀ a, R a b → a = u ∨ a = v) (n : ℕ) :
    (extremalNumber n (bipGraph R)) ^ 2 ≤
      (Fintype.card A + (Fintype.card A + Fintype.card B) ^ 2) * n ^ 3 := by
  classical
  let S : Finset (SimpleGraph (Fin n)) := {G | (bipGraph R).Free G}
  change (S.sup (fun G => G.edgeFinset.card)) ^ 2 ≤ _
  by_cases hS : S.Nonempty
  · obtain ⟨G, hG, he⟩ := exists_mem_eq_sup S hS (fun G => G.edgeFinset.card)
    rw [he]
    have hfree : (bipGraph R).Free G := by simpa [S] using hG
    simpa only [Fintype.card_fin] using degree_two_edge_sq_le R G hR hfree
  · rw [not_nonempty_iff_eq_empty.mp hS]
    simp

theorem exponent_upper_of_containment {A B W : Type*} [Fintype A] [Fintype B]
    (R : A → B → Prop) (hR : ∀ b, ∃ u v, ∀ a, R a b → a = u ∨ a = v)
    {H : SimpleGraph W} (hH : H ⊑ bipGraph R) {a c : ℝ} (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a ≤ (3 : ℝ) / 2 := by
  have hO : (fun n : ℕ => (n : ℝ) ^ a) =O[atTop]
      (fun n : ℕ => (extremalNumber n H : ℝ)) :=
    (isBigO_const_mul_left_iff hc).mp h.isBigO_symm
  have hP : (fun n : ℕ => (n : ℝ) ^ (a * (2 : ℝ))) =O[atTop]
      (fun n : ℕ => (extremalNumber n H : ℝ) ^ (2 : ℕ)) := by
    have he (n : ℕ) : ((n : ℝ) ^ a) ^ (2 : ℕ) = (n : ℝ) ^ (a * (2 : ℝ)) := by
      have hh := Real.rpow_mul_natCast (Nat.cast_nonneg (α := ℝ) n) a 2
      norm_num only [Nat.cast_ofNat] at hh
      exact hh.symm
    simpa only [he] using hO.pow 2
  have hB : (fun n : ℕ => (extremalNumber n H : ℝ) ^ (2 : ℕ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (3 : ℝ)) := by
    apply IsBigO.of_bound ((Fintype.card A + (Fintype.card A + Fintype.card B) ^ 2 : ℕ) : ℝ)
    filter_upwards with n
    rw [Real.norm_of_nonneg (pow_nonneg (Nat.cast_nonneg _) _)]
    have hn3 : (n : ℝ) ^ (3 : ℝ) = (n : ℝ) ^ (3 : ℕ) := by
      exact_mod_cast Real.rpow_natCast (n : ℝ) 3
    rw [hn3, Real.norm_of_nonneg (pow_nonneg (Nat.cast_nonneg _) _)]
    exact_mod_cast (Nat.pow_le_pow_left (hH.extremalNumber_le (n := n)) 2).trans
      (extremal_sq_le R hR n)
  have hExp := Erdos713C4.exponent_le_of_isBigO (hP.trans hB)
  linarith

theorem exponent_eq_of_containment {A B W : Type*} [Fintype A] [Fintype B]
    (R : A → B → Prop) (hR : ∀ b, ∃ u v, ∀ a, R a b → a = u ∨ a = v)
    {H : SimpleGraph W} (hlo : Erdos713C4.K22 ⊑ H) (hhi : H ⊑ bipGraph R)
    {a c : ℝ} (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a = (3 : ℝ) / 2 := by
  apply le_antisymm (exponent_upper_of_containment R hR hhi hc h)
  have hO : (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ a) :=
    (isBigO_const_mul_right_iff hc).mp h.isBigO
  apply Erdos713C4.lower_exponent_of_prime_bound hO
  intro p hp
  exact (Erdos713C4.extremal_lower_prime p hp).trans hlo.extremalNumber_le

theorem rational_of_containment {A B W : Type*} [Fintype A] [Fintype B]
    (R : A → B → Prop) (hR : ∀ b, ∃ u v, ∀ a, R a b → a = u ∨ a = v)
    {H : SimpleGraph W} (hlo : Erdos713C4.K22 ⊑ H) (hhi : H ⊑ bipGraph R)
    {a c : ℝ} (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a ∈ Set.range ((↑) : ℚ → ℝ) := by
  refine ⟨3 / 2, ?_⟩
  simpa using (exponent_eq_of_containment R hR hlo hhi hc h).symm

end Erdos713DRC

#print axioms Erdos713DRC.rational_of_containment

namespace Erdos713DRC
open Erdos713C6

theorem exponent_eq_of_bipartition {W : Type*} [Fintype W] (H : SimpleGraph W)
    (S : Set W) (hB : H.IsBipartiteWith S Sᶜ)
    (hdeg : ∀ v ∈ Sᶜ, Nat.card (H.neighborSet v) ≤ 2)
    (hlo : Erdos713C4.K22 ⊑ H) {a c : ℝ} (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a = (3 : ℝ) / 2 := by
  classical
  haveI : Nonempty S := by
    obtain ⟨f⟩ := hlo
    have he : H.Adj (f (Sum.inl 0)) (f (Sum.inr 0)) := f.toHom.map_adj (by simp [Erdos713C4.K22, completeBipartiteGraph])
    rcases hB.2 he with ⟨hu, _⟩ | ⟨_, hv⟩
    · exact ⟨⟨_, hu⟩⟩
    · exact ⟨⟨_, hv⟩⟩
  let R : S → ↥(Sᶜ) → Prop := fun u v => H.Adj u.val v.val
  have hR (b : ↥(Sᶜ)) : Fintype.card {a : S // R a b} ≤ 2 := by
    let f : {a : S // R a b} ↪ H.neighborSet b.val :=
      ⟨fun a => ⟨a.val.val, a.prop.symm⟩,
        by
          intro x y hxy
          apply Subtype.ext
          apply Subtype.ext
          exact congrArg (fun z : H.neighborSet b.val => z.val) hxy⟩
    have hc := (Fintype.card_le_of_embedding f).trans
      (show Fintype.card (H.neighborSet b.val) ≤ 2 by
        simpa only [Nat.card_eq_fintype_card] using hdeg b.val b.prop)
    exact hc
  have hhi : H ⊑ bipGraph R := by
    let e := (Equiv.Set.sumCompl S).symm
    refine ⟨⟨⟨e, ?_⟩, e.injective⟩⟩
    intro u v huv
    rcases hB.2 huv with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · have hv' : v ∉ S := hv
      simpa [e, Equiv.Set.sumCompl_symm_apply_of_mem hu,
        Equiv.Set.sumCompl_symm_apply_of_notMem hv', bipGraph, R] using huv
    · have hu' : u ∉ S := hu
      simpa [e, Equiv.Set.sumCompl_symm_apply_of_mem hv,
        Equiv.Set.sumCompl_symm_apply_of_notMem hu', bipGraph, R] using huv.symm
  exact exponent_eq_of_containment R (pair_cover_of_degree_two R hR) hlo hhi hc h

theorem rational_of_bipartition {W : Type*} [Fintype W] (H : SimpleGraph W)
    (S : Set W) (hB : H.IsBipartiteWith S Sᶜ)
    (hdeg : ∀ v ∈ Sᶜ, Nat.card (H.neighborSet v) ≤ 2)
    (hlo : Erdos713C4.K22 ⊑ H) {a c : ℝ} (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a ∈ Set.range ((↑) : ℚ → ℝ) := by
  refine ⟨3 / 2, ?_⟩
  simpa using (exponent_eq_of_bipartition H S hB hdeg hlo hc h).symm

end Erdos713DRC

#print axioms Erdos713DRC.rational_of_bipartition
