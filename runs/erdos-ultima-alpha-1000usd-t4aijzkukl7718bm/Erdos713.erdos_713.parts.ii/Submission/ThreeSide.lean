import FormalConjecturesUtil
import Submission.Verified

open Filter SimpleGraph Asymptotics

namespace Erdos713ThreeSide
open Finset Erdos713C6

theorem complement_of_pair : ∀ i j : Fin 3, i ≠ j →
    ∃ k : Fin 3, ∀ a, a ≠ k → a = i ∨ a = j := by decide

theorem pair_avoiding : ∀ k : Fin 3, ∃ i j : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k := by decide

open scoped Classical in
theorem right_card_le_three_of_no_rectangle {B : Type*} [Fintype B]
    (R : Fin 3 → B → Prop)
    (hd : ∀ b, 2 ≤ Nat.card ((bipGraph R).neighborSet (Sum.inr b)))
    (hfree : Erdos713C4.K22.Free (bipGraph R)) : Fintype.card B ≤ 3 := by
  classical
  have hcol (b : B) : ∃ k : Fin 3, ∀ a, a ≠ k → R a b := by
    have hd' : 2 ≤ (bipGraph R).degree (Sum.inr b) := by
      simpa only [Nat.card_eq_fintype_card, card_neighborSet_eq_degree] using hd b
    obtain ⟨x, y, hx, hy, hxy⟩ := Erdos713SmallCore.exists_two_neighbors (bipGraph R) (Sum.inr b) hd'
    obtain ⟨i, hxi, hib⟩ := left_of_adj_right hx
    obtain ⟨j, hyj, hjb⟩ := left_of_adj_right hy
    have hij : i ≠ j := fun he => hxy (hxi.trans ((congrArg Sum.inl he).trans hyj.symm))
    obtain ⟨k, hk⟩ := complement_of_pair i j hij
    refine ⟨k, ?_⟩
    intro a ha
    rcases hk a ha with rfl | rfl
    · exact hib
    · exact hjb
  choose k hk using hcol
  have hinj : Function.Injective k := by
    intro b b' hbb
    by_contra hne
    obtain ⟨i, j, hij, hik, hjk⟩ := pair_avoiding (k b)
    exact Erdos713C4.no_rectangle hfree (u := Sum.inl i) (v := Sum.inl j)
      (a := Sum.inr b) (b := Sum.inr b') (by simpa using hij) (by simpa using hne)
      (hk b i hik) (hk b j hjk) (hk b' i (hbb ▸ hik)) (hk b' j (hbb ▸ hjk))
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective k hinj

theorem matrix_contained_K3t {B : Type*} [Fintype B] (R : Fin 3 → B → Prop) :
    bipGraph R ⊑ Erdos713K3t.K3t (Fintype.card B) := by
  classical
  let e := Fintype.equivFin B
  refine ⟨⟨⟨Sum.map id e, ?_⟩, Sum.map_injective.mpr ⟨Function.injective_id, e.injective⟩⟩⟩
  intro u v huv
  cases u <;> cases v <;> simp_all [bipGraph, Erdos713K3t.K3t, completeBipartiteGraph]

theorem contains_K33_of_three_full_columns {B : Type*} [Fintype B]
    (R : Fin 3 → B → Prop) (hc : 3 ≤ Nat.card {b // ∀ a, R a b}) :
    Erdos713Norm.K33 ⊑ bipGraph R := by
  classical
  let e : Fin 3 ↪ {b // ∀ a, R a b} := Classical.choice (Function.Embedding.nonempty_of_card_le
    (by simpa only [Fintype.card_fin, Nat.card_eq_fintype_card] using hc))
  have he : Erdos713Norm.K33 = bipGraph (fun (_ _ : Fin 3) => True) := by
    ext u v
    cases u <;> cases v <;> simp [Erdos713Norm.K33, completeBipartiteGraph, bipGraph]
  rw [he]
  apply Erdos713Anchors.bipGraph_contained_of_maps _ _ Sum.inl (fun b => Sum.inr (e b).val)
    Sum.inl_injective (Sum.inr_injective.comp (Subtype.val_injective.comp e.injective)) (by simp)
  intro a b _
  exact (e b).prop a

open scoped Classical in
theorem nonfull_column_small {B : Type*} (R : Fin 3 → B → Prop) (b : B)
    (hb : ¬∀ a, R a b) : Nat.card {a // R a b} ≤ 2 := by
  classical
  have hne : (univ.filter (R · b) : Finset (Fin 3)) ≠ univ := by
    intro he
    apply hb
    intro a
    have ha : a ∈ univ.filter (R · b) := by rw [he]; exact mem_univ _
    exact (mem_filter.mp ha).2
  have hc := (card_lt_iff_ne_univ _).mpr hne
  simp only [Fintype.card_fin] at hc
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using (show
    (univ.filter (R · b)).card ≤ 2 by omega)

theorem rational_matrix_core {B : Type*} [Fintype B] (R : Fin 3 → B → Prop)
    (hd : ∀ v, 2 ≤ Nat.card ((bipGraph R).neighborSet v)) {a c : ℝ} (ha : 1 < a) (hc : 0 < c)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n (bipGraph R) : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a ∈ Set.range ((↑) : ℚ → ℝ) := by
  classical
  by_cases hFull : 3 ≤ Nat.card {b // ∀ i, R i b}
  · exact Erdos713K3t.rational_exponent_of_containment
      (contains_K33_of_three_full_columns R hFull) (matrix_contained_K3t R) (by linarith) hc h
  by_cases hC4 : Erdos713C4.K22 ⊑ bipGraph R
  · exact Erdos713Anchors.rational_of_exceptional_columns R {b | ∀ i, R i b}
      (by change Nat.card {b // ∀ i, R i b} ≤ 2; omega) (fun b hb => nonfull_column_small R b hb) hC4 (.refl _) hc.ne' h
  have hcard := right_card_le_three_of_no_rectangle R (fun b => hd (Sum.inr b)) hC4
  apply Erdos713Six.rational_core_of_card_le_six (bipGraph R) ?_ ?_ hd ha hc h
  · refine ⟨⟨Sum.elim (fun _ => 0) (fun _ => 1), ?_⟩⟩
    intro u v huv
    cases u <;> cases v <;> simp_all [bipGraph]
  · simp only [Fintype.card_sum, Fintype.card_fin]
    omega

end Erdos713ThreeSide

#print axioms Erdos713ThreeSide.rational_matrix_core

namespace Erdos713ThreeSide
open Finset Erdos713C6
universe u

theorem exists_matrix_iso {W : Type*} [Fintype W] (H : SimpleGraph W) (S : Set W)
    (hB : H.IsBipartiteWith S Sᶜ) (hS : Nat.card S = 3) :
    ∃ R : Fin 3 → ↥(Sᶜ) → Prop, Nonempty (H ≃g bipGraph R) := by
  classical
  let eL : S ≃ Fin 3 := Fintype.equivFinOfCardEq (by simpa only [Nat.card_eq_fintype_card] using hS)
  let eR : ↥(Sᶜ) ≃ ↥(Sᶜ) := Equiv.refl _
  let e : W ≃ Fin 3 ⊕ ↥(Sᶜ) := (Equiv.Set.sumCompl S).symm.trans (Equiv.sumCongr eL eR)
  let R : Fin 3 → ↥(Sᶜ) → Prop := fun i j => H.Adj (e.symm (Sum.inl i)) (e.symm (Sum.inr j))
  have hl (i : Fin 3) : e.symm (Sum.inl i) ∈ S := (eL.symm i).prop
  have hr (j : ↥(Sᶜ)) : e.symm (Sum.inr j) ∈ Sᶜ := (eR.symm j).prop
  have hnoL (i j : Fin 3) : ¬H.Adj (e.symm (Sum.inl i)) (e.symm (Sum.inl j)) := by
    intro hij
    exact (hB.mem_of_mem_adj (hl i) hij) (hl j)
  have hnoR (i j : ↥(Sᶜ)) : ¬H.Adj (e.symm (Sum.inr i)) (e.symm (Sum.inr j)) := by
    intro hij
    exact hr j (hB.symm.mem_of_mem_adj (hr i) hij)
  have he : H.comap e.symm = bipGraph R := by
    ext u v
    cases u with
    | inl i =>
      cases v with
      | inl j => exact iff_false_intro (hnoL i j)
      | inr j => rfl
    | inr i =>
      cases v with
      | inl j => exact adj_comm H _ _
      | inr j => exact iff_false_intro (hnoR i j)
  refine ⟨R, ⟨?_⟩⟩
  rw [← he]
  exact (SimpleGraph.Iso.comap e.symm H).symm

theorem rational_core_of_small_bipartition {W : Type*} [Fintype W] [Nonempty W]
    (H : SimpleGraph W) (S : Set W) (hB : H.IsBipartiteWith S Sᶜ) (hS : Nat.card S ≤ 3)
    (hd : ∀ v, 2 ≤ Nat.card (H.neighborSet v)) {a c : ℝ} (ha : 1 < a) (hc : 0 < c)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a ∈ Set.range ((↑) : ℚ → ℝ) := by
  classical
  by_cases hS2 : Nat.card S ≤ 2
  · have hhi := Erdos713SmallCore.contained_of_small_bipartition H S hS2 hB
    have hd' : ∀ v, 2 ≤ H.degree v := by
      intro v
      simpa only [Nat.card_eq_fintype_card, card_neighborSet_eq_degree] using hd v
    have hlo := Erdos713SmallCore.contains_K22_of_degree_two H hd' hhi
    exact Erdos713K2t.rational_exponent_of_containment hlo hhi hc h
  obtain ⟨R, ⟨e⟩⟩ := exists_matrix_iso H S hB (by omega)
  have hDeg : ∀ v, 2 ≤ Nat.card ((bipGraph R).neighborSet v) := by
    intro v
    rw [Nat.card_congr (e.symm.mapNeighborSet v)]
    exact hd (e.symm v)
  apply rational_matrix_core R hDeg ha hc
  simpa only [extremalNumber_congr_right e] using h

/-- A bipartite forbidden graph with a colour class of size at most three has a
rational pure-power asymptotic exponent, including leaves and isolated vertices. -/
theorem rational_of_small_bipartition {W : Type u} [Fintype W]
    (H : SimpleGraph W) (S : Set W) (hB : H.IsBipartiteWith S Sᶜ) (hS : Nat.card S ≤ 3)
    {a c : ℝ} (ha : 1 ≤ a) (hc : 0 < c)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a ∈ Set.range ((↑) : ℚ → ℝ) := by
  classical
  by_cases ha1 : a = 1
  · exact ⟨1, by simpa using ha1.symm⟩
  have ha' : 1 < a := lt_of_le_of_ne ha (Ne.symm ha1)
  suffices hP : ∀ k : ℕ, ∀ (W : Type u) [Fintype W], Fintype.card W = k →
      ∀ (G : SimpleGraph W) (S : Set W), G.IsBipartiteWith S Sᶜ → Nat.card S ≤ 3 →
        IsEquivalent atTop (fun n : ℕ => (extremalNumber n G : ℝ))
          (fun n : ℕ => c * (n : ℝ) ^ a) → a ∈ Set.range ((↑) : ℚ → ℝ) from
    hP _ W rfl H S hB hS h
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro W _ hW G S hB hS h
    by_cases hd : ∀ v, 2 ≤ Nat.card (G.neighborSet v)
    · letI : Nonempty W := Erdos713Core.nonempty_of_asymptotic G hc.ne' h
      exact rational_core_of_small_bipartition G S hB hS hd ha' hc h
    push_neg at hd
    obtain ⟨x, hx⟩ := hd
    have hx' : G.degree x < 2 := by
      simpa only [Nat.card_eq_fintype_card, card_neighborSet_eq_degree] using hx
    have hsmall : Fintype.card ↥({x}ᶜ : Set W) < k :=
      (Fintype.card_subtype_lt (x := x) (by simp)).trans_eq hW
    let T : Set ↥({x}ᶜ : Set W) := {v | v.val ∈ S}
    have hB' : (G.induce {x}ᶜ).IsBipartiteWith T Tᶜ := by
      refine ⟨disjoint_compl_right, ?_⟩
      intro u v huv
      exact hB.2 huv
    have hT : Nat.card T ≤ 3 := by
      let f : T ↪ S := ⟨fun v => ⟨v.val.val, v.prop⟩, by
        intro u v huv
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : S => z.val) huv⟩
      have hh := Fintype.card_le_of_embedding f
      simp only [Fintype.card_eq_nat_card] at hh
      exact hh.trans hS
    apply ih _ hsmall _ rfl (G.induce {x}ᶜ) T hB' hT
    have hx01 : G.degree x = 0 ∨ G.degree x = 1 := by omega
    rcases hx01 with hx0 | hx1
    · exact Erdos713Leaf.isolated_asymptotic G hx0 h
    · obtain ⟨y, hxy, _⟩ := degree_eq_one_iff_existsUnique_adj.mp hx1
      exact Erdos713Leaf.leaf_asymptotic G hx1 hxy ha' hc.ne' h

theorem rational_exponent_all_small_graphs {W : Type*} [Fintype W]
    (H : SimpleGraph W) (hB : H.IsBipartite) (hcard : Fintype.card W ≤ 7)
    {a c : ℝ} (ha : 1 ≤ a) (hc : 0 < c)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a ∈ Set.range ((↑) : ℚ → ℝ) := by
  classical
  obtain ⟨χ⟩ := hB
  let S : Set W := {v | χ v = 0}
  have hS : H.IsBipartiteWith S Sᶜ := by
    refine ⟨disjoint_compl_right, ?_⟩
    intro u v huv
    have hχ := χ.valid huv
    simp only [S, Set.mem_setOf_eq, Set.mem_compl_iff]
    omega
  by_cases hcS : Nat.card S ≤ 3
  · exact rational_of_small_bipartition H S hS hcS ha hc h
  have hcomp : Nat.card ↥(Sᶜ) = Fintype.card W - Nat.card S := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_compl_set]
  exact rational_of_small_bipartition H Sᶜ
    (by simpa only [compl_compl] using hS.symm) (by omega) ha hc h

end Erdos713ThreeSide

#print axioms Erdos713ThreeSide.rational_of_small_bipartition
#print axioms Erdos713ThreeSide.rational_exponent_all_small_graphs
