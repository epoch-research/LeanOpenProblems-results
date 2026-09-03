import FormalConjecturesUtil
import Submission.Verified

open Filter SimpleGraph Asymptotics

namespace Erdos713Structural
open Finset Erdos713C6 Erdos713Reduction
universe u

theorem matrix_sandwich (R : Fin 3 → Fin 3 → Prop)
    (hd : ∀ v, 2 ≤ Nat.card ((bipGraph R).neighborSet v)) :
    (Erdos713Norm.K33 ⊑ bipGraph R ∧ bipGraph R ⊑ Erdos713Norm.K33) ∨
    (Erdos713C4.K22 ⊑ bipGraph R ∧ bipGraph R ⊑ Erdos713Minus.D33) ∨
    (C6 ⊑ bipGraph R ∧ bipGraph R ⊑ C6) := by
  classical
  by_cases hAll : ∀ i j, R i j
  · have he : bipGraph R = Erdos713Norm.K33 := by
      ext u v
      cases u <;> cases v <;> simp [bipGraph, Erdos713Norm.K33, completeBipartiteGraph, hAll]
    rw [he]
    exact Or.inl ⟨.refl _, .refl _⟩
  push_neg at hAll
  obtain ⟨i, j, hij⟩ := hAll
  have hhi := Erdos713Six.matrix_contained_minus hij
  by_cases hC4 : Erdos713C4.K22 ⊑ bipGraph R
  · exact Or.inr (Or.inl ⟨hC4, hhi⟩)
  have hTwo (i : Fin 3) : ∃ j k, j ≠ k ∧ R i j ∧ R i k := by
    have hd' : 2 ≤ (bipGraph R).degree (Sum.inl i) := by
      simpa only [Nat.card_eq_fintype_card, card_neighborSet_eq_degree] using hd (Sum.inl i)
    obtain ⟨x, y, hx, hy, hxy⟩ := Erdos713SmallCore.exists_two_neighbors (bipGraph R) (Sum.inl i) hd'
    obtain ⟨j, hj, hij⟩ := right_of_adj_left hx
    obtain ⟨k, hk, hik⟩ := right_of_adj_left hy
    exact ⟨j, k, fun he => hxy (hj.trans ((congrArg Sum.inr he).trans hk.symm)), hij, hik⟩
  have hNo : ∀ i k j l, i ≠ k → j ≠ l → R i j → R k j → R i l → R k l → False := by
    intro i k j l hik hjl hij hkj hil hkl
    exact Erdos713C4.no_rectangle hC4 (u := Sum.inl i) (v := Sum.inl k)
      (a := Sum.inr j) (b := Sum.inr l) (by simpa using hik) (by simpa using hjl) hij hkj hil hkl
  obtain ⟨σ, hσ⟩ := Erdos713Six.complement_permutation R hTwo hNo
  let e : C6 ≃g bipGraph R := Erdos713Six.cycle_crown_iso.trans (Erdos713Six.crown_matrix_iso R σ hσ)
  exact Or.inr (Or.inr ⟨⟨e.toCopy⟩, ⟨e.symm.toCopy⟩⟩)


theorem reduces_of_small_matrix_iso {W : Type*} [Fintype W] (H : SimpleGraph W)
    (R : Fin 3 → Fin 3 → Prop) (e : H ≃g bipGraph R)
    (hd : ∀ v, 2 ≤ Nat.card ((bipGraph R).neighborSet v)) : Reduces W H := by
  rcases matrix_sandwich R hd with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
  · exact .core3 (hlo.trans ⟨e.symm.toCopy⟩) ((show H ⊑ bipGraph R from ⟨e.toCopy⟩).trans hhi)
  · exact .minus (hlo.trans ⟨e.symm.toCopy⟩) ((show H ⊑ bipGraph R from ⟨e.toCopy⟩).trans hhi)
  · exact .cycle6 (hlo.trans ⟨e.symm.toCopy⟩) ((show H ⊑ bipGraph R from ⟨e.toCopy⟩).trans hhi)

theorem reduces_core_of_card_le_six {W : Type*} [Fintype W] [Nonempty W]
    (H : SimpleGraph W) (hB : H.IsBipartite) (hcard : Fintype.card W ≤ 6)
    (hd : ∀ v, 2 ≤ Nat.card (H.neighborSet v)) : Reduces W H := by
  classical
  obtain ⟨χ⟩ := hB
  let S : Set W := {v | χ v = 0}
  have hS : H.IsBipartiteWith S Sᶜ := by
    refine ⟨disjoint_compl_right, ?_⟩
    intro u v huv
    have hχ := χ.valid huv
    simp only [S, Set.mem_setOf_eq, Set.mem_compl_iff]
    omega
  have hd' : ∀ v, 2 ≤ H.degree v := by
    intro v
    simpa only [Nat.card_eq_fintype_card, card_neighborSet_eq_degree] using hd v
  by_cases hcS : Nat.card S ≤ 2
  · have hhi := Erdos713SmallCore.contained_of_small_bipartition H S hcS hS
    have hlo := Erdos713SmallCore.contains_K22_of_degree_two H hd' hhi
    exact .core hlo hhi
  by_cases hcSc : Nat.card ↥(Sᶜ) ≤ 2
  · have hhi := Erdos713SmallCore.contained_of_small_bipartition H Sᶜ hcSc
      (by simpa only [compl_compl] using hS.symm)
    have hlo := Erdos713SmallCore.contains_K22_of_degree_two H hd' hhi
    exact .core hlo hhi
  have hcomp : Nat.card ↥(Sᶜ) = Fintype.card W - Nat.card S := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_compl_set]
  have hcardS : Nat.card S ≤ Fintype.card W := by
    simpa only [Nat.card_eq_fintype_card] using Fintype.card_subtype_le (· ∈ S)
  obtain ⟨R, ⟨e⟩⟩ := Erdos713Six.exists_matrix_iso H S hS (by omega) (by omega)
  have hDeg : ∀ v, 2 ≤ Nat.card ((bipGraph R).neighborSet v) := by
    intro v
    rw [Nat.card_congr (e.symm.mapNeighborSet v)]
    exact hd (e.symm v)
  exact reduces_of_small_matrix_iso H R e hDeg

noncomputable def rightNeighborEquiv {A B : Type*} (R : A → B → Prop) (b : B) :
    (bipGraph R).neighborSet (Sum.inr b) ≃ {a // R a b} where
  toFun x := by
    obtain ⟨x, hx⟩ := x
    cases x with
    | inl a => exact ⟨a, hx⟩
    | inr b' => exact hx.elim
  invFun a := ⟨Sum.inl a.val, a.prop⟩
  left_inv x := by
    obtain ⟨x, hx⟩ := x
    cases x with
    | inl a => rfl
    | inr b' => exact hx.elim
  right_inv a := rfl

theorem reduces_matrix_core {B : Type*} [Fintype B] (R : Fin 3 → B → Prop)
    (hd : ∀ v, 2 ≤ Nat.card ((bipGraph R).neighborSet v)) : Reduces (Fin 3 ⊕ B) (bipGraph R) := by
  classical
  by_cases hFull : 3 ≤ Nat.card {b // ∀ i, R i b}
  · exact .core3 (Erdos713ThreeSide.contains_K33_of_three_full_columns R hFull)
      (Erdos713ThreeSide.matrix_contained_K3t R)
  by_cases hC4 : Erdos713C4.K22 ⊑ bipGraph R
  · let S : Set (Fin 3 ⊕ B) := {v | v.isLeft}
    let P : Finset B := univ.filter (fun b => ∀ i, R i b)
    let E : Set (Fin 3 ⊕ B) := (P.image (Sum.inr : B → Fin 3 ⊕ B) : Set (Fin 3 ⊕ B))
    have hB : (bipGraph R).IsBipartiteWith S Sᶜ := by
      refine ⟨disjoint_compl_right, ?_⟩
      intro u v huv
      cases u <;> cases v <;> simp [bipGraph] at huv ⊢
      all_goals simp [S]
    have hE : Nat.card E ≤ 2 := by
      have hP : P.card = Nat.card {b // ∀ i, R i b} := by
        simp only [P, Nat.card_eq_fintype_card, Fintype.card_subtype]
      simpa only [E, Nat.card_coe_set_eq, Set.ncard_coe_finset,
        card_image_of_injective _ Sum.inr_injective, hP] using
        (show Nat.card {b // ∀ i, R i b} ≤ 2 by omega)
    apply Reduces.twoExceptions S E hB hE ?_ hC4
    intro v hv hvE
    cases v with
    | inl a => simp [S] at hv
    | inr b =>
      have hb : ¬∀ i, R i b := by simpa [E, P] using hvE
      rw [Nat.card_congr (rightNeighborEquiv R b)]
      exact Erdos713ThreeSide.nonfull_column_small R b hb
  have hcard := Erdos713ThreeSide.right_card_le_three_of_no_rectangle R (fun b => hd (Sum.inr b)) hC4
  apply reduces_core_of_card_le_six (bipGraph R) ?_ ?_ hd
  · refine ⟨⟨Sum.elim (fun _ => 0) (fun _ => 1), ?_⟩⟩
    intro u v huv
    cases u <;> cases v <;> simp [bipGraph] at huv ⊢
    all_goals decide
  · simp only [Fintype.card_sum, Fintype.card_fin]
    omega

theorem reduces_core_of_small_bipartition {W : Type*} [Fintype W] [Nonempty W]
    (H : SimpleGraph W) (S : Set W) (hB : H.IsBipartiteWith S Sᶜ) (hS : Nat.card S ≤ 3)
    (hd : ∀ v, 2 ≤ Nat.card (H.neighborSet v)) : Reduces W H := by
  classical
  by_cases hS2 : Nat.card S ≤ 2
  · have hhi := Erdos713SmallCore.contained_of_small_bipartition H S hS2 hB
    have hd' : ∀ v, 2 ≤ H.degree v := by
      intro v
      simpa only [Nat.card_eq_fintype_card, card_neighborSet_eq_degree] using hd v
    have hlo := Erdos713SmallCore.contains_K22_of_degree_two H hd' hhi
    exact .core hlo hhi
  obtain ⟨R, ⟨e⟩⟩ := Erdos713ThreeSide.exists_matrix_iso H S hB (by omega)
  have hDeg : ∀ v, 2 ≤ Nat.card ((bipGraph R).neighborSet v) := by
    intro v
    rw [Nat.card_congr (e.symm.mapNeighborSet v)]
    exact hd (e.symm v)
  exact .iso e (reduces_matrix_core R hDeg)

theorem reduces_of_small_bipartition {W : Type u} [Fintype W]
    (H : SimpleGraph W) (S : Set W) (hB : H.IsBipartiteWith S Sᶜ) (hS : Nat.card S ≤ 3) : Reduces W H := by
  classical
  suffices hP : ∀ k : ℕ, ∀ (W : Type u) [Fintype W], Fintype.card W = k →
      ∀ (G : SimpleGraph W) (S : Set W), G.IsBipartiteWith S Sᶜ → Nat.card S ≤ 3 → Reduces W G from
    hP _ W rfl H S hB hS
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro W _ hW G S hB hS
    by_cases hne : Nonempty W
    swap
    · letI : IsEmpty W := not_nonempty_iff.mp hne
      exact .forest (by intro v; exact isEmptyElim v)
    letI := hne
    by_cases hd : ∀ v, 2 ≤ Nat.card (G.neighborSet v)
    · exact reduces_core_of_small_bipartition G S hB hS hd
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
    have hRed := ih _ hsmall _ rfl (G.induce {x}ᶜ) T hB' hT
    have hx01 : G.degree x = 0 ∨ G.degree x = 1 := by omega
    rcases hx01 with hx0 | hx1
    · apply Reduces.isolated (x := x) _ hRed
      simpa only [Nat.card_eq_fintype_card, card_neighborSet_eq_degree] using hx0
    · obtain ⟨y, hxy, _⟩ := degree_eq_one_iff_existsUnique_adj.mp hx1
      apply Reduces.leaf (x := x) (y := y) _ hxy hRed
      simpa only [Nat.card_eq_fintype_card, card_neighborSet_eq_degree] using hx1

theorem reduces_of_card_le_seven {W : Type*} [Fintype W]
    (H : SimpleGraph W) (hB : H.IsBipartite) (hcard : Fintype.card W ≤ 7) : Reduces W H := by
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
  · exact reduces_of_small_bipartition H S hS hcS
  have hcomp : Nat.card ↥(Sᶜ) = Fintype.card W - Nat.card S := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_compl_set]
  exact reduces_of_small_bipartition H Sᶜ
    (by simpa only [compl_compl] using hS.symm) (by omega)

end Erdos713Structural

#print axioms Erdos713Structural.reduces_matrix_core
#print axioms Erdos713Structural.reduces_of_small_bipartition
#print axioms Erdos713Structural.reduces_of_card_le_seven
