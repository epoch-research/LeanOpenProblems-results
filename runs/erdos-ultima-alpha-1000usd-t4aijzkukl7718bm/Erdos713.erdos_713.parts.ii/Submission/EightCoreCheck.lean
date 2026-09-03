import FormalConjecturesUtil
import Submission.EightCoreDataPrefix

/-! Classification of the first core size not covered by the existing rate reductions. -/
namespace Erdos713EightCore
open SimpleGraph Finset
open Erdos713C6 Erdos713Reduction

abbrev Graph (r : Rows) := bipGraph (fun i j => bit r i j = true)

instance (r : Rows) : DecidableRel (Graph r).Adj := by
  intro u v
  cases u <;> cases v <;> dsimp [Graph, bipGraph] <;> infer_instance

noncomputable def leftNeighborEquiv (r : Rows) (i : Fin 4) :
    (Graph r).neighborSet (Sum.inl i) ≃ {j : Fin 4 // bit r i j = true} where
  toFun x := by
    obtain ⟨x,hx⟩ := x
    cases x with
    | inl j => exact hx.elim
    | inr j => exact ⟨j,hx⟩
  invFun j := ⟨Sum.inr j.val,j.prop⟩
  left_inv x := by
    obtain ⟨x,hx⟩ := x
    cases x with
    | inl j => exact hx.elim
    | inr j => rfl
  right_inv j := rfl

lemma count_four (f : Fin 4 → Bool) : Nat.card {j // f j = true} =
    (f 0).toNat + (f 1).toNat + (f 2).toNat + (f 3).toNat := by
  classical
  simp only [Nat.card_eq_fintype_card,Fintype.card_subtype,Finset.card_eq_sum_ones,
    Finset.sum_filter,Fin.sum_univ_succ]
  cases h0 : f 0 <;> cases h1 : f 1 <;> cases h2 : f 2 <;> cases h3 : f 3 <;>
    simp [h0,h1,h2,h3,Bool.toNat]

lemma degree_left (r : Rows) (i : Fin 4) :
    Nat.card ((Graph r).neighborSet (Sum.inl i)) = rowCount r i := by
  rw [Nat.card_congr (leftNeighborEquiv r i)]
  exact count_four _

lemma degree_right (r : Rows) (j : Fin 4) :
    Nat.card ((Graph r).neighborSet (Sum.inr j)) = colCount r j := by
  rw [Nat.card_congr (Erdos713Structural.rightNeighborEquiv (fun i j => bit r i j = true) j)]
  exact count_four _

lemma good_iff (r : Rows) : Good r ↔ ∀ v, 2 ≤ Nat.card ((Graph r).neighborSet v) := by
  constructor
  · rintro ⟨hl,hr⟩ v
    cases v with
    | inl i => simpa only [degree_left] using hl i
    | inr j => simpa only [degree_right] using hr j
  · intro hd
    exact ⟨fun i => (degree_left r i) ▸ hd (Sum.inl i),
      fun j => (degree_right r j) ▸ hd (Sum.inr j)⟩

def transportIso (r s : Rows) (p q : Equiv.Perm (Fin 4))
    (h : ∀ i j, bit s i j = bit r (p i) (q j)) : Graph s ≃g Graph r where
  toEquiv := Equiv.sumCongr p q
  map_rel_iff' := by
    intro u v
    cases u <;> cases v <;> dsimp [Graph,bipGraph] <;> simp only [h]

def transportFlipIso (r s : Rows) (p q : Equiv.Perm (Fin 4))
    (h : ∀ i j, bit s i j = bit r (q j) (p i)) : Graph s ≃g Graph r where
  toEquiv := (Equiv.sumCongr p q).trans (Equiv.sumComm _ _)
  map_rel_iff' := by
    intro u v
    cases u <;> cases v <;> dsimp [Graph,bipGraph] <;> simp only [h]

lemma left_bipartition (r : Rows) :
    (Graph r).IsBipartiteWith {v | v.isLeft} {v | v.isLeft}ᶜ := by
  refine ⟨disjoint_compl_right,?_⟩
  intro u v huv
  cases u <;> cases v <;> simp [Graph,bipGraph] at huv ⊢

lemma rectangle_copy (r : Rows) (a b : Fin 2 → Fin 4)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (he : ∀ i j, bit r (a i) (b j) = true) : Erdos713C4.K22 ⊑ Graph r := by
  refine ⟨⟨⟨Sum.elim (Sum.inl ∘ a) (Sum.inr ∘ b),?_⟩,?_⟩⟩
  · intro u v huv
    cases u <;> cases v <;> simp [Erdos713C4.K22,completeBipartiteGraph] at huv
    all_goals exact he _ _
  · intro u v huv
    change Sum.elim (Sum.inl ∘ a) (Sum.inr ∘ b) u =
      Sum.elim (Sum.inl ∘ a) (Sum.inr ∘ b) v at huv
    cases u with
    | inl i =>
      cases v with
      | inl j => exact congrArg Sum.inl (ha (Sum.inl.inj huv))
      | inr j => cases huv
    | inr i =>
      cases v with
      | inl j => cases huv
      | inr j => exact congrArg Sum.inr (hb (Sum.inr.inj huv))

lemma reduces_of_two_exception_columns (r : Rows) (E : Finset (Fin 4))
    (hE : E.card ≤ 2) (hd : ∀ j, j ∉ E → colCount r j ≤ 2)
    (hlo : Erdos713C4.K22 ⊑ Graph r) : Reduces (Fin 4 ⊕ Fin 4) (Graph r) := by
  classical
  let S : Set (Fin 4 ⊕ Fin 4) := {v | v.isLeft}
  let T : Set (Fin 4 ⊕ Fin 4) := (E.image Sum.inr : Finset (Fin 4 ⊕ Fin 4))
  apply Reduces.twoExceptions S T (left_bipartition r) ?_ ?_ hlo
  · simpa only [T,Nat.card_coe_set_eq,Set.ncard_coe_finset,
      card_image_of_injective _ Sum.inr_injective] using hE
  · intro v hv hvT
    cases v with
    | inl i => simp [S] at hv
    | inr j =>
      rw [degree_right]
      exact hd j (by simpa [T] using hvT)

lemma contained_of_map {A B : Type*} (G : SimpleGraph A) (H : SimpleGraph B) (f : A → B)
    (hf : Function.Injective f) (hAdj : ∀ u v, G.Adj u v → H.Adj (f u) (f v)) : G ⊑ H :=
  ⟨⟨⟨f,fun {u v} h => hAdj u v h⟩,hf⟩⟩

local instance : DecidableRel Erdos713Minus44.D44.Adj := by
  intro u v
  cases u <;> cases v <;> dsimp [Erdos713Minus44.D44,bipGraph] <;> infer_instance

local instance : DecidableRel (Erdos713Theta3.theta 3).Adj := by
  rintro (i | i) (j | j) <;> cases i <;> cases j <;>
    dsimp [Erdos713Theta3.theta,bipGraph,Erdos713Theta3.Rel] <;> infer_instance

local instance : DecidableRel Erdos713Norm.K33.Adj := by
  intro u v
  cases u <;> cases v <;> dsimp [Erdos713Norm.K33,completeBipartiteGraph] <;> infer_instance

lemma representative_3_reduces : Reduces (Fin 4 ⊕ Fin 4) (Graph (representative 3)) := by
  let p : Fin 4 ≃ Option (Fin 3) := Equiv.ofBijective
    ![some 0,some 1,some 2,none] (by decide)
  let q : Fin 4 ≃ Option (Fin 3) := Equiv.ofBijective
    ![none,some 0,some 1,some 2] (by decide)
  let e : Graph (representative 3) ≃g Erdos713Theta3.theta 3 :=
    { toEquiv := Equiv.sumCongr p q
      map_rel_iff' := by decide }
  exact .iso e (.theta3 (Erdos713Theta3.c6_contained (by decide : 2 ≤ 3)) (.refl _))

lemma representative_0_reduces : Reduces (Fin 4 ⊕ Fin 4) (Graph (representative 0)) := by
  apply reduces_of_two_exception_columns (representative 0) ∅ (by decide) (by decide)
  exact rectangle_copy (representative 0) ![0, 1] ![0, 1] (by decide) (by decide) (by decide)

lemma representative_2_reduces : Reduces (Fin 4 ⊕ Fin 4) (Graph (representative 2)) := by
  apply reduces_of_two_exception_columns (representative 2) {0} (by decide) (by decide)
  exact rectangle_copy (representative 2) ![0, 1] ![0, 1] (by decide) (by decide) (by decide)

lemma representative_4_reduces : Reduces (Fin 4 ⊕ Fin 4) (Graph (representative 4)) := by
  apply reduces_of_two_exception_columns (representative 4) {0} (by decide) (by decide)
  exact rectangle_copy (representative 4) ![1, 3] ![0, 2] (by decide) (by decide) (by decide)

lemma representative_5_reduces : Reduces (Fin 4 ⊕ Fin 4) (Graph (representative 5)) := by
  apply reduces_of_two_exception_columns (representative 5) {0, 1} (by decide) (by decide)
  exact rectangle_copy (representative 5) ![0, 1] ![0, 1] (by decide) (by decide) (by decide)

lemma representative_6_reduces : Reduces (Fin 4 ⊕ Fin 4) (Graph (representative 6)) := by
  apply reduces_of_two_exception_columns (representative 6) {0, 1} (by decide) (by decide)
  exact rectangle_copy (representative 6) ![0, 1] ![0, 1] (by decide) (by decide) (by decide)

lemma representative_7_reduces : Reduces (Fin 4 ⊕ Fin 4) (Graph (representative 7)) := by
  apply reduces_of_two_exception_columns (representative 7) {0} (by decide) (by decide)
  exact rectangle_copy (representative 7) ![0, 3] ![0, 1] (by decide) (by decide) (by decide)

lemma representative_8_reduces : Reduces (Fin 4 ⊕ Fin 4) (Graph (representative 8)) := by
  apply reduces_of_two_exception_columns (representative 8) {0, 1} (by decide) (by decide)
  exact rectangle_copy (representative 8) ![0, 3] ![0, 1] (by decide) (by decide) (by decide)

lemma representative_9_reduces : Reduces (Fin 4 ⊕ Fin 4) (Graph (representative 9)) := by
  apply reduces_of_two_exception_columns (representative 9) {0, 1} (by decide) (by decide)
  exact rectangle_copy (representative 9) ![0, 2] ![0, 1] (by decide) (by decide) (by decide)

lemma representative_10_reduces : Reduces (Fin 4 ⊕ Fin 4) (Graph (representative 10)) := by
  apply reduces_of_two_exception_columns (representative 10) {1, 2} (by decide) (by decide)
  exact rectangle_copy (representative 10) ![2, 3] ![1, 2] (by decide) (by decide) (by decide)

lemma representative_11_reduces : Reduces (Fin 4 ⊕ Fin 4) (Graph (representative 11)) := by
  apply reduces_of_two_exception_columns (representative 11) {0, 2} (by decide) (by decide)
  exact rectangle_copy (representative 11) ![0, 1] ![0, 1] (by decide) (by decide) (by decide)

lemma representative_12_reduces : Reduces (Fin 4 ⊕ Fin 4) (Graph (representative 12)) := by
  apply reduces_of_two_exception_columns (representative 12) {0, 1} (by decide) (by decide)
  exact rectangle_copy (representative 12) ![0, 1] ![0, 1] (by decide) (by decide) (by decide)

lemma representative_13_reduces : Reduces (Fin 4 ⊕ Fin 4) (Graph (representative 13)) := by
  apply reduces_of_two_exception_columns (representative 13) {0, 1} (by decide) (by decide)
  exact rectangle_copy (representative 13) ![0, 2] ![0, 1] (by decide) (by decide) (by decide)

lemma representative_14_reduces : Reduces (Fin 4 ⊕ Fin 4) (Graph (representative 14)) := by
  let s : Rows := ![11, 13, 14, 12]
  let e : Graph s ≃g Graph (representative 14) :=
    transportFlipIso (representative 14) s (Equiv.refl _) (Equiv.refl _) (by decide)
  apply Reduces.iso e.symm
  apply reduces_of_two_exception_columns s {2, 3} (by decide) (by decide)
  exact rectangle_copy s ![0, 1] ![0, 3] (by decide) (by decide) (by decide)

lemma representative_15_reduces : Reduces (Fin 4 ⊕ Fin 4) (Graph (representative 15)) := by
  let s : Rows := ![11, 11, 14, 12]
  let e : Graph s ≃g Graph (representative 15) :=
    transportFlipIso (representative 15) s (Equiv.refl _) (Equiv.refl _) (by decide)
  apply Reduces.iso e.symm
  apply reduces_of_two_exception_columns s {1, 3} (by decide) (by decide)
  exact rectangle_copy s ![0, 1] ![0, 1] (by decide) (by decide) (by decide)

lemma representative_18_reduces : Reduces (Fin 4 ⊕ Fin 4) (Graph (representative 18)) := by
  apply reduces_of_two_exception_columns (representative 18) {0, 1} (by decide) (by decide)
  exact rectangle_copy (representative 18) ![0, 1] ![0, 1] (by decide) (by decide) (by decide)

lemma representative_19_reduces : Reduces (Fin 4 ⊕ Fin 4) (Graph (representative 19)) := by
  let s : Rows := ![15, 13, 14, 12]
  let e : Graph s ≃g Graph (representative 19) :=
    transportFlipIso (representative 19) s (Equiv.refl _) (Equiv.refl _) (by decide)
  apply Reduces.iso e.symm
  apply reduces_of_two_exception_columns s {2, 3} (by decide) (by decide)
  exact rectangle_copy s ![0, 1] ![0, 2] (by decide) (by decide) (by decide)

lemma representative_21_reduces : Reduces (Fin 4 ⊕ Fin 4) (Graph (representative 21)) := by
  let s : Rows := ![13, 13, 14, 14]
  let e : Graph s ≃g Graph (representative 21) :=
    transportFlipIso (representative 21) s (Equiv.refl _) (Equiv.refl _) (by decide)
  apply Reduces.iso e.symm
  apply reduces_of_two_exception_columns s {2, 3} (by decide) (by decide)
  exact rectangle_copy s ![0, 1] ![0, 2] (by decide) (by decide) (by decide)

lemma representative_22_reduces : Reduces (Fin 4 ⊕ Fin 4) (Graph (representative 22)) := by
  apply Reduces.minus4
  · exact contained_of_map Erdos713Norm.K33 (Graph (representative 22))
      (Sum.map (![1, 2, 3] : Fin 3 → Fin 4) (![0, 2, 3] : Fin 3 → Fin 4)) (by decide) (by decide)
  · exact contained_of_map (Graph (representative 22)) Erdos713Minus44.D44
      (Sum.map (![3, 0, 1, 2] : Fin 4 → Fin 4) (![0, 1, 3, 2] : Fin 4 → Fin 4)) (by decide) (by decide)

lemma representative_25_reduces : Reduces (Fin 4 ⊕ Fin 4) (Graph (representative 25)) := by
  apply Reduces.minus4
  · exact contained_of_map Erdos713Norm.K33 (Graph (representative 25))
      (Sum.map (![1, 2, 3] : Fin 3 → Fin 4) (![0, 1, 2] : Fin 3 → Fin 4)) (by decide) (by decide)
  · exact contained_of_map (Graph (representative 25)) Erdos713Minus44.D44
      (Sum.map (![3, 0, 1, 2] : Fin 4 → Fin 4) (![0, 1, 3, 2] : Fin 4 → Fin 4)) (by decide) (by decide)

lemma representative_26_reduces : Reduces (Fin 4 ⊕ Fin 4) (Graph (representative 26)) := by
  apply Reduces.minus4
  · exact contained_of_map Erdos713Norm.K33 (Graph (representative 26))
      (Sum.map (![1, 2, 3] : Fin 3 → Fin 4) (![0, 2, 3] : Fin 3 → Fin 4)) (by decide) (by decide)
  · exact contained_of_map (Graph (representative 26)) Erdos713Minus44.D44
      (Sum.map (![3, 0, 1, 2] : Fin 4 → Fin 4) (![0, 1, 3, 2] : Fin 4 → Fin 4)) (by decide) (by decide)

lemma representative_28_reduces : Reduces (Fin 4 ⊕ Fin 4) (Graph (representative 28)) := by
  apply Reduces.minus4
  · exact contained_of_map Erdos713Norm.K33 (Graph (representative 28))
      (Sum.map (![1, 2, 3] : Fin 3 → Fin 4) (![0, 1, 2] : Fin 3 → Fin 4)) (by decide) (by decide)
  · exact contained_of_map (Graph (representative 28)) Erdos713Minus44.D44
      (Sum.map (![3, 0, 1, 2] : Fin 4 → Fin 4) (![0, 1, 3, 2] : Fin 4 → Fin 4)) (by decide) (by decide)

lemma representative_29_reduces : Reduces (Fin 4 ⊕ Fin 4) (Graph (representative 29)) := by
  apply Reduces.minus4
  · exact contained_of_map Erdos713Norm.K33 (Graph (representative 29))
      (Sum.map (![0, 2, 3] : Fin 3 → Fin 4) (![0, 1, 2] : Fin 3 → Fin 4)) (by decide) (by decide)
  · exact contained_of_map (Graph (representative 29)) Erdos713Minus44.D44
      (Sum.map (![3, 0, 1, 2] : Fin 4 → Fin 4) (![0, 1, 2, 3] : Fin 4 → Fin 4)) (by decide) (by decide)

lemma representative_30_reduces : Reduces (Fin 4 ⊕ Fin 4) (Graph (representative 30)) := by
  apply Reduces.minus4
  · exact contained_of_map Erdos713Norm.K33 (Graph (representative 30))
      (Sum.map (![0, 1, 2] : Fin 3 → Fin 4) (![0, 1, 2] : Fin 3 → Fin 4)) (by decide) (by decide)
  · exact contained_of_map (Graph (representative 30)) Erdos713Minus44.D44
      (Sum.map (![3, 0, 1, 2] : Fin 4 → Fin 4) (![0, 1, 2, 3] : Fin 4 → Fin 4)) (by decide) (by decide)

def Exceptional (k : Fin 32) : Prop := k ∈ ({1, 16, 17, 20, 23, 24, 27, 31} : Finset (Fin 32))
instance (k : Fin 32) : Decidable (Exceptional k) := inferInstanceAs (Decidable (_ ∈ _))

lemma representative_reduces_or_exceptional (k : Fin 32) :
    Reduces (Fin 4 ⊕ Fin 4) (Graph (representative k)) ∨ Exceptional k := by
  fin_cases k
  · exact Or.inl representative_0_reduces
  · exact Or.inr (by decide)
  · exact Or.inl representative_2_reduces
  · exact Or.inl representative_3_reduces
  · exact Or.inl representative_4_reduces
  · exact Or.inl representative_5_reduces
  · exact Or.inl representative_6_reduces
  · exact Or.inl representative_7_reduces
  · exact Or.inl representative_8_reduces
  · exact Or.inl representative_9_reduces
  · exact Or.inl representative_10_reduces
  · exact Or.inl representative_11_reduces
  · exact Or.inl representative_12_reduces
  · exact Or.inl representative_13_reduces
  · exact Or.inl representative_14_reduces
  · exact Or.inl representative_15_reduces
  · exact Or.inr (by decide)
  · exact Or.inr (by decide)
  · exact Or.inl representative_18_reduces
  · exact Or.inl representative_19_reduces
  · exact Or.inr (by decide)
  · exact Or.inl representative_21_reduces
  · exact Or.inl representative_22_reduces
  · exact Or.inr (by decide)
  · exact Or.inr (by decide)
  · exact Or.inl representative_25_reduces
  · exact Or.inl representative_26_reduces
  · exact Or.inr (by decide)
  · exact Or.inl representative_28_reduces
  · exact Or.inl representative_29_reduces
  · exact Or.inl representative_30_reduces
  · exact Or.inr (by decide)

def pack (f : Fin 4 → Bool) : Fin 16 :=
  ⟨(f 0).toNat + 2*(f 1).toNat + 4*(f 2).toNat + 8*(f 3).toNat,by
    have h0 : (f 0).toNat ≤ 1 := by cases f 0 <;> decide
    have h1 : (f 1).toNat ≤ 1 := by cases f 1 <;> decide
    have h2 : (f 2).toNat ≤ 1 := by cases f 2 <;> decide
    have h3 : (f 3).toNat ≤ 1 := by cases f 3 <;> decide
    omega⟩

lemma pack_bit : ∀ (f : Fin 4 → Bool) (j : Fin 4), (pack f).val.testBit j.val = f j := by
  decide

lemma matrix_encoded (R : Fin 4 → Fin 4 → Prop) : ∃ r : Rows, bipGraph R = Graph r := by
  classical
  let r : Rows := fun i => pack (fun j => decide (R i j))
  refine ⟨r,?_⟩
  have he (i j : Fin 4) : bit r i j = decide (R i j) := pack_bit _ _
  ext u v
  cases u <;> cases v <;> dsimp [Graph,bipGraph] <;> simp only [he,decide_eq_true_eq]

lemma exists_matrix_iso {W : Type*} [Fintype W] (H : SimpleGraph W) (S : Set W)
    (hB : H.IsBipartiteWith S Sᶜ) (hS : Nat.card S = 4) (hSc : Nat.card ↥(Sᶜ) = 4) :
    ∃ r : Rows, Nonempty (H ≃g Graph r) := by
  classical
  let eL : S ≃ Fin 4 := Fintype.equivFinOfCardEq (by simpa only [Nat.card_eq_fintype_card] using hS)
  let eR : ↥(Sᶜ) ≃ Fin 4 := Fintype.equivFinOfCardEq (by simpa only [Nat.card_eq_fintype_card] using hSc)
  let e : W ≃ Fin 4 ⊕ Fin 4 := (Equiv.Set.sumCompl S).symm.trans (Equiv.sumCongr eL eR)
  let R : Fin 4 → Fin 4 → Prop := fun i j => H.Adj (e.symm (Sum.inl i)) (e.symm (Sum.inr j))
  have hl (i : Fin 4) : e.symm (Sum.inl i) ∈ S := (eL.symm i).prop
  have hr (j : Fin 4) : e.symm (Sum.inr j) ∈ Sᶜ := (eR.symm j).prop
  have hnoL (i j : Fin 4) : ¬H.Adj (e.symm (Sum.inl i)) (e.symm (Sum.inl j)) := by
    intro hij
    exact (hB.mem_of_mem_adj (hl i) hij) (hl j)
  have hnoR (i j : Fin 4) : ¬H.Adj (e.symm (Sum.inr i)) (e.symm (Sum.inr j)) := by
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
  obtain ⟨r,hr⟩ := matrix_encoded R
  refine ⟨r,⟨?_⟩⟩
  rw [← hr,← he]
  exact (SimpleGraph.Iso.comap e.symm H).symm


end Erdos713EightCore
