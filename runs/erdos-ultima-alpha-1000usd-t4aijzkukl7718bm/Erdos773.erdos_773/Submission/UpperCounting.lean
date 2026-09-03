import FormalConjecturesUtil

/-!
Counting reductions for upper bounds on Sidon subsets of the squares.
These are auxiliary results; they do not settle Erdős 773.
-/

namespace Erdos773

open Finset

def squareSumValues (N : ℕ) : Finset ℕ :=
  ((Icc 1 N) ×ˢ (Icc 1 N)).image (fun p : ℕ × ℕ => p.1 ^ 2 + p.2 ^ 2)

def unorderedPairSum : Sym2 ℕ → ℕ :=
  Sym2.lift ⟨fun a b : ℕ => a + b, Nat.add_comm⟩

lemma sidon_card_choose_le_squareSumValues {N : ℕ} {A : Finset ℕ}
    (hA : A ⊆ (Icc 1 N).image (fun n : ℕ => n ^ 2))
    (hs : IsSidon (A : Set ℕ)) :
    (A.card + 1).choose 2 ≤ (squareSumValues N).card := by
  rw [← Finset.card_sym2]
  apply Finset.card_le_card_of_injOn unorderedPairSum
  · intro p hp
    induction p using Sym2.ind with
    | _ a b =>
      obtain ⟨ha, hb⟩ := Finset.mk_mem_sym2_iff.mp hp
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (hA ha)
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (hA hb)
      exact Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩
  · intro p hp q hq he
    induction p using Sym2.ind with
    | _ a b =>
      induction q using Sym2.ind with
      | _ c d =>
        obtain ⟨ha, hb⟩ := Finset.mk_mem_sym2_iff.mp hp
        obtain ⟨hc, hd⟩ := Finset.mk_mem_sym2_iff.mp hq
        exact Sym2.eq_iff.mpr (hs a ha c hc b hb d hd he)

lemma maxSidon_card_choose_le_squareSumValues (N : ℕ) :
    (Finset.maxSidonSubsetCard
      ((Icc 1 N).image (fun n : ℕ => n ^ 2)) + 1).choose 2 ≤
      (squareSumValues N).card := by
  classical
  let S := (Icc 1 N).image (fun n : ℕ => n ^ 2)
  have hne : (S.powerset.filter (fun A : Finset ℕ => IsSidon (A : Set ℕ))).Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨by simp, ?_⟩⟩
    intro a ha
    simp at ha
  obtain ⟨A, hA, he⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  have hA' := Finset.mem_filter.mp hA
  change ((S.powerset.filter (fun A : Finset ℕ => IsSidon (A : Set ℕ))).sup
    Finset.card + 1).choose 2 ≤ _
  rw [he]
  exact sidon_card_choose_le_squareSumValues (Finset.mem_powerset.mp hA'.1) hA'.2

lemma squareSumValues_le (N : ℕ) {s : ℕ} (hs : s ∈ squareSumValues N) :
    s ≤ 2 * N ^ 2 := by
  obtain ⟨⟨a,b⟩, hp, rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
  have ha' := (Finset.mem_Icc.mp ha).2
  have hb' := (Finset.mem_Icc.mp hb).2
  have ha2 := Nat.pow_le_pow_left ha' 2
  have hb2 := Nat.pow_le_pow_left hb' 2
  dsimp at ha2 hb2 ⊢
  omega

lemma card_le_residue_capacity {S C : Finset ℕ} {L q : ℕ}
    (hL : ∀ n ∈ S, n ≤ L) (hC : ∀ n ∈ S, n % q ∈ C) :
    S.card ≤ C.card * (L / q + 1) := by
  calc
    S.card ≤ (C ×ˢ Finset.range (L / q + 1)).card := by
      apply Finset.card_le_card_of_injOn (fun n : ℕ => (n % q, n / q))
      · intro n hn
        exact Finset.mem_product.mpr ⟨hC n hn,
          Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (hL n hn)))⟩
      · intro n hn m hm he
        have hr : n % q = m % q := congrArg Prod.fst he
        have hd : n / q = m / q := congrArg Prod.snd he
        have hn' := Nat.mod_add_div n q
        have hm' := Nat.mod_add_div m q
        rw [hr, hd] at hn'
        omega
    _ = C.card * (L / q + 1) := by simp

lemma maxSidon_card_choose_le_residue_capacity (N q : ℕ)
    (C : Finset ℕ)
    (hC : ∀ a ∈ Icc 1 N, ∀ b ∈ Icc 1 N, (a ^ 2 + b ^ 2) % q ∈ C) :
    (Finset.maxSidonSubsetCard
      ((Icc 1 N).image (fun n : ℕ => n ^ 2)) + 1).choose 2 ≤
      C.card * (2 * N ^ 2 / q + 1) := by
  apply (maxSidon_card_choose_le_squareSumValues N).trans
  apply card_le_residue_capacity (fun n hn => squareSumValues_le N hn)
  intro n hn
  obtain ⟨⟨a,b⟩, hp, rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
  exact hC a ha b hb

#print axioms maxSidon_card_choose_le_residue_capacity

end Erdos773
