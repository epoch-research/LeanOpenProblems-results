import FormalConjecturesUtil

/-! Finite natural-number mixed-pair counts and their total mass. These are
auxiliary identities, not a construction for the conjecture. -/
namespace Erdos66NatPairAlgebra
open AdditiveCombinatorics
open scoped Classical

noncomputable def pairs (A B : Finset ℕ) (n : ℕ) : ℕ :=
  ((A.product B).filter (fun p ↦ p.1+p.2=n)).card

lemma pairs_self (A : Finset ℕ) (n : ℕ) : pairs A A n = sumRep (A : Set ℕ) n := by
  rw [pairs,sumRep_def]
  congr 1
  ext p
  simp only [Finset.product_eq_sprod,Finset.mem_filter,Finset.mem_product,Finset.mem_antidiagonal,Finset.mem_coe]
  tauto

lemma pairs_comm (A B : Finset ℕ) (n : ℕ) : pairs A B n = pairs B A n := by
  unfold pairs
  apply Finset.card_bij (fun p _ ↦ p.swap)
  · intro p hp
    obtain ⟨hp,he⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨(Finset.mem_product.mp hp).2,(Finset.mem_product.mp hp).1⟩,by dsimp; omega⟩
  · intro p hp q hq he
    exact Prod.swap_injective he
  · intro p hp
    refine ⟨p.swap,?_,by simp⟩
    obtain ⟨hp,he⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨(Finset.mem_product.mp hp).2,(Finset.mem_product.mp hp).1⟩,by dsimp; omega⟩

lemma pairs_eq_filter (A B : Finset ℕ) (n : ℕ) :
    pairs A B n = (A.filter (fun a ↦ a ≤ n ∧ n-a ∈ B)).card := by
  unfold pairs
  apply Finset.card_bij (fun p _ ↦ p.1)
  · intro p hp
    obtain ⟨hp,he⟩ := Finset.mem_filter.mp hp
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hp
    refine Finset.mem_filter.mpr ⟨ha,by omega,?_⟩
    convert hb using 1
    omega
  · intro p hp q hq he
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    exact Prod.ext he (by omega)
  · intro a ha
    obtain ⟨ha,han,hb⟩ := Finset.mem_filter.mp ha
    exact ⟨(a,n-a),Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨ha,hb⟩,by dsimp; omega⟩,rfl⟩

lemma pairs_union_left (A B C : Finset ℕ) (n : ℕ) (h : Disjoint A B) :
    pairs (A ∪ B) C n = pairs A C n+pairs B C n := by
  simp only [pairs_eq_filter,Finset.filter_union]
  exact Finset.card_union_of_disjoint (Finset.disjoint_filter_filter h)

lemma pairs_union_right (A B C : Finset ℕ) (n : ℕ) (h : Disjoint B C) :
    pairs A (B ∪ C) n = pairs A B n+pairs A C n := by
  rw [pairs_comm A,pairs_union_left _ _ _ _ h,pairs_comm B,pairs_comm C]

lemma pairs_union_self (A B : Finset ℕ) (n : ℕ) (h : Disjoint A B) :
    pairs (A ∪ B) (A ∪ B) n = pairs A A n+2*pairs A B n+pairs B B n := by
  rw [pairs_union_left _ _ _ _ h,pairs_union_right _ _ _ _ h,
    pairs_union_right _ _ _ _ h,pairs_comm B A]
  omega

lemma pairs_sum (A B T : Finset ℕ) :
    (∑ n ∈ T, pairs A B n) = ((A.product B).filter (fun p ↦ p.1+p.2 ∈ T)).card := by
  exact Finset.sum_card_fiberwise_eq_card_filter _ _ _

lemma pairs_sum_le (A B T : Finset ℕ) : (∑ n ∈ T, pairs A B n) ≤ A.card*B.card := by
  rw [pairs_sum]
  simpa only [Finset.product_eq_sprod,Finset.card_product] using
    Finset.card_le_card (Finset.filter_subset (fun p : ℕ × ℕ ↦ p.1+p.2 ∈ T) (A.product B))

lemma sumRep_union_self (A B : Finset ℕ) (n : ℕ) (h : Disjoint A B) :
    sumRep ((A ∪ B : Finset ℕ) : Set ℕ) n =
      sumRep (A : Set ℕ) n+2*pairs A B n+sumRep (B : Set ℕ) n := by
  simpa only [pairs_self] using pairs_union_self A B n h

lemma pairs_zero_of_lower (A B : Finset ℕ) (a b n : ℕ)
    (hA : ∀ x ∈ A, a ≤ x) (hB : ∀ x ∈ B, b ≤ x) (hn : n < a+b) : pairs A B n = 0 := by
  rw [pairs,Finset.card_eq_zero,Finset.filter_eq_empty_iff]
  intro p hp he
  obtain ⟨hp₁,hp₂⟩ := Finset.mem_product.mp hp
  have ha := hA p.1 hp₁
  have hb := hB p.2 hp₂
  omega

end Erdos66NatPairAlgebra
