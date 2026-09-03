import FormalConjecturesUtil

/-!
An elementary modular upper bound for Sidon sets. This is an auxiliary result,
not a settlement of Erdős 773.
-/

namespace Erdos773
open Finset

lemma congruent_pair_quotient_injective {A : Finset ℕ} (hs : IsSidon (A : Set ℕ))
    (q : ℕ) {a b c d : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (hab : a ≠ b) (hmab : a % q = b % q) (hmcd : c % q = d % q)
    (he : ((a / q : ℕ) : ℤ) - (b / q : ℕ) = ((c / q : ℕ) : ℤ) - (d / q : ℕ)) :
    a = c ∧ b = d := by
  have hquot : a / q + d / q = c / q + b / q := by omega
  have hmul := congrArg (fun n : ℕ => q * n) hquot
  simp only [mul_add] at hmul
  have has := Nat.mod_add_div a q
  have hbs := Nat.mod_add_div b q
  have hcs := Nat.mod_add_div c q
  have hds := Nat.mod_add_div d q
  have heq : a + d = c + b := by omega
  rcases hs a ha c hc d hd b hb heq with h | h
  · exact ⟨h.1, h.2.symm⟩
  · exact (hab h.1).elim

lemma congruent_pairs_card_bound {A : Finset ℕ} {L : ℕ}
    (hs : IsSidon (A : Set ℕ)) (hL : ∀ a ∈ A, a ≤ L) (q : ℕ) :
    ((A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 % q = p.2 % q)).card ≤
      A.card + 2 * (L / q) + 1 := by
  let f : ℕ × ℕ → ℕ ⊕ ℤ := fun p =>
    if p.1 = p.2 then Sum.inl p.1 else
      Sum.inr ((p.1 / q : ℕ) - ((p.2 / q : ℕ) : ℤ))
  have hh : ((A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 % q = p.2 % q)).card ≤
      (A.disjSum (Icc (-((L / q : ℕ) : ℤ)) ((L / q : ℕ) : ℤ))).card := by
    apply Finset.card_le_card_of_injOn f
    · rintro ⟨a,b⟩ hp
      obtain ⟨hp, hm⟩ := Finset.mem_filter.mp hp
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
      dsimp [f]
      split_ifs with he
      · simp [ha]
      · have haL := Nat.div_le_div_right (hL a ha) (c := q)
        have hbL := Nat.div_le_div_right (hL b hb) (c := q)
        apply Finset.mem_disjSum.mpr
        right
        refine ⟨_, ?_, rfl⟩
        apply mem_Icc.mpr
        have ha0 : 0 ≤ (a : ℤ) / q := Int.ediv_nonneg (by omega) (by omega)
        have hb0 : 0 ≤ (b : ℤ) / q := Int.ediv_nonneg (by omega) (by omega)
        constructor <;> omega
    · rintro ⟨a,b⟩ hp ⟨c,d⟩ hr he
      obtain ⟨hp, hmab⟩ := Finset.mem_filter.mp hp
      obtain ⟨hr, hmcd⟩ := Finset.mem_filter.mp hr
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
      obtain ⟨hc, hd⟩ := Finset.mem_product.mp hr
      dsimp [f] at he
      split_ifs at he with hab hcd hcd
      · simp only [Sum.inl.injEq] at he
        exact Prod.ext he (by omega)
      · have he' := Sum.inr.inj he
        have hpair := congruent_pair_quotient_injective hs q ha hb hc hd hab hmab hmcd he'
        exact Prod.ext hpair.1 hpair.2
  rw [card_disjSum, Int.card_Icc] at hh
  have hcard : (((L / q : ℕ) : ℤ) + 1 - -((L / q : ℕ) : ℤ)).toNat = 2 * (L / q) + 1 := by omega
  rw [hcard] at hh
  omega

lemma card_sq_le_residue_count_mul_pairs (A C : Finset ℕ) (q : ℕ)
    (hC : ∀ a ∈ A, a % q ∈ C) :
    A.card ^ 2 ≤ C.card *
      ((A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 % q = p.2 % q)).card := by
  let F := (A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 % q = p.2 % q)
  have hsum : A.card = ∑ r ∈ C, (A.filter (fun a => a % q = r)).card :=
    Finset.card_eq_sum_card_fiberwise hC
  have hsum2 : F.card = ∑ r ∈ C, (A.filter (fun a => a % q = r)).card ^ 2 := by
    have hm : Set.MapsTo (fun p : ℕ × ℕ => p.1 % q) (F : Set (ℕ × ℕ)) C := by
      intro p hp
      exact hC p.1 (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
    rw [Finset.card_eq_sum_card_fiberwise hm]
    apply Finset.sum_congr rfl
    intro r hr
    have hf : F.filter (fun p => p.1 % q = r) =
        (A.filter (fun a => a % q = r)) ×ˢ (A.filter (fun a => a % q = r)) := by
      ext p
      simp only [F, mem_filter, mem_product]
      aesop
    rw [hf, card_product, pow_two]
  change A.card ^ 2 ≤ C.card * F.card
  rw [hsum2, hsum]
  exact sq_sum_le_card_mul_sum_sq

lemma sidon_modular_card_bound {A C : Finset ℕ} {L q : ℕ}
    (hs : IsSidon (A : Set ℕ)) (hL : ∀ a ∈ A, a ≤ L)
    (hC : ∀ a ∈ A, a % q ∈ C) :
    A.card ^ 2 ≤ C.card * (A.card + 2 * (L / q) + 1) := by
  exact (card_sq_le_residue_count_mul_pairs A C q hC).trans
    (Nat.mul_le_mul_left C.card (congruent_pairs_card_bound hs hL q))

#print axioms sidon_modular_card_bound

end Erdos773
