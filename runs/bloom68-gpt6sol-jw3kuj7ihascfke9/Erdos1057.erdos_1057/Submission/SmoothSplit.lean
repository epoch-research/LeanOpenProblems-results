import Submission.LargePrime

/-!
# Splitting Carmichael numbers into smooth and large-prime parts

A Carmichael number at most `X` is either `Y`-smooth or has a prime divisor at least `Y`.
Combining this covering with the smooth-number estimate in Mathlib and the large-prime
estimate in `Submission.LargePrime` gives an elementary upper bound for its count.
-/

namespace Erdos1057

/-- Every Carmichael number at most `X` is either `Y`-smooth or belongs to
`largePrimeCarmichaels X Y`. This holds for all natural numbers `X` and `Y`. -/
theorem carmichaelsUpTo_subset_smooth_union_largePrime (X Y : ℕ) :
    {n : ℕ | IsCarmichael n ∧ n ≤ X} ⊆
      (Nat.smoothNumbersUpTo X Y : Set ℕ) ∪ largePrimeCarmichaels X Y := by
  intro n hn
  by_cases hlarge : ∃ p : ℕ, p.Prime ∧ Y ≤ p ∧ p ∣ n
  · exact Or.inr ⟨hn.1, hn.2, hlarge⟩
  · refine Or.inl (Nat.mem_smoothNumbersUpTo.mpr ⟨hn.2, ?_⟩)
    exact Nat.mem_smoothNumbers'.mpr (fun p hp hpn ↦
      lt_of_not_ge (fun hpY ↦ hlarge ⟨p, hp, hpY, hpn⟩))

/-- The count of Carmichael numbers up to `X` is bounded by the count of
`Y`-smooth numbers up to `X`, plus the large-prime estimate when `Y ≥ 3`. -/
theorem carmichaelsUpTo_card_le_smooth_add_largePrime (X Y : ℕ) (hY : 3 ≤ Y) :
    ({n : ℕ | IsCarmichael n ∧ n ≤ X}).ncard ≤
      (Nat.smoothNumbersUpTo X Y).card + 2 * X / Y := by
  have hfinite : ((Nat.smoothNumbersUpTo X Y : Set ℕ) ∪
      largePrimeCarmichaels X Y).Finite := by
    apply (Set.finite_le_nat X).subset
    intro n hn
    rcases hn with hs | hl
    · exact (Nat.mem_smoothNumbersUpTo.mp hs).1
    · exact hl.2.1
  calc
    ({n : ℕ | IsCarmichael n ∧ n ≤ X}).ncard ≤
        ((Nat.smoothNumbersUpTo X Y : Set ℕ) ∪ largePrimeCarmichaels X Y).ncard :=
      Set.ncard_le_ncard (carmichaelsUpTo_subset_smooth_union_largePrime X Y) hfinite
    _ ≤ (Nat.smoothNumbersUpTo X Y).card + (largePrimeCarmichaels X Y).ncard := by
      simpa only [Set.ncard_coe_finset] using
        (Set.ncard_union_le (Nat.smoothNumbersUpTo X Y : Set ℕ)
          (largePrimeCarmichaels X Y))
    _ ≤ (Nat.smoothNumbersUpTo X Y).card + 2 * X / Y :=
      Nat.add_le_add_left (largePrimeCarmichaels_card_le X Y hY) _

/-- An unconditional smooth/large-prime upper bound for Carmichael numbers up to `X`
when `Y ≥ 3`. The bound is also valid, in particular, when `X ≥ 3`. -/
theorem carmichaelsUpTo_card_le_smooth_split (X Y : ℕ) (hY : 3 ≤ Y) :
    ({n : ℕ | IsCarmichael n ∧ n ≤ X}).ncard ≤
      2 ^ Y.primesBelow.card * X.sqrt + 2 * X / Y := by
  calc
    ({n : ℕ | IsCarmichael n ∧ n ≤ X}).ncard ≤
        (Nat.smoothNumbersUpTo X Y).card + 2 * X / Y :=
      carmichaelsUpTo_card_le_smooth_add_largePrime X Y hY
    _ ≤ 2 ^ Y.primesBelow.card * X.sqrt + 2 * X / Y :=
      Nat.add_le_add_right (Nat.smoothNumbersUpTo_card_le X Y) _

end Erdos1057
