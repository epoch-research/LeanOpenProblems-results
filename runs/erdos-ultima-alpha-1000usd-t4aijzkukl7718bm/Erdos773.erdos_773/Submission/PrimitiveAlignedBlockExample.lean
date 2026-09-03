import Submission.AlignedBlockCollision
import Submission.DistinctDigitCarryObstacle

/-!
Concrete arbitrarily long, pairwise-coprime, aligned-block histogram collisions.
These are obstructions to a proposed sufficient condition, NOT to Erdős 773.
-/
namespace Erdos773.PrimitiveAlignedBlockExample

open Finset AlignedBlockCollision DistinctDigitCarry

set_option maxHeartbeats 1000000

abbrev digits : Fin 4 → Fin 28 → ℕ := words 615 606
abbrev baseValue : Fin 4 → ℕ := value 615 606 372689
abbrev roots (k : ℕ) : Fin 4 → ℕ := repeatedValue baseValue (372689 ^ 28) k

lemma base_bounds : ∀ i, 1 < baseValue i ∧ baseValue i < 372689 ^ 28 := by
  decide +kernel

lemma base_collision : baseValue 0 ^ 2 + baseValue 1 ^ 2 =
    baseValue 2 ^ 2 + baseValue 3 ^ 2 := collision _ _ _ (by norm_num)

/-- Each block is canonical, has common ends, and has exactly the original histogram.
The global word has repeated digits and does not claim global Eisenstein conditions. -/
lemma digit_conditions (i : Fin 4) (b : ℕ) :
    repeatedWord digits i b 0 = 3 ∧ repeatedWord digits i b 27 = 1 ∧
      (∀ r : Fin 28, 0 < repeatedWord digits i b r ∧
        2 * repeatedWord digits i b r < 372689) := by
  have h (i : Fin 4) := concrete_digit_conditions i
  change (if b = 0 then digits i 0 else digits i.rev 0) = 3 ∧
    (if b = 0 then digits i 27 else digits i.rev 27) = 1 ∧ _
  by_cases hb : b = 0
  · refine ⟨by simp [hb, (h i).2.1], by simp [hb, (h i).1], ?_⟩
    intro r
    simpa [repeatedWord, hb] using ⟨((h i).2.2.2.1 r).1, ((h i).2.2.2.1 r).2.1⟩
  · refine ⟨by simp [hb, (h i.rev).2.1], by simp [hb, (h i.rev).1], ?_⟩
    intro r
    simpa [repeatedWord, hb] using
      ⟨((h i.rev).2.2.2.1 r).1, ((h i.rev).2.2.2.1 r).2.1⟩

lemma statistics {M : Type*} [AddCommMonoid M]
    (i j : Fin 4) (blocks : Finset ℕ) (f : ℕ → M) :
    ∑ b ∈ blocks, ∑ r : Fin 28, f (repeatedWord digits i b r) =
      ∑ b ∈ blocks, ∑ r : Fin 28, f (repeatedWord digits j b r) :=
  aligned_statistics digits (histogram_perm _ _) i j blocks f

lemma evaluation (k : ℕ) (i : Fin 4) :
    (∑ b ∈ range (k + 1), ∑ r : Fin 28,
      repeatedWord digits i b r * 372689 ^ (28 * b + r.val)) = roots k i :=
  repeatedWord_value digits _ k i

/-- There are unbounded lengths, with genuine non-Sidon squares and pairwise-coprime roots. -/
theorem arbitrarily_long (n : ℕ) :
    ∃ k, n < k ∧ Pairwise (fun i j => (roots k i).Coprime (roots k j)) ∧
      Function.Injective (roots k) ∧
      ¬ IsSidon ((univ.image (fun i => roots k i ^ 2)) : Set ℕ) := by
  obtain ⟨k, hnk, hc, hi, _⟩ := arbitrarily_long_coprime_repetitions
    concrete_pairwise_coprime (fun i => (base_bounds i).1)
    (fun i => (base_bounds i).2) base_collision n
  refine ⟨k, hnk, hc, hi, ?_⟩
  exact repeated_not_sidon
    (coprime_injective concrete_pairwise_coprime (fun i => (base_bounds i).1))
    (fun i => (base_bounds i).2) base_collision k


/-- An explicit scope check: the short block's leading 1 is now an interior digit.
Thus this construction does not retain the global inert-prime Eisenstein condition. -/
lemma interior_not_divisible (k : ℕ) (hk : 0 < k) (i : Fin 4) :
    27 < 28 * (k + 1) - 1 ∧
      ¬ 3 ∣ repeatedWord digits i 0 27 := by
  refine ⟨by omega, ?_⟩
  rw [(digit_conditions i 0).2.1]
  decide

lemma total_digit_sum (k : ℕ) (i : Fin 4) :
    (∑ b ∈ range (k + 1), ∑ r : Fin 28, repeatedWord digits i b r) =
      (k + 1) * 111799 := by
  have hs (b : ℕ) : (∑ r : Fin 28, repeatedWord digits i b r) = 111799 := by
    by_cases hb : b = 0
    · simpa [repeatedWord, hb, digits] using digit_sum 615 606 i
    · simpa [repeatedWord, hb, digits] using digit_sum 615 606 i.rev
  simp_rw [hs]
  simp

#print axioms interior_not_divisible
#print axioms total_digit_sum

#print axioms digit_conditions
#print axioms statistics
#print axioms evaluation
#print axioms arbitrarily_long

end Erdos773.PrimitiveAlignedBlockExample
