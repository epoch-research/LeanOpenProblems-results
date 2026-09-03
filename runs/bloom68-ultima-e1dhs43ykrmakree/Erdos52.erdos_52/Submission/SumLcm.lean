import Mathlib

/-!
# Reconstruction from a sum and an lcm

For natural numbers `a, b`, their sum and lcm determine their gcd, hence their
product, and finally the pair up to swapping. The statements also cover zero,
so in particular they hold for positive natural numbers.

As a finite counting consequence, the sum is injective on pairs in `A × A`
with `a ≤ b` and a fixed lcm. No sum-product conjecture is asserted here.
This file imports only Mathlib.
-/

open scoped Pointwise

namespace Erdos52.SumLcm

/-- The gcd of the sum and the lcm is the gcd of the original pair. -/
theorem gcd_add_lcm_eq_gcd (a b : ℕ) :
    Nat.gcd (a + b) (Nat.lcm a b) = Nat.gcd a b := by
  obtain ⟨x, y, hxy, hax, hby⟩ := Nat.exists_coprime a b
  generalize Nat.gcd a b = g at *
  have hcop : Nat.Coprime (x + y) (x * y) :=
    (Nat.coprime_self_add_left.mpr hxy.symm).mul_right
      (Nat.coprime_add_self_left.mpr hxy)
  rw [hax, hby, ← Nat.add_mul, Nat.lcm_mul_right, hxy.lcm_eq_mul,
    Nat.gcd_mul_right, hcop.gcd_eq_one, one_mul]

/-- The product is determined by the sum and the lcm. -/
theorem mul_eq_lcm_mul_gcd_add_lcm (a b : ℕ) :
    a * b = Nat.lcm a b * Nat.gcd (a + b) (Nat.lcm a b) := by
  rw [gcd_add_lcm_eq_gcd, Nat.lcm_mul_gcd]

/-- Equal sums and equal lcms determine a natural-number pair up to swapping. -/
theorem eq_or_swap_of_add_eq_of_lcm_eq {a b c d : ℕ}
    (hsum : a + b = c + d) (hlcm : Nat.lcm a b = Nat.lcm c d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hprod : a * b = c * d := by
    rw [mul_eq_lcm_mul_gcd_add_lcm a b, mul_eq_lcm_mul_gcd_add_lcm c d,
      hsum, hlcm]
  have hsumZ : (a : ℤ) + b = (c : ℤ) + d := by exact_mod_cast hsum
  have hprodZ : (a : ℤ) * b = (c : ℤ) * d := by exact_mod_cast hprod
  have hroot : ((a : ℤ) - c) * ((a : ℤ) - d) = 0 := by
    nlinarith only [hprodZ, congrArg (fun z : ℤ => (a : ℤ) * z) hsumZ]
  rcases mul_eq_zero.mp hroot with hac | had
  · have hac' : a = c := by exact_mod_cast (sub_eq_zero.mp hac)
    exact Or.inl ⟨hac', by omega⟩
  · have had' : a = d := by exact_mod_cast (sub_eq_zero.mp had)
    exact Or.inr ⟨had', by omega⟩

/-- Ordering the entries removes the swapping ambiguity. -/
theorem eq_of_le_of_add_eq_of_lcm_eq {a b c d : ℕ}
    (hab : a ≤ b) (hcd : c ≤ d)
    (hsum : a + b = c + d) (hlcm : Nat.lcm a b = Nat.lcm c d) :
    a = c ∧ b = d := by
  rcases eq_or_swap_of_add_eq_of_lcm_eq hsum hlcm with h | ⟨had, hbc⟩
  · exact h
  · constructor <;> omega

/-- Pairs in the Cartesian square, with nondecreasing entries and fixed lcm. -/
def orderedPairs (A : Finset ℕ) (L : ℕ) : Finset (ℕ × ℕ) :=
  (A ×ˢ A).filter fun p => p.1 ≤ p.2 ∧ Nat.lcm p.1 p.2 = L

/-- Within a fixed-lcm family of nondecreasing pairs, sums are injective. -/
theorem sum_injOn_orderedPairs (A : Finset ℕ) (L : ℕ) :
    Set.InjOn (fun p : ℕ × ℕ => p.1 + p.2) (orderedPairs A L : Set (ℕ × ℕ)) := by
  intro p hp q hq hsum
  rcases Finset.mem_filter.mp hp with ⟨_, hpord, hplcm⟩
  rcases Finset.mem_filter.mp hq with ⟨_, hqord, hqlcm⟩
  have h := eq_of_le_of_add_eq_of_lcm_eq hpord hqord hsum (hplcm.trans hqlcm.symm)
  exact Prod.ext h.1 h.2

/-- The number of nondecreasing pairs in `A × A` with lcm `L` is at most
 the cardinality of the sumset `A + A`. -/
theorem card_orderedPairs_le_sumset (A : Finset ℕ) (L : ℕ) :
    (orderedPairs A L).card ≤ (A + A).card := by
  refine Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.1 + p.2) ?_
    (sum_injOn_orderedPairs A L)
  intro p hp
  rcases Finset.mem_product.mp (Finset.mem_filter.mp hp).1 with ⟨ha, hb⟩
  exact Finset.add_mem_add ha hb

end Erdos52.SumLcm

#print axioms Erdos52.SumLcm.gcd_add_lcm_eq_gcd
#print axioms Erdos52.SumLcm.mul_eq_lcm_mul_gcd_add_lcm
#print axioms Erdos52.SumLcm.eq_or_swap_of_add_eq_of_lcm_eq
#print axioms Erdos52.SumLcm.eq_of_le_of_add_eq_of_lcm_eq
#print axioms Erdos52.SumLcm.sum_injOn_orderedPairs
#print axioms Erdos52.SumLcm.card_orderedPairs_le_sumset
