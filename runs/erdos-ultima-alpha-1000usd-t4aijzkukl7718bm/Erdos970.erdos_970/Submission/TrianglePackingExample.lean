import Submission.TrianglePacking

/-! A three-pattern obstruction invisible to every common-product spacing
inequality on these primes and to every separate rounded intersection bound.
The synthetic population is NOT an actual residue configuration. -/
namespace Erdos970.PatternPacking.TriangleExample
open BlockSieve.SievePolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def primes : Finset ℕ := {5, 7, 11}
def family : Finset (Finset ℕ) := {{5, 7}, {5, 11}, {7, 11}}

lemma prime_members : ∀ A ∈ family, ∀ p ∈ A, p.Prime := by decide +kernel

theorem no_triangle : NoTriangle 12 family := by decide +kernel

/-- At most two positions can hit two of 5,7,11 in a length-twelve interval. -/
theorem actual_card_le_two (r : ℕ → ℕ) : patternCount 12 family r ≤ 2 :=
  patternCount_le_two_of_noTriangle 12 family prime_members no_triangle r

/-- The bound two is attained; it is not merely an empty-family obstruction. -/
theorem attained : patternCount 12 family (fun p => if p = 11 then 7 else 0) = 2 := by
  decide +kernel

/-- Nine empty atoms and one of each two-prime pattern. -/
def syntheticMoment (Q : Finset ℕ) : ℕ :=
  (if Q = ∅ then 9 else 0) + ∑ A ∈ family, if Q ⊆ A then 1 else 0

def syntheticUnion (G : Finset (Finset ℕ)) : ℕ :=
  (if ∅ ∈ G then 9 else 0) +
    (family.filter (fun A => ∃ B ∈ G, B ⊆ A)).card

/-- Every individual CRT intersection count has its required floor/ceiling size. -/
theorem all_rounded_moments (Q : Finset ℕ) (hQ : Q ⊆ primes) :
    12 / (∏ p ∈ Q, p) ≤ syntheticMoment Q ∧
    syntheticMoment Q ≤ ceilQuotient 12 (∏ p ∈ Q, p) := by
  have h : ∀ Q ∈ primes.powerset,
      12 / (∏ p ∈ Q, p) ≤ syntheticMoment Q ∧
      syntheticMoment Q ≤ ceilQuotient 12 (∏ p ∈ Q, p) := by decide +kernel
  exact h Q (Finset.mem_powerset.mpr hQ)

/-- A finite check of ALL pattern families on these three primes. It suffices
to check separators1 through12: larger separators have the same budget1. -/
lemma finite_spacing_check : ∀ G ∈ primes.powerset.powerset, ∀ d : Fin 13,
    0 < d.val →
    (∀ A ∈ G, ∀ B ∈ G, d.val ≤ commonProduct A B) →
    syntheticUnion G ≤ ceilQuotient 12 d.val := by
  decide +kernel

/-- The synthetic population satisfies every previously available common-product
spacing bound, not just those for subfamilies of the displayed three patterns. -/
theorem all_common_product_packing (G : Finset (Finset ℕ))
    (hG : ∀ A ∈ G, A ⊆ primes) (d : ℕ) (hd : 0 < d)
    (hcommon : ∀ A ∈ G, ∀ B ∈ G, d ≤ commonProduct A B) :
    syntheticUnion G ≤ ceilQuotient 12 d := by
  have hmem : G ∈ primes.powerset.powerset := Finset.mem_powerset.mpr
    (fun A hA => Finset.mem_powerset.mpr (hG A hA))
  by_cases hd12 : d ≤ 12
  · exact finite_spacing_check G hmem ⟨d, by omega⟩ hd hcommon
  · have hbig : 12 < d := by omega
    have hh := finite_spacing_check G hmem ⟨12, by omega⟩ (by change 0 < 12; omega)
      (fun A hA B hB => (by omega : 12 ≤ d).trans (hcommon A hA B hB))
    have h12 : ceilQuotient 12 12 = 1 := by decide +kernel
    have hceil : ceilQuotient 12 d = 1 := by
      simp [ceilQuotient, Nat.div_eq_of_lt hbig, Nat.mod_eq_of_lt hbig]
    rw [hceil]
    simpa only [h12] using hh

/-- It nevertheless violates the exact three-position compatibility bound. -/
theorem triangle_violation : syntheticUnion family = 3 := by decide +kernel

/-- There is no choice of the three forbidden residues realizing these pattern
masses. Separate rounded moments and all common-product spacing inequalities
are therefore still not a complete positional model. -/
theorem synthetic_population_not_realizable :
    ¬∃ r : ℕ → ℕ, patternCount 12 family r = syntheticUnion family := by
  rintro ⟨r, hr⟩
  have hh := actual_card_le_two r
  rw [hr, triangle_violation] at hh
  omega

#print axioms no_triangle
#print axioms actual_card_le_two
#print axioms all_rounded_moments
#print axioms all_common_product_packing
#print axioms synthetic_population_not_realizable
end Erdos970.PatternPacking.TriangleExample
