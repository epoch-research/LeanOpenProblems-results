import FormalConjecturesUtil
import Submission.Reduction

/-!
# Independent finite audit of the strictly ordered Erdős–Straus formulation

`Good` is the exact ordered positive-Nat proposition in `Spec.lean`, but this
file does not import `Spec.lean` or invoke its sorry-containing theorem. The
finite proof below does not assert the still-open universal statement.
-/

namespace Erdos242

/-- The version allowing equal positive natural denominators. -/
def UnorderedNat (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 1 ≤ x ∧ 1 ≤ y ∧ 1 ≤ z ∧
    (4 / n : ℚ) = 1 / x + 1 / y + 1 / z

/-- The exact ordered version with positive integer (rather than Nat) denominators. -/
def OrderedInt (n : ℕ) : Prop :=
  ∃ x y z : ℤ, 1 ≤ x ∧ x < y ∧ y < z ∧
    (4 / n : ℚ) = 1 / x + 1 / y + 1 / z

/-- The version allowing equal positive integer denominators. -/
def UnorderedInt (n : ℕ) : Prop :=
  ∃ x y z : ℤ, 1 ≤ x ∧ 1 ≤ y ∧ 1 ≤ z ∧
    (4 / n : ℚ) = 1 / x + 1 / y + 1 / z

/-- Ordered witnesses give unordered witnesses for all natural numerators. -/
theorem ordered_implies_unordered_nat {n : ℕ} (h : Good n) : UnorderedNat n := by
  rcases h with ⟨x, y, z, hx, hxy, hyz, heq⟩
  exact ⟨x, y, z, hx, by omega, by omega, heq⟩

/-- On positive denominators, Nat versus Int is *universally* just a change
of type: the ordered existence propositions are equivalent. -/
theorem ordered_nat_iff_ordered_int (n : ℕ) : Good n ↔ OrderedInt n := by
  constructor
  · rintro ⟨x, y, z, hx, hxy, hyz, heq⟩
    refine ⟨(x : ℤ), (y : ℤ), (z : ℤ), ?_, ?_, ?_, ?_⟩
    · exact_mod_cast hx
    · exact_mod_cast hxy
    · exact_mod_cast hyz
    · simpa only [Int.cast_natCast] using heq
  · rintro ⟨x, y, z, hx, hxy, hyz, heq⟩
    have hx' : (x.toNat : ℤ) = x := Int.toNat_of_nonneg (by omega)
    have hy' : (y.toNat : ℤ) = y := Int.toNat_of_nonneg (by omega)
    have hz' : (z.toNat : ℤ) = z := Int.toNat_of_nonneg (by omega)
    refine ⟨x.toNat, y.toNat, z.toNat, ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · omega
    · have hxq : (x.toNat : ℚ) = (x : ℚ) := by exact_mod_cast hx'
      have hyq : (y.toNat : ℚ) = (y : ℚ) := by exact_mod_cast hy'
      have hzq : (z.toNat : ℚ) = (z : ℚ) := by exact_mod_cast hz'
      simpa only [hxq, hyq, hzq] using heq

/-- Equal denominators really are permitted in the unordered statement. -/
theorem unordered_3_has_repeated_denominators :
    ∃ x y z : ℕ, 1 ≤ x ∧ 1 ≤ y ∧ 1 ≤ z ∧ y = z ∧
      (4 / 3 : ℚ) = 1 / x + 1 / y + 1 / z := by
  exact ⟨1, 6, 6, by norm_num, by norm_num, by norm_num, rfl, by norm_num⟩

/-- A complete, formally checked positive certificate for all `3 ≤ n ≤ 200`.
The other 190 cases follow from the symbolic outside-24 residue proof in
`Reduction.lean`; the eight cases `n ≡ 1 (mod 24)` use explicit ordered
triples checked as exact rational identities. -/
theorem good_from_three_through_two_hundred (n : ℕ) (hn : 2 < n) (hle : n ≤ 200) :
    Good n := by
  by_cases hmod : n % 24 = 1
  · have hcases : n = 25 ∨ n = 49 ∨ n = 73 ∨ n = 97 ∨
        n = 121 ∨ n = 145 ∨ n = 169 ∨ n = 193 := by omega
    rcases hcases with h | h | h | h | h | h | h | h
    · subst n
      exact ⟨10, 25, 50, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · subst n
      exact ⟨21, 42, 98, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · subst n
      exact ⟨20, 292, 730, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · subst n
      exact ⟨28, 194, 2716, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · subst n
      exact ⟨44, 132, 363, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · subst n
      exact ⟨58, 145, 290, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · subst n
      exact ⟨52, 338, 676, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · subst n
      exact ⟨50, 1930, 4825, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact good_outside_24 n hn hmod

/-- Both the Nat and Int, ordered and unordered, formulations are true for
*every* n in the certified range. In particular none is a counterexample
introduced by the strict-order condition. -/
theorem four_formulations_three_through_two_hundred (n : ℕ)
    (hn : 2 < n) (hle : n ≤ 200) :
    Good n ∧ UnorderedNat n ∧ OrderedInt n ∧ UnorderedInt n := by
  have h : Good n := good_from_three_through_two_hundred n hn hle
  have hi : OrderedInt n := (ordered_nat_iff_ordered_int n).mp h
  rcases hi with ⟨x, y, z, hx, hxy, hyz, heq⟩
  exact ⟨h, ordered_implies_unordered_nat h,
    ⟨x, y, z, hx, hxy, hyz, heq⟩,
    ⟨x, y, z, hx, by omega, by omega, heq⟩⟩

end Erdos242

#print axioms Erdos242.good_from_three_through_two_hundred
#print axioms Erdos242.ordered_nat_iff_ordered_int
#print axioms Erdos242.four_formulations_three_through_two_hundred
