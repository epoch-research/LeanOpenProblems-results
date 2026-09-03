import Submission.CRTWindowRigidity

/-!
# Exact finite checks of the CRT window analysis

A covered 17-row histogram satisfies every exact floor/ceiling constraint and
every two-block CRT-bit compatibility test, including blocks with more than
one prime. Nevertheless its columns cannot have one common residue assignment.
All finite checks below use kernel-checked `decide`.
-/

namespace IntegerSieve.CRTWindow.Examples

open Finset

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Five distinct primes, not a reduction of the general problem to primorials. -/
def primes17 : Finset ℕ := {2, 3, 5, 7, 11}

/-- `5·{2}, 3·{3}, {2,3}, 2·{5}, {2,5}, {2,3,5}, 2·{7}, {2,3,7}, {11}`. -/
def rows17 (i : Fin 17) : Finset ℕ :=
  if i.val < 5 then {2}
  else if i.val < 8 then {3}
  else if i.val < 9 then {2, 3}
  else if i.val < 11 then {5}
  else if i.val < 12 then {2, 5}
  else if i.val < 13 then {2, 3, 5}
  else if i.val < 15 then {7}
  else if i.val < 16 then {2, 3, 7}
  else {11}

theorem primes17_prime : ∀ p ∈ primes17, Nat.Prime p := by decide

theorem rows17_subsets : ∀ i, rows17 i ⊆ primes17 := by decide

theorem rows17_covered : ∀ i, (rows17 i).Nonempty := by decide

theorem rows17_rounded : RoundedIntersections 17 primes17 rows17 := by
  unfold RoundedIntersections
  decide

/-- A single CRT root realizes the three indicated counts for THESE two blocks.
Roots for different block pairs are deliberately NOT required to be consistent. -/
def BlockPairWitness (A B : Finset ℕ) (r : ℕ) : Prop :=
  r < modulus A * modulus B ∧
  rowCount rows17 A = 17 / modulus A +
    (if r % modulus A < 17 % modulus A then 1 else 0) ∧
  rowCount rows17 B = 17 / modulus B +
    (if r % modulus B < 17 % modulus B then 1 else 0) ∧
  rowCount rows17 (A ∪ B) = 17 / (modulus A * modulus B) +
    (if r < 17 % (modulus A * modulus B) then 1 else 0)

/-- All 180 ordered pairs of disjoint nonempty blocks pass. The uniform witness
bound 46 is just a small certificate bound; each witness is ALSO below its own
CRT modulus. This tests all three bits, not only a particular implication. -/
theorem all_block_pairs_compatible17 :
    ∀ A ∈ primes17.powerset, ∀ B ∈ primes17.powerset,
      A.Nonempty → B.Nonempty → Disjoint A B →
        ∃ r : Fin 46, BlockPairWitness A B r.val := by
  unfold BlockPairWitness
  decide

theorem rows17_key_counts :
    rowCount rows17 {2} = 9 ∧ rowCount rows17 {3} = 6 ∧
    rowCount rows17 {7} = 3 ∧ rowCount rows17 {2, 7} = 1 ∧
    rowCount rows17 {2, 3, 7} = 1 := by decide

/-- Those five counts already have no common choice of the three residue roots.
There are only 42 normalized choices; this is an exact bounded check. -/
theorem no_normalized_realization17 : ¬ ∃ (a : Fin 2) (b : Fin 3) (c : Fin 7),
    Nat.count (fun n => n % 2 = a.val) 17 = rowCount rows17 {2} ∧
    Nat.count (fun n => n % 3 = b.val) 17 = rowCount rows17 {3} ∧
    Nat.count (fun n => n % 7 = c.val) 17 = rowCount rows17 {7} ∧
    Nat.count (fun n => n % 2 = a.val ∧ n % 7 = c.val) 17 = rowCount rows17 {2, 7} ∧
    Nat.count (fun n => n % 2 = a.val ∧ n % 3 = b.val ∧ n % 7 = c.val) 17 =
      rowCount rows17 {2, 3, 7} := by decide

/-- Normalization removes every bound on the original residues. -/
theorem no_residue_realization17 : ¬ ∃ a b c : ℕ,
    Nat.count (fun n => n ≡ a [MOD 2]) 17 = rowCount rows17 {2} ∧
    Nat.count (fun n => n ≡ b [MOD 3]) 17 = rowCount rows17 {3} ∧
    Nat.count (fun n => n ≡ c [MOD 7]) 17 = rowCount rows17 {7} ∧
    Nat.count (fun n => n ≡ a [MOD 2] ∧ n ≡ c [MOD 7]) 17 = rowCount rows17 {2, 7} ∧
    Nat.count (fun n => n ≡ a [MOD 2] ∧ n ≡ b [MOD 3] ∧ n ≡ c [MOD 7]) 17 =
      rowCount rows17 {2, 3, 7} := by
  rintro ⟨a, b, c, h⟩
  apply no_normalized_realization17
  refine ⟨⟨a % 2, Nat.mod_lt _ (by decide)⟩,
    ⟨b % 3, Nat.mod_lt _ (by decide)⟩, ⟨c % 7, Nat.mod_lt _ (by decide)⟩, ?_⟩
  simpa only [Nat.ModEq] using h

/-- A concrete instance of the general nearby-prime obstruction. -/
theorem nearby_primes_disjoint_maxima : ∃ a b : ℕ,
    residueCount 1000 101 a = 10 ∧ residueCount 1000 103 b = 10 ∧
      Nat.count (fun n => n ≡ a [MOD 101] ∧ n ≡ b [MOD 103]) 1000 = 0 := by
  obtain ⟨a, b, ha, hb, hab⟩ := disjoint_maximal_columns_of_small_gap
    (p := 101) (q := 103) (L := 1000) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  refine ⟨a, b, ?_, ?_, hab⟩
  · simpa only [residueCount, Nat.count_modEq_card 1000 (by decide : 0 < 101),
      Nat.zero_mod] using ha
  · simpa only [residueCount, Nat.count_modEq_card 1000 (by decide : 0 < 103),
      Nat.zero_mod] using hb

end IntegerSieve.CRTWindow.Examples

#print axioms IntegerSieve.CRTWindow.Examples.rows17_rounded
#print axioms IntegerSieve.CRTWindow.Examples.all_block_pairs_compatible17
#print axioms IntegerSieve.CRTWindow.Examples.no_residue_realization17
#print axioms IntegerSieve.CRTWindow.Examples.nearby_primes_disjoint_maxima
