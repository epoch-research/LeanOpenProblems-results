import Submission.IntegerSieveArithmetic

/-!
# Verified finite examples for the integer-sieve relaxation

These examples were obtained by explicit Boolean-cube trades, not an LP search.
They are not asymptotic counterexamples and do not settle Erdős 970.
All finite checks use kernel-checked `decide`, not `native_decide`.
-/

namespace IntegerSieve.Examples

open Finset

/-- Four distinct prime labels. -/
def primes19 : Finset ℕ := {2, 3, 5, 7}

/-- Histogram: 6·{2}, 4·{3}, 3·{5}, 2·{7}, 2·{2,3}, {2,7}, {2,3,5}. -/
def rows19 (i : Fin 19) : Finset ℕ :=
  if i.val < 6 then {2}
  else if i.val < 10 then {3}
  else if i.val < 13 then {5}
  else if i.val < 15 then {7}
  else if i.val < 17 then {2, 3}
  else if i.val < 18 then {2, 7}
  else {2, 3, 5}

theorem primes19_prime : ∀ p ∈ primes19, Nat.Prime p := by decide

theorem rows19_subsets : ∀ i, rows19 i ⊆ primes19 := by decide

theorem rows19_covered : ∀ i, (rows19 i).Nonempty := by decide

/-- All 16 intersections, including the empty intersection, satisfy the stronger
exact floor/ceiling constraints. -/
theorem rows19_rounded : RoundedIntersections 19 primes19 rows19 := by
  unfold RoundedIntersections
  decide

theorem rows19_pair_products : ∀ i j : Fin 19, i ≠ j →
    modulus (rows19 i ∩ rows19 j) < 19 := by
  intro i j hij
  exact common_product_lt_length rows19 rows19_subsets rows19_rounded hij

theorem nineteen_gt_card_sq : primes19.card ^ 2 < 19 := by decide

/-- Four singleton trades and one cubic trade. -/
def trades19 : Finset (Finset ℕ) := {{2}, {3}, {5}, {7}, {2, 3, 5}}

theorem trades19_subsets : ∀ R ∈ trades19, R ⊆ primes19 := by decide

theorem trades19_odd : ∀ R ∈ trades19, Odd R.card := by decide

theorem trades19_capacities : ∀ T ∈ primes19.powerset, Even T.card →
    (load trades19 T : ℤ) ≤ histogram (baseRows primes19 19) T := by decide

theorem trades19_size : histogram (baseRows primes19 19) ∅ = (trades19.card : ℤ) := by
  decide

theorem trades19_slack : ∀ R ∈ trades19, ¬ modulus R ∣ 19 := by decide

/-- The displayed rows are exactly the histogram obtained from the proved trade
construction; this is not merely a separately checked numerical example. -/
theorem trades19_match_rows : ∀ T ∈ primes19.powerset,
    traded (histogram (baseRows primes19 19)) trades19 T = histogram rows19 T := by
  decide

/-- Direct instantiation of the general covering-specific prime-packing lemma. -/
theorem nineteen_from_prime_cube_packing :
    ∃ w : Finset ℕ → ℤ,
      (∀ T ⊆ primes19, 0 ≤ w T) ∧ w ∅ = 0 ∧
        (∀ S ⊆ primes19,
          ((19 / modulus S : ℕ) : ℤ) ≤ upperCount primes19 w S ∧
          upperCount primes19 w S ≤ (((19 + modulus S - 1) / modulus S : ℕ) : ℤ)) := by
  exact prime_cube_packing_cover 19 primes19_prime trades19_subsets trades19_odd
    (fun T hTP => trades19_capacities T (Finset.mem_powerset.mpr hTP))
    trades19_size trades19_slack

theorem rows19_counts : rowCount rows19 {2} = 10 ∧
    rowCount rows19 {3} = 7 ∧ rowCount rows19 {2, 3} = 3 := by decide

/-- The general CRT rounding lemma, not a search over residues, proves that the
19-row example cannot be realized by full residue columns in a real interval. -/
theorem no_residue_count_realization19 : ¬ ∃ a b : ℕ,
    Nat.count (fun n => n ≡ a [MOD 2]) 19 = rowCount rows19 {2} ∧
    Nat.count (fun n => n ≡ b [MOD 3]) 19 = rowCount rows19 {3} ∧
    Nat.count (fun n => n ≡ a [MOD 2] ∧ n ≡ b [MOD 3]) 19 =
      rowCount rows19 {2, 3} := by
  rintro ⟨a, b, ha, hb, hab⟩
  obtain ⟨h2, h3, h23⟩ := rows19_counts
  rw [h2] at ha
  rw [h3] at hb
  rw [h23] at hab
  have hc := maximal_counts_force_maximal_pair
    (L := 19) (p := 2) (q := 3) (by decide) (by decide) (by decide) (by decide)
    a b (by simpa using ha) (by simpa using hb)
  norm_num at hc
  omega

/-- A smaller example exposes a specific CRT rounding incompatibility. -/
def primes11 : Finset ℕ := {2, 3, 5}

/-- Histogram: 4·{2}, 3·{3}, 2·{5}, {2,3}, {2,5}. -/
def rows11 (i : Fin 11) : Finset ℕ :=
  if i.val < 4 then {2}
  else if i.val < 7 then {3}
  else if i.val < 9 then {5}
  else if i.val < 10 then {2, 3}
  else {2, 5}

theorem primes11_prime : ∀ p ∈ primes11, Nat.Prime p := by decide

theorem rows11_subsets : ∀ i, rows11 i ⊆ primes11 := by decide

theorem rows11_covered : ∀ i, (rows11 i).Nonempty := by decide

theorem rows11_rounded : RoundedIntersections 11 primes11 rows11 := by
  unfold RoundedIntersections
  decide

theorem rows11_counts : rowCount rows11 {2} = 6 ∧
    rowCount rows11 {3} = 4 ∧ rowCount rows11 {2, 3} = 1 := by decide

/-- In an actual eleven-position interval, simultaneously maximal counts for
one residue modulo 2 and one modulo 3 force two, not one, common positions.
The six residue choices are checked exactly. -/
theorem actual_rounding_correlation : ∀ (a : Fin 2) (b : Fin 3),
    (Finset.univ.filter (fun i : Fin 11 => i.val % 2 = a.val)).card = 6 →
    (Finset.univ.filter (fun i : Fin 11 => i.val % 3 = b.val)).card = 4 →
    (Finset.univ.filter (fun i : Fin 11 =>
      i.val % 2 = a.val ∧ i.val % 3 = b.val)).card = 2 := by decide

/-- The three counts of the abstract example cannot be the counts of full
residue classes in an eleven-position interval, in any order of its rows. -/
theorem no_residue_count_realization11 : ¬ ∃ (a : Fin 2) (b : Fin 3),
    (Finset.univ.filter (fun i : Fin 11 => i.val % 2 = a.val)).card =
      rowCount rows11 {2} ∧
    (Finset.univ.filter (fun i : Fin 11 => i.val % 3 = b.val)).card =
      rowCount rows11 {3} ∧
    (Finset.univ.filter (fun i : Fin 11 =>
      i.val % 2 = a.val ∧ i.val % 3 = b.val)).card = rowCount rows11 {2, 3} := by
  rintro ⟨a, b, ha, hb, hab⟩
  obtain ⟨h2, h3, h23⟩ := rows11_counts
  rw [h2] at ha
  rw [h3] at hb
  rw [h23] at hab
  have hc := actual_rounding_correlation a b ha hb
  omega

end IntegerSieve.Examples

#print axioms IntegerSieve.Examples.rows19_rounded
#print axioms IntegerSieve.Examples.rows19_covered
#print axioms IntegerSieve.Examples.rows19_pair_products
#print axioms IntegerSieve.Examples.trades19_match_rows
#print axioms IntegerSieve.Examples.nineteen_from_prime_cube_packing
#print axioms IntegerSieve.Examples.no_residue_count_realization19
#print axioms IntegerSieve.Examples.rows11_rounded
#print axioms IntegerSieve.Examples.no_residue_count_realization11
