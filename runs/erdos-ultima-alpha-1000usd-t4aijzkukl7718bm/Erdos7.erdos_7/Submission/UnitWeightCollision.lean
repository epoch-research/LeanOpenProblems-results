import FormalConjecturesUtil

/-! A finite obstruction to two simple collision-fiber budgets in odd
unit-orbit descent. This partial family does NOT cover the integers. -/
namespace Erdos7UnitWeightCollision
open Fin.NatCast
open scoped BigOperators
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

abbrev modulus : Fin 23 → ℕ := ![3, 5, 7, 9, 13, 15, 21, 35, 39, 45, 63, 65, 91, 105, 117, 195, 273, 315, 455, 585, 819, 1365, 4095]
abbrev residue : Fin 23 → ℤ := ![0, 0, 0, 7, 0, 1, 20, 29, 35, 11, 31, 54, 72, 82, 53, 133, 173, 302, 272, 536, 193, 743, 3478]
abbrev privatePoint : Fin 23 → ℤ := ![3414, 3415, 3416, 3418, 3419, 3421, 3422, 3424, 3428, 3431, 3433, 3434, 3439, 3442, 3446, 3448, 3449, 3452, 3457, 3461, 3469, 3473, 3478]

lemma modulus_injective : Function.Injective modulus := by decide +kernel
lemma odd_nontrivial : ∀ i, Odd (modulus i) ∧ 1 < modulus i := by decide +kernel
lemma modulus_dvd : ∀ i, modulus i ∣ 4095 := by decide +kernel
lemma divisor_closed : ∀ i, ∀ d ∈ (modulus i).divisors,
    1 < d → ∃ j, modulus j = d := by decide +kernel
lemma private_points : ∀ i,
    (modulus i : ℤ) ∣ privatePoint i - residue i ∧
    ∀ j, j ≠ i → ¬ (modulus j : ℤ) ∣ privatePoint i - residue j := by
  decide +kernel
lemma normalized_primes : ∀ i, (modulus i).Prime → residue i = 0 := by
  decide +kernel
lemma composite_units : ∀ i, ¬ (modulus i).Prime →
    Nat.Coprime (residue i).natAbs (modulus i) := by decide +kernel
lemma two_uncovered : ∀ i, ¬ (modulus i : ℤ) ∣ 2-residue i := by decide +kernel

abbrev collisionIndex : Fin 18 → Fin 23 := ![3, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]
abbrev collisionModulus (i : Fin 18) : ℕ := modulus (collisionIndex i)
abbrev totientTable : Fin 18 → ℕ := ![6, 12, 24, 24, 24, 36, 48, 72, 48, 72, 96, 144, 144, 288, 288, 432, 576, 1728]
abbrev twoPartTable : Fin 18 → ℕ := ![2, 4, 8, 8, 8, 4, 16, 8, 16, 8, 32, 16, 16, 32, 32, 16, 64, 64]

lemma collision_index_injective : Function.Injective collisionIndex := by decide +kernel
lemma collision_composite : ∀ i, ¬ (collisionModulus i).Prime := by decide +kernel

/-- Every listed modulus has exactly three distinct powers of the generator.
Its induced period is therefore three, not the odd part of its totient. -/
lemma local_order_three : ∀ i,
    1381^3 % collisionModulus i = 1 ∧
    Function.Injective (fun t : Fin 3 => 1381^t.val % collisionModulus i) := by
  decide +kernel

lemma generator_unit : Nat.Coprime 1381 4095 := by decide
lemma generator_cube : 1381^3 % 4095 = 1 := by decide +kernel

lemma totient_table : ∀ i, (collisionModulus i).totient = totientTable i := by
  decide +kernel
lemma two_part_table : ∀ i, ordProj[2] ((collisionModulus i).totient) = twoPartTable i := by
  intro i
  rw [← Nat.primeFactorsList_count_eq]
  revert i
  decide +kernel

/-- Discarding only the 2-primary part does not bound one collision fiber
by one, even with distinct odd moduli and an irredundant normalized family. -/
theorem two_primary_weight :
    (∑ i : Fin 18, 1 / ((ordProj[2] ((collisionModulus i).totient) : ℕ) : ℚ)) = 33/16 := by
  simp_rw [two_part_table]
  norm_num [twoPartTable, Fin.sum_univ_succ]

/-- The corrected uniform-translate meeting weights also exceed one.
No inference that every translate has a collision is made here. -/
theorem translate_weight :
    (∑ i : Fin 18, 3 / ((collisionModulus i).totient : ℚ)) = 439/288 := by
  simp_rw [totient_table]
  norm_num [totientTable, Fin.sum_univ_succ]

lemma both_weights_gt_one :
    (1 : ℚ) < (∑ i : Fin 18, 1 / ((ordProj[2] ((collisionModulus i).totient) : ℕ) : ℚ)) ∧
    (1 : ℚ) < (∑ i : Fin 18, 3 / ((collisionModulus i).totient : ℚ)) := by
  rw [two_primary_weight, translate_weight]
  norm_num

abbrev coveredOrbit : Fin 3 → ℕ := ![82,2677,3247]
lemma covered_orbit_units : ∀ t, Nat.Coprime (coveredOrbit t) 4095 := by decide +kernel
lemma covered_orbit_action : ∀ t : Fin 3,
    coveredOrbit (t+1) = (coveredOrbit t * 1381) % 4095 := by decide +kernel
lemma covered_orbit : ∀ t : Fin 3, ∃ i,
    (modulus i : ℤ) ∣ (coveredOrbit t : ℤ)-residue i := by decide +kernel

/-- There are also clean orbits. Thus the failed numerical fiber bounds do
not refute an adaptive choice of a useful orbit. -/
abbrev cleanOrbit : Fin 3 → ℕ := ![2,2762,1877]
lemma clean_orbit_units : ∀ t, Nat.Coprime (cleanOrbit t) 4095 := by decide +kernel
lemma clean_orbit_action : ∀ t : Fin 3,
    cleanOrbit (t+1) = (cleanOrbit t * 1381) % 4095 := by decide +kernel
lemma clean_orbit_meets_at_most_one : ∃ i : Fin 23, ∀ t j,
    (modulus j : ℤ) ∣ (cleanOrbit t : ℤ)-residue j → j=i := by decide +kernel


/-- Direct finite check of the uniform-translate interpretation of the weights.
A translate is sampled among all 1728 units modulo 4095. -/
abbrev meetingCount (i : Fin 18) : ℕ :=
  ((Finset.range 4095).filter (fun u => Nat.Coprime u 4095 ∧
    ∃ t : Fin 3, (u * 1381^t.val) % collisionModulus i =
      (residue (collisionIndex i)).toNat)).card

lemma unit_count : ((Finset.range 4095).filter (fun u => Nat.Coprime u 4095)).card = 1728 := by
  decide +kernel

set_option maxHeartbeats 12000000 in
lemma meeting_counts : ∀ i, meetingCount i = 3*1728 / totientTable i := by
  decide +kernel

theorem mean_active_collision_count : (∑ i : Fin 18, (meetingCount i : ℚ)) / 1728 = 439/288 := by
  simp_rw [meeting_counts]
  norm_num [totientTable, Fin.sum_univ_succ]


abbrev periodThreeActiveCount (u : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin 18)).filter (fun i =>
    ∃ t : Fin 3, (u * 1381^t.val) % collisionModulus i =
      (residue (collisionIndex i)).toNat)).card

lemma unit_event_count : ((Finset.range 4095).filter (fun u =>
    Nat.Coprime u 4095 ∧ u % 15 = 1)).card = 216 := by decide +kernel

set_option maxHeartbeats 16000000 in
lemma pair_charge_count : (∑ u ∈ Finset.range 4095,
    if Nat.Coprime u 4095 then (periodThreeActiveCount u).choose 2 else 0) = 1269 := by
  decide +kernel

/-- Here a second-order collision charge succeeds even though the raw
first-moment fiber bounds exceed one. This is only this finite partial family. -/
theorem collision_charge_lt_one :
    ((((Finset.range 4095).filter (fun u => Nat.Coprime u 4095 ∧ u % 15 = 1)).card : ℚ) +
      ((∑ u ∈ Finset.range 4095, if Nat.Coprime u 4095 then
        (periodThreeActiveCount u).choose 2 else 0 : ℕ) : ℚ)) / 1728 = 55/64 ∧
    (55/64 : ℚ) < 1 := by
  rw [unit_event_count, pair_charge_count]
  norm_num

lemma composite_index_split : ∀ i, ¬ (modulus i).Prime →
    i = 5 ∨ ∃ k, collisionIndex k = i := by decide +kernel

#print axioms collision_charge_lt_one

#print axioms mean_active_collision_count

#print axioms private_points
#print axioms local_order_three
#print axioms two_primary_weight
#print axioms translate_weight
#print axioms covered_orbit
#print axioms clean_orbit_meets_at_most_one
end Erdos7UnitWeightCollision
