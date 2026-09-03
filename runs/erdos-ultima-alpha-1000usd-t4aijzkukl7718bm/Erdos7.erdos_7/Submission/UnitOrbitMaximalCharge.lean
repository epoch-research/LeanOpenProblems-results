import Submission.UnitOrbitPhaseProbability

/-! A small normalized irredundant partial family defeats the proposed
phase-sensitive union bound for a maximal local odd-order generator.
It is not a cover, and it does not rule out a better generator or translate. -/
namespace Erdos7UnitOrbitMaximalCharge
open Erdos7UnitOrbitProbability Erdos7UnitOrbitKernel Erdos7UnitOrbitPhaseProbability
open scoped BigOperators
open Fin.NatCast
set_option maxRecDepth 1000000
set_option maxHeartbeats 12000000

abbrev modulus : Fin 11 → ℕ := ![3,7,9,21,49,63,147,343,441,1029,3087]
abbrev residue : Fin 11 → ℕ := ![0,0,1,4,8,16,22,23,43,58,85]
abbrev witness : Fin 11 → ℕ := ![3,7,1,4,8,16,22,23,43,58,85]
lemma modulus_injective : Function.Injective modulus := by decide +kernel
lemma odd_nontrivial : ∀ i, Odd (modulus i) ∧ 1 < modulus i := by decide +kernel
lemma divisor_closed : ∀ i, ∀ d ∈ (modulus i).divisors,
    1 < d → ∃ j, modulus j = d := by decide +kernel
lemma private_points : ∀ i, witness i % modulus i = residue i ∧
    ∀ j, j ≠ i → witness i % modulus j ≠ residue j := by decide +kernel
lemma normalized_primes : ∀ i, (modulus i).Prime → residue i = 0 := by decide +kernel
lemma composite_units : ∀ i, ¬ (modulus i).Prime → Nat.Coprime (residue i) (modulus i) := by
  decide +kernel
lemma two_uncovered : ∀ i, 2 % modulus i ≠ residue i := by decide +kernel

abbrev m : Fin 9 → ℕ := ![9,21,49,63,147,343,441,1029,3087]
abbrev r : Fin 9 → ℕ := ![1,4,8,16,22,23,43,58,85]
lemma mdvd : ∀ i, m i ∣ 3087 := by decide +kernel
lemma rcoprime : ∀ i, Nat.Coprime (r i) (m i) := by decide +kernel

def u : (ZMod 3087)ˣ := ZMod.unitOfCoprime 1381 (by decide)
def a (i : Fin 9) : (ZMod (m i))ˣ := ZMod.unitOfCoprime (r i) (rcoprime i)

def period (d : ℕ) : ℕ :=
  if d % 343 = 0 then 147 else if d % 49 = 0 then 21 else
    if d % 7 = 0 ∨ d % 9 = 0 then 3 else 1

lemma period_pos (d : ℕ) : 0 < period d := by unfold period; split_ifs <;> norm_num

lemma order_checks : ∀ d ∈ Nat.divisors 3087,
    (1381 : ZMod d) ^ period d = 1 ∧
    ∀ k : Fin (period d), 0 < k.val → (1381 : ZMod d)^k.val ≠ 1 := by
  decide +kernel

lemma reduction_order {d : ℕ} (hd : d ∣ 3087) :
    orderOf (ZMod.unitsMap hd u) = period d := by
  rw [← orderOf_units, ZMod.unitsMap_val, u, ZMod.coe_unitOfCoprime, ZMod.cast_natCast hd]
  apply (orderOf_eq_iff (period_pos d)).mpr
  have hh := order_checks d (Nat.mem_divisors.mpr ⟨hd, by decide⟩)
  exact ⟨hh.1, fun k hk hk0 => hh.2 ⟨k,hk⟩ hk0⟩

lemma period_table : ∀ i, period (m i) = (![3,3,21,3,21,147,21,147,147] : Fin 9 → ℕ) i := by
  decide +kernel

/-- The chosen generator has the full odd local order at 9 and at 343. -/
lemma maximal_local_orders :
    orderOf (ZMod.unitsMap (by decide : 9 ∣ 3087) u) = 3 ∧
    orderOf (ZMod.unitsMap (by decide : 343 ∣ 3087) u) = 147 ∧ orderOf u = 147 := by
  rw [reduction_order, reduction_order]
  have h := reduction_order (dvd_refl 3087)
  simp only [ZMod.unitsMap_self, MonoidHom.id_apply] at h
  exact ⟨by decide, by decide, h⟩

lemma compatibility_checks : ∀ i j : Fin 9, period (m i) = period (m j) →
    ∃ t : Fin 147,
      ZMod.unitsMap (Nat.gcd_dvd_left (m i) (m j)) (a i) *
        (ZMod.unitsMap ((Nat.gcd_dvd_left (m i) (m j)).trans (mdvd i)) u)^t.val =
      ZMod.unitsMap (Nat.gcd_dvd_right (m i) (m j)) (a j) := by
  decide +kernel

lemma compatible_equal (i j : Fin 9) (he : period (m i) = period (m j)) :
    Compatible (mdvd i) (mdvd j) u (a i) (a j) := by
  obtain ⟨t,ht⟩ := compatibility_checks i j he
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨(t.val : ℤ), ?_⟩
  rw [zpow_natCast, eq_inv_mul_iff_mul_eq]
  exact ht

/-- Among distinct equal-period pairs, only 9 and 21 admit a common point. -/
lemma crt_checks : ∀ i j : Fin 9, i < j → period (m i) = period (m j) →
    (CRTCompatible (a i) (a j) ↔ i = 0 ∧ j = 1) := by
  unfold CRTCompatible
  decide +kernel

/-- The exact pair probability in this explicit family. -/
lemma pair_value (i j : Fin 9) (hij : i < j) (he : period (m i) = period (m j)) :
    (Nat.card {v : (ZMod 3087)ˣ //
      (Meets (ZMod.unitsMap (mdvd i)) u (a i) v ∧ Meets (ZMod.unitsMap (mdvd j)) u (a j) v) ∧
        ¬ CoMeets (mdvd i) (mdvd j) u (a i) (a j) v} : ℚ) / (3087).totient =
    ((period (m i) : ℚ) * period (m j)) /
      ((period ((m i).gcd (m j)) : ℚ) * ((m i).lcm (m j)).totient) -
      (if i = 0 ∧ j = 1 then (period ((m i).lcm (m j)) : ℚ) /
        ((m i).lcm (m j)).totient else 0) := by
  classical
  rw [distinct_phase_probability, if_pos (compatible_equal i j he)]
  simp_rw [reduction_order]
  rw [crt_checks i j hij he]
  split_ifs <;> rfl

/-- The actual uniform-translate phase-collision budget is 7/6, not below one.
The nine participating pairs come from the three equal-period fibers. -/
theorem maximal_generator_charge :
    (∑ i : Fin 9, ∑ j : Fin 9,
      if i < j ∧ period (m i) = period (m j) then
        (Nat.card {v : (ZMod 3087)ˣ //
          (Meets (ZMod.unitsMap (mdvd i)) u (a i) v ∧ Meets (ZMod.unitsMap (mdvd j)) u (a j) v) ∧
            ¬ CoMeets (mdvd i) (mdvd j) u (a i) (a j) v} : ℚ) / (3087).totient
      else 0) = 7/6 := by
  classical
  have hp : ∀ i j : Fin 9,
      (if i < j ∧ period (m i) = period (m j) then
        (Nat.card {v : (ZMod 3087)ˣ //
          (Meets (ZMod.unitsMap (mdvd i)) u (a i) v ∧ Meets (ZMod.unitsMap (mdvd j)) u (a j) v) ∧
            ¬ CoMeets (mdvd i) (mdvd j) u (a i) (a j) v} : ℚ) / (3087).totient
      else 0) =
      if i < j ∧ period (m i) = period (m j) then
        ((period (m i) : ℚ) * period (m j)) /
          ((period ((m i).gcd (m j)) : ℚ) * ((m i).lcm (m j)).totient) -
          (if i = 0 ∧ j = 1 then (period ((m i).lcm (m j)) : ℚ) /
            ((m i).lcm (m j)).totient else 0)
      else 0 := by
    intro i j
    by_cases h : i < j ∧ period (m i) = period (m j)
    · simp only [if_pos h]
      exact pair_value i j h.1 h.2
    · simp only [if_neg h]
  simp_rw [hp]
  decide +kernel

lemma all_periods_nonunit : ∀ i : Fin 9, 1 < orderOf (ZMod.unitsMap (mdvd i) u) := by
  simp_rw [reduction_order]
  decide +kernel

lemma generator_odd : Odd (orderOf u) := by
  rw [maximal_local_orders.2.2]
  decide

lemma generator_charge_gt_one :
    (1 : ℚ) < (∑ i : Fin 9, ∑ j : Fin 9,
      if i < j ∧ period (m i) = period (m j) then
        (Nat.card {v : (ZMod 3087)ˣ //
          (Meets (ZMod.unitsMap (mdvd i)) u (a i) v ∧ Meets (ZMod.unitsMap (mdvd j)) u (a j) v) ∧
            ¬ CoMeets (mdvd i) (mdvd j) u (a i) (a j) v} : ℚ) / (3087).totient
      else 0) := by
  rw [maximal_generator_charge]
  norm_num

#print axioms generator_charge_gt_one
#print axioms private_points
#print axioms maximal_local_orders
#print axioms maximal_generator_charge
end Erdos7UnitOrbitMaximalCharge
