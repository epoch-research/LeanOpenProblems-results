import Submission.FourthPowerAlmostPrime

/-! A fixed factor-count refinement of the rough almost-prime theorem.
This does not assert that the fixed count is one, and does not settle
Erdős 972. -/
namespace Erdos972FixedRoughFactorCount

open Finset Filter
open Erdos972PrimePowerError Erdos972PrimeAlmostPrime
open Erdos972PrimeRoughOutputs Erdos972GrowingCoprimeCandidates
open Erdos972EfficientPrimeAlmostPrime Erdos972FourthPowerAlmostPrime

set_option autoImplicit false
set_option maxHeartbeats 1000000
attribute [local irreducible] quarterRoot

lemma prime_iff_factor_length_one {n : ℕ} (hn : n ≠ 0) :
    n.Prime ↔ n.primeFactorsList.length = 1 := by
  constructor
  · intro hp
    simp [Nat.primeFactorsList_prime hp]
  · intro h
    obtain ⟨p, hp⟩ := List.length_eq_one_iff.mp h
    have hprod := Nat.prod_primeFactorsList hn
    rw [hp] at hprod
    have hnp : n = p := by simpa using hprod.symm
    have hmem : p ∈ n.primeFactorsList := by rw [hp]; simp
    simpa only [hnp] using Nat.prime_of_mem_primeFactorsList hmem

/-- Both the input and every output prime factor can exceed prescribed
bounds while retaining the factor count bound. -/
theorem exists_rough_almostPrime_beyond {α : ℝ} (hα : 1 < α)
    (hI : Irrational α) (B Z : ℕ) :
    ∃ p : ℕ, B < p ∧ p.Prime ∧
      (floorMul α p).primeFactorsList.length ≤ 6144 ∧
      (floorMul α p).Coprime Z.factorial := by
  let T := max (max ⌈14*fourthConstant*(B:ℝ)⌉₊ ⌈α⌉₊) Z
  obtain ⟨u, hu, hZ, hweight⟩ :=
    Erdos972FourthPowerAlmostPrime.exists_prime_rough_log_scale hα hI T
  have hu1 : 1 ≤ u := (Nat.zero_le T).trans_lt hu
  have hlargeU : 14*fourthConstant*(B:ℝ) < u :=
    (Nat.le_ceil _).trans_lt (Nat.cast_lt.mpr
      (((le_max_left _ _).trans (le_max_left _ _)).trans_lt hu))
  have hweightLarge : 7*(B:ℝ) <
      coprimePrimeWeight α (quarterRoot u).factorial (u^6) :=
    (seven_mul_lt_div fourthConstant_pos hlargeU).trans_le
      ((linear_below_log_weight fourthConstant_pos hu1).trans hweight)
  obtain ⟨p, hpB, hpN, hp, hpc⟩ := prime_beyond_of_coprime_weight hweightLarge
  have hαZ : α ≤ quarterRoot u := (Nat.le_ceil α).trans
    (Nat.cast_le.mpr (((le_max_right _ _).trans (le_max_left _ _)).trans hZ.le))
  have hZZ : Z ≤ quarterRoot u := (le_max_right _ _).trans hZ.le
  exact ⟨p, hpB, hp,
    Erdos972FourthPowerAlmostPrime.rough_output_factor_bound hα.le hp.pos hpN hαZ hpc,
    Nat.Coprime.of_dvd_right (Nat.factorial_dvd_factorial hZZ) hpc⟩

/-- The SAME count works for all input and roughness thresholds.
It is chosen by a finite pigeonhole argument, not separately at each scale. -/
theorem exists_fixed_rough_factor_count {α : ℝ} (hα : 1 < α)
    (hI : Irrational α) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ 6144 ∧ ∀ B Z : ℕ,
      ∃ p : ℕ, B < p ∧ p.Prime ∧
        (floorMul α p).primeFactorsList.length = k ∧
        (floorMul α p).Coprime Z.factorial := by
  have hf : ∃ᶠ n : ℕ in atTop, ∃ k ∈ Icc 1 6144,
      ∃ p : ℕ, n < p ∧ p.Prime ∧
        (floorMul α p).primeFactorsList.length = k ∧
        (floorMul α p).Coprime n.factorial := by
    apply Filter.Eventually.frequently
    apply Filter.Eventually.of_forall
    intro n
    obtain ⟨p, hnp, hp, hlen, hc⟩ := exists_rough_almostPrime_beyond hα hI n n
    have hq : 1 < floorMul α p := hp.one_lt.trans_le (self_le_floorMul hα.le p)
    have hlenpos : 0 < (floorMul α p).primeFactorsList.length :=
      List.length_pos_iff.mpr (Nat.primeFactorsList_ne_nil _ |>.mpr hq)
    exact ⟨_, mem_Icc.mpr ⟨hlenpos, hlen⟩, p, hnp, hp, rfl, hc⟩
  obtain ⟨k, hk, hkfreq⟩ := (Finset.frequently_exists (Icc 1 6144)).mp hf
  refine ⟨k, (mem_Icc.mp hk).1, (mem_Icc.mp hk).2, ?_⟩
  intro B Z
  obtain ⟨n, hn, p, hnp, hp, hlen, hc⟩ := frequently_atTop.mp hkfreq (max B Z)
  exact ⟨p, ((le_max_left B Z).trans hn).trans_lt hnp, hp, hlen,
    Nat.Coprime.of_dvd_right
      (Nat.factorial_dvd_factorial ((le_max_right B Z).trans hn)) hc⟩

lemma prime_factor_gt_of_coprime_factorial {q Z r : ℕ}
    (hc : q.Coprime Z.factorial) (hr : r.Prime) (hrq : r ∣ q) : Z < r := by
  by_contra h
  exact hr.ne_one (Nat.eq_one_of_dvd_coprimes hc hrq
    (hr.dvd_factorial.mpr (le_of_not_gt h)))

/-- A counterexample would have a fixed COMPOSITE factor count with
arbitrarily large inputs and arbitrarily large least output prime factor.
This is a necessary condition, not a contradiction. -/
theorem fixed_composite_count_of_finite {α : ℝ} (hα : 1 < α)
    (hI : Irrational α)
    (hfin : {p : ℕ | p.Prime ∧ (floorMul α p).Prime}.Finite) :
    ∃ k : ℕ, 2 ≤ k ∧ k ≤ 6144 ∧ ∀ B Z : ℕ,
      ∃ p : ℕ, B < p ∧ p.Prime ∧
        (floorMul α p).primeFactorsList.length = k ∧
        ∀ r : ℕ, r.Prime → r ∣ floorMul α p → Z < r := by
  obtain ⟨k, hk1, hkK, hk⟩ := exists_fixed_rough_factor_count hα hI
  have hkne : k ≠ 1 := by
    intro he
    obtain ⟨B, hB⟩ := hfin.bddAbove
    obtain ⟨p, hpB, hp, hlen, _⟩ := hk B 0
    have hq : (floorMul α p).Prime :=
      (prime_iff_factor_length_one (floorMul_pos hα.le hp.pos).ne').mpr (hlen.trans he)
    exact (not_le_of_gt hpB) (hB ⟨hp, hq⟩)
  refine ⟨k, by omega, hkK, ?_⟩
  intro B Z
  obtain ⟨p, hpB, hp, hlen, hc⟩ := hk B Z
  exact ⟨p, hpB, hp, hlen, fun r hr hrd =>
    prime_factor_gt_of_coprime_factorial hc hr hrd⟩

#print axioms exists_rough_almostPrime_beyond
#print axioms exists_fixed_rough_factor_count
#print axioms fixed_composite_count_of_finite

end Erdos972FixedRoughFactorCount
