import Submission.CubicRootObstruction
import Submission.ValuationStructure

/-! Good cubes with arbitrarily large two-adic valuation can avoid any fixed
finite set of odd primes. These numbers are not powers of two. This is an
obstruction to a finite-prime sieve, not a settlement of Erdős 406. -/

namespace Erdos406CubicPrimeAvoidance
open Erdos406Work Erdos406Structure

lemma odd_exponent_factor_valuation (L : ℕ) (hL : Odd L) :
    padicValNat 2 (3 ^ L + 1) = 2 := by
  obtain ⟨t, rfl⟩ := hL
  have hm : (3 ^ (2 * t + 1) + 1) % 8 = 4 := by
    norm_num [pow_add, pow_mul, Nat.pow_mod, Nat.add_mod, Nat.mul_mod]
  have h4 : 2 ^ 2 ∣ 3 ^ (2 * t + 1) + 1 := by
    apply Nat.dvd_of_mod_eq_zero
    have hh := congrArg (fun a : ℕ => a % 4) hm
    simpa [Nat.mod_mod_of_dvd _ (by decide : 4 ∣ 8)] using hh
  have h8 : ¬ 2 ^ 3 ∣ 3 ^ (2 * t + 1) + 1 := by
    intro h
    have hh := Nat.mod_eq_zero_of_dvd h
    norm_num at hh
    omega
  have hlo := (padicValNat_dvd_iff_le (by positivity : 3 ^ (2 * t + 1) + 1 ≠ 0)).mp h4
  have hhi : ¬ 3 ≤ padicValNat 2 (3 ^ (2 * t + 1) + 1) := by
    intro h
    exact h8 ((padicValNat_dvd_iff_le (by positivity)).mpr h)
  omega

/-- A separated cubic block can be chosen in a prescribed congruence class.
It adds exactly two factors of two, while preserving the digit restrictions
on both the root and the cube. -/
lemma amplify (q n B : ℕ) (hq : Nat.Coprime 3 q) (hn : 0 < n)
    (hg : Nat.digits 3 n ⊆ [0, 1])
    (hc : Nat.digits 3 (n ^ 3) ⊆ [0, 1]) :
    ∃ m : ℕ, B < m ∧ 0 < m ∧
      Nat.digits 3 m ⊆ [0, 1] ∧ Nat.digits 3 (m ^ 3) ⊆ [0, 1] ∧
      padicValNat 2 m = padicValNat 2 n + 2 ∧
      Nat.ModEq q m (4 * n) ∧ m % 3 = n % 3 ∧ ¬ m.isPowerOfTwo := by
  have hqpos : 0 < q := by
    by_contra h
    have hz : q = 0 := by omega
    simp [hz] at hq
  let T := q.totient
  have hT : 0 < T := Nat.totient_pos.mpr hqpos
  let R := (Nat.digits 3 n).length + (Nat.digits 3 (n ^ 3)).length + B + 1
  let L := 2 * T * (R + 1) + 1
  have hlarge : R < L := by
    dsimp [L]
    have hh := Nat.le_mul_of_pos_left (R + 1) (show 0 < 2 * T by positivity)
    omega
  have hLn : (Nat.digits 3 n).length ≤ L := by dsimp [R] at hlarge; omega
  have hLc : (Nat.digits 3 (n ^ 3)).length ≤ L - 1 := by dsimp [R] at hlarge; omega
  have hLB : B < L := by dsimp [R] at hlarge; omega
  have hL1 : 1 < L := by dsimp [R] at hlarge; omega
  have hLo : Odd L := ⟨T * (R + 1), by dsimp [L]; ring⟩
  have hpow : Nat.ModEq q (3 ^ L) 3 := by
    have hh := ((Nat.ModEq.pow_totient hq).pow (2 * (R + 1))).mul_right 3
    have he : L = q.totient * (2 * (R + 1)) + 1 := by dsimp [L, T]; ring
    simpa only [he, pow_add, pow_one, pow_mul, one_pow, one_mul] using hh
  let m := n * (3 ^ L + 1)
  have hmpos : 0 < m := by dsimp [m]; positivity
  have hmB : B < m := by
    have hp : L < 3 ^ L := Nat.lt_pow_self (by decide)
    have hh : 3 ^ L + 1 ≤ m := Nat.le_mul_of_pos_left _ hn
    omega
  have hnlt : n < 3 ^ L :=
    (Nat.lt_base_pow_length_digits (b := 3) (m := n) (by decide)).trans_le
      (Nat.pow_le_pow_right (by decide) hLn)
  have hmg : Nat.digits 3 m ⊆ [0, 1] := by
    have he : m = n + 3 ^ L * n := by dsimp [m]; ring
    rw [he]
    exact good_add_shifted hnlt hg hg
  have hmc : Nat.digits 3 (m ^ 3) ⊆ [0, 1] := by
    have hh := good_cube_mul_separated hc hLc
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ L)] using hh
  have hval : padicValNat 2 m = padicValNat 2 n + 2 := by
    rw [show m = n * (3 ^ L + 1) from rfl,
      padicValNat.mul (ne_of_gt hn) (by positivity), odd_exponent_factor_valuation L hLo]
  have hmres : Nat.ModEq q m (4 * n) := by
    have hh := (hpow.add_right 1).mul_left n
    simpa only [show 3 + 1 = (4 : ℕ) by decide, Nat.mul_comm n 4] using hh
  have hm3 : m % 3 = n % 3 := by
    dsimp [m, L]
    norm_num [pow_succ, Nat.mul_mod, Nat.add_mod]
  have hnot : ¬ m.isPowerOfTwo := by
    rintro ⟨k, hk⟩
    have hd : 3 ^ L + 1 ∣ 2 ^ k := by
      rw [← hk]
      exact dvd_mul_left _ _
    have hh := three_pow_add_one_dvd_two_pow (by omega : 0 < L) hd
    omega
  exact ⟨m, hmB, hmpos, hmg, hmc, hval, hmres, hm3, hnot⟩

/-- At every positive even valuation, there are arbitrarily large examples
in the indicated power-of-four residue class. -/
theorem arbitrary_valuation_and_residue (q K B : ℕ) (hq : Nat.Coprime 3 q) :
    ∃ n : ℕ, B < n ∧ 0 < n ∧
      Nat.digits 3 n ⊆ [0, 1] ∧ Nat.digits 3 (n ^ 3) ⊆ [0, 1] ∧
      padicValNat 2 n = 2 * (K + 1) ∧
      Nat.ModEq q n (4 ^ (K + 1)) ∧ n % 3 = 1 ∧ ¬ n.isPowerOfTwo := by
  induction K with
  | zero =>
    obtain ⟨n, hB, hn, hg, hc, hv, hr, h3, hnot⟩ :=
      amplify q 1 B hq (by decide) (by decide +kernel) (by decide +kernel)
    exact ⟨n, hB, hn, hg, hc, by simpa using hv, by simpa using hr,
      by simpa using h3, hnot⟩
  | succ K ih =>
    obtain ⟨n, _, hn, hg, hc, hv, hr, h3, _⟩ := ih
    obtain ⟨m, hB, hm, hmg, hmc, hmv, hmr, hm3, hnot⟩ := amplify q n B hq hn hg hc
    refine ⟨m, hB, hm, hmg, hmc, by omega, ?_, hm3.trans h3, hnot⟩
    simpa only [pow_succ'] using hmr.trans (hr.mul_left 4)

/-- No prescribed finite set of odd primes is forced to divide these roots,
even though both the roots and their cubes are ternary-good. -/
theorem avoid_finitely_many_odd_primes (S : Finset ℕ) (K B : ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p ∧ p ≠ 2) :
    ∃ n : ℕ, B < n ∧ 0 < n ∧
      Nat.digits 3 n ⊆ [0, 1] ∧ Nat.digits 3 (n ^ 3) ⊆ [0, 1] ∧
      padicValNat 2 n = 2 * (K + 1) ∧ n % 3 = 1 ∧
      (∀ p ∈ S, ¬ p ∣ n) ∧ ¬ n.isPowerOfTwo ∧ ¬ (n ^ 3).isPowerOfTwo := by
  let q := ∏ p ∈ S.erase 3, p
  have hq : Nat.Coprime 3 q := by
    apply Nat.Coprime.prod_right
    intro p hp
    obtain ⟨h3, hmem⟩ := Finset.mem_erase.mp hp
    exact (Nat.coprime_primes (by decide) (hS p hmem).1).mpr (Ne.symm h3)
  obtain ⟨n, hnB, hn, hg, hc, hv, hr, h3, hnot⟩ := arbitrary_valuation_and_residue q K B hq
  have havoid : ∀ p ∈ S, ¬ p ∣ n := by
    intro p hp hpn
    by_cases hp3 : p = 3
    · subst p
      have hh := Nat.mod_eq_zero_of_dvd hpn
      omega
    · have hpd : p ∣ q := Finset.dvd_prod_of_mem (fun p : ℕ => p)
        (Finset.mem_erase.mpr ⟨hp3, hp⟩)
      have hh : p ∣ 4 ^ (K + 1) := (hr.dvd_iff hpd).mp hpn
      have hh4 : p ∣ 4 := (hS p hp).1.dvd_of_dvd_pow hh
      have hh2 : p ∣ 2 := (hS p hp).1.dvd_of_dvd_pow
        (show p ∣ 2 ^ 2 from hh4)
      rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hh2 with h1 | h2
      · exact (hS p hp).1.ne_one h1
      · exact (hS p hp).2 h2
  have hcnot : ¬ (n ^ 3).isPowerOfTwo := by
    rintro ⟨k, hk⟩
    have hd : n ∣ 2 ^ k := by rw [← hk]; exact dvd_pow_self n (by decide)
    obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).mp hd
    exact hnot ⟨j, hj⟩
  exact ⟨n, hnB, hn, hg, hc, hv, h3, havoid, hnot, hcnot⟩

/-- The least odd prime factor has no bound that depends only on a prescribed
two-adic divisibility threshold, even within good cubes with good roots. -/
theorem arbitrarily_rough_good_cubes (P K B : ℕ) :
    ∃ n : ℕ, B < n ∧ 0 < n ∧
      Nat.digits 3 n ⊆ [0, 1] ∧ Nat.digits 3 (n ^ 3) ⊆ [0, 1] ∧
      padicValNat 2 n = 2 * (K + 1) ∧ n % 3 = 1 ∧
      (∀ p : ℕ, Nat.Prime p → p ≠ 2 → p ∣ n → P < p) ∧
      ¬ n.isPowerOfTwo ∧ ¬ (n ^ 3).isPowerOfTwo := by
  let S := (Finset.range (P + 1)).filter (fun p => Nat.Prime p ∧ p ≠ 2)
  have hS : ∀ p ∈ S, Nat.Prime p ∧ p ≠ 2 := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  obtain ⟨n, hB, hn, hg, hc, hv, h3, ha, hnot, hcnot⟩ :=
    avoid_finitely_many_odd_primes S K B hS
  refine ⟨n, hB, hn, hg, hc, hv, h3, ?_, hnot, hcnot⟩
  intro p hp hp2 hpn
  by_contra h
  have hmem : p ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp, hp2⟩
  exact ha p hmem hpn

#print axioms odd_exponent_factor_valuation
#print axioms arbitrary_valuation_and_residue
#print axioms avoid_finitely_many_odd_primes
#print axioms arbitrarily_rough_good_cubes
end Erdos406CubicPrimeAvoidance
