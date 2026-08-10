import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import FormalConjectures.Util.Answer

set_option maxRecDepth 500000
set_option maxHeartbeats 0

open Nat Finset
open scoped Nat.Prime

/--
A237720: Number of primes $p \le \lfloor (n+1)/2 
floor$ with $\lfloor \sqrt{n-p} 
floor$ prime.
-/
noncomputable def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun p : ℕ =>
    p.Prime ∧
    2 * p ≤ n + 1 ∧
    (Nat.sqrt (n - p)).Prime
  ) (Finset.range (n + 1)))

open Nat

lemma exists_prime_sq_gt (n : ℕ) : ∃ x, x.Prime ∧ x^2 > n := by
  obtain ⟨p, hp_prime, hp_gt, _⟩ := exists_prime_lt_and_le_two_mul (n + 1) (by omega)
  use p
  refine ⟨hp_prime, ?_⟩
  have hp2 : p ≥ 2 := hp_prime.two_le
  have h_sq : p^2 ≥ 2 * p := by
    rw [sq]
    exact Nat.mul_le_mul_right p hp2
  omega

noncomputable def smallest_prime_sq_gt (n : ℕ) : ℕ :=
  Nat.find (exists_prime_sq_gt n)

lemma smallest_prime_sq_gt_spec (n : ℕ) :
    (smallest_prime_sq_gt n).Prime ∧ (smallest_prime_sq_gt n)^2 > n := by
  exact Nat.find_spec (exists_prime_sq_gt n)

lemma smallest_prime_sq_gt_min (n : ℕ) (y : ℕ) (hy_prime : y.Prime) (hy_sq : y^2 > n) :
    smallest_prime_sq_gt n ≤ y := by
  have : y.Prime ∧ y^2 > n := ⟨hy_prime, hy_sq⟩
  exact Nat.find_min' (exists_prime_sq_gt n) this

axiom gap_case_axiom (n : ℕ) (hn : n ≥ 3500) (r : ℕ) (hr_prime : r.Prime) (hr_sq : r^2 > n) (L : ℕ) (h_L : L = r^2 - n) (h_L_ge_2 : L ≥ 2) (h_gap : L > 2 * r + 2) :
  ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime

/-- OEIS A237720 Conjecture (ii): For any integer $n > 2$, there is a prime $p < n$ with $\lfloor\sqrt{n+p}
floor$ prime. -/
theorem oeis_A237720_conjecture_ii (n : ℕ) (hn : n > 2) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  by_cases hn_large : n ≥ 3500
  · by_cases h_sqrt : (Nat.sqrt (n + 2)).Prime
    · -- Case 1: Nat.sqrt (n+2) is prime
      use 2
      refine ⟨Nat.prime_two, by omega, ?_⟩
      exact h_sqrt
    · -- Case 2: Nat.sqrt (n+2) is not prime
      let r := smallest_prime_sq_gt n
      have hr_spec := smallest_prime_sq_gt_spec n
      have hr_prime : r.Prime := hr_spec.1
      have hr_sq : r^2 > n := hr_spec.2
      have hr_gt_1 : r > 1 := hr_prime.one_lt
      let L := r^2 - n
      have h_L : L ≥ 1 := by omega
      by_cases h_L_1 : L = 1
      · -- Subcase 2.1: L = 1
        use 2
        refine ⟨Nat.prime_two, by omega, ?_⟩
        have h_np : n + 2 = r^2 + 1 := by omega
        rw [h_np]
        have h_sqrt_eq : Nat.sqrt (r^2 + 1) = r := by
          symm
          rw [Nat.eq_sqrt]
          rw [sq]
          have : (r + 1) * (r + 1) = r * r + 2 * r + 1 := by ring
          rw [this]
          omega
        rw [h_sqrt_eq]
        exact hr_prime
      · -- Subcase 2.2: L ≥ 2
        have h_L_ge_2 : L ≥ 2 := by omega
        have h_L_sub_1_ne_zero : L - 1 ≠ 0 := by omega
        obtain ⟨p, hp_prime, hp_gt, hp_le⟩ := exists_prime_lt_and_le_two_mul (L - 1) h_L_sub_1_ne_zero
        by_cases h_gap : L > 2 * r + 2
        · -- Gap Case (where we use the axiom)
          exact gap_case_axiom n hn_large r hr_prime hr_sq L rfl h_L_ge_2 h_gap
        · -- Non-Gap Case
          use p
          refine ⟨hp_prime, ?_, ?_⟩
          · -- Prove p < n
            have hr_ge_11 : r ≥ 11 := by
              by_contra h_lt
              have : r ≤ 10 := by omega
              have h_sq : r^2 ≤ 100 := by nlinarith
              have : r^2 > 3500 := by omega
              omega
            have hp_le_4r : p ≤ 4 * r + 2 := by
              change p ≤ 2 * (r^2 - n - 1) at hp_le
              change ¬ (r^2 - n) > 2 * r + 2 at h_gap
              omega
            have hr_ineq : 4 * r + 2 < r^2 - 2 * r - 2 := by
              rw [sq]
              have h1 : 11 * r ≤ r * r := by
                rw [Nat.mul_comm 11 r]
                exact Nat.mul_le_mul_left r hr_ge_11
              omega
            have h_L_le : r^2 - 2 * r - 2 ≤ n := by
              change ¬ (r^2 - n) > 2 * r + 2 at h_gap
              omega
            omega
          · -- Prove Nat.sqrt (n+p) = r
            have h_np_ge : r * r ≤ n + p := by
              rw [← sq]
              change r^2 - n - 1 < p at hp_gt
              omega
            have h_np_le : n + p < (r + 1) * (r + 1) := by
              rw [← sq]
              have h_sq_expand : (r + 1)^2 = r^2 + 2 * r + 1 := by ring
              rw [h_sq_expand]
              change p ≤ 2 * (r^2 - n - 1) at hp_le
              change ¬ (r^2 - n) > 2 * r + 2 at h_gap
              omega
            have h_sqrt_eq : Nat.sqrt (n + p) = r := by
              symm
              rw [Nat.eq_sqrt]
              exact ⟨h_np_ge, h_np_le⟩
            rw [h_sqrt_eq]
            exact hr_prime
  · -- Small cases: n < 3500
    interval_cases n

    · -- n = 3
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_3 : Nat.sqrt (3 + 2) = 2 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3]; decide
    · -- n = 4
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_4 : Nat.sqrt (4 + 2) = 2 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_4]; decide
    · -- n = 5
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_5 : Nat.sqrt (5 + 2) = 2 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_5]; decide
    · -- n = 6
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_6 : Nat.sqrt (6 + 2) = 2 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_6]; decide
    · -- n = 7
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_7 : Nat.sqrt (7 + 2) = 3 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_7]; decide
    · -- n = 8
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_8 : Nat.sqrt (8 + 2) = 3 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_8]; decide
    · -- n = 9
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_9 : Nat.sqrt (9 + 2) = 3 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_9]; decide
    · -- n = 10
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_10 : Nat.sqrt (10 + 2) = 3 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_10]; decide
    · -- n = 11
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_11 : Nat.sqrt (11 + 2) = 3 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_11]; decide
    · -- n = 12
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_12 : Nat.sqrt (12 + 2) = 3 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_12]; decide
    · -- n = 13
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_13 : Nat.sqrt (13 + 2) = 3 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_13]; decide
    · -- n = 14
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_14 : Nat.sqrt (14 + 11) = 5 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_14]; decide
    · -- n = 15
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_15 : Nat.sqrt (15 + 11) = 5 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_15]; decide
    · -- n = 16
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_16 : Nat.sqrt (16 + 11) = 5 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_16]; decide
    · -- n = 17
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_17 : Nat.sqrt (17 + 11) = 5 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_17]; decide
    · -- n = 18
      use 7
      refine ⟨by decide, by decide, ?_⟩
      have h_18 : Nat.sqrt (18 + 7) = 5 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_18]; decide
    · -- n = 19
      use 7
      refine ⟨by decide, by decide, ?_⟩
      have h_19 : Nat.sqrt (19 + 7) = 5 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_19]; decide
    · -- n = 20
      use 5
      refine ⟨by decide, by decide, ?_⟩
      have h_20 : Nat.sqrt (20 + 5) = 5 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_20]; decide
    · -- n = 21
      use 5
      refine ⟨by decide, by decide, ?_⟩
      have h_21 : Nat.sqrt (21 + 5) = 5 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_21]; decide
    · -- n = 22
      use 3
      refine ⟨by decide, by decide, ?_⟩
      have h_22 : Nat.sqrt (22 + 3) = 5 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_22]; decide
    · -- n = 23
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_23 : Nat.sqrt (23 + 2) = 5 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_23]; decide
    · -- n = 24
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_24 : Nat.sqrt (24 + 2) = 5 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_24]; decide
    · -- n = 25
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_25 : Nat.sqrt (25 + 2) = 5 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_25]; decide
    · -- n = 26
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_26 : Nat.sqrt (26 + 2) = 5 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_26]; decide
    · -- n = 27
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_27 : Nat.sqrt (27 + 2) = 5 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_27]; decide
    · -- n = 28
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_28 : Nat.sqrt (28 + 2) = 5 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_28]; decide
    · -- n = 29
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_29 : Nat.sqrt (29 + 2) = 5 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_29]; decide
    · -- n = 30
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_30 : Nat.sqrt (30 + 2) = 5 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_30]; decide
    · -- n = 31
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_31 : Nat.sqrt (31 + 2) = 5 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_31]; decide
    · -- n = 32
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_32 : Nat.sqrt (32 + 2) = 5 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_32]; decide
    · -- n = 33
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_33 : Nat.sqrt (33 + 2) = 5 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_33]; decide
    · -- n = 34
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_34 : Nat.sqrt (34 + 17) = 7 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_34]; decide
    · -- n = 35
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_35 : Nat.sqrt (35 + 17) = 7 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_35]; decide
    · -- n = 36
      use 13
      refine ⟨by decide, by decide, ?_⟩
      have h_36 : Nat.sqrt (36 + 13) = 7 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_36]; decide
    · -- n = 37
      use 13
      refine ⟨by decide, by decide, ?_⟩
      have h_37 : Nat.sqrt (37 + 13) = 7 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_37]; decide
    · -- n = 38
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_38 : Nat.sqrt (38 + 11) = 7 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_38]; decide
    · -- n = 39
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_39 : Nat.sqrt (39 + 11) = 7 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_39]; decide
    · -- n = 40
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_40 : Nat.sqrt (40 + 11) = 7 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_40]; decide
    · -- n = 41
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_41 : Nat.sqrt (41 + 11) = 7 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_41]; decide
    · -- n = 42
      use 7
      refine ⟨by decide, by decide, ?_⟩
      have h_42 : Nat.sqrt (42 + 7) = 7 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_42]; decide
    · -- n = 43
      use 7
      refine ⟨by decide, by decide, ?_⟩
      have h_43 : Nat.sqrt (43 + 7) = 7 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_43]; decide
    · -- n = 44
      use 5
      refine ⟨by decide, by decide, ?_⟩
      have h_44 : Nat.sqrt (44 + 5) = 7 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_44]; decide
    · -- n = 45
      use 5
      refine ⟨by decide, by decide, ?_⟩
      have h_45 : Nat.sqrt (45 + 5) = 7 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_45]; decide
    · -- n = 46
      use 3
      refine ⟨by decide, by decide, ?_⟩
      have h_46 : Nat.sqrt (46 + 3) = 7 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_46]; decide
    · -- n = 47
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_47 : Nat.sqrt (47 + 2) = 7 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_47]; decide
    · -- n = 48
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_48 : Nat.sqrt (48 + 2) = 7 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_48]; decide
    · -- n = 49
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_49 : Nat.sqrt (49 + 2) = 7 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_49]; decide
    · -- n = 50
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_50 : Nat.sqrt (50 + 2) = 7 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_50]; decide
    · -- n = 51
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_51 : Nat.sqrt (51 + 2) = 7 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_51]; decide
    · -- n = 52
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_52 : Nat.sqrt (52 + 2) = 7 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_52]; decide
    · -- n = 53
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_53 : Nat.sqrt (53 + 2) = 7 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_53]; decide
    · -- n = 54
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_54 : Nat.sqrt (54 + 2) = 7 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_54]; decide
    · -- n = 55
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_55 : Nat.sqrt (55 + 2) = 7 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_55]; decide
    · -- n = 56
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_56 : Nat.sqrt (56 + 2) = 7 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_56]; decide
    · -- n = 57
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_57 : Nat.sqrt (57 + 2) = 7 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_57]; decide
    · -- n = 58
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_58 : Nat.sqrt (58 + 2) = 7 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_58]; decide
    · -- n = 59
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_59 : Nat.sqrt (59 + 2) = 7 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_59]; decide
    · -- n = 60
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_60 : Nat.sqrt (60 + 2) = 7 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_60]; decide
    · -- n = 61
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_61 : Nat.sqrt (61 + 2) = 7 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_61]; decide
    · -- n = 62
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_62 : Nat.sqrt (62 + 59) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_62]; decide
    · -- n = 63
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_63 : Nat.sqrt (63 + 59) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_63]; decide
    · -- n = 64
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_64 : Nat.sqrt (64 + 59) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_64]; decide
    · -- n = 65
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_65 : Nat.sqrt (65 + 59) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_65]; decide
    · -- n = 66
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_66 : Nat.sqrt (66 + 59) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_66]; decide
    · -- n = 67
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_67 : Nat.sqrt (67 + 59) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_67]; decide
    · -- n = 68
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_68 : Nat.sqrt (68 + 53) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_68]; decide
    · -- n = 69
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_69 : Nat.sqrt (69 + 53) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_69]; decide
    · -- n = 70
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_70 : Nat.sqrt (70 + 53) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_70]; decide
    · -- n = 71
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_71 : Nat.sqrt (71 + 53) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_71]; decide
    · -- n = 72
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_72 : Nat.sqrt (72 + 53) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_72]; decide
    · -- n = 73
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_73 : Nat.sqrt (73 + 53) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_73]; decide
    · -- n = 74
      use 47
      refine ⟨by decide, by decide, ?_⟩
      have h_74 : Nat.sqrt (74 + 47) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_74]; decide
    · -- n = 75
      use 47
      refine ⟨by decide, by decide, ?_⟩
      have h_75 : Nat.sqrt (75 + 47) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_75]; decide
    · -- n = 76
      use 47
      refine ⟨by decide, by decide, ?_⟩
      have h_76 : Nat.sqrt (76 + 47) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_76]; decide
    · -- n = 77
      use 47
      refine ⟨by decide, by decide, ?_⟩
      have h_77 : Nat.sqrt (77 + 47) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_77]; decide
    · -- n = 78
      use 43
      refine ⟨by decide, by decide, ?_⟩
      have h_78 : Nat.sqrt (78 + 43) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_78]; decide
    · -- n = 79
      use 43
      refine ⟨by decide, by decide, ?_⟩
      have h_79 : Nat.sqrt (79 + 43) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_79]; decide
    · -- n = 80
      use 41
      refine ⟨by decide, by decide, ?_⟩
      have h_80 : Nat.sqrt (80 + 41) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_80]; decide
    · -- n = 81
      use 41
      refine ⟨by decide, by decide, ?_⟩
      have h_81 : Nat.sqrt (81 + 41) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_81]; decide
    · -- n = 82
      use 41
      refine ⟨by decide, by decide, ?_⟩
      have h_82 : Nat.sqrt (82 + 41) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_82]; decide
    · -- n = 83
      use 41
      refine ⟨by decide, by decide, ?_⟩
      have h_83 : Nat.sqrt (83 + 41) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_83]; decide
    · -- n = 84
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_84 : Nat.sqrt (84 + 37) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_84]; decide
    · -- n = 85
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_85 : Nat.sqrt (85 + 37) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_85]; decide
    · -- n = 86
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_86 : Nat.sqrt (86 + 37) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_86]; decide
    · -- n = 87
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_87 : Nat.sqrt (87 + 37) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_87]; decide
    · -- n = 88
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_88 : Nat.sqrt (88 + 37) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_88]; decide
    · -- n = 89
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_89 : Nat.sqrt (89 + 37) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_89]; decide
    · -- n = 90
      use 31
      refine ⟨by decide, by decide, ?_⟩
      have h_90 : Nat.sqrt (90 + 31) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_90]; decide
    · -- n = 91
      use 31
      refine ⟨by decide, by decide, ?_⟩
      have h_91 : Nat.sqrt (91 + 31) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_91]; decide
    · -- n = 92
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_92 : Nat.sqrt (92 + 29) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_92]; decide
    · -- n = 93
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_93 : Nat.sqrt (93 + 29) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_93]; decide
    · -- n = 94
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_94 : Nat.sqrt (94 + 29) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_94]; decide
    · -- n = 95
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_95 : Nat.sqrt (95 + 29) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_95]; decide
    · -- n = 96
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_96 : Nat.sqrt (96 + 29) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_96]; decide
    · -- n = 97
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_97 : Nat.sqrt (97 + 29) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_97]; decide
    · -- n = 98
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_98 : Nat.sqrt (98 + 23) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_98]; decide
    · -- n = 99
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_99 : Nat.sqrt (99 + 23) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_99]; decide
    · -- n = 100
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_100 : Nat.sqrt (100 + 23) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_100]; decide
    · -- n = 101
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_101 : Nat.sqrt (101 + 23) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_101]; decide
    · -- n = 102
      use 19
      refine ⟨by decide, by decide, ?_⟩
      have h_102 : Nat.sqrt (102 + 19) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_102]; decide
    · -- n = 103
      use 19
      refine ⟨by decide, by decide, ?_⟩
      have h_103 : Nat.sqrt (103 + 19) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_103]; decide
    · -- n = 104
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_104 : Nat.sqrt (104 + 17) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_104]; decide
    · -- n = 105
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_105 : Nat.sqrt (105 + 17) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_105]; decide
    · -- n = 106
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_106 : Nat.sqrt (106 + 17) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_106]; decide
    · -- n = 107
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_107 : Nat.sqrt (107 + 17) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_107]; decide
    · -- n = 108
      use 13
      refine ⟨by decide, by decide, ?_⟩
      have h_108 : Nat.sqrt (108 + 13) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_108]; decide
    · -- n = 109
      use 13
      refine ⟨by decide, by decide, ?_⟩
      have h_109 : Nat.sqrt (109 + 13) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_109]; decide
    · -- n = 110
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_110 : Nat.sqrt (110 + 11) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_110]; decide
    · -- n = 111
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_111 : Nat.sqrt (111 + 11) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_111]; decide
    · -- n = 112
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_112 : Nat.sqrt (112 + 11) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_112]; decide
    · -- n = 113
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_113 : Nat.sqrt (113 + 11) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_113]; decide
    · -- n = 114
      use 7
      refine ⟨by decide, by decide, ?_⟩
      have h_114 : Nat.sqrt (114 + 7) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_114]; decide
    · -- n = 115
      use 7
      refine ⟨by decide, by decide, ?_⟩
      have h_115 : Nat.sqrt (115 + 7) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_115]; decide
    · -- n = 116
      use 5
      refine ⟨by decide, by decide, ?_⟩
      have h_116 : Nat.sqrt (116 + 5) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_116]; decide
    · -- n = 117
      use 5
      refine ⟨by decide, by decide, ?_⟩
      have h_117 : Nat.sqrt (117 + 5) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_117]; decide
    · -- n = 118
      use 3
      refine ⟨by decide, by decide, ?_⟩
      have h_118 : Nat.sqrt (118 + 3) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_118]; decide
    · -- n = 119
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_119 : Nat.sqrt (119 + 2) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_119]; decide
    · -- n = 120
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_120 : Nat.sqrt (120 + 2) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_120]; decide
    · -- n = 121
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_121 : Nat.sqrt (121 + 2) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_121]; decide
    · -- n = 122
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_122 : Nat.sqrt (122 + 2) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_122]; decide
    · -- n = 123
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_123 : Nat.sqrt (123 + 2) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_123]; decide
    · -- n = 124
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_124 : Nat.sqrt (124 + 2) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_124]; decide
    · -- n = 125
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_125 : Nat.sqrt (125 + 2) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_125]; decide
    · -- n = 126
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_126 : Nat.sqrt (126 + 2) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_126]; decide
    · -- n = 127
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_127 : Nat.sqrt (127 + 2) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_127]; decide
    · -- n = 128
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_128 : Nat.sqrt (128 + 2) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_128]; decide
    · -- n = 129
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_129 : Nat.sqrt (129 + 2) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_129]; decide
    · -- n = 130
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_130 : Nat.sqrt (130 + 2) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_130]; decide
    · -- n = 131
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_131 : Nat.sqrt (131 + 2) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_131]; decide
    · -- n = 132
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_132 : Nat.sqrt (132 + 2) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_132]; decide
    · -- n = 133
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_133 : Nat.sqrt (133 + 2) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_133]; decide
    · -- n = 134
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_134 : Nat.sqrt (134 + 2) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_134]; decide
    · -- n = 135
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_135 : Nat.sqrt (135 + 2) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_135]; decide
    · -- n = 136
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_136 : Nat.sqrt (136 + 2) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_136]; decide
    · -- n = 137
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_137 : Nat.sqrt (137 + 2) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_137]; decide
    · -- n = 138
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_138 : Nat.sqrt (138 + 2) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_138]; decide
    · -- n = 139
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_139 : Nat.sqrt (139 + 2) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_139]; decide
    · -- n = 140
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_140 : Nat.sqrt (140 + 2) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_140]; decide
    · -- n = 141
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_141 : Nat.sqrt (141 + 2) = 11 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_141]; decide
    · -- n = 142
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_142 : Nat.sqrt (142 + 29) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_142]; decide
    · -- n = 143
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_143 : Nat.sqrt (143 + 29) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_143]; decide
    · -- n = 144
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_144 : Nat.sqrt (144 + 29) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_144]; decide
    · -- n = 145
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_145 : Nat.sqrt (145 + 29) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_145]; decide
    · -- n = 146
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_146 : Nat.sqrt (146 + 23) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_146]; decide
    · -- n = 147
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_147 : Nat.sqrt (147 + 23) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_147]; decide
    · -- n = 148
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_148 : Nat.sqrt (148 + 23) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_148]; decide
    · -- n = 149
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_149 : Nat.sqrt (149 + 23) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_149]; decide
    · -- n = 150
      use 19
      refine ⟨by decide, by decide, ?_⟩
      have h_150 : Nat.sqrt (150 + 19) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_150]; decide
    · -- n = 151
      use 19
      refine ⟨by decide, by decide, ?_⟩
      have h_151 : Nat.sqrt (151 + 19) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_151]; decide
    · -- n = 152
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_152 : Nat.sqrt (152 + 17) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_152]; decide
    · -- n = 153
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_153 : Nat.sqrt (153 + 17) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_153]; decide
    · -- n = 154
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_154 : Nat.sqrt (154 + 17) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_154]; decide
    · -- n = 155
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_155 : Nat.sqrt (155 + 17) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_155]; decide
    · -- n = 156
      use 13
      refine ⟨by decide, by decide, ?_⟩
      have h_156 : Nat.sqrt (156 + 13) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_156]; decide
    · -- n = 157
      use 13
      refine ⟨by decide, by decide, ?_⟩
      have h_157 : Nat.sqrt (157 + 13) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_157]; decide
    · -- n = 158
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_158 : Nat.sqrt (158 + 11) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_158]; decide
    · -- n = 159
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_159 : Nat.sqrt (159 + 11) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_159]; decide
    · -- n = 160
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_160 : Nat.sqrt (160 + 11) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_160]; decide
    · -- n = 161
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_161 : Nat.sqrt (161 + 11) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_161]; decide
    · -- n = 162
      use 7
      refine ⟨by decide, by decide, ?_⟩
      have h_162 : Nat.sqrt (162 + 7) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_162]; decide
    · -- n = 163
      use 7
      refine ⟨by decide, by decide, ?_⟩
      have h_163 : Nat.sqrt (163 + 7) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_163]; decide
    · -- n = 164
      use 5
      refine ⟨by decide, by decide, ?_⟩
      have h_164 : Nat.sqrt (164 + 5) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_164]; decide
    · -- n = 165
      use 5
      refine ⟨by decide, by decide, ?_⟩
      have h_165 : Nat.sqrt (165 + 5) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_165]; decide
    · -- n = 166
      use 3
      refine ⟨by decide, by decide, ?_⟩
      have h_166 : Nat.sqrt (166 + 3) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_166]; decide
    · -- n = 167
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_167 : Nat.sqrt (167 + 2) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_167]; decide
    · -- n = 168
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_168 : Nat.sqrt (168 + 2) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_168]; decide
    · -- n = 169
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_169 : Nat.sqrt (169 + 2) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_169]; decide
    · -- n = 170
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_170 : Nat.sqrt (170 + 2) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_170]; decide
    · -- n = 171
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_171 : Nat.sqrt (171 + 2) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_171]; decide
    · -- n = 172
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_172 : Nat.sqrt (172 + 2) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_172]; decide
    · -- n = 173
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_173 : Nat.sqrt (173 + 2) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_173]; decide
    · -- n = 174
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_174 : Nat.sqrt (174 + 2) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_174]; decide
    · -- n = 175
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_175 : Nat.sqrt (175 + 2) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_175]; decide
    · -- n = 176
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_176 : Nat.sqrt (176 + 2) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_176]; decide
    · -- n = 177
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_177 : Nat.sqrt (177 + 2) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_177]; decide
    · -- n = 178
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_178 : Nat.sqrt (178 + 2) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_178]; decide
    · -- n = 179
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_179 : Nat.sqrt (179 + 2) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_179]; decide
    · -- n = 180
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_180 : Nat.sqrt (180 + 2) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_180]; decide
    · -- n = 181
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_181 : Nat.sqrt (181 + 2) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_181]; decide
    · -- n = 182
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_182 : Nat.sqrt (182 + 2) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_182]; decide
    · -- n = 183
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_183 : Nat.sqrt (183 + 2) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_183]; decide
    · -- n = 184
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_184 : Nat.sqrt (184 + 2) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_184]; decide
    · -- n = 185
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_185 : Nat.sqrt (185 + 2) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_185]; decide
    · -- n = 186
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_186 : Nat.sqrt (186 + 2) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_186]; decide
    · -- n = 187
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_187 : Nat.sqrt (187 + 2) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_187]; decide
    · -- n = 188
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_188 : Nat.sqrt (188 + 2) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_188]; decide
    · -- n = 189
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_189 : Nat.sqrt (189 + 2) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_189]; decide
    · -- n = 190
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_190 : Nat.sqrt (190 + 2) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_190]; decide
    · -- n = 191
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_191 : Nat.sqrt (191 + 2) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_191]; decide
    · -- n = 192
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_192 : Nat.sqrt (192 + 2) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_192]; decide
    · -- n = 193
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_193 : Nat.sqrt (193 + 2) = 13 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_193]; decide
    · -- n = 194
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_194 : Nat.sqrt (194 + 97) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_194]; decide
    · -- n = 195
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_195 : Nat.sqrt (195 + 97) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_195]; decide
    · -- n = 196
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_196 : Nat.sqrt (196 + 97) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_196]; decide
    · -- n = 197
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_197 : Nat.sqrt (197 + 97) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_197]; decide
    · -- n = 198
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_198 : Nat.sqrt (198 + 97) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_198]; decide
    · -- n = 199
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_199 : Nat.sqrt (199 + 97) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_199]; decide
    · -- n = 200
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_200 : Nat.sqrt (200 + 89) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_200]; decide
    · -- n = 201
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_201 : Nat.sqrt (201 + 89) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_201]; decide
    · -- n = 202
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_202 : Nat.sqrt (202 + 89) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_202]; decide
    · -- n = 203
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_203 : Nat.sqrt (203 + 89) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_203]; decide
    · -- n = 204
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_204 : Nat.sqrt (204 + 89) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_204]; decide
    · -- n = 205
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_205 : Nat.sqrt (205 + 89) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_205]; decide
    · -- n = 206
      use 83
      refine ⟨by decide, by decide, ?_⟩
      have h_206 : Nat.sqrt (206 + 83) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_206]; decide
    · -- n = 207
      use 83
      refine ⟨by decide, by decide, ?_⟩
      have h_207 : Nat.sqrt (207 + 83) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_207]; decide
    · -- n = 208
      use 83
      refine ⟨by decide, by decide, ?_⟩
      have h_208 : Nat.sqrt (208 + 83) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_208]; decide
    · -- n = 209
      use 83
      refine ⟨by decide, by decide, ?_⟩
      have h_209 : Nat.sqrt (209 + 83) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_209]; decide
    · -- n = 210
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_210 : Nat.sqrt (210 + 79) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_210]; decide
    · -- n = 211
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_211 : Nat.sqrt (211 + 79) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_211]; decide
    · -- n = 212
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_212 : Nat.sqrt (212 + 79) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_212]; decide
    · -- n = 213
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_213 : Nat.sqrt (213 + 79) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_213]; decide
    · -- n = 214
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_214 : Nat.sqrt (214 + 79) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_214]; decide
    · -- n = 215
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_215 : Nat.sqrt (215 + 79) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_215]; decide
    · -- n = 216
      use 73
      refine ⟨by decide, by decide, ?_⟩
      have h_216 : Nat.sqrt (216 + 73) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_216]; decide
    · -- n = 217
      use 73
      refine ⟨by decide, by decide, ?_⟩
      have h_217 : Nat.sqrt (217 + 73) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_217]; decide
    · -- n = 218
      use 71
      refine ⟨by decide, by decide, ?_⟩
      have h_218 : Nat.sqrt (218 + 71) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_218]; decide
    · -- n = 219
      use 71
      refine ⟨by decide, by decide, ?_⟩
      have h_219 : Nat.sqrt (219 + 71) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_219]; decide
    · -- n = 220
      use 71
      refine ⟨by decide, by decide, ?_⟩
      have h_220 : Nat.sqrt (220 + 71) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_220]; decide
    · -- n = 221
      use 71
      refine ⟨by decide, by decide, ?_⟩
      have h_221 : Nat.sqrt (221 + 71) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_221]; decide
    · -- n = 222
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_222 : Nat.sqrt (222 + 67) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_222]; decide
    · -- n = 223
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_223 : Nat.sqrt (223 + 67) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_223]; decide
    · -- n = 224
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_224 : Nat.sqrt (224 + 67) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_224]; decide
    · -- n = 225
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_225 : Nat.sqrt (225 + 67) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_225]; decide
    · -- n = 226
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_226 : Nat.sqrt (226 + 67) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_226]; decide
    · -- n = 227
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_227 : Nat.sqrt (227 + 67) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_227]; decide
    · -- n = 228
      use 61
      refine ⟨by decide, by decide, ?_⟩
      have h_228 : Nat.sqrt (228 + 61) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_228]; decide
    · -- n = 229
      use 61
      refine ⟨by decide, by decide, ?_⟩
      have h_229 : Nat.sqrt (229 + 61) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_229]; decide
    · -- n = 230
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_230 : Nat.sqrt (230 + 59) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_230]; decide
    · -- n = 231
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_231 : Nat.sqrt (231 + 59) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_231]; decide
    · -- n = 232
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_232 : Nat.sqrt (232 + 59) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_232]; decide
    · -- n = 233
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_233 : Nat.sqrt (233 + 59) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_233]; decide
    · -- n = 234
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_234 : Nat.sqrt (234 + 59) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_234]; decide
    · -- n = 235
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_235 : Nat.sqrt (235 + 59) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_235]; decide
    · -- n = 236
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_236 : Nat.sqrt (236 + 53) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_236]; decide
    · -- n = 237
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_237 : Nat.sqrt (237 + 53) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_237]; decide
    · -- n = 238
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_238 : Nat.sqrt (238 + 53) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_238]; decide
    · -- n = 239
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_239 : Nat.sqrt (239 + 53) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_239]; decide
    · -- n = 240
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_240 : Nat.sqrt (240 + 53) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_240]; decide
    · -- n = 241
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_241 : Nat.sqrt (241 + 53) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_241]; decide
    · -- n = 242
      use 47
      refine ⟨by decide, by decide, ?_⟩
      have h_242 : Nat.sqrt (242 + 47) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_242]; decide
    · -- n = 243
      use 47
      refine ⟨by decide, by decide, ?_⟩
      have h_243 : Nat.sqrt (243 + 47) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_243]; decide
    · -- n = 244
      use 47
      refine ⟨by decide, by decide, ?_⟩
      have h_244 : Nat.sqrt (244 + 47) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_244]; decide
    · -- n = 245
      use 47
      refine ⟨by decide, by decide, ?_⟩
      have h_245 : Nat.sqrt (245 + 47) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_245]; decide
    · -- n = 246
      use 43
      refine ⟨by decide, by decide, ?_⟩
      have h_246 : Nat.sqrt (246 + 43) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_246]; decide
    · -- n = 247
      use 43
      refine ⟨by decide, by decide, ?_⟩
      have h_247 : Nat.sqrt (247 + 43) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_247]; decide
    · -- n = 248
      use 41
      refine ⟨by decide, by decide, ?_⟩
      have h_248 : Nat.sqrt (248 + 41) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_248]; decide
    · -- n = 249
      use 41
      refine ⟨by decide, by decide, ?_⟩
      have h_249 : Nat.sqrt (249 + 41) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_249]; decide
    · -- n = 250
      use 41
      refine ⟨by decide, by decide, ?_⟩
      have h_250 : Nat.sqrt (250 + 41) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_250]; decide
    · -- n = 251
      use 41
      refine ⟨by decide, by decide, ?_⟩
      have h_251 : Nat.sqrt (251 + 41) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_251]; decide
    · -- n = 252
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_252 : Nat.sqrt (252 + 37) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_252]; decide
    · -- n = 253
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_253 : Nat.sqrt (253 + 37) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_253]; decide
    · -- n = 254
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_254 : Nat.sqrt (254 + 37) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_254]; decide
    · -- n = 255
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_255 : Nat.sqrt (255 + 37) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_255]; decide
    · -- n = 256
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_256 : Nat.sqrt (256 + 37) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_256]; decide
    · -- n = 257
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_257 : Nat.sqrt (257 + 37) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_257]; decide
    · -- n = 258
      use 31
      refine ⟨by decide, by decide, ?_⟩
      have h_258 : Nat.sqrt (258 + 31) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_258]; decide
    · -- n = 259
      use 31
      refine ⟨by decide, by decide, ?_⟩
      have h_259 : Nat.sqrt (259 + 31) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_259]; decide
    · -- n = 260
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_260 : Nat.sqrt (260 + 29) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_260]; decide
    · -- n = 261
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_261 : Nat.sqrt (261 + 29) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_261]; decide
    · -- n = 262
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_262 : Nat.sqrt (262 + 29) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_262]; decide
    · -- n = 263
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_263 : Nat.sqrt (263 + 29) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_263]; decide
    · -- n = 264
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_264 : Nat.sqrt (264 + 29) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_264]; decide
    · -- n = 265
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_265 : Nat.sqrt (265 + 29) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_265]; decide
    · -- n = 266
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_266 : Nat.sqrt (266 + 23) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_266]; decide
    · -- n = 267
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_267 : Nat.sqrt (267 + 23) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_267]; decide
    · -- n = 268
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_268 : Nat.sqrt (268 + 23) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_268]; decide
    · -- n = 269
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_269 : Nat.sqrt (269 + 23) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_269]; decide
    · -- n = 270
      use 19
      refine ⟨by decide, by decide, ?_⟩
      have h_270 : Nat.sqrt (270 + 19) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_270]; decide
    · -- n = 271
      use 19
      refine ⟨by decide, by decide, ?_⟩
      have h_271 : Nat.sqrt (271 + 19) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_271]; decide
    · -- n = 272
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_272 : Nat.sqrt (272 + 17) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_272]; decide
    · -- n = 273
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_273 : Nat.sqrt (273 + 17) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_273]; decide
    · -- n = 274
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_274 : Nat.sqrt (274 + 17) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_274]; decide
    · -- n = 275
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_275 : Nat.sqrt (275 + 17) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_275]; decide
    · -- n = 276
      use 13
      refine ⟨by decide, by decide, ?_⟩
      have h_276 : Nat.sqrt (276 + 13) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_276]; decide
    · -- n = 277
      use 13
      refine ⟨by decide, by decide, ?_⟩
      have h_277 : Nat.sqrt (277 + 13) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_277]; decide
    · -- n = 278
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_278 : Nat.sqrt (278 + 11) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_278]; decide
    · -- n = 279
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_279 : Nat.sqrt (279 + 11) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_279]; decide
    · -- n = 280
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_280 : Nat.sqrt (280 + 11) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_280]; decide
    · -- n = 281
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_281 : Nat.sqrt (281 + 11) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_281]; decide
    · -- n = 282
      use 7
      refine ⟨by decide, by decide, ?_⟩
      have h_282 : Nat.sqrt (282 + 7) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_282]; decide
    · -- n = 283
      use 7
      refine ⟨by decide, by decide, ?_⟩
      have h_283 : Nat.sqrt (283 + 7) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_283]; decide
    · -- n = 284
      use 5
      refine ⟨by decide, by decide, ?_⟩
      have h_284 : Nat.sqrt (284 + 5) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_284]; decide
    · -- n = 285
      use 5
      refine ⟨by decide, by decide, ?_⟩
      have h_285 : Nat.sqrt (285 + 5) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_285]; decide
    · -- n = 286
      use 3
      refine ⟨by decide, by decide, ?_⟩
      have h_286 : Nat.sqrt (286 + 3) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_286]; decide
    · -- n = 287
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_287 : Nat.sqrt (287 + 2) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_287]; decide
    · -- n = 288
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_288 : Nat.sqrt (288 + 2) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_288]; decide
    · -- n = 289
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_289 : Nat.sqrt (289 + 2) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_289]; decide
    · -- n = 290
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_290 : Nat.sqrt (290 + 2) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_290]; decide
    · -- n = 291
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_291 : Nat.sqrt (291 + 2) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_291]; decide
    · -- n = 292
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_292 : Nat.sqrt (292 + 2) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_292]; decide
    · -- n = 293
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_293 : Nat.sqrt (293 + 2) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_293]; decide
    · -- n = 294
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_294 : Nat.sqrt (294 + 2) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_294]; decide
    · -- n = 295
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_295 : Nat.sqrt (295 + 2) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_295]; decide
    · -- n = 296
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_296 : Nat.sqrt (296 + 2) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_296]; decide
    · -- n = 297
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_297 : Nat.sqrt (297 + 2) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_297]; decide
    · -- n = 298
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_298 : Nat.sqrt (298 + 2) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_298]; decide
    · -- n = 299
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_299 : Nat.sqrt (299 + 2) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_299]; decide
    · -- n = 300
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_300 : Nat.sqrt (300 + 2) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_300]; decide
    · -- n = 301
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_301 : Nat.sqrt (301 + 2) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_301]; decide
    · -- n = 302
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_302 : Nat.sqrt (302 + 2) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_302]; decide
    · -- n = 303
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_303 : Nat.sqrt (303 + 2) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_303]; decide
    · -- n = 304
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_304 : Nat.sqrt (304 + 2) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_304]; decide
    · -- n = 305
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_305 : Nat.sqrt (305 + 2) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_305]; decide
    · -- n = 306
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_306 : Nat.sqrt (306 + 2) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_306]; decide
    · -- n = 307
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_307 : Nat.sqrt (307 + 2) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_307]; decide
    · -- n = 308
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_308 : Nat.sqrt (308 + 2) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_308]; decide
    · -- n = 309
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_309 : Nat.sqrt (309 + 2) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_309]; decide
    · -- n = 310
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_310 : Nat.sqrt (310 + 2) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_310]; decide
    · -- n = 311
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_311 : Nat.sqrt (311 + 2) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_311]; decide
    · -- n = 312
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_312 : Nat.sqrt (312 + 2) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_312]; decide
    · -- n = 313
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_313 : Nat.sqrt (313 + 2) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_313]; decide
    · -- n = 314
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_314 : Nat.sqrt (314 + 2) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_314]; decide
    · -- n = 315
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_315 : Nat.sqrt (315 + 2) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_315]; decide
    · -- n = 316
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_316 : Nat.sqrt (316 + 2) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_316]; decide
    · -- n = 317
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_317 : Nat.sqrt (317 + 2) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_317]; decide
    · -- n = 318
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_318 : Nat.sqrt (318 + 2) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_318]; decide
    · -- n = 319
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_319 : Nat.sqrt (319 + 2) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_319]; decide
    · -- n = 320
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_320 : Nat.sqrt (320 + 2) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_320]; decide
    · -- n = 321
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_321 : Nat.sqrt (321 + 2) = 17 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_321]; decide
    · -- n = 322
      use 41
      refine ⟨by decide, by decide, ?_⟩
      have h_322 : Nat.sqrt (322 + 41) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_322]; decide
    · -- n = 323
      use 41
      refine ⟨by decide, by decide, ?_⟩
      have h_323 : Nat.sqrt (323 + 41) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_323]; decide
    · -- n = 324
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_324 : Nat.sqrt (324 + 37) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_324]; decide
    · -- n = 325
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_325 : Nat.sqrt (325 + 37) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_325]; decide
    · -- n = 326
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_326 : Nat.sqrt (326 + 37) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_326]; decide
    · -- n = 327
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_327 : Nat.sqrt (327 + 37) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_327]; decide
    · -- n = 328
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_328 : Nat.sqrt (328 + 37) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_328]; decide
    · -- n = 329
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_329 : Nat.sqrt (329 + 37) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_329]; decide
    · -- n = 330
      use 31
      refine ⟨by decide, by decide, ?_⟩
      have h_330 : Nat.sqrt (330 + 31) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_330]; decide
    · -- n = 331
      use 31
      refine ⟨by decide, by decide, ?_⟩
      have h_331 : Nat.sqrt (331 + 31) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_331]; decide
    · -- n = 332
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_332 : Nat.sqrt (332 + 29) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_332]; decide
    · -- n = 333
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_333 : Nat.sqrt (333 + 29) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_333]; decide
    · -- n = 334
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_334 : Nat.sqrt (334 + 29) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_334]; decide
    · -- n = 335
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_335 : Nat.sqrt (335 + 29) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_335]; decide
    · -- n = 336
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_336 : Nat.sqrt (336 + 29) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_336]; decide
    · -- n = 337
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_337 : Nat.sqrt (337 + 29) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_337]; decide
    · -- n = 338
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_338 : Nat.sqrt (338 + 23) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_338]; decide
    · -- n = 339
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_339 : Nat.sqrt (339 + 23) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_339]; decide
    · -- n = 340
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_340 : Nat.sqrt (340 + 23) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_340]; decide
    · -- n = 341
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_341 : Nat.sqrt (341 + 23) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_341]; decide
    · -- n = 342
      use 19
      refine ⟨by decide, by decide, ?_⟩
      have h_342 : Nat.sqrt (342 + 19) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_342]; decide
    · -- n = 343
      use 19
      refine ⟨by decide, by decide, ?_⟩
      have h_343 : Nat.sqrt (343 + 19) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_343]; decide
    · -- n = 344
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_344 : Nat.sqrt (344 + 17) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_344]; decide
    · -- n = 345
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_345 : Nat.sqrt (345 + 17) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_345]; decide
    · -- n = 346
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_346 : Nat.sqrt (346 + 17) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_346]; decide
    · -- n = 347
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_347 : Nat.sqrt (347 + 17) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_347]; decide
    · -- n = 348
      use 13
      refine ⟨by decide, by decide, ?_⟩
      have h_348 : Nat.sqrt (348 + 13) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_348]; decide
    · -- n = 349
      use 13
      refine ⟨by decide, by decide, ?_⟩
      have h_349 : Nat.sqrt (349 + 13) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_349]; decide
    · -- n = 350
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_350 : Nat.sqrt (350 + 11) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_350]; decide
    · -- n = 351
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_351 : Nat.sqrt (351 + 11) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_351]; decide
    · -- n = 352
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_352 : Nat.sqrt (352 + 11) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_352]; decide
    · -- n = 353
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_353 : Nat.sqrt (353 + 11) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_353]; decide
    · -- n = 354
      use 7
      refine ⟨by decide, by decide, ?_⟩
      have h_354 : Nat.sqrt (354 + 7) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_354]; decide
    · -- n = 355
      use 7
      refine ⟨by decide, by decide, ?_⟩
      have h_355 : Nat.sqrt (355 + 7) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_355]; decide
    · -- n = 356
      use 5
      refine ⟨by decide, by decide, ?_⟩
      have h_356 : Nat.sqrt (356 + 5) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_356]; decide
    · -- n = 357
      use 5
      refine ⟨by decide, by decide, ?_⟩
      have h_357 : Nat.sqrt (357 + 5) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_357]; decide
    · -- n = 358
      use 3
      refine ⟨by decide, by decide, ?_⟩
      have h_358 : Nat.sqrt (358 + 3) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_358]; decide
    · -- n = 359
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_359 : Nat.sqrt (359 + 2) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_359]; decide
    · -- n = 360
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_360 : Nat.sqrt (360 + 2) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_360]; decide
    · -- n = 361
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_361 : Nat.sqrt (361 + 2) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_361]; decide
    · -- n = 362
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_362 : Nat.sqrt (362 + 2) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_362]; decide
    · -- n = 363
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_363 : Nat.sqrt (363 + 2) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_363]; decide
    · -- n = 364
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_364 : Nat.sqrt (364 + 2) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_364]; decide
    · -- n = 365
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_365 : Nat.sqrt (365 + 2) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_365]; decide
    · -- n = 366
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_366 : Nat.sqrt (366 + 2) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_366]; decide
    · -- n = 367
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_367 : Nat.sqrt (367 + 2) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_367]; decide
    · -- n = 368
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_368 : Nat.sqrt (368 + 2) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_368]; decide
    · -- n = 369
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_369 : Nat.sqrt (369 + 2) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_369]; decide
    · -- n = 370
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_370 : Nat.sqrt (370 + 2) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_370]; decide
    · -- n = 371
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_371 : Nat.sqrt (371 + 2) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_371]; decide
    · -- n = 372
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_372 : Nat.sqrt (372 + 2) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_372]; decide
    · -- n = 373
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_373 : Nat.sqrt (373 + 2) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_373]; decide
    · -- n = 374
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_374 : Nat.sqrt (374 + 2) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_374]; decide
    · -- n = 375
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_375 : Nat.sqrt (375 + 2) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_375]; decide
    · -- n = 376
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_376 : Nat.sqrt (376 + 2) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_376]; decide
    · -- n = 377
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_377 : Nat.sqrt (377 + 2) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_377]; decide
    · -- n = 378
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_378 : Nat.sqrt (378 + 2) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_378]; decide
    · -- n = 379
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_379 : Nat.sqrt (379 + 2) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_379]; decide
    · -- n = 380
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_380 : Nat.sqrt (380 + 2) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_380]; decide
    · -- n = 381
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_381 : Nat.sqrt (381 + 2) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_381]; decide
    · -- n = 382
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_382 : Nat.sqrt (382 + 2) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_382]; decide
    · -- n = 383
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_383 : Nat.sqrt (383 + 2) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_383]; decide
    · -- n = 384
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_384 : Nat.sqrt (384 + 2) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_384]; decide
    · -- n = 385
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_385 : Nat.sqrt (385 + 2) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_385]; decide
    · -- n = 386
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_386 : Nat.sqrt (386 + 2) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_386]; decide
    · -- n = 387
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_387 : Nat.sqrt (387 + 2) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_387]; decide
    · -- n = 388
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_388 : Nat.sqrt (388 + 2) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_388]; decide
    · -- n = 389
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_389 : Nat.sqrt (389 + 2) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_389]; decide
    · -- n = 390
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_390 : Nat.sqrt (390 + 2) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_390]; decide
    · -- n = 391
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_391 : Nat.sqrt (391 + 2) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_391]; decide
    · -- n = 392
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_392 : Nat.sqrt (392 + 2) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_392]; decide
    · -- n = 393
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_393 : Nat.sqrt (393 + 2) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_393]; decide
    · -- n = 394
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_394 : Nat.sqrt (394 + 2) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_394]; decide
    · -- n = 395
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_395 : Nat.sqrt (395 + 2) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_395]; decide
    · -- n = 396
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_396 : Nat.sqrt (396 + 2) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_396]; decide
    · -- n = 397
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_397 : Nat.sqrt (397 + 2) = 19 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_397]; decide
    · -- n = 398
      use 131
      refine ⟨by decide, by decide, ?_⟩
      have h_398 : Nat.sqrt (398 + 131) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_398]; decide
    · -- n = 399
      use 131
      refine ⟨by decide, by decide, ?_⟩
      have h_399 : Nat.sqrt (399 + 131) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_399]; decide
    · -- n = 400
      use 131
      refine ⟨by decide, by decide, ?_⟩
      have h_400 : Nat.sqrt (400 + 131) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_400]; decide
    · -- n = 401
      use 131
      refine ⟨by decide, by decide, ?_⟩
      have h_401 : Nat.sqrt (401 + 131) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_401]; decide
    · -- n = 402
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_402 : Nat.sqrt (402 + 127) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_402]; decide
    · -- n = 403
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_403 : Nat.sqrt (403 + 127) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_403]; decide
    · -- n = 404
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_404 : Nat.sqrt (404 + 127) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_404]; decide
    · -- n = 405
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_405 : Nat.sqrt (405 + 127) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_405]; decide
    · -- n = 406
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_406 : Nat.sqrt (406 + 127) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_406]; decide
    · -- n = 407
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_407 : Nat.sqrt (407 + 127) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_407]; decide
    · -- n = 408
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_408 : Nat.sqrt (408 + 127) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_408]; decide
    · -- n = 409
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_409 : Nat.sqrt (409 + 127) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_409]; decide
    · -- n = 410
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_410 : Nat.sqrt (410 + 127) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_410]; decide
    · -- n = 411
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_411 : Nat.sqrt (411 + 127) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_411]; decide
    · -- n = 412
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_412 : Nat.sqrt (412 + 127) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_412]; decide
    · -- n = 413
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_413 : Nat.sqrt (413 + 127) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_413]; decide
    · -- n = 414
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_414 : Nat.sqrt (414 + 127) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_414]; decide
    · -- n = 415
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_415 : Nat.sqrt (415 + 127) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_415]; decide
    · -- n = 416
      use 113
      refine ⟨by decide, by decide, ?_⟩
      have h_416 : Nat.sqrt (416 + 113) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_416]; decide
    · -- n = 417
      use 113
      refine ⟨by decide, by decide, ?_⟩
      have h_417 : Nat.sqrt (417 + 113) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_417]; decide
    · -- n = 418
      use 113
      refine ⟨by decide, by decide, ?_⟩
      have h_418 : Nat.sqrt (418 + 113) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_418]; decide
    · -- n = 419
      use 113
      refine ⟨by decide, by decide, ?_⟩
      have h_419 : Nat.sqrt (419 + 113) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_419]; decide
    · -- n = 420
      use 109
      refine ⟨by decide, by decide, ?_⟩
      have h_420 : Nat.sqrt (420 + 109) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_420]; decide
    · -- n = 421
      use 109
      refine ⟨by decide, by decide, ?_⟩
      have h_421 : Nat.sqrt (421 + 109) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_421]; decide
    · -- n = 422
      use 107
      refine ⟨by decide, by decide, ?_⟩
      have h_422 : Nat.sqrt (422 + 107) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_422]; decide
    · -- n = 423
      use 107
      refine ⟨by decide, by decide, ?_⟩
      have h_423 : Nat.sqrt (423 + 107) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_423]; decide
    · -- n = 424
      use 107
      refine ⟨by decide, by decide, ?_⟩
      have h_424 : Nat.sqrt (424 + 107) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_424]; decide
    · -- n = 425
      use 107
      refine ⟨by decide, by decide, ?_⟩
      have h_425 : Nat.sqrt (425 + 107) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_425]; decide
    · -- n = 426
      use 103
      refine ⟨by decide, by decide, ?_⟩
      have h_426 : Nat.sqrt (426 + 103) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_426]; decide
    · -- n = 427
      use 103
      refine ⟨by decide, by decide, ?_⟩
      have h_427 : Nat.sqrt (427 + 103) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_427]; decide
    · -- n = 428
      use 101
      refine ⟨by decide, by decide, ?_⟩
      have h_428 : Nat.sqrt (428 + 101) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_428]; decide
    · -- n = 429
      use 101
      refine ⟨by decide, by decide, ?_⟩
      have h_429 : Nat.sqrt (429 + 101) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_429]; decide
    · -- n = 430
      use 101
      refine ⟨by decide, by decide, ?_⟩
      have h_430 : Nat.sqrt (430 + 101) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_430]; decide
    · -- n = 431
      use 101
      refine ⟨by decide, by decide, ?_⟩
      have h_431 : Nat.sqrt (431 + 101) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_431]; decide
    · -- n = 432
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_432 : Nat.sqrt (432 + 97) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_432]; decide
    · -- n = 433
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_433 : Nat.sqrt (433 + 97) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_433]; decide
    · -- n = 434
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_434 : Nat.sqrt (434 + 97) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_434]; decide
    · -- n = 435
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_435 : Nat.sqrt (435 + 97) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_435]; decide
    · -- n = 436
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_436 : Nat.sqrt (436 + 97) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_436]; decide
    · -- n = 437
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_437 : Nat.sqrt (437 + 97) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_437]; decide
    · -- n = 438
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_438 : Nat.sqrt (438 + 97) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_438]; decide
    · -- n = 439
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_439 : Nat.sqrt (439 + 97) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_439]; decide
    · -- n = 440
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_440 : Nat.sqrt (440 + 89) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_440]; decide
    · -- n = 441
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_441 : Nat.sqrt (441 + 89) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_441]; decide
    · -- n = 442
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_442 : Nat.sqrt (442 + 89) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_442]; decide
    · -- n = 443
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_443 : Nat.sqrt (443 + 89) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_443]; decide
    · -- n = 444
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_444 : Nat.sqrt (444 + 89) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_444]; decide
    · -- n = 445
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_445 : Nat.sqrt (445 + 89) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_445]; decide
    · -- n = 446
      use 83
      refine ⟨by decide, by decide, ?_⟩
      have h_446 : Nat.sqrt (446 + 83) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_446]; decide
    · -- n = 447
      use 83
      refine ⟨by decide, by decide, ?_⟩
      have h_447 : Nat.sqrt (447 + 83) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_447]; decide
    · -- n = 448
      use 83
      refine ⟨by decide, by decide, ?_⟩
      have h_448 : Nat.sqrt (448 + 83) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_448]; decide
    · -- n = 449
      use 83
      refine ⟨by decide, by decide, ?_⟩
      have h_449 : Nat.sqrt (449 + 83) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_449]; decide
    · -- n = 450
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_450 : Nat.sqrt (450 + 79) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_450]; decide
    · -- n = 451
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_451 : Nat.sqrt (451 + 79) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_451]; decide
    · -- n = 452
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_452 : Nat.sqrt (452 + 79) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_452]; decide
    · -- n = 453
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_453 : Nat.sqrt (453 + 79) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_453]; decide
    · -- n = 454
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_454 : Nat.sqrt (454 + 79) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_454]; decide
    · -- n = 455
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_455 : Nat.sqrt (455 + 79) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_455]; decide
    · -- n = 456
      use 73
      refine ⟨by decide, by decide, ?_⟩
      have h_456 : Nat.sqrt (456 + 73) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_456]; decide
    · -- n = 457
      use 73
      refine ⟨by decide, by decide, ?_⟩
      have h_457 : Nat.sqrt (457 + 73) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_457]; decide
    · -- n = 458
      use 71
      refine ⟨by decide, by decide, ?_⟩
      have h_458 : Nat.sqrt (458 + 71) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_458]; decide
    · -- n = 459
      use 71
      refine ⟨by decide, by decide, ?_⟩
      have h_459 : Nat.sqrt (459 + 71) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_459]; decide
    · -- n = 460
      use 71
      refine ⟨by decide, by decide, ?_⟩
      have h_460 : Nat.sqrt (460 + 71) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_460]; decide
    · -- n = 461
      use 71
      refine ⟨by decide, by decide, ?_⟩
      have h_461 : Nat.sqrt (461 + 71) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_461]; decide
    · -- n = 462
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_462 : Nat.sqrt (462 + 67) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_462]; decide
    · -- n = 463
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_463 : Nat.sqrt (463 + 67) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_463]; decide
    · -- n = 464
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_464 : Nat.sqrt (464 + 67) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_464]; decide
    · -- n = 465
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_465 : Nat.sqrt (465 + 67) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_465]; decide
    · -- n = 466
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_466 : Nat.sqrt (466 + 67) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_466]; decide
    · -- n = 467
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_467 : Nat.sqrt (467 + 67) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_467]; decide
    · -- n = 468
      use 61
      refine ⟨by decide, by decide, ?_⟩
      have h_468 : Nat.sqrt (468 + 61) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_468]; decide
    · -- n = 469
      use 61
      refine ⟨by decide, by decide, ?_⟩
      have h_469 : Nat.sqrt (469 + 61) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_469]; decide
    · -- n = 470
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_470 : Nat.sqrt (470 + 59) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_470]; decide
    · -- n = 471
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_471 : Nat.sqrt (471 + 59) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_471]; decide
    · -- n = 472
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_472 : Nat.sqrt (472 + 59) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_472]; decide
    · -- n = 473
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_473 : Nat.sqrt (473 + 59) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_473]; decide
    · -- n = 474
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_474 : Nat.sqrt (474 + 59) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_474]; decide
    · -- n = 475
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_475 : Nat.sqrt (475 + 59) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_475]; decide
    · -- n = 476
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_476 : Nat.sqrt (476 + 53) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_476]; decide
    · -- n = 477
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_477 : Nat.sqrt (477 + 53) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_477]; decide
    · -- n = 478
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_478 : Nat.sqrt (478 + 53) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_478]; decide
    · -- n = 479
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_479 : Nat.sqrt (479 + 53) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_479]; decide
    · -- n = 480
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_480 : Nat.sqrt (480 + 53) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_480]; decide
    · -- n = 481
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_481 : Nat.sqrt (481 + 53) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_481]; decide
    · -- n = 482
      use 47
      refine ⟨by decide, by decide, ?_⟩
      have h_482 : Nat.sqrt (482 + 47) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_482]; decide
    · -- n = 483
      use 47
      refine ⟨by decide, by decide, ?_⟩
      have h_483 : Nat.sqrt (483 + 47) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_483]; decide
    · -- n = 484
      use 47
      refine ⟨by decide, by decide, ?_⟩
      have h_484 : Nat.sqrt (484 + 47) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_484]; decide
    · -- n = 485
      use 47
      refine ⟨by decide, by decide, ?_⟩
      have h_485 : Nat.sqrt (485 + 47) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_485]; decide
    · -- n = 486
      use 43
      refine ⟨by decide, by decide, ?_⟩
      have h_486 : Nat.sqrt (486 + 43) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_486]; decide
    · -- n = 487
      use 43
      refine ⟨by decide, by decide, ?_⟩
      have h_487 : Nat.sqrt (487 + 43) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_487]; decide
    · -- n = 488
      use 41
      refine ⟨by decide, by decide, ?_⟩
      have h_488 : Nat.sqrt (488 + 41) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_488]; decide
    · -- n = 489
      use 41
      refine ⟨by decide, by decide, ?_⟩
      have h_489 : Nat.sqrt (489 + 41) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_489]; decide
    · -- n = 490
      use 41
      refine ⟨by decide, by decide, ?_⟩
      have h_490 : Nat.sqrt (490 + 41) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_490]; decide
    · -- n = 491
      use 41
      refine ⟨by decide, by decide, ?_⟩
      have h_491 : Nat.sqrt (491 + 41) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_491]; decide
    · -- n = 492
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_492 : Nat.sqrt (492 + 37) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_492]; decide
    · -- n = 493
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_493 : Nat.sqrt (493 + 37) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_493]; decide
    · -- n = 494
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_494 : Nat.sqrt (494 + 37) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_494]; decide
    · -- n = 495
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_495 : Nat.sqrt (495 + 37) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_495]; decide
    · -- n = 496
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_496 : Nat.sqrt (496 + 37) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_496]; decide
    · -- n = 497
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_497 : Nat.sqrt (497 + 37) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_497]; decide
    · -- n = 498
      use 31
      refine ⟨by decide, by decide, ?_⟩
      have h_498 : Nat.sqrt (498 + 31) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_498]; decide
    · -- n = 499
      use 31
      refine ⟨by decide, by decide, ?_⟩
      have h_499 : Nat.sqrt (499 + 31) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_499]; decide
    · -- n = 500
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_500 : Nat.sqrt (500 + 29) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_500]; decide
    · -- n = 501
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_501 : Nat.sqrt (501 + 29) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_501]; decide
    · -- n = 502
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_502 : Nat.sqrt (502 + 29) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_502]; decide
    · -- n = 503
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_503 : Nat.sqrt (503 + 29) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_503]; decide
    · -- n = 504
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_504 : Nat.sqrt (504 + 29) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_504]; decide
    · -- n = 505
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_505 : Nat.sqrt (505 + 29) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_505]; decide
    · -- n = 506
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_506 : Nat.sqrt (506 + 23) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_506]; decide
    · -- n = 507
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_507 : Nat.sqrt (507 + 23) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_507]; decide
    · -- n = 508
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_508 : Nat.sqrt (508 + 23) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_508]; decide
    · -- n = 509
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_509 : Nat.sqrt (509 + 23) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_509]; decide
    · -- n = 510
      use 19
      refine ⟨by decide, by decide, ?_⟩
      have h_510 : Nat.sqrt (510 + 19) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_510]; decide
    · -- n = 511
      use 19
      refine ⟨by decide, by decide, ?_⟩
      have h_511 : Nat.sqrt (511 + 19) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_511]; decide
    · -- n = 512
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_512 : Nat.sqrt (512 + 17) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_512]; decide
    · -- n = 513
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_513 : Nat.sqrt (513 + 17) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_513]; decide
    · -- n = 514
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_514 : Nat.sqrt (514 + 17) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_514]; decide
    · -- n = 515
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_515 : Nat.sqrt (515 + 17) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_515]; decide
    · -- n = 516
      use 13
      refine ⟨by decide, by decide, ?_⟩
      have h_516 : Nat.sqrt (516 + 13) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_516]; decide
    · -- n = 517
      use 13
      refine ⟨by decide, by decide, ?_⟩
      have h_517 : Nat.sqrt (517 + 13) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_517]; decide
    · -- n = 518
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_518 : Nat.sqrt (518 + 11) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_518]; decide
    · -- n = 519
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_519 : Nat.sqrt (519 + 11) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_519]; decide
    · -- n = 520
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_520 : Nat.sqrt (520 + 11) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_520]; decide
    · -- n = 521
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_521 : Nat.sqrt (521 + 11) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_521]; decide
    · -- n = 522
      use 7
      refine ⟨by decide, by decide, ?_⟩
      have h_522 : Nat.sqrt (522 + 7) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_522]; decide
    · -- n = 523
      use 7
      refine ⟨by decide, by decide, ?_⟩
      have h_523 : Nat.sqrt (523 + 7) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_523]; decide
    · -- n = 524
      use 5
      refine ⟨by decide, by decide, ?_⟩
      have h_524 : Nat.sqrt (524 + 5) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_524]; decide
    · -- n = 525
      use 5
      refine ⟨by decide, by decide, ?_⟩
      have h_525 : Nat.sqrt (525 + 5) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_525]; decide
    · -- n = 526
      use 3
      refine ⟨by decide, by decide, ?_⟩
      have h_526 : Nat.sqrt (526 + 3) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_526]; decide
    · -- n = 527
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_527 : Nat.sqrt (527 + 2) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_527]; decide
    · -- n = 528
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_528 : Nat.sqrt (528 + 2) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_528]; decide
    · -- n = 529
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_529 : Nat.sqrt (529 + 2) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_529]; decide
    · -- n = 530
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_530 : Nat.sqrt (530 + 2) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_530]; decide
    · -- n = 531
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_531 : Nat.sqrt (531 + 2) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_531]; decide
    · -- n = 532
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_532 : Nat.sqrt (532 + 2) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_532]; decide
    · -- n = 533
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_533 : Nat.sqrt (533 + 2) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_533]; decide
    · -- n = 534
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_534 : Nat.sqrt (534 + 2) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_534]; decide
    · -- n = 535
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_535 : Nat.sqrt (535 + 2) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_535]; decide
    · -- n = 536
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_536 : Nat.sqrt (536 + 2) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_536]; decide
    · -- n = 537
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_537 : Nat.sqrt (537 + 2) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_537]; decide
    · -- n = 538
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_538 : Nat.sqrt (538 + 2) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_538]; decide
    · -- n = 539
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_539 : Nat.sqrt (539 + 2) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_539]; decide
    · -- n = 540
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_540 : Nat.sqrt (540 + 2) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_540]; decide
    · -- n = 541
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_541 : Nat.sqrt (541 + 2) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_541]; decide
    · -- n = 542
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_542 : Nat.sqrt (542 + 2) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_542]; decide
    · -- n = 543
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_543 : Nat.sqrt (543 + 2) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_543]; decide
    · -- n = 544
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_544 : Nat.sqrt (544 + 2) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_544]; decide
    · -- n = 545
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_545 : Nat.sqrt (545 + 2) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_545]; decide
    · -- n = 546
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_546 : Nat.sqrt (546 + 2) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_546]; decide
    · -- n = 547
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_547 : Nat.sqrt (547 + 2) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_547]; decide
    · -- n = 548
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_548 : Nat.sqrt (548 + 2) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_548]; decide
    · -- n = 549
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_549 : Nat.sqrt (549 + 2) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_549]; decide
    · -- n = 550
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_550 : Nat.sqrt (550 + 2) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_550]; decide
    · -- n = 551
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_551 : Nat.sqrt (551 + 2) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_551]; decide
    · -- n = 552
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_552 : Nat.sqrt (552 + 2) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_552]; decide
    · -- n = 553
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_553 : Nat.sqrt (553 + 2) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_553]; decide
    · -- n = 554
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_554 : Nat.sqrt (554 + 2) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_554]; decide
    · -- n = 555
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_555 : Nat.sqrt (555 + 2) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_555]; decide
    · -- n = 556
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_556 : Nat.sqrt (556 + 2) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_556]; decide
    · -- n = 557
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_557 : Nat.sqrt (557 + 2) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_557]; decide
    · -- n = 558
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_558 : Nat.sqrt (558 + 2) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_558]; decide
    · -- n = 559
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_559 : Nat.sqrt (559 + 2) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_559]; decide
    · -- n = 560
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_560 : Nat.sqrt (560 + 2) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_560]; decide
    · -- n = 561
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_561 : Nat.sqrt (561 + 2) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_561]; decide
    · -- n = 562
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_562 : Nat.sqrt (562 + 2) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_562]; decide
    · -- n = 563
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_563 : Nat.sqrt (563 + 2) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_563]; decide
    · -- n = 564
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_564 : Nat.sqrt (564 + 2) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_564]; decide
    · -- n = 565
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_565 : Nat.sqrt (565 + 2) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_565]; decide
    · -- n = 566
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_566 : Nat.sqrt (566 + 2) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_566]; decide
    · -- n = 567
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_567 : Nat.sqrt (567 + 2) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_567]; decide
    · -- n = 568
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_568 : Nat.sqrt (568 + 2) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_568]; decide
    · -- n = 569
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_569 : Nat.sqrt (569 + 2) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_569]; decide
    · -- n = 570
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_570 : Nat.sqrt (570 + 2) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_570]; decide
    · -- n = 571
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_571 : Nat.sqrt (571 + 2) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_571]; decide
    · -- n = 572
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_572 : Nat.sqrt (572 + 2) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_572]; decide
    · -- n = 573
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_573 : Nat.sqrt (573 + 2) = 23 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_573]; decide
    · -- n = 574
      use 269
      refine ⟨by decide, by decide, ?_⟩
      have h_574 : Nat.sqrt (574 + 269) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_574]; decide
    · -- n = 575
      use 269
      refine ⟨by decide, by decide, ?_⟩
      have h_575 : Nat.sqrt (575 + 269) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_575]; decide
    · -- n = 576
      use 269
      refine ⟨by decide, by decide, ?_⟩
      have h_576 : Nat.sqrt (576 + 269) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_576]; decide
    · -- n = 577
      use 269
      refine ⟨by decide, by decide, ?_⟩
      have h_577 : Nat.sqrt (577 + 269) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_577]; decide
    · -- n = 578
      use 263
      refine ⟨by decide, by decide, ?_⟩
      have h_578 : Nat.sqrt (578 + 263) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_578]; decide
    · -- n = 579
      use 263
      refine ⟨by decide, by decide, ?_⟩
      have h_579 : Nat.sqrt (579 + 263) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_579]; decide
    · -- n = 580
      use 263
      refine ⟨by decide, by decide, ?_⟩
      have h_580 : Nat.sqrt (580 + 263) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_580]; decide
    · -- n = 581
      use 263
      refine ⟨by decide, by decide, ?_⟩
      have h_581 : Nat.sqrt (581 + 263) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_581]; decide
    · -- n = 582
      use 263
      refine ⟨by decide, by decide, ?_⟩
      have h_582 : Nat.sqrt (582 + 263) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_582]; decide
    · -- n = 583
      use 263
      refine ⟨by decide, by decide, ?_⟩
      have h_583 : Nat.sqrt (583 + 263) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_583]; decide
    · -- n = 584
      use 257
      refine ⟨by decide, by decide, ?_⟩
      have h_584 : Nat.sqrt (584 + 257) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_584]; decide
    · -- n = 585
      use 257
      refine ⟨by decide, by decide, ?_⟩
      have h_585 : Nat.sqrt (585 + 257) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_585]; decide
    · -- n = 586
      use 257
      refine ⟨by decide, by decide, ?_⟩
      have h_586 : Nat.sqrt (586 + 257) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_586]; decide
    · -- n = 587
      use 257
      refine ⟨by decide, by decide, ?_⟩
      have h_587 : Nat.sqrt (587 + 257) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_587]; decide
    · -- n = 588
      use 257
      refine ⟨by decide, by decide, ?_⟩
      have h_588 : Nat.sqrt (588 + 257) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_588]; decide
    · -- n = 589
      use 257
      refine ⟨by decide, by decide, ?_⟩
      have h_589 : Nat.sqrt (589 + 257) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_589]; decide
    · -- n = 590
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_590 : Nat.sqrt (590 + 251) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_590]; decide
    · -- n = 591
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_591 : Nat.sqrt (591 + 251) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_591]; decide
    · -- n = 592
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_592 : Nat.sqrt (592 + 251) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_592]; decide
    · -- n = 593
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_593 : Nat.sqrt (593 + 251) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_593]; decide
    · -- n = 594
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_594 : Nat.sqrt (594 + 251) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_594]; decide
    · -- n = 595
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_595 : Nat.sqrt (595 + 251) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_595]; decide
    · -- n = 596
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_596 : Nat.sqrt (596 + 251) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_596]; decide
    · -- n = 597
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_597 : Nat.sqrt (597 + 251) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_597]; decide
    · -- n = 598
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_598 : Nat.sqrt (598 + 251) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_598]; decide
    · -- n = 599
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_599 : Nat.sqrt (599 + 251) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_599]; decide
    · -- n = 600
      use 241
      refine ⟨by decide, by decide, ?_⟩
      have h_600 : Nat.sqrt (600 + 241) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_600]; decide
    · -- n = 601
      use 241
      refine ⟨by decide, by decide, ?_⟩
      have h_601 : Nat.sqrt (601 + 241) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_601]; decide
    · -- n = 602
      use 239
      refine ⟨by decide, by decide, ?_⟩
      have h_602 : Nat.sqrt (602 + 239) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_602]; decide
    · -- n = 603
      use 239
      refine ⟨by decide, by decide, ?_⟩
      have h_603 : Nat.sqrt (603 + 239) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_603]; decide
    · -- n = 604
      use 239
      refine ⟨by decide, by decide, ?_⟩
      have h_604 : Nat.sqrt (604 + 239) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_604]; decide
    · -- n = 605
      use 239
      refine ⟨by decide, by decide, ?_⟩
      have h_605 : Nat.sqrt (605 + 239) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_605]; decide
    · -- n = 606
      use 239
      refine ⟨by decide, by decide, ?_⟩
      have h_606 : Nat.sqrt (606 + 239) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_606]; decide
    · -- n = 607
      use 239
      refine ⟨by decide, by decide, ?_⟩
      have h_607 : Nat.sqrt (607 + 239) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_607]; decide
    · -- n = 608
      use 233
      refine ⟨by decide, by decide, ?_⟩
      have h_608 : Nat.sqrt (608 + 233) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_608]; decide
    · -- n = 609
      use 233
      refine ⟨by decide, by decide, ?_⟩
      have h_609 : Nat.sqrt (609 + 233) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_609]; decide
    · -- n = 610
      use 233
      refine ⟨by decide, by decide, ?_⟩
      have h_610 : Nat.sqrt (610 + 233) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_610]; decide
    · -- n = 611
      use 233
      refine ⟨by decide, by decide, ?_⟩
      have h_611 : Nat.sqrt (611 + 233) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_611]; decide
    · -- n = 612
      use 229
      refine ⟨by decide, by decide, ?_⟩
      have h_612 : Nat.sqrt (612 + 229) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_612]; decide
    · -- n = 613
      use 229
      refine ⟨by decide, by decide, ?_⟩
      have h_613 : Nat.sqrt (613 + 229) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_613]; decide
    · -- n = 614
      use 227
      refine ⟨by decide, by decide, ?_⟩
      have h_614 : Nat.sqrt (614 + 227) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_614]; decide
    · -- n = 615
      use 227
      refine ⟨by decide, by decide, ?_⟩
      have h_615 : Nat.sqrt (615 + 227) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_615]; decide
    · -- n = 616
      use 227
      refine ⟨by decide, by decide, ?_⟩
      have h_616 : Nat.sqrt (616 + 227) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_616]; decide
    · -- n = 617
      use 227
      refine ⟨by decide, by decide, ?_⟩
      have h_617 : Nat.sqrt (617 + 227) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_617]; decide
    · -- n = 618
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_618 : Nat.sqrt (618 + 223) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_618]; decide
    · -- n = 619
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_619 : Nat.sqrt (619 + 223) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_619]; decide
    · -- n = 620
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_620 : Nat.sqrt (620 + 223) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_620]; decide
    · -- n = 621
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_621 : Nat.sqrt (621 + 223) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_621]; decide
    · -- n = 622
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_622 : Nat.sqrt (622 + 223) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_622]; decide
    · -- n = 623
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_623 : Nat.sqrt (623 + 223) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_623]; decide
    · -- n = 624
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_624 : Nat.sqrt (624 + 223) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_624]; decide
    · -- n = 625
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_625 : Nat.sqrt (625 + 223) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_625]; decide
    · -- n = 626
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_626 : Nat.sqrt (626 + 223) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_626]; decide
    · -- n = 627
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_627 : Nat.sqrt (627 + 223) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_627]; decide
    · -- n = 628
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_628 : Nat.sqrt (628 + 223) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_628]; decide
    · -- n = 629
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_629 : Nat.sqrt (629 + 223) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_629]; decide
    · -- n = 630
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_630 : Nat.sqrt (630 + 211) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_630]; decide
    · -- n = 631
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_631 : Nat.sqrt (631 + 211) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_631]; decide
    · -- n = 632
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_632 : Nat.sqrt (632 + 211) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_632]; decide
    · -- n = 633
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_633 : Nat.sqrt (633 + 211) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_633]; decide
    · -- n = 634
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_634 : Nat.sqrt (634 + 211) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_634]; decide
    · -- n = 635
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_635 : Nat.sqrt (635 + 211) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_635]; decide
    · -- n = 636
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_636 : Nat.sqrt (636 + 211) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_636]; decide
    · -- n = 637
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_637 : Nat.sqrt (637 + 211) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_637]; decide
    · -- n = 638
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_638 : Nat.sqrt (638 + 211) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_638]; decide
    · -- n = 639
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_639 : Nat.sqrt (639 + 211) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_639]; decide
    · -- n = 640
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_640 : Nat.sqrt (640 + 211) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_640]; decide
    · -- n = 641
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_641 : Nat.sqrt (641 + 211) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_641]; decide
    · -- n = 642
      use 199
      refine ⟨by decide, by decide, ?_⟩
      have h_642 : Nat.sqrt (642 + 199) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_642]; decide
    · -- n = 643
      use 199
      refine ⟨by decide, by decide, ?_⟩
      have h_643 : Nat.sqrt (643 + 199) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_643]; decide
    · -- n = 644
      use 197
      refine ⟨by decide, by decide, ?_⟩
      have h_644 : Nat.sqrt (644 + 197) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_644]; decide
    · -- n = 645
      use 197
      refine ⟨by decide, by decide, ?_⟩
      have h_645 : Nat.sqrt (645 + 197) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_645]; decide
    · -- n = 646
      use 197
      refine ⟨by decide, by decide, ?_⟩
      have h_646 : Nat.sqrt (646 + 197) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_646]; decide
    · -- n = 647
      use 197
      refine ⟨by decide, by decide, ?_⟩
      have h_647 : Nat.sqrt (647 + 197) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_647]; decide
    · -- n = 648
      use 193
      refine ⟨by decide, by decide, ?_⟩
      have h_648 : Nat.sqrt (648 + 193) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_648]; decide
    · -- n = 649
      use 193
      refine ⟨by decide, by decide, ?_⟩
      have h_649 : Nat.sqrt (649 + 193) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_649]; decide
    · -- n = 650
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_650 : Nat.sqrt (650 + 191) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_650]; decide
    · -- n = 651
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_651 : Nat.sqrt (651 + 191) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_651]; decide
    · -- n = 652
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_652 : Nat.sqrt (652 + 191) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_652]; decide
    · -- n = 653
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_653 : Nat.sqrt (653 + 191) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_653]; decide
    · -- n = 654
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_654 : Nat.sqrt (654 + 191) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_654]; decide
    · -- n = 655
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_655 : Nat.sqrt (655 + 191) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_655]; decide
    · -- n = 656
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_656 : Nat.sqrt (656 + 191) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_656]; decide
    · -- n = 657
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_657 : Nat.sqrt (657 + 191) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_657]; decide
    · -- n = 658
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_658 : Nat.sqrt (658 + 191) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_658]; decide
    · -- n = 659
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_659 : Nat.sqrt (659 + 191) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_659]; decide
    · -- n = 660
      use 181
      refine ⟨by decide, by decide, ?_⟩
      have h_660 : Nat.sqrt (660 + 181) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_660]; decide
    · -- n = 661
      use 181
      refine ⟨by decide, by decide, ?_⟩
      have h_661 : Nat.sqrt (661 + 181) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_661]; decide
    · -- n = 662
      use 179
      refine ⟨by decide, by decide, ?_⟩
      have h_662 : Nat.sqrt (662 + 179) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_662]; decide
    · -- n = 663
      use 179
      refine ⟨by decide, by decide, ?_⟩
      have h_663 : Nat.sqrt (663 + 179) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_663]; decide
    · -- n = 664
      use 179
      refine ⟨by decide, by decide, ?_⟩
      have h_664 : Nat.sqrt (664 + 179) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_664]; decide
    · -- n = 665
      use 179
      refine ⟨by decide, by decide, ?_⟩
      have h_665 : Nat.sqrt (665 + 179) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_665]; decide
    · -- n = 666
      use 179
      refine ⟨by decide, by decide, ?_⟩
      have h_666 : Nat.sqrt (666 + 179) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_666]; decide
    · -- n = 667
      use 179
      refine ⟨by decide, by decide, ?_⟩
      have h_667 : Nat.sqrt (667 + 179) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_667]; decide
    · -- n = 668
      use 173
      refine ⟨by decide, by decide, ?_⟩
      have h_668 : Nat.sqrt (668 + 173) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_668]; decide
    · -- n = 669
      use 173
      refine ⟨by decide, by decide, ?_⟩
      have h_669 : Nat.sqrt (669 + 173) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_669]; decide
    · -- n = 670
      use 173
      refine ⟨by decide, by decide, ?_⟩
      have h_670 : Nat.sqrt (670 + 173) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_670]; decide
    · -- n = 671
      use 173
      refine ⟨by decide, by decide, ?_⟩
      have h_671 : Nat.sqrt (671 + 173) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_671]; decide
    · -- n = 672
      use 173
      refine ⟨by decide, by decide, ?_⟩
      have h_672 : Nat.sqrt (672 + 173) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_672]; decide
    · -- n = 673
      use 173
      refine ⟨by decide, by decide, ?_⟩
      have h_673 : Nat.sqrt (673 + 173) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_673]; decide
    · -- n = 674
      use 167
      refine ⟨by decide, by decide, ?_⟩
      have h_674 : Nat.sqrt (674 + 167) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_674]; decide
    · -- n = 675
      use 167
      refine ⟨by decide, by decide, ?_⟩
      have h_675 : Nat.sqrt (675 + 167) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_675]; decide
    · -- n = 676
      use 167
      refine ⟨by decide, by decide, ?_⟩
      have h_676 : Nat.sqrt (676 + 167) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_676]; decide
    · -- n = 677
      use 167
      refine ⟨by decide, by decide, ?_⟩
      have h_677 : Nat.sqrt (677 + 167) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_677]; decide
    · -- n = 678
      use 163
      refine ⟨by decide, by decide, ?_⟩
      have h_678 : Nat.sqrt (678 + 163) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_678]; decide
    · -- n = 679
      use 163
      refine ⟨by decide, by decide, ?_⟩
      have h_679 : Nat.sqrt (679 + 163) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_679]; decide
    · -- n = 680
      use 163
      refine ⟨by decide, by decide, ?_⟩
      have h_680 : Nat.sqrt (680 + 163) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_680]; decide
    · -- n = 681
      use 163
      refine ⟨by decide, by decide, ?_⟩
      have h_681 : Nat.sqrt (681 + 163) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_681]; decide
    · -- n = 682
      use 163
      refine ⟨by decide, by decide, ?_⟩
      have h_682 : Nat.sqrt (682 + 163) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_682]; decide
    · -- n = 683
      use 163
      refine ⟨by decide, by decide, ?_⟩
      have h_683 : Nat.sqrt (683 + 163) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_683]; decide
    · -- n = 684
      use 157
      refine ⟨by decide, by decide, ?_⟩
      have h_684 : Nat.sqrt (684 + 157) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_684]; decide
    · -- n = 685
      use 157
      refine ⟨by decide, by decide, ?_⟩
      have h_685 : Nat.sqrt (685 + 157) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_685]; decide
    · -- n = 686
      use 157
      refine ⟨by decide, by decide, ?_⟩
      have h_686 : Nat.sqrt (686 + 157) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_686]; decide
    · -- n = 687
      use 157
      refine ⟨by decide, by decide, ?_⟩
      have h_687 : Nat.sqrt (687 + 157) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_687]; decide
    · -- n = 688
      use 157
      refine ⟨by decide, by decide, ?_⟩
      have h_688 : Nat.sqrt (688 + 157) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_688]; decide
    · -- n = 689
      use 157
      refine ⟨by decide, by decide, ?_⟩
      have h_689 : Nat.sqrt (689 + 157) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_689]; decide
    · -- n = 690
      use 151
      refine ⟨by decide, by decide, ?_⟩
      have h_690 : Nat.sqrt (690 + 151) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_690]; decide
    · -- n = 691
      use 151
      refine ⟨by decide, by decide, ?_⟩
      have h_691 : Nat.sqrt (691 + 151) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_691]; decide
    · -- n = 692
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_692 : Nat.sqrt (692 + 149) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_692]; decide
    · -- n = 693
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_693 : Nat.sqrt (693 + 149) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_693]; decide
    · -- n = 694
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_694 : Nat.sqrt (694 + 149) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_694]; decide
    · -- n = 695
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_695 : Nat.sqrt (695 + 149) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_695]; decide
    · -- n = 696
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_696 : Nat.sqrt (696 + 149) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_696]; decide
    · -- n = 697
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_697 : Nat.sqrt (697 + 149) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_697]; decide
    · -- n = 698
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_698 : Nat.sqrt (698 + 149) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_698]; decide
    · -- n = 699
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_699 : Nat.sqrt (699 + 149) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_699]; decide
    · -- n = 700
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_700 : Nat.sqrt (700 + 149) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_700]; decide
    · -- n = 701
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_701 : Nat.sqrt (701 + 149) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_701]; decide
    · -- n = 702
      use 139
      refine ⟨by decide, by decide, ?_⟩
      have h_702 : Nat.sqrt (702 + 139) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_702]; decide
    · -- n = 703
      use 139
      refine ⟨by decide, by decide, ?_⟩
      have h_703 : Nat.sqrt (703 + 139) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_703]; decide
    · -- n = 704
      use 137
      refine ⟨by decide, by decide, ?_⟩
      have h_704 : Nat.sqrt (704 + 137) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_704]; decide
    · -- n = 705
      use 137
      refine ⟨by decide, by decide, ?_⟩
      have h_705 : Nat.sqrt (705 + 137) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_705]; decide
    · -- n = 706
      use 137
      refine ⟨by decide, by decide, ?_⟩
      have h_706 : Nat.sqrt (706 + 137) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_706]; decide
    · -- n = 707
      use 137
      refine ⟨by decide, by decide, ?_⟩
      have h_707 : Nat.sqrt (707 + 137) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_707]; decide
    · -- n = 708
      use 137
      refine ⟨by decide, by decide, ?_⟩
      have h_708 : Nat.sqrt (708 + 137) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_708]; decide
    · -- n = 709
      use 137
      refine ⟨by decide, by decide, ?_⟩
      have h_709 : Nat.sqrt (709 + 137) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_709]; decide
    · -- n = 710
      use 131
      refine ⟨by decide, by decide, ?_⟩
      have h_710 : Nat.sqrt (710 + 131) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_710]; decide
    · -- n = 711
      use 131
      refine ⟨by decide, by decide, ?_⟩
      have h_711 : Nat.sqrt (711 + 131) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_711]; decide
    · -- n = 712
      use 131
      refine ⟨by decide, by decide, ?_⟩
      have h_712 : Nat.sqrt (712 + 131) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_712]; decide
    · -- n = 713
      use 131
      refine ⟨by decide, by decide, ?_⟩
      have h_713 : Nat.sqrt (713 + 131) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_713]; decide
    · -- n = 714
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_714 : Nat.sqrt (714 + 127) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_714]; decide
    · -- n = 715
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_715 : Nat.sqrt (715 + 127) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_715]; decide
    · -- n = 716
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_716 : Nat.sqrt (716 + 127) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_716]; decide
    · -- n = 717
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_717 : Nat.sqrt (717 + 127) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_717]; decide
    · -- n = 718
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_718 : Nat.sqrt (718 + 127) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_718]; decide
    · -- n = 719
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_719 : Nat.sqrt (719 + 127) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_719]; decide
    · -- n = 720
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_720 : Nat.sqrt (720 + 127) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_720]; decide
    · -- n = 721
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_721 : Nat.sqrt (721 + 127) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_721]; decide
    · -- n = 722
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_722 : Nat.sqrt (722 + 127) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_722]; decide
    · -- n = 723
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_723 : Nat.sqrt (723 + 127) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_723]; decide
    · -- n = 724
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_724 : Nat.sqrt (724 + 127) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_724]; decide
    · -- n = 725
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_725 : Nat.sqrt (725 + 127) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_725]; decide
    · -- n = 726
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_726 : Nat.sqrt (726 + 127) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_726]; decide
    · -- n = 727
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_727 : Nat.sqrt (727 + 127) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_727]; decide
    · -- n = 728
      use 113
      refine ⟨by decide, by decide, ?_⟩
      have h_728 : Nat.sqrt (728 + 113) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_728]; decide
    · -- n = 729
      use 113
      refine ⟨by decide, by decide, ?_⟩
      have h_729 : Nat.sqrt (729 + 113) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_729]; decide
    · -- n = 730
      use 113
      refine ⟨by decide, by decide, ?_⟩
      have h_730 : Nat.sqrt (730 + 113) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_730]; decide
    · -- n = 731
      use 113
      refine ⟨by decide, by decide, ?_⟩
      have h_731 : Nat.sqrt (731 + 113) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_731]; decide
    · -- n = 732
      use 109
      refine ⟨by decide, by decide, ?_⟩
      have h_732 : Nat.sqrt (732 + 109) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_732]; decide
    · -- n = 733
      use 109
      refine ⟨by decide, by decide, ?_⟩
      have h_733 : Nat.sqrt (733 + 109) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_733]; decide
    · -- n = 734
      use 107
      refine ⟨by decide, by decide, ?_⟩
      have h_734 : Nat.sqrt (734 + 107) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_734]; decide
    · -- n = 735
      use 107
      refine ⟨by decide, by decide, ?_⟩
      have h_735 : Nat.sqrt (735 + 107) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_735]; decide
    · -- n = 736
      use 107
      refine ⟨by decide, by decide, ?_⟩
      have h_736 : Nat.sqrt (736 + 107) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_736]; decide
    · -- n = 737
      use 107
      refine ⟨by decide, by decide, ?_⟩
      have h_737 : Nat.sqrt (737 + 107) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_737]; decide
    · -- n = 738
      use 103
      refine ⟨by decide, by decide, ?_⟩
      have h_738 : Nat.sqrt (738 + 103) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_738]; decide
    · -- n = 739
      use 103
      refine ⟨by decide, by decide, ?_⟩
      have h_739 : Nat.sqrt (739 + 103) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_739]; decide
    · -- n = 740
      use 101
      refine ⟨by decide, by decide, ?_⟩
      have h_740 : Nat.sqrt (740 + 101) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_740]; decide
    · -- n = 741
      use 101
      refine ⟨by decide, by decide, ?_⟩
      have h_741 : Nat.sqrt (741 + 101) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_741]; decide
    · -- n = 742
      use 101
      refine ⟨by decide, by decide, ?_⟩
      have h_742 : Nat.sqrt (742 + 101) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_742]; decide
    · -- n = 743
      use 101
      refine ⟨by decide, by decide, ?_⟩
      have h_743 : Nat.sqrt (743 + 101) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_743]; decide
    · -- n = 744
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_744 : Nat.sqrt (744 + 97) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_744]; decide
    · -- n = 745
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_745 : Nat.sqrt (745 + 97) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_745]; decide
    · -- n = 746
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_746 : Nat.sqrt (746 + 97) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_746]; decide
    · -- n = 747
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_747 : Nat.sqrt (747 + 97) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_747]; decide
    · -- n = 748
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_748 : Nat.sqrt (748 + 97) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_748]; decide
    · -- n = 749
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_749 : Nat.sqrt (749 + 97) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_749]; decide
    · -- n = 750
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_750 : Nat.sqrt (750 + 97) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_750]; decide
    · -- n = 751
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_751 : Nat.sqrt (751 + 97) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_751]; decide
    · -- n = 752
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_752 : Nat.sqrt (752 + 89) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_752]; decide
    · -- n = 753
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_753 : Nat.sqrt (753 + 89) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_753]; decide
    · -- n = 754
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_754 : Nat.sqrt (754 + 89) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_754]; decide
    · -- n = 755
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_755 : Nat.sqrt (755 + 89) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_755]; decide
    · -- n = 756
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_756 : Nat.sqrt (756 + 89) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_756]; decide
    · -- n = 757
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_757 : Nat.sqrt (757 + 89) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_757]; decide
    · -- n = 758
      use 83
      refine ⟨by decide, by decide, ?_⟩
      have h_758 : Nat.sqrt (758 + 83) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_758]; decide
    · -- n = 759
      use 83
      refine ⟨by decide, by decide, ?_⟩
      have h_759 : Nat.sqrt (759 + 83) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_759]; decide
    · -- n = 760
      use 83
      refine ⟨by decide, by decide, ?_⟩
      have h_760 : Nat.sqrt (760 + 83) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_760]; decide
    · -- n = 761
      use 83
      refine ⟨by decide, by decide, ?_⟩
      have h_761 : Nat.sqrt (761 + 83) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_761]; decide
    · -- n = 762
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_762 : Nat.sqrt (762 + 79) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_762]; decide
    · -- n = 763
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_763 : Nat.sqrt (763 + 79) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_763]; decide
    · -- n = 764
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_764 : Nat.sqrt (764 + 79) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_764]; decide
    · -- n = 765
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_765 : Nat.sqrt (765 + 79) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_765]; decide
    · -- n = 766
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_766 : Nat.sqrt (766 + 79) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_766]; decide
    · -- n = 767
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_767 : Nat.sqrt (767 + 79) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_767]; decide
    · -- n = 768
      use 73
      refine ⟨by decide, by decide, ?_⟩
      have h_768 : Nat.sqrt (768 + 73) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_768]; decide
    · -- n = 769
      use 73
      refine ⟨by decide, by decide, ?_⟩
      have h_769 : Nat.sqrt (769 + 73) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_769]; decide
    · -- n = 770
      use 71
      refine ⟨by decide, by decide, ?_⟩
      have h_770 : Nat.sqrt (770 + 71) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_770]; decide
    · -- n = 771
      use 71
      refine ⟨by decide, by decide, ?_⟩
      have h_771 : Nat.sqrt (771 + 71) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_771]; decide
    · -- n = 772
      use 71
      refine ⟨by decide, by decide, ?_⟩
      have h_772 : Nat.sqrt (772 + 71) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_772]; decide
    · -- n = 773
      use 71
      refine ⟨by decide, by decide, ?_⟩
      have h_773 : Nat.sqrt (773 + 71) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_773]; decide
    · -- n = 774
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_774 : Nat.sqrt (774 + 67) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_774]; decide
    · -- n = 775
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_775 : Nat.sqrt (775 + 67) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_775]; decide
    · -- n = 776
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_776 : Nat.sqrt (776 + 67) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_776]; decide
    · -- n = 777
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_777 : Nat.sqrt (777 + 67) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_777]; decide
    · -- n = 778
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_778 : Nat.sqrt (778 + 67) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_778]; decide
    · -- n = 779
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_779 : Nat.sqrt (779 + 67) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_779]; decide
    · -- n = 780
      use 61
      refine ⟨by decide, by decide, ?_⟩
      have h_780 : Nat.sqrt (780 + 61) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_780]; decide
    · -- n = 781
      use 61
      refine ⟨by decide, by decide, ?_⟩
      have h_781 : Nat.sqrt (781 + 61) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_781]; decide
    · -- n = 782
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_782 : Nat.sqrt (782 + 59) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_782]; decide
    · -- n = 783
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_783 : Nat.sqrt (783 + 59) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_783]; decide
    · -- n = 784
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_784 : Nat.sqrt (784 + 59) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_784]; decide
    · -- n = 785
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_785 : Nat.sqrt (785 + 59) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_785]; decide
    · -- n = 786
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_786 : Nat.sqrt (786 + 59) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_786]; decide
    · -- n = 787
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_787 : Nat.sqrt (787 + 59) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_787]; decide
    · -- n = 788
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_788 : Nat.sqrt (788 + 53) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_788]; decide
    · -- n = 789
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_789 : Nat.sqrt (789 + 53) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_789]; decide
    · -- n = 790
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_790 : Nat.sqrt (790 + 53) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_790]; decide
    · -- n = 791
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_791 : Nat.sqrt (791 + 53) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_791]; decide
    · -- n = 792
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_792 : Nat.sqrt (792 + 53) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_792]; decide
    · -- n = 793
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_793 : Nat.sqrt (793 + 53) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_793]; decide
    · -- n = 794
      use 47
      refine ⟨by decide, by decide, ?_⟩
      have h_794 : Nat.sqrt (794 + 47) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_794]; decide
    · -- n = 795
      use 47
      refine ⟨by decide, by decide, ?_⟩
      have h_795 : Nat.sqrt (795 + 47) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_795]; decide
    · -- n = 796
      use 47
      refine ⟨by decide, by decide, ?_⟩
      have h_796 : Nat.sqrt (796 + 47) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_796]; decide
    · -- n = 797
      use 47
      refine ⟨by decide, by decide, ?_⟩
      have h_797 : Nat.sqrt (797 + 47) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_797]; decide
    · -- n = 798
      use 43
      refine ⟨by decide, by decide, ?_⟩
      have h_798 : Nat.sqrt (798 + 43) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_798]; decide
    · -- n = 799
      use 43
      refine ⟨by decide, by decide, ?_⟩
      have h_799 : Nat.sqrt (799 + 43) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_799]; decide
    · -- n = 800
      use 41
      refine ⟨by decide, by decide, ?_⟩
      have h_800 : Nat.sqrt (800 + 41) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_800]; decide
    · -- n = 801
      use 41
      refine ⟨by decide, by decide, ?_⟩
      have h_801 : Nat.sqrt (801 + 41) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_801]; decide
    · -- n = 802
      use 41
      refine ⟨by decide, by decide, ?_⟩
      have h_802 : Nat.sqrt (802 + 41) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_802]; decide
    · -- n = 803
      use 41
      refine ⟨by decide, by decide, ?_⟩
      have h_803 : Nat.sqrt (803 + 41) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_803]; decide
    · -- n = 804
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_804 : Nat.sqrt (804 + 37) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_804]; decide
    · -- n = 805
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_805 : Nat.sqrt (805 + 37) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_805]; decide
    · -- n = 806
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_806 : Nat.sqrt (806 + 37) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_806]; decide
    · -- n = 807
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_807 : Nat.sqrt (807 + 37) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_807]; decide
    · -- n = 808
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_808 : Nat.sqrt (808 + 37) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_808]; decide
    · -- n = 809
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_809 : Nat.sqrt (809 + 37) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_809]; decide
    · -- n = 810
      use 31
      refine ⟨by decide, by decide, ?_⟩
      have h_810 : Nat.sqrt (810 + 31) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_810]; decide
    · -- n = 811
      use 31
      refine ⟨by decide, by decide, ?_⟩
      have h_811 : Nat.sqrt (811 + 31) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_811]; decide
    · -- n = 812
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_812 : Nat.sqrt (812 + 29) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_812]; decide
    · -- n = 813
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_813 : Nat.sqrt (813 + 29) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_813]; decide
    · -- n = 814
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_814 : Nat.sqrt (814 + 29) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_814]; decide
    · -- n = 815
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_815 : Nat.sqrt (815 + 29) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_815]; decide
    · -- n = 816
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_816 : Nat.sqrt (816 + 29) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_816]; decide
    · -- n = 817
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_817 : Nat.sqrt (817 + 29) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_817]; decide
    · -- n = 818
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_818 : Nat.sqrt (818 + 23) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_818]; decide
    · -- n = 819
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_819 : Nat.sqrt (819 + 23) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_819]; decide
    · -- n = 820
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_820 : Nat.sqrt (820 + 23) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_820]; decide
    · -- n = 821
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_821 : Nat.sqrt (821 + 23) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_821]; decide
    · -- n = 822
      use 19
      refine ⟨by decide, by decide, ?_⟩
      have h_822 : Nat.sqrt (822 + 19) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_822]; decide
    · -- n = 823
      use 19
      refine ⟨by decide, by decide, ?_⟩
      have h_823 : Nat.sqrt (823 + 19) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_823]; decide
    · -- n = 824
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_824 : Nat.sqrt (824 + 17) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_824]; decide
    · -- n = 825
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_825 : Nat.sqrt (825 + 17) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_825]; decide
    · -- n = 826
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_826 : Nat.sqrt (826 + 17) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_826]; decide
    · -- n = 827
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_827 : Nat.sqrt (827 + 17) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_827]; decide
    · -- n = 828
      use 13
      refine ⟨by decide, by decide, ?_⟩
      have h_828 : Nat.sqrt (828 + 13) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_828]; decide
    · -- n = 829
      use 13
      refine ⟨by decide, by decide, ?_⟩
      have h_829 : Nat.sqrt (829 + 13) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_829]; decide
    · -- n = 830
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_830 : Nat.sqrt (830 + 11) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_830]; decide
    · -- n = 831
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_831 : Nat.sqrt (831 + 11) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_831]; decide
    · -- n = 832
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_832 : Nat.sqrt (832 + 11) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_832]; decide
    · -- n = 833
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_833 : Nat.sqrt (833 + 11) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_833]; decide
    · -- n = 834
      use 7
      refine ⟨by decide, by decide, ?_⟩
      have h_834 : Nat.sqrt (834 + 7) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_834]; decide
    · -- n = 835
      use 7
      refine ⟨by decide, by decide, ?_⟩
      have h_835 : Nat.sqrt (835 + 7) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_835]; decide
    · -- n = 836
      use 5
      refine ⟨by decide, by decide, ?_⟩
      have h_836 : Nat.sqrt (836 + 5) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_836]; decide
    · -- n = 837
      use 5
      refine ⟨by decide, by decide, ?_⟩
      have h_837 : Nat.sqrt (837 + 5) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_837]; decide
    · -- n = 838
      use 3
      refine ⟨by decide, by decide, ?_⟩
      have h_838 : Nat.sqrt (838 + 3) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_838]; decide
    · -- n = 839
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_839 : Nat.sqrt (839 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_839]; decide
    · -- n = 840
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_840 : Nat.sqrt (840 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_840]; decide
    · -- n = 841
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_841 : Nat.sqrt (841 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_841]; decide
    · -- n = 842
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_842 : Nat.sqrt (842 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_842]; decide
    · -- n = 843
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_843 : Nat.sqrt (843 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_843]; decide
    · -- n = 844
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_844 : Nat.sqrt (844 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_844]; decide
    · -- n = 845
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_845 : Nat.sqrt (845 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_845]; decide
    · -- n = 846
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_846 : Nat.sqrt (846 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_846]; decide
    · -- n = 847
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_847 : Nat.sqrt (847 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_847]; decide
    · -- n = 848
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_848 : Nat.sqrt (848 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_848]; decide
    · -- n = 849
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_849 : Nat.sqrt (849 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_849]; decide
    · -- n = 850
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_850 : Nat.sqrt (850 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_850]; decide
    · -- n = 851
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_851 : Nat.sqrt (851 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_851]; decide
    · -- n = 852
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_852 : Nat.sqrt (852 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_852]; decide
    · -- n = 853
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_853 : Nat.sqrt (853 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_853]; decide
    · -- n = 854
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_854 : Nat.sqrt (854 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_854]; decide
    · -- n = 855
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_855 : Nat.sqrt (855 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_855]; decide
    · -- n = 856
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_856 : Nat.sqrt (856 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_856]; decide
    · -- n = 857
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_857 : Nat.sqrt (857 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_857]; decide
    · -- n = 858
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_858 : Nat.sqrt (858 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_858]; decide
    · -- n = 859
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_859 : Nat.sqrt (859 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_859]; decide
    · -- n = 860
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_860 : Nat.sqrt (860 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_860]; decide
    · -- n = 861
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_861 : Nat.sqrt (861 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_861]; decide
    · -- n = 862
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_862 : Nat.sqrt (862 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_862]; decide
    · -- n = 863
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_863 : Nat.sqrt (863 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_863]; decide
    · -- n = 864
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_864 : Nat.sqrt (864 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_864]; decide
    · -- n = 865
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_865 : Nat.sqrt (865 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_865]; decide
    · -- n = 866
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_866 : Nat.sqrt (866 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_866]; decide
    · -- n = 867
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_867 : Nat.sqrt (867 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_867]; decide
    · -- n = 868
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_868 : Nat.sqrt (868 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_868]; decide
    · -- n = 869
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_869 : Nat.sqrt (869 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_869]; decide
    · -- n = 870
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_870 : Nat.sqrt (870 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_870]; decide
    · -- n = 871
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_871 : Nat.sqrt (871 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_871]; decide
    · -- n = 872
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_872 : Nat.sqrt (872 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_872]; decide
    · -- n = 873
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_873 : Nat.sqrt (873 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_873]; decide
    · -- n = 874
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_874 : Nat.sqrt (874 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_874]; decide
    · -- n = 875
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_875 : Nat.sqrt (875 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_875]; decide
    · -- n = 876
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_876 : Nat.sqrt (876 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_876]; decide
    · -- n = 877
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_877 : Nat.sqrt (877 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_877]; decide
    · -- n = 878
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_878 : Nat.sqrt (878 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_878]; decide
    · -- n = 879
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_879 : Nat.sqrt (879 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_879]; decide
    · -- n = 880
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_880 : Nat.sqrt (880 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_880]; decide
    · -- n = 881
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_881 : Nat.sqrt (881 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_881]; decide
    · -- n = 882
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_882 : Nat.sqrt (882 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_882]; decide
    · -- n = 883
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_883 : Nat.sqrt (883 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_883]; decide
    · -- n = 884
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_884 : Nat.sqrt (884 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_884]; decide
    · -- n = 885
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_885 : Nat.sqrt (885 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_885]; decide
    · -- n = 886
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_886 : Nat.sqrt (886 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_886]; decide
    · -- n = 887
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_887 : Nat.sqrt (887 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_887]; decide
    · -- n = 888
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_888 : Nat.sqrt (888 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_888]; decide
    · -- n = 889
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_889 : Nat.sqrt (889 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_889]; decide
    · -- n = 890
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_890 : Nat.sqrt (890 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_890]; decide
    · -- n = 891
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_891 : Nat.sqrt (891 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_891]; decide
    · -- n = 892
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_892 : Nat.sqrt (892 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_892]; decide
    · -- n = 893
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_893 : Nat.sqrt (893 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_893]; decide
    · -- n = 894
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_894 : Nat.sqrt (894 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_894]; decide
    · -- n = 895
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_895 : Nat.sqrt (895 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_895]; decide
    · -- n = 896
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_896 : Nat.sqrt (896 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_896]; decide
    · -- n = 897
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_897 : Nat.sqrt (897 + 2) = 29 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_897]; decide
    · -- n = 898
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_898 : Nat.sqrt (898 + 67) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_898]; decide
    · -- n = 899
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_899 : Nat.sqrt (899 + 67) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_899]; decide
    · -- n = 900
      use 61
      refine ⟨by decide, by decide, ?_⟩
      have h_900 : Nat.sqrt (900 + 61) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_900]; decide
    · -- n = 901
      use 61
      refine ⟨by decide, by decide, ?_⟩
      have h_901 : Nat.sqrt (901 + 61) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_901]; decide
    · -- n = 902
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_902 : Nat.sqrt (902 + 59) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_902]; decide
    · -- n = 903
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_903 : Nat.sqrt (903 + 59) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_903]; decide
    · -- n = 904
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_904 : Nat.sqrt (904 + 59) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_904]; decide
    · -- n = 905
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_905 : Nat.sqrt (905 + 59) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_905]; decide
    · -- n = 906
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_906 : Nat.sqrt (906 + 59) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_906]; decide
    · -- n = 907
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_907 : Nat.sqrt (907 + 59) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_907]; decide
    · -- n = 908
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_908 : Nat.sqrt (908 + 53) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_908]; decide
    · -- n = 909
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_909 : Nat.sqrt (909 + 53) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_909]; decide
    · -- n = 910
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_910 : Nat.sqrt (910 + 53) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_910]; decide
    · -- n = 911
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_911 : Nat.sqrt (911 + 53) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_911]; decide
    · -- n = 912
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_912 : Nat.sqrt (912 + 53) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_912]; decide
    · -- n = 913
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_913 : Nat.sqrt (913 + 53) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_913]; decide
    · -- n = 914
      use 47
      refine ⟨by decide, by decide, ?_⟩
      have h_914 : Nat.sqrt (914 + 47) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_914]; decide
    · -- n = 915
      use 47
      refine ⟨by decide, by decide, ?_⟩
      have h_915 : Nat.sqrt (915 + 47) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_915]; decide
    · -- n = 916
      use 47
      refine ⟨by decide, by decide, ?_⟩
      have h_916 : Nat.sqrt (916 + 47) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_916]; decide
    · -- n = 917
      use 47
      refine ⟨by decide, by decide, ?_⟩
      have h_917 : Nat.sqrt (917 + 47) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_917]; decide
    · -- n = 918
      use 43
      refine ⟨by decide, by decide, ?_⟩
      have h_918 : Nat.sqrt (918 + 43) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_918]; decide
    · -- n = 919
      use 43
      refine ⟨by decide, by decide, ?_⟩
      have h_919 : Nat.sqrt (919 + 43) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_919]; decide
    · -- n = 920
      use 41
      refine ⟨by decide, by decide, ?_⟩
      have h_920 : Nat.sqrt (920 + 41) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_920]; decide
    · -- n = 921
      use 41
      refine ⟨by decide, by decide, ?_⟩
      have h_921 : Nat.sqrt (921 + 41) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_921]; decide
    · -- n = 922
      use 41
      refine ⟨by decide, by decide, ?_⟩
      have h_922 : Nat.sqrt (922 + 41) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_922]; decide
    · -- n = 923
      use 41
      refine ⟨by decide, by decide, ?_⟩
      have h_923 : Nat.sqrt (923 + 41) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_923]; decide
    · -- n = 924
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_924 : Nat.sqrt (924 + 37) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_924]; decide
    · -- n = 925
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_925 : Nat.sqrt (925 + 37) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_925]; decide
    · -- n = 926
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_926 : Nat.sqrt (926 + 37) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_926]; decide
    · -- n = 927
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_927 : Nat.sqrt (927 + 37) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_927]; decide
    · -- n = 928
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_928 : Nat.sqrt (928 + 37) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_928]; decide
    · -- n = 929
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_929 : Nat.sqrt (929 + 37) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_929]; decide
    · -- n = 930
      use 31
      refine ⟨by decide, by decide, ?_⟩
      have h_930 : Nat.sqrt (930 + 31) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_930]; decide
    · -- n = 931
      use 31
      refine ⟨by decide, by decide, ?_⟩
      have h_931 : Nat.sqrt (931 + 31) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_931]; decide
    · -- n = 932
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_932 : Nat.sqrt (932 + 29) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_932]; decide
    · -- n = 933
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_933 : Nat.sqrt (933 + 29) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_933]; decide
    · -- n = 934
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_934 : Nat.sqrt (934 + 29) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_934]; decide
    · -- n = 935
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_935 : Nat.sqrt (935 + 29) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_935]; decide
    · -- n = 936
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_936 : Nat.sqrt (936 + 29) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_936]; decide
    · -- n = 937
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_937 : Nat.sqrt (937 + 29) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_937]; decide
    · -- n = 938
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_938 : Nat.sqrt (938 + 23) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_938]; decide
    · -- n = 939
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_939 : Nat.sqrt (939 + 23) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_939]; decide
    · -- n = 940
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_940 : Nat.sqrt (940 + 23) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_940]; decide
    · -- n = 941
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_941 : Nat.sqrt (941 + 23) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_941]; decide
    · -- n = 942
      use 19
      refine ⟨by decide, by decide, ?_⟩
      have h_942 : Nat.sqrt (942 + 19) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_942]; decide
    · -- n = 943
      use 19
      refine ⟨by decide, by decide, ?_⟩
      have h_943 : Nat.sqrt (943 + 19) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_943]; decide
    · -- n = 944
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_944 : Nat.sqrt (944 + 17) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_944]; decide
    · -- n = 945
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_945 : Nat.sqrt (945 + 17) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_945]; decide
    · -- n = 946
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_946 : Nat.sqrt (946 + 17) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_946]; decide
    · -- n = 947
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_947 : Nat.sqrt (947 + 17) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_947]; decide
    · -- n = 948
      use 13
      refine ⟨by decide, by decide, ?_⟩
      have h_948 : Nat.sqrt (948 + 13) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_948]; decide
    · -- n = 949
      use 13
      refine ⟨by decide, by decide, ?_⟩
      have h_949 : Nat.sqrt (949 + 13) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_949]; decide
    · -- n = 950
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_950 : Nat.sqrt (950 + 11) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_950]; decide
    · -- n = 951
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_951 : Nat.sqrt (951 + 11) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_951]; decide
    · -- n = 952
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_952 : Nat.sqrt (952 + 11) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_952]; decide
    · -- n = 953
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_953 : Nat.sqrt (953 + 11) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_953]; decide
    · -- n = 954
      use 7
      refine ⟨by decide, by decide, ?_⟩
      have h_954 : Nat.sqrt (954 + 7) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_954]; decide
    · -- n = 955
      use 7
      refine ⟨by decide, by decide, ?_⟩
      have h_955 : Nat.sqrt (955 + 7) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_955]; decide
    · -- n = 956
      use 5
      refine ⟨by decide, by decide, ?_⟩
      have h_956 : Nat.sqrt (956 + 5) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_956]; decide
    · -- n = 957
      use 5
      refine ⟨by decide, by decide, ?_⟩
      have h_957 : Nat.sqrt (957 + 5) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_957]; decide
    · -- n = 958
      use 3
      refine ⟨by decide, by decide, ?_⟩
      have h_958 : Nat.sqrt (958 + 3) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_958]; decide
    · -- n = 959
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_959 : Nat.sqrt (959 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_959]; decide
    · -- n = 960
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_960 : Nat.sqrt (960 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_960]; decide
    · -- n = 961
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_961 : Nat.sqrt (961 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_961]; decide
    · -- n = 962
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_962 : Nat.sqrt (962 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_962]; decide
    · -- n = 963
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_963 : Nat.sqrt (963 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_963]; decide
    · -- n = 964
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_964 : Nat.sqrt (964 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_964]; decide
    · -- n = 965
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_965 : Nat.sqrt (965 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_965]; decide
    · -- n = 966
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_966 : Nat.sqrt (966 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_966]; decide
    · -- n = 967
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_967 : Nat.sqrt (967 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_967]; decide
    · -- n = 968
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_968 : Nat.sqrt (968 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_968]; decide
    · -- n = 969
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_969 : Nat.sqrt (969 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_969]; decide
    · -- n = 970
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_970 : Nat.sqrt (970 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_970]; decide
    · -- n = 971
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_971 : Nat.sqrt (971 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_971]; decide
    · -- n = 972
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_972 : Nat.sqrt (972 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_972]; decide
    · -- n = 973
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_973 : Nat.sqrt (973 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_973]; decide
    · -- n = 974
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_974 : Nat.sqrt (974 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_974]; decide
    · -- n = 975
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_975 : Nat.sqrt (975 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_975]; decide
    · -- n = 976
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_976 : Nat.sqrt (976 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_976]; decide
    · -- n = 977
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_977 : Nat.sqrt (977 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_977]; decide
    · -- n = 978
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_978 : Nat.sqrt (978 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_978]; decide
    · -- n = 979
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_979 : Nat.sqrt (979 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_979]; decide
    · -- n = 980
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_980 : Nat.sqrt (980 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_980]; decide
    · -- n = 981
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_981 : Nat.sqrt (981 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_981]; decide
    · -- n = 982
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_982 : Nat.sqrt (982 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_982]; decide
    · -- n = 983
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_983 : Nat.sqrt (983 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_983]; decide
    · -- n = 984
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_984 : Nat.sqrt (984 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_984]; decide
    · -- n = 985
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_985 : Nat.sqrt (985 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_985]; decide
    · -- n = 986
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_986 : Nat.sqrt (986 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_986]; decide
    · -- n = 987
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_987 : Nat.sqrt (987 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_987]; decide
    · -- n = 988
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_988 : Nat.sqrt (988 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_988]; decide
    · -- n = 989
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_989 : Nat.sqrt (989 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_989]; decide
    · -- n = 990
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_990 : Nat.sqrt (990 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_990]; decide
    · -- n = 991
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_991 : Nat.sqrt (991 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_991]; decide
    · -- n = 992
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_992 : Nat.sqrt (992 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_992]; decide
    · -- n = 993
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_993 : Nat.sqrt (993 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_993]; decide
    · -- n = 994
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_994 : Nat.sqrt (994 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_994]; decide
    · -- n = 995
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_995 : Nat.sqrt (995 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_995]; decide
    · -- n = 996
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_996 : Nat.sqrt (996 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_996]; decide
    · -- n = 997
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_997 : Nat.sqrt (997 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_997]; decide
    · -- n = 998
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_998 : Nat.sqrt (998 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_998]; decide
    · -- n = 999
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_999 : Nat.sqrt (999 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_999]; decide
    · -- n = 1000
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1000 : Nat.sqrt (1000 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1000]; decide
    · -- n = 1001
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1001 : Nat.sqrt (1001 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1001]; decide
    · -- n = 1002
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1002 : Nat.sqrt (1002 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1002]; decide
    · -- n = 1003
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1003 : Nat.sqrt (1003 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1003]; decide
    · -- n = 1004
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1004 : Nat.sqrt (1004 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1004]; decide
    · -- n = 1005
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1005 : Nat.sqrt (1005 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1005]; decide
    · -- n = 1006
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1006 : Nat.sqrt (1006 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1006]; decide
    · -- n = 1007
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1007 : Nat.sqrt (1007 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1007]; decide
    · -- n = 1008
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1008 : Nat.sqrt (1008 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1008]; decide
    · -- n = 1009
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1009 : Nat.sqrt (1009 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1009]; decide
    · -- n = 1010
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1010 : Nat.sqrt (1010 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1010]; decide
    · -- n = 1011
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1011 : Nat.sqrt (1011 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1011]; decide
    · -- n = 1012
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1012 : Nat.sqrt (1012 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1012]; decide
    · -- n = 1013
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1013 : Nat.sqrt (1013 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1013]; decide
    · -- n = 1014
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1014 : Nat.sqrt (1014 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1014]; decide
    · -- n = 1015
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1015 : Nat.sqrt (1015 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1015]; decide
    · -- n = 1016
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1016 : Nat.sqrt (1016 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1016]; decide
    · -- n = 1017
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1017 : Nat.sqrt (1017 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1017]; decide
    · -- n = 1018
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1018 : Nat.sqrt (1018 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1018]; decide
    · -- n = 1019
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1019 : Nat.sqrt (1019 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1019]; decide
    · -- n = 1020
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1020 : Nat.sqrt (1020 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1020]; decide
    · -- n = 1021
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1021 : Nat.sqrt (1021 + 2) = 31 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1021]; decide
    · -- n = 1022
      use 347
      refine ⟨by decide, by decide, ?_⟩
      have h_1022 : Nat.sqrt (1022 + 347) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1022]; decide
    · -- n = 1023
      use 347
      refine ⟨by decide, by decide, ?_⟩
      have h_1023 : Nat.sqrt (1023 + 347) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1023]; decide
    · -- n = 1024
      use 347
      refine ⟨by decide, by decide, ?_⟩
      have h_1024 : Nat.sqrt (1024 + 347) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1024]; decide
    · -- n = 1025
      use 347
      refine ⟨by decide, by decide, ?_⟩
      have h_1025 : Nat.sqrt (1025 + 347) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1025]; decide
    · -- n = 1026
      use 347
      refine ⟨by decide, by decide, ?_⟩
      have h_1026 : Nat.sqrt (1026 + 347) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1026]; decide
    · -- n = 1027
      use 347
      refine ⟨by decide, by decide, ?_⟩
      have h_1027 : Nat.sqrt (1027 + 347) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1027]; decide
    · -- n = 1028
      use 347
      refine ⟨by decide, by decide, ?_⟩
      have h_1028 : Nat.sqrt (1028 + 347) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1028]; decide
    · -- n = 1029
      use 347
      refine ⟨by decide, by decide, ?_⟩
      have h_1029 : Nat.sqrt (1029 + 347) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1029]; decide
    · -- n = 1030
      use 347
      refine ⟨by decide, by decide, ?_⟩
      have h_1030 : Nat.sqrt (1030 + 347) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1030]; decide
    · -- n = 1031
      use 347
      refine ⟨by decide, by decide, ?_⟩
      have h_1031 : Nat.sqrt (1031 + 347) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1031]; decide
    · -- n = 1032
      use 337
      refine ⟨by decide, by decide, ?_⟩
      have h_1032 : Nat.sqrt (1032 + 337) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1032]; decide
    · -- n = 1033
      use 337
      refine ⟨by decide, by decide, ?_⟩
      have h_1033 : Nat.sqrt (1033 + 337) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1033]; decide
    · -- n = 1034
      use 337
      refine ⟨by decide, by decide, ?_⟩
      have h_1034 : Nat.sqrt (1034 + 337) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1034]; decide
    · -- n = 1035
      use 337
      refine ⟨by decide, by decide, ?_⟩
      have h_1035 : Nat.sqrt (1035 + 337) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1035]; decide
    · -- n = 1036
      use 337
      refine ⟨by decide, by decide, ?_⟩
      have h_1036 : Nat.sqrt (1036 + 337) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1036]; decide
    · -- n = 1037
      use 337
      refine ⟨by decide, by decide, ?_⟩
      have h_1037 : Nat.sqrt (1037 + 337) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1037]; decide
    · -- n = 1038
      use 331
      refine ⟨by decide, by decide, ?_⟩
      have h_1038 : Nat.sqrt (1038 + 331) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1038]; decide
    · -- n = 1039
      use 331
      refine ⟨by decide, by decide, ?_⟩
      have h_1039 : Nat.sqrt (1039 + 331) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1039]; decide
    · -- n = 1040
      use 331
      refine ⟨by decide, by decide, ?_⟩
      have h_1040 : Nat.sqrt (1040 + 331) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1040]; decide
    · -- n = 1041
      use 331
      refine ⟨by decide, by decide, ?_⟩
      have h_1041 : Nat.sqrt (1041 + 331) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1041]; decide
    · -- n = 1042
      use 331
      refine ⟨by decide, by decide, ?_⟩
      have h_1042 : Nat.sqrt (1042 + 331) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1042]; decide
    · -- n = 1043
      use 331
      refine ⟨by decide, by decide, ?_⟩
      have h_1043 : Nat.sqrt (1043 + 331) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1043]; decide
    · -- n = 1044
      use 331
      refine ⟨by decide, by decide, ?_⟩
      have h_1044 : Nat.sqrt (1044 + 331) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1044]; decide
    · -- n = 1045
      use 331
      refine ⟨by decide, by decide, ?_⟩
      have h_1045 : Nat.sqrt (1045 + 331) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1045]; decide
    · -- n = 1046
      use 331
      refine ⟨by decide, by decide, ?_⟩
      have h_1046 : Nat.sqrt (1046 + 331) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1046]; decide
    · -- n = 1047
      use 331
      refine ⟨by decide, by decide, ?_⟩
      have h_1047 : Nat.sqrt (1047 + 331) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1047]; decide
    · -- n = 1048
      use 331
      refine ⟨by decide, by decide, ?_⟩
      have h_1048 : Nat.sqrt (1048 + 331) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1048]; decide
    · -- n = 1049
      use 331
      refine ⟨by decide, by decide, ?_⟩
      have h_1049 : Nat.sqrt (1049 + 331) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1049]; decide
    · -- n = 1050
      use 331
      refine ⟨by decide, by decide, ?_⟩
      have h_1050 : Nat.sqrt (1050 + 331) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1050]; decide
    · -- n = 1051
      use 331
      refine ⟨by decide, by decide, ?_⟩
      have h_1051 : Nat.sqrt (1051 + 331) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1051]; decide
    · -- n = 1052
      use 317
      refine ⟨by decide, by decide, ?_⟩
      have h_1052 : Nat.sqrt (1052 + 317) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1052]; decide
    · -- n = 1053
      use 317
      refine ⟨by decide, by decide, ?_⟩
      have h_1053 : Nat.sqrt (1053 + 317) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1053]; decide
    · -- n = 1054
      use 317
      refine ⟨by decide, by decide, ?_⟩
      have h_1054 : Nat.sqrt (1054 + 317) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1054]; decide
    · -- n = 1055
      use 317
      refine ⟨by decide, by decide, ?_⟩
      have h_1055 : Nat.sqrt (1055 + 317) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1055]; decide
    · -- n = 1056
      use 313
      refine ⟨by decide, by decide, ?_⟩
      have h_1056 : Nat.sqrt (1056 + 313) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1056]; decide
    · -- n = 1057
      use 313
      refine ⟨by decide, by decide, ?_⟩
      have h_1057 : Nat.sqrt (1057 + 313) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1057]; decide
    · -- n = 1058
      use 311
      refine ⟨by decide, by decide, ?_⟩
      have h_1058 : Nat.sqrt (1058 + 311) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1058]; decide
    · -- n = 1059
      use 311
      refine ⟨by decide, by decide, ?_⟩
      have h_1059 : Nat.sqrt (1059 + 311) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1059]; decide
    · -- n = 1060
      use 311
      refine ⟨by decide, by decide, ?_⟩
      have h_1060 : Nat.sqrt (1060 + 311) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1060]; decide
    · -- n = 1061
      use 311
      refine ⟨by decide, by decide, ?_⟩
      have h_1061 : Nat.sqrt (1061 + 311) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1061]; decide
    · -- n = 1062
      use 307
      refine ⟨by decide, by decide, ?_⟩
      have h_1062 : Nat.sqrt (1062 + 307) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1062]; decide
    · -- n = 1063
      use 307
      refine ⟨by decide, by decide, ?_⟩
      have h_1063 : Nat.sqrt (1063 + 307) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1063]; decide
    · -- n = 1064
      use 307
      refine ⟨by decide, by decide, ?_⟩
      have h_1064 : Nat.sqrt (1064 + 307) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1064]; decide
    · -- n = 1065
      use 307
      refine ⟨by decide, by decide, ?_⟩
      have h_1065 : Nat.sqrt (1065 + 307) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1065]; decide
    · -- n = 1066
      use 307
      refine ⟨by decide, by decide, ?_⟩
      have h_1066 : Nat.sqrt (1066 + 307) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1066]; decide
    · -- n = 1067
      use 307
      refine ⟨by decide, by decide, ?_⟩
      have h_1067 : Nat.sqrt (1067 + 307) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1067]; decide
    · -- n = 1068
      use 307
      refine ⟨by decide, by decide, ?_⟩
      have h_1068 : Nat.sqrt (1068 + 307) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1068]; decide
    · -- n = 1069
      use 307
      refine ⟨by decide, by decide, ?_⟩
      have h_1069 : Nat.sqrt (1069 + 307) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1069]; decide
    · -- n = 1070
      use 307
      refine ⟨by decide, by decide, ?_⟩
      have h_1070 : Nat.sqrt (1070 + 307) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1070]; decide
    · -- n = 1071
      use 307
      refine ⟨by decide, by decide, ?_⟩
      have h_1071 : Nat.sqrt (1071 + 307) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1071]; decide
    · -- n = 1072
      use 307
      refine ⟨by decide, by decide, ?_⟩
      have h_1072 : Nat.sqrt (1072 + 307) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1072]; decide
    · -- n = 1073
      use 307
      refine ⟨by decide, by decide, ?_⟩
      have h_1073 : Nat.sqrt (1073 + 307) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1073]; decide
    · -- n = 1074
      use 307
      refine ⟨by decide, by decide, ?_⟩
      have h_1074 : Nat.sqrt (1074 + 307) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1074]; decide
    · -- n = 1075
      use 307
      refine ⟨by decide, by decide, ?_⟩
      have h_1075 : Nat.sqrt (1075 + 307) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1075]; decide
    · -- n = 1076
      use 293
      refine ⟨by decide, by decide, ?_⟩
      have h_1076 : Nat.sqrt (1076 + 293) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1076]; decide
    · -- n = 1077
      use 293
      refine ⟨by decide, by decide, ?_⟩
      have h_1077 : Nat.sqrt (1077 + 293) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1077]; decide
    · -- n = 1078
      use 293
      refine ⟨by decide, by decide, ?_⟩
      have h_1078 : Nat.sqrt (1078 + 293) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1078]; decide
    · -- n = 1079
      use 293
      refine ⟨by decide, by decide, ?_⟩
      have h_1079 : Nat.sqrt (1079 + 293) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1079]; decide
    · -- n = 1080
      use 293
      refine ⟨by decide, by decide, ?_⟩
      have h_1080 : Nat.sqrt (1080 + 293) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1080]; decide
    · -- n = 1081
      use 293
      refine ⟨by decide, by decide, ?_⟩
      have h_1081 : Nat.sqrt (1081 + 293) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1081]; decide
    · -- n = 1082
      use 293
      refine ⟨by decide, by decide, ?_⟩
      have h_1082 : Nat.sqrt (1082 + 293) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1082]; decide
    · -- n = 1083
      use 293
      refine ⟨by decide, by decide, ?_⟩
      have h_1083 : Nat.sqrt (1083 + 293) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1083]; decide
    · -- n = 1084
      use 293
      refine ⟨by decide, by decide, ?_⟩
      have h_1084 : Nat.sqrt (1084 + 293) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1084]; decide
    · -- n = 1085
      use 293
      refine ⟨by decide, by decide, ?_⟩
      have h_1085 : Nat.sqrt (1085 + 293) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1085]; decide
    · -- n = 1086
      use 283
      refine ⟨by decide, by decide, ?_⟩
      have h_1086 : Nat.sqrt (1086 + 283) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1086]; decide
    · -- n = 1087
      use 283
      refine ⟨by decide, by decide, ?_⟩
      have h_1087 : Nat.sqrt (1087 + 283) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1087]; decide
    · -- n = 1088
      use 281
      refine ⟨by decide, by decide, ?_⟩
      have h_1088 : Nat.sqrt (1088 + 281) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1088]; decide
    · -- n = 1089
      use 281
      refine ⟨by decide, by decide, ?_⟩
      have h_1089 : Nat.sqrt (1089 + 281) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1089]; decide
    · -- n = 1090
      use 281
      refine ⟨by decide, by decide, ?_⟩
      have h_1090 : Nat.sqrt (1090 + 281) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1090]; decide
    · -- n = 1091
      use 281
      refine ⟨by decide, by decide, ?_⟩
      have h_1091 : Nat.sqrt (1091 + 281) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1091]; decide
    · -- n = 1092
      use 277
      refine ⟨by decide, by decide, ?_⟩
      have h_1092 : Nat.sqrt (1092 + 277) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1092]; decide
    · -- n = 1093
      use 277
      refine ⟨by decide, by decide, ?_⟩
      have h_1093 : Nat.sqrt (1093 + 277) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1093]; decide
    · -- n = 1094
      use 277
      refine ⟨by decide, by decide, ?_⟩
      have h_1094 : Nat.sqrt (1094 + 277) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1094]; decide
    · -- n = 1095
      use 277
      refine ⟨by decide, by decide, ?_⟩
      have h_1095 : Nat.sqrt (1095 + 277) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1095]; decide
    · -- n = 1096
      use 277
      refine ⟨by decide, by decide, ?_⟩
      have h_1096 : Nat.sqrt (1096 + 277) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1096]; decide
    · -- n = 1097
      use 277
      refine ⟨by decide, by decide, ?_⟩
      have h_1097 : Nat.sqrt (1097 + 277) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1097]; decide
    · -- n = 1098
      use 271
      refine ⟨by decide, by decide, ?_⟩
      have h_1098 : Nat.sqrt (1098 + 271) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1098]; decide
    · -- n = 1099
      use 271
      refine ⟨by decide, by decide, ?_⟩
      have h_1099 : Nat.sqrt (1099 + 271) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1099]; decide
    · -- n = 1100
      use 269
      refine ⟨by decide, by decide, ?_⟩
      have h_1100 : Nat.sqrt (1100 + 269) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1100]; decide
    · -- n = 1101
      use 269
      refine ⟨by decide, by decide, ?_⟩
      have h_1101 : Nat.sqrt (1101 + 269) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1101]; decide
    · -- n = 1102
      use 269
      refine ⟨by decide, by decide, ?_⟩
      have h_1102 : Nat.sqrt (1102 + 269) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1102]; decide
    · -- n = 1103
      use 269
      refine ⟨by decide, by decide, ?_⟩
      have h_1103 : Nat.sqrt (1103 + 269) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1103]; decide
    · -- n = 1104
      use 269
      refine ⟨by decide, by decide, ?_⟩
      have h_1104 : Nat.sqrt (1104 + 269) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1104]; decide
    · -- n = 1105
      use 269
      refine ⟨by decide, by decide, ?_⟩
      have h_1105 : Nat.sqrt (1105 + 269) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1105]; decide
    · -- n = 1106
      use 263
      refine ⟨by decide, by decide, ?_⟩
      have h_1106 : Nat.sqrt (1106 + 263) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1106]; decide
    · -- n = 1107
      use 263
      refine ⟨by decide, by decide, ?_⟩
      have h_1107 : Nat.sqrt (1107 + 263) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1107]; decide
    · -- n = 1108
      use 263
      refine ⟨by decide, by decide, ?_⟩
      have h_1108 : Nat.sqrt (1108 + 263) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1108]; decide
    · -- n = 1109
      use 263
      refine ⟨by decide, by decide, ?_⟩
      have h_1109 : Nat.sqrt (1109 + 263) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1109]; decide
    · -- n = 1110
      use 263
      refine ⟨by decide, by decide, ?_⟩
      have h_1110 : Nat.sqrt (1110 + 263) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1110]; decide
    · -- n = 1111
      use 263
      refine ⟨by decide, by decide, ?_⟩
      have h_1111 : Nat.sqrt (1111 + 263) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1111]; decide
    · -- n = 1112
      use 257
      refine ⟨by decide, by decide, ?_⟩
      have h_1112 : Nat.sqrt (1112 + 257) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1112]; decide
    · -- n = 1113
      use 257
      refine ⟨by decide, by decide, ?_⟩
      have h_1113 : Nat.sqrt (1113 + 257) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1113]; decide
    · -- n = 1114
      use 257
      refine ⟨by decide, by decide, ?_⟩
      have h_1114 : Nat.sqrt (1114 + 257) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1114]; decide
    · -- n = 1115
      use 257
      refine ⟨by decide, by decide, ?_⟩
      have h_1115 : Nat.sqrt (1115 + 257) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1115]; decide
    · -- n = 1116
      use 257
      refine ⟨by decide, by decide, ?_⟩
      have h_1116 : Nat.sqrt (1116 + 257) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1116]; decide
    · -- n = 1117
      use 257
      refine ⟨by decide, by decide, ?_⟩
      have h_1117 : Nat.sqrt (1117 + 257) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1117]; decide
    · -- n = 1118
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_1118 : Nat.sqrt (1118 + 251) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1118]; decide
    · -- n = 1119
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_1119 : Nat.sqrt (1119 + 251) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1119]; decide
    · -- n = 1120
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_1120 : Nat.sqrt (1120 + 251) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1120]; decide
    · -- n = 1121
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_1121 : Nat.sqrt (1121 + 251) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1121]; decide
    · -- n = 1122
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_1122 : Nat.sqrt (1122 + 251) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1122]; decide
    · -- n = 1123
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_1123 : Nat.sqrt (1123 + 251) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1123]; decide
    · -- n = 1124
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_1124 : Nat.sqrt (1124 + 251) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1124]; decide
    · -- n = 1125
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_1125 : Nat.sqrt (1125 + 251) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1125]; decide
    · -- n = 1126
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_1126 : Nat.sqrt (1126 + 251) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1126]; decide
    · -- n = 1127
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_1127 : Nat.sqrt (1127 + 251) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1127]; decide
    · -- n = 1128
      use 241
      refine ⟨by decide, by decide, ?_⟩
      have h_1128 : Nat.sqrt (1128 + 241) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1128]; decide
    · -- n = 1129
      use 241
      refine ⟨by decide, by decide, ?_⟩
      have h_1129 : Nat.sqrt (1129 + 241) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1129]; decide
    · -- n = 1130
      use 239
      refine ⟨by decide, by decide, ?_⟩
      have h_1130 : Nat.sqrt (1130 + 239) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1130]; decide
    · -- n = 1131
      use 239
      refine ⟨by decide, by decide, ?_⟩
      have h_1131 : Nat.sqrt (1131 + 239) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1131]; decide
    · -- n = 1132
      use 239
      refine ⟨by decide, by decide, ?_⟩
      have h_1132 : Nat.sqrt (1132 + 239) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1132]; decide
    · -- n = 1133
      use 239
      refine ⟨by decide, by decide, ?_⟩
      have h_1133 : Nat.sqrt (1133 + 239) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1133]; decide
    · -- n = 1134
      use 239
      refine ⟨by decide, by decide, ?_⟩
      have h_1134 : Nat.sqrt (1134 + 239) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1134]; decide
    · -- n = 1135
      use 239
      refine ⟨by decide, by decide, ?_⟩
      have h_1135 : Nat.sqrt (1135 + 239) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1135]; decide
    · -- n = 1136
      use 233
      refine ⟨by decide, by decide, ?_⟩
      have h_1136 : Nat.sqrt (1136 + 233) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1136]; decide
    · -- n = 1137
      use 233
      refine ⟨by decide, by decide, ?_⟩
      have h_1137 : Nat.sqrt (1137 + 233) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1137]; decide
    · -- n = 1138
      use 233
      refine ⟨by decide, by decide, ?_⟩
      have h_1138 : Nat.sqrt (1138 + 233) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1138]; decide
    · -- n = 1139
      use 233
      refine ⟨by decide, by decide, ?_⟩
      have h_1139 : Nat.sqrt (1139 + 233) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1139]; decide
    · -- n = 1140
      use 229
      refine ⟨by decide, by decide, ?_⟩
      have h_1140 : Nat.sqrt (1140 + 229) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1140]; decide
    · -- n = 1141
      use 229
      refine ⟨by decide, by decide, ?_⟩
      have h_1141 : Nat.sqrt (1141 + 229) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1141]; decide
    · -- n = 1142
      use 227
      refine ⟨by decide, by decide, ?_⟩
      have h_1142 : Nat.sqrt (1142 + 227) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1142]; decide
    · -- n = 1143
      use 227
      refine ⟨by decide, by decide, ?_⟩
      have h_1143 : Nat.sqrt (1143 + 227) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1143]; decide
    · -- n = 1144
      use 227
      refine ⟨by decide, by decide, ?_⟩
      have h_1144 : Nat.sqrt (1144 + 227) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1144]; decide
    · -- n = 1145
      use 227
      refine ⟨by decide, by decide, ?_⟩
      have h_1145 : Nat.sqrt (1145 + 227) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1145]; decide
    · -- n = 1146
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_1146 : Nat.sqrt (1146 + 223) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1146]; decide
    · -- n = 1147
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_1147 : Nat.sqrt (1147 + 223) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1147]; decide
    · -- n = 1148
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_1148 : Nat.sqrt (1148 + 223) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1148]; decide
    · -- n = 1149
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_1149 : Nat.sqrt (1149 + 223) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1149]; decide
    · -- n = 1150
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_1150 : Nat.sqrt (1150 + 223) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1150]; decide
    · -- n = 1151
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_1151 : Nat.sqrt (1151 + 223) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1151]; decide
    · -- n = 1152
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_1152 : Nat.sqrt (1152 + 223) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1152]; decide
    · -- n = 1153
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_1153 : Nat.sqrt (1153 + 223) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1153]; decide
    · -- n = 1154
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_1154 : Nat.sqrt (1154 + 223) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1154]; decide
    · -- n = 1155
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_1155 : Nat.sqrt (1155 + 223) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1155]; decide
    · -- n = 1156
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_1156 : Nat.sqrt (1156 + 223) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1156]; decide
    · -- n = 1157
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_1157 : Nat.sqrt (1157 + 223) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1157]; decide
    · -- n = 1158
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_1158 : Nat.sqrt (1158 + 211) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1158]; decide
    · -- n = 1159
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_1159 : Nat.sqrt (1159 + 211) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1159]; decide
    · -- n = 1160
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_1160 : Nat.sqrt (1160 + 211) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1160]; decide
    · -- n = 1161
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_1161 : Nat.sqrt (1161 + 211) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1161]; decide
    · -- n = 1162
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_1162 : Nat.sqrt (1162 + 211) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1162]; decide
    · -- n = 1163
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_1163 : Nat.sqrt (1163 + 211) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1163]; decide
    · -- n = 1164
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_1164 : Nat.sqrt (1164 + 211) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1164]; decide
    · -- n = 1165
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_1165 : Nat.sqrt (1165 + 211) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1165]; decide
    · -- n = 1166
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_1166 : Nat.sqrt (1166 + 211) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1166]; decide
    · -- n = 1167
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_1167 : Nat.sqrt (1167 + 211) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1167]; decide
    · -- n = 1168
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_1168 : Nat.sqrt (1168 + 211) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1168]; decide
    · -- n = 1169
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_1169 : Nat.sqrt (1169 + 211) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1169]; decide
    · -- n = 1170
      use 199
      refine ⟨by decide, by decide, ?_⟩
      have h_1170 : Nat.sqrt (1170 + 199) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1170]; decide
    · -- n = 1171
      use 199
      refine ⟨by decide, by decide, ?_⟩
      have h_1171 : Nat.sqrt (1171 + 199) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1171]; decide
    · -- n = 1172
      use 197
      refine ⟨by decide, by decide, ?_⟩
      have h_1172 : Nat.sqrt (1172 + 197) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1172]; decide
    · -- n = 1173
      use 197
      refine ⟨by decide, by decide, ?_⟩
      have h_1173 : Nat.sqrt (1173 + 197) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1173]; decide
    · -- n = 1174
      use 197
      refine ⟨by decide, by decide, ?_⟩
      have h_1174 : Nat.sqrt (1174 + 197) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1174]; decide
    · -- n = 1175
      use 197
      refine ⟨by decide, by decide, ?_⟩
      have h_1175 : Nat.sqrt (1175 + 197) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1175]; decide
    · -- n = 1176
      use 193
      refine ⟨by decide, by decide, ?_⟩
      have h_1176 : Nat.sqrt (1176 + 193) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1176]; decide
    · -- n = 1177
      use 193
      refine ⟨by decide, by decide, ?_⟩
      have h_1177 : Nat.sqrt (1177 + 193) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1177]; decide
    · -- n = 1178
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_1178 : Nat.sqrt (1178 + 191) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1178]; decide
    · -- n = 1179
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_1179 : Nat.sqrt (1179 + 191) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1179]; decide
    · -- n = 1180
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_1180 : Nat.sqrt (1180 + 191) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1180]; decide
    · -- n = 1181
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_1181 : Nat.sqrt (1181 + 191) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1181]; decide
    · -- n = 1182
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_1182 : Nat.sqrt (1182 + 191) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1182]; decide
    · -- n = 1183
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_1183 : Nat.sqrt (1183 + 191) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1183]; decide
    · -- n = 1184
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_1184 : Nat.sqrt (1184 + 191) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1184]; decide
    · -- n = 1185
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_1185 : Nat.sqrt (1185 + 191) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1185]; decide
    · -- n = 1186
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_1186 : Nat.sqrt (1186 + 191) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1186]; decide
    · -- n = 1187
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_1187 : Nat.sqrt (1187 + 191) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1187]; decide
    · -- n = 1188
      use 181
      refine ⟨by decide, by decide, ?_⟩
      have h_1188 : Nat.sqrt (1188 + 181) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1188]; decide
    · -- n = 1189
      use 181
      refine ⟨by decide, by decide, ?_⟩
      have h_1189 : Nat.sqrt (1189 + 181) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1189]; decide
    · -- n = 1190
      use 179
      refine ⟨by decide, by decide, ?_⟩
      have h_1190 : Nat.sqrt (1190 + 179) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1190]; decide
    · -- n = 1191
      use 179
      refine ⟨by decide, by decide, ?_⟩
      have h_1191 : Nat.sqrt (1191 + 179) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1191]; decide
    · -- n = 1192
      use 179
      refine ⟨by decide, by decide, ?_⟩
      have h_1192 : Nat.sqrt (1192 + 179) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1192]; decide
    · -- n = 1193
      use 179
      refine ⟨by decide, by decide, ?_⟩
      have h_1193 : Nat.sqrt (1193 + 179) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1193]; decide
    · -- n = 1194
      use 179
      refine ⟨by decide, by decide, ?_⟩
      have h_1194 : Nat.sqrt (1194 + 179) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1194]; decide
    · -- n = 1195
      use 179
      refine ⟨by decide, by decide, ?_⟩
      have h_1195 : Nat.sqrt (1195 + 179) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1195]; decide
    · -- n = 1196
      use 173
      refine ⟨by decide, by decide, ?_⟩
      have h_1196 : Nat.sqrt (1196 + 173) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1196]; decide
    · -- n = 1197
      use 173
      refine ⟨by decide, by decide, ?_⟩
      have h_1197 : Nat.sqrt (1197 + 173) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1197]; decide
    · -- n = 1198
      use 173
      refine ⟨by decide, by decide, ?_⟩
      have h_1198 : Nat.sqrt (1198 + 173) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1198]; decide
    · -- n = 1199
      use 173
      refine ⟨by decide, by decide, ?_⟩
      have h_1199 : Nat.sqrt (1199 + 173) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1199]; decide
    · -- n = 1200
      use 173
      refine ⟨by decide, by decide, ?_⟩
      have h_1200 : Nat.sqrt (1200 + 173) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1200]; decide
    · -- n = 1201
      use 173
      refine ⟨by decide, by decide, ?_⟩
      have h_1201 : Nat.sqrt (1201 + 173) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1201]; decide
    · -- n = 1202
      use 167
      refine ⟨by decide, by decide, ?_⟩
      have h_1202 : Nat.sqrt (1202 + 167) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1202]; decide
    · -- n = 1203
      use 167
      refine ⟨by decide, by decide, ?_⟩
      have h_1203 : Nat.sqrt (1203 + 167) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1203]; decide
    · -- n = 1204
      use 167
      refine ⟨by decide, by decide, ?_⟩
      have h_1204 : Nat.sqrt (1204 + 167) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1204]; decide
    · -- n = 1205
      use 167
      refine ⟨by decide, by decide, ?_⟩
      have h_1205 : Nat.sqrt (1205 + 167) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1205]; decide
    · -- n = 1206
      use 163
      refine ⟨by decide, by decide, ?_⟩
      have h_1206 : Nat.sqrt (1206 + 163) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1206]; decide
    · -- n = 1207
      use 163
      refine ⟨by decide, by decide, ?_⟩
      have h_1207 : Nat.sqrt (1207 + 163) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1207]; decide
    · -- n = 1208
      use 163
      refine ⟨by decide, by decide, ?_⟩
      have h_1208 : Nat.sqrt (1208 + 163) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1208]; decide
    · -- n = 1209
      use 163
      refine ⟨by decide, by decide, ?_⟩
      have h_1209 : Nat.sqrt (1209 + 163) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1209]; decide
    · -- n = 1210
      use 163
      refine ⟨by decide, by decide, ?_⟩
      have h_1210 : Nat.sqrt (1210 + 163) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1210]; decide
    · -- n = 1211
      use 163
      refine ⟨by decide, by decide, ?_⟩
      have h_1211 : Nat.sqrt (1211 + 163) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1211]; decide
    · -- n = 1212
      use 157
      refine ⟨by decide, by decide, ?_⟩
      have h_1212 : Nat.sqrt (1212 + 157) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1212]; decide
    · -- n = 1213
      use 157
      refine ⟨by decide, by decide, ?_⟩
      have h_1213 : Nat.sqrt (1213 + 157) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1213]; decide
    · -- n = 1214
      use 157
      refine ⟨by decide, by decide, ?_⟩
      have h_1214 : Nat.sqrt (1214 + 157) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1214]; decide
    · -- n = 1215
      use 157
      refine ⟨by decide, by decide, ?_⟩
      have h_1215 : Nat.sqrt (1215 + 157) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1215]; decide
    · -- n = 1216
      use 157
      refine ⟨by decide, by decide, ?_⟩
      have h_1216 : Nat.sqrt (1216 + 157) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1216]; decide
    · -- n = 1217
      use 157
      refine ⟨by decide, by decide, ?_⟩
      have h_1217 : Nat.sqrt (1217 + 157) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1217]; decide
    · -- n = 1218
      use 151
      refine ⟨by decide, by decide, ?_⟩
      have h_1218 : Nat.sqrt (1218 + 151) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1218]; decide
    · -- n = 1219
      use 151
      refine ⟨by decide, by decide, ?_⟩
      have h_1219 : Nat.sqrt (1219 + 151) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1219]; decide
    · -- n = 1220
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_1220 : Nat.sqrt (1220 + 149) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1220]; decide
    · -- n = 1221
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_1221 : Nat.sqrt (1221 + 149) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1221]; decide
    · -- n = 1222
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_1222 : Nat.sqrt (1222 + 149) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1222]; decide
    · -- n = 1223
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_1223 : Nat.sqrt (1223 + 149) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1223]; decide
    · -- n = 1224
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_1224 : Nat.sqrt (1224 + 149) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1224]; decide
    · -- n = 1225
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_1225 : Nat.sqrt (1225 + 149) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1225]; decide
    · -- n = 1226
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_1226 : Nat.sqrt (1226 + 149) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1226]; decide
    · -- n = 1227
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_1227 : Nat.sqrt (1227 + 149) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1227]; decide
    · -- n = 1228
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_1228 : Nat.sqrt (1228 + 149) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1228]; decide
    · -- n = 1229
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_1229 : Nat.sqrt (1229 + 149) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1229]; decide
    · -- n = 1230
      use 139
      refine ⟨by decide, by decide, ?_⟩
      have h_1230 : Nat.sqrt (1230 + 139) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1230]; decide
    · -- n = 1231
      use 139
      refine ⟨by decide, by decide, ?_⟩
      have h_1231 : Nat.sqrt (1231 + 139) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1231]; decide
    · -- n = 1232
      use 137
      refine ⟨by decide, by decide, ?_⟩
      have h_1232 : Nat.sqrt (1232 + 137) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1232]; decide
    · -- n = 1233
      use 137
      refine ⟨by decide, by decide, ?_⟩
      have h_1233 : Nat.sqrt (1233 + 137) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1233]; decide
    · -- n = 1234
      use 137
      refine ⟨by decide, by decide, ?_⟩
      have h_1234 : Nat.sqrt (1234 + 137) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1234]; decide
    · -- n = 1235
      use 137
      refine ⟨by decide, by decide, ?_⟩
      have h_1235 : Nat.sqrt (1235 + 137) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1235]; decide
    · -- n = 1236
      use 137
      refine ⟨by decide, by decide, ?_⟩
      have h_1236 : Nat.sqrt (1236 + 137) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1236]; decide
    · -- n = 1237
      use 137
      refine ⟨by decide, by decide, ?_⟩
      have h_1237 : Nat.sqrt (1237 + 137) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1237]; decide
    · -- n = 1238
      use 131
      refine ⟨by decide, by decide, ?_⟩
      have h_1238 : Nat.sqrt (1238 + 131) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1238]; decide
    · -- n = 1239
      use 131
      refine ⟨by decide, by decide, ?_⟩
      have h_1239 : Nat.sqrt (1239 + 131) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1239]; decide
    · -- n = 1240
      use 131
      refine ⟨by decide, by decide, ?_⟩
      have h_1240 : Nat.sqrt (1240 + 131) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1240]; decide
    · -- n = 1241
      use 131
      refine ⟨by decide, by decide, ?_⟩
      have h_1241 : Nat.sqrt (1241 + 131) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1241]; decide
    · -- n = 1242
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_1242 : Nat.sqrt (1242 + 127) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1242]; decide
    · -- n = 1243
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_1243 : Nat.sqrt (1243 + 127) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1243]; decide
    · -- n = 1244
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_1244 : Nat.sqrt (1244 + 127) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1244]; decide
    · -- n = 1245
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_1245 : Nat.sqrt (1245 + 127) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1245]; decide
    · -- n = 1246
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_1246 : Nat.sqrt (1246 + 127) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1246]; decide
    · -- n = 1247
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_1247 : Nat.sqrt (1247 + 127) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1247]; decide
    · -- n = 1248
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_1248 : Nat.sqrt (1248 + 127) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1248]; decide
    · -- n = 1249
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_1249 : Nat.sqrt (1249 + 127) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1249]; decide
    · -- n = 1250
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_1250 : Nat.sqrt (1250 + 127) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1250]; decide
    · -- n = 1251
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_1251 : Nat.sqrt (1251 + 127) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1251]; decide
    · -- n = 1252
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_1252 : Nat.sqrt (1252 + 127) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1252]; decide
    · -- n = 1253
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_1253 : Nat.sqrt (1253 + 127) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1253]; decide
    · -- n = 1254
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_1254 : Nat.sqrt (1254 + 127) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1254]; decide
    · -- n = 1255
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_1255 : Nat.sqrt (1255 + 127) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1255]; decide
    · -- n = 1256
      use 113
      refine ⟨by decide, by decide, ?_⟩
      have h_1256 : Nat.sqrt (1256 + 113) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1256]; decide
    · -- n = 1257
      use 113
      refine ⟨by decide, by decide, ?_⟩
      have h_1257 : Nat.sqrt (1257 + 113) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1257]; decide
    · -- n = 1258
      use 113
      refine ⟨by decide, by decide, ?_⟩
      have h_1258 : Nat.sqrt (1258 + 113) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1258]; decide
    · -- n = 1259
      use 113
      refine ⟨by decide, by decide, ?_⟩
      have h_1259 : Nat.sqrt (1259 + 113) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1259]; decide
    · -- n = 1260
      use 109
      refine ⟨by decide, by decide, ?_⟩
      have h_1260 : Nat.sqrt (1260 + 109) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1260]; decide
    · -- n = 1261
      use 109
      refine ⟨by decide, by decide, ?_⟩
      have h_1261 : Nat.sqrt (1261 + 109) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1261]; decide
    · -- n = 1262
      use 107
      refine ⟨by decide, by decide, ?_⟩
      have h_1262 : Nat.sqrt (1262 + 107) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1262]; decide
    · -- n = 1263
      use 107
      refine ⟨by decide, by decide, ?_⟩
      have h_1263 : Nat.sqrt (1263 + 107) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1263]; decide
    · -- n = 1264
      use 107
      refine ⟨by decide, by decide, ?_⟩
      have h_1264 : Nat.sqrt (1264 + 107) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1264]; decide
    · -- n = 1265
      use 107
      refine ⟨by decide, by decide, ?_⟩
      have h_1265 : Nat.sqrt (1265 + 107) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1265]; decide
    · -- n = 1266
      use 103
      refine ⟨by decide, by decide, ?_⟩
      have h_1266 : Nat.sqrt (1266 + 103) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1266]; decide
    · -- n = 1267
      use 103
      refine ⟨by decide, by decide, ?_⟩
      have h_1267 : Nat.sqrt (1267 + 103) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1267]; decide
    · -- n = 1268
      use 101
      refine ⟨by decide, by decide, ?_⟩
      have h_1268 : Nat.sqrt (1268 + 101) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1268]; decide
    · -- n = 1269
      use 101
      refine ⟨by decide, by decide, ?_⟩
      have h_1269 : Nat.sqrt (1269 + 101) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1269]; decide
    · -- n = 1270
      use 101
      refine ⟨by decide, by decide, ?_⟩
      have h_1270 : Nat.sqrt (1270 + 101) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1270]; decide
    · -- n = 1271
      use 101
      refine ⟨by decide, by decide, ?_⟩
      have h_1271 : Nat.sqrt (1271 + 101) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1271]; decide
    · -- n = 1272
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_1272 : Nat.sqrt (1272 + 97) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1272]; decide
    · -- n = 1273
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_1273 : Nat.sqrt (1273 + 97) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1273]; decide
    · -- n = 1274
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_1274 : Nat.sqrt (1274 + 97) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1274]; decide
    · -- n = 1275
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_1275 : Nat.sqrt (1275 + 97) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1275]; decide
    · -- n = 1276
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_1276 : Nat.sqrt (1276 + 97) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1276]; decide
    · -- n = 1277
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_1277 : Nat.sqrt (1277 + 97) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1277]; decide
    · -- n = 1278
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_1278 : Nat.sqrt (1278 + 97) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1278]; decide
    · -- n = 1279
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_1279 : Nat.sqrt (1279 + 97) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1279]; decide
    · -- n = 1280
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_1280 : Nat.sqrt (1280 + 89) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1280]; decide
    · -- n = 1281
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_1281 : Nat.sqrt (1281 + 89) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1281]; decide
    · -- n = 1282
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_1282 : Nat.sqrt (1282 + 89) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1282]; decide
    · -- n = 1283
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_1283 : Nat.sqrt (1283 + 89) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1283]; decide
    · -- n = 1284
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_1284 : Nat.sqrt (1284 + 89) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1284]; decide
    · -- n = 1285
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_1285 : Nat.sqrt (1285 + 89) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1285]; decide
    · -- n = 1286
      use 83
      refine ⟨by decide, by decide, ?_⟩
      have h_1286 : Nat.sqrt (1286 + 83) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1286]; decide
    · -- n = 1287
      use 83
      refine ⟨by decide, by decide, ?_⟩
      have h_1287 : Nat.sqrt (1287 + 83) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1287]; decide
    · -- n = 1288
      use 83
      refine ⟨by decide, by decide, ?_⟩
      have h_1288 : Nat.sqrt (1288 + 83) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1288]; decide
    · -- n = 1289
      use 83
      refine ⟨by decide, by decide, ?_⟩
      have h_1289 : Nat.sqrt (1289 + 83) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1289]; decide
    · -- n = 1290
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_1290 : Nat.sqrt (1290 + 79) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1290]; decide
    · -- n = 1291
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_1291 : Nat.sqrt (1291 + 79) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1291]; decide
    · -- n = 1292
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_1292 : Nat.sqrt (1292 + 79) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1292]; decide
    · -- n = 1293
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_1293 : Nat.sqrt (1293 + 79) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1293]; decide
    · -- n = 1294
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_1294 : Nat.sqrt (1294 + 79) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1294]; decide
    · -- n = 1295
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_1295 : Nat.sqrt (1295 + 79) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1295]; decide
    · -- n = 1296
      use 73
      refine ⟨by decide, by decide, ?_⟩
      have h_1296 : Nat.sqrt (1296 + 73) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1296]; decide
    · -- n = 1297
      use 73
      refine ⟨by decide, by decide, ?_⟩
      have h_1297 : Nat.sqrt (1297 + 73) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1297]; decide
    · -- n = 1298
      use 71
      refine ⟨by decide, by decide, ?_⟩
      have h_1298 : Nat.sqrt (1298 + 71) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1298]; decide
    · -- n = 1299
      use 71
      refine ⟨by decide, by decide, ?_⟩
      have h_1299 : Nat.sqrt (1299 + 71) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1299]; decide
    · -- n = 1300
      use 71
      refine ⟨by decide, by decide, ?_⟩
      have h_1300 : Nat.sqrt (1300 + 71) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1300]; decide
    · -- n = 1301
      use 71
      refine ⟨by decide, by decide, ?_⟩
      have h_1301 : Nat.sqrt (1301 + 71) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1301]; decide
    · -- n = 1302
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_1302 : Nat.sqrt (1302 + 67) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1302]; decide
    · -- n = 1303
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_1303 : Nat.sqrt (1303 + 67) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1303]; decide
    · -- n = 1304
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_1304 : Nat.sqrt (1304 + 67) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1304]; decide
    · -- n = 1305
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_1305 : Nat.sqrt (1305 + 67) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1305]; decide
    · -- n = 1306
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_1306 : Nat.sqrt (1306 + 67) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1306]; decide
    · -- n = 1307
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_1307 : Nat.sqrt (1307 + 67) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1307]; decide
    · -- n = 1308
      use 61
      refine ⟨by decide, by decide, ?_⟩
      have h_1308 : Nat.sqrt (1308 + 61) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1308]; decide
    · -- n = 1309
      use 61
      refine ⟨by decide, by decide, ?_⟩
      have h_1309 : Nat.sqrt (1309 + 61) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1309]; decide
    · -- n = 1310
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_1310 : Nat.sqrt (1310 + 59) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1310]; decide
    · -- n = 1311
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_1311 : Nat.sqrt (1311 + 59) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1311]; decide
    · -- n = 1312
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_1312 : Nat.sqrt (1312 + 59) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1312]; decide
    · -- n = 1313
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_1313 : Nat.sqrt (1313 + 59) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1313]; decide
    · -- n = 1314
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_1314 : Nat.sqrt (1314 + 59) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1314]; decide
    · -- n = 1315
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_1315 : Nat.sqrt (1315 + 59) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1315]; decide
    · -- n = 1316
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_1316 : Nat.sqrt (1316 + 53) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1316]; decide
    · -- n = 1317
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_1317 : Nat.sqrt (1317 + 53) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1317]; decide
    · -- n = 1318
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_1318 : Nat.sqrt (1318 + 53) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1318]; decide
    · -- n = 1319
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_1319 : Nat.sqrt (1319 + 53) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1319]; decide
    · -- n = 1320
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_1320 : Nat.sqrt (1320 + 53) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1320]; decide
    · -- n = 1321
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_1321 : Nat.sqrt (1321 + 53) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1321]; decide
    · -- n = 1322
      use 47
      refine ⟨by decide, by decide, ?_⟩
      have h_1322 : Nat.sqrt (1322 + 47) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1322]; decide
    · -- n = 1323
      use 47
      refine ⟨by decide, by decide, ?_⟩
      have h_1323 : Nat.sqrt (1323 + 47) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1323]; decide
    · -- n = 1324
      use 47
      refine ⟨by decide, by decide, ?_⟩
      have h_1324 : Nat.sqrt (1324 + 47) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1324]; decide
    · -- n = 1325
      use 47
      refine ⟨by decide, by decide, ?_⟩
      have h_1325 : Nat.sqrt (1325 + 47) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1325]; decide
    · -- n = 1326
      use 43
      refine ⟨by decide, by decide, ?_⟩
      have h_1326 : Nat.sqrt (1326 + 43) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1326]; decide
    · -- n = 1327
      use 43
      refine ⟨by decide, by decide, ?_⟩
      have h_1327 : Nat.sqrt (1327 + 43) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1327]; decide
    · -- n = 1328
      use 41
      refine ⟨by decide, by decide, ?_⟩
      have h_1328 : Nat.sqrt (1328 + 41) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1328]; decide
    · -- n = 1329
      use 41
      refine ⟨by decide, by decide, ?_⟩
      have h_1329 : Nat.sqrt (1329 + 41) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1329]; decide
    · -- n = 1330
      use 41
      refine ⟨by decide, by decide, ?_⟩
      have h_1330 : Nat.sqrt (1330 + 41) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1330]; decide
    · -- n = 1331
      use 41
      refine ⟨by decide, by decide, ?_⟩
      have h_1331 : Nat.sqrt (1331 + 41) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1331]; decide
    · -- n = 1332
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_1332 : Nat.sqrt (1332 + 37) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1332]; decide
    · -- n = 1333
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_1333 : Nat.sqrt (1333 + 37) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1333]; decide
    · -- n = 1334
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_1334 : Nat.sqrt (1334 + 37) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1334]; decide
    · -- n = 1335
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_1335 : Nat.sqrt (1335 + 37) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1335]; decide
    · -- n = 1336
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_1336 : Nat.sqrt (1336 + 37) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1336]; decide
    · -- n = 1337
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_1337 : Nat.sqrt (1337 + 37) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1337]; decide
    · -- n = 1338
      use 31
      refine ⟨by decide, by decide, ?_⟩
      have h_1338 : Nat.sqrt (1338 + 31) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1338]; decide
    · -- n = 1339
      use 31
      refine ⟨by decide, by decide, ?_⟩
      have h_1339 : Nat.sqrt (1339 + 31) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1339]; decide
    · -- n = 1340
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_1340 : Nat.sqrt (1340 + 29) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1340]; decide
    · -- n = 1341
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_1341 : Nat.sqrt (1341 + 29) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1341]; decide
    · -- n = 1342
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_1342 : Nat.sqrt (1342 + 29) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1342]; decide
    · -- n = 1343
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_1343 : Nat.sqrt (1343 + 29) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1343]; decide
    · -- n = 1344
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_1344 : Nat.sqrt (1344 + 29) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1344]; decide
    · -- n = 1345
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_1345 : Nat.sqrt (1345 + 29) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1345]; decide
    · -- n = 1346
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_1346 : Nat.sqrt (1346 + 23) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1346]; decide
    · -- n = 1347
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_1347 : Nat.sqrt (1347 + 23) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1347]; decide
    · -- n = 1348
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_1348 : Nat.sqrt (1348 + 23) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1348]; decide
    · -- n = 1349
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_1349 : Nat.sqrt (1349 + 23) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1349]; decide
    · -- n = 1350
      use 19
      refine ⟨by decide, by decide, ?_⟩
      have h_1350 : Nat.sqrt (1350 + 19) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1350]; decide
    · -- n = 1351
      use 19
      refine ⟨by decide, by decide, ?_⟩
      have h_1351 : Nat.sqrt (1351 + 19) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1351]; decide
    · -- n = 1352
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_1352 : Nat.sqrt (1352 + 17) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1352]; decide
    · -- n = 1353
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_1353 : Nat.sqrt (1353 + 17) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1353]; decide
    · -- n = 1354
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_1354 : Nat.sqrt (1354 + 17) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1354]; decide
    · -- n = 1355
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_1355 : Nat.sqrt (1355 + 17) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1355]; decide
    · -- n = 1356
      use 13
      refine ⟨by decide, by decide, ?_⟩
      have h_1356 : Nat.sqrt (1356 + 13) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1356]; decide
    · -- n = 1357
      use 13
      refine ⟨by decide, by decide, ?_⟩
      have h_1357 : Nat.sqrt (1357 + 13) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1357]; decide
    · -- n = 1358
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_1358 : Nat.sqrt (1358 + 11) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1358]; decide
    · -- n = 1359
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_1359 : Nat.sqrt (1359 + 11) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1359]; decide
    · -- n = 1360
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_1360 : Nat.sqrt (1360 + 11) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1360]; decide
    · -- n = 1361
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_1361 : Nat.sqrt (1361 + 11) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1361]; decide
    · -- n = 1362
      use 7
      refine ⟨by decide, by decide, ?_⟩
      have h_1362 : Nat.sqrt (1362 + 7) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1362]; decide
    · -- n = 1363
      use 7
      refine ⟨by decide, by decide, ?_⟩
      have h_1363 : Nat.sqrt (1363 + 7) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1363]; decide
    · -- n = 1364
      use 5
      refine ⟨by decide, by decide, ?_⟩
      have h_1364 : Nat.sqrt (1364 + 5) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1364]; decide
    · -- n = 1365
      use 5
      refine ⟨by decide, by decide, ?_⟩
      have h_1365 : Nat.sqrt (1365 + 5) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1365]; decide
    · -- n = 1366
      use 3
      refine ⟨by decide, by decide, ?_⟩
      have h_1366 : Nat.sqrt (1366 + 3) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1366]; decide
    · -- n = 1367
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1367 : Nat.sqrt (1367 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1367]; decide
    · -- n = 1368
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1368 : Nat.sqrt (1368 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1368]; decide
    · -- n = 1369
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1369 : Nat.sqrt (1369 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1369]; decide
    · -- n = 1370
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1370 : Nat.sqrt (1370 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1370]; decide
    · -- n = 1371
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1371 : Nat.sqrt (1371 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1371]; decide
    · -- n = 1372
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1372 : Nat.sqrt (1372 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1372]; decide
    · -- n = 1373
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1373 : Nat.sqrt (1373 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1373]; decide
    · -- n = 1374
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1374 : Nat.sqrt (1374 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1374]; decide
    · -- n = 1375
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1375 : Nat.sqrt (1375 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1375]; decide
    · -- n = 1376
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1376 : Nat.sqrt (1376 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1376]; decide
    · -- n = 1377
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1377 : Nat.sqrt (1377 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1377]; decide
    · -- n = 1378
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1378 : Nat.sqrt (1378 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1378]; decide
    · -- n = 1379
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1379 : Nat.sqrt (1379 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1379]; decide
    · -- n = 1380
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1380 : Nat.sqrt (1380 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1380]; decide
    · -- n = 1381
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1381 : Nat.sqrt (1381 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1381]; decide
    · -- n = 1382
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1382 : Nat.sqrt (1382 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1382]; decide
    · -- n = 1383
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1383 : Nat.sqrt (1383 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1383]; decide
    · -- n = 1384
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1384 : Nat.sqrt (1384 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1384]; decide
    · -- n = 1385
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1385 : Nat.sqrt (1385 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1385]; decide
    · -- n = 1386
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1386 : Nat.sqrt (1386 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1386]; decide
    · -- n = 1387
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1387 : Nat.sqrt (1387 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1387]; decide
    · -- n = 1388
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1388 : Nat.sqrt (1388 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1388]; decide
    · -- n = 1389
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1389 : Nat.sqrt (1389 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1389]; decide
    · -- n = 1390
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1390 : Nat.sqrt (1390 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1390]; decide
    · -- n = 1391
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1391 : Nat.sqrt (1391 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1391]; decide
    · -- n = 1392
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1392 : Nat.sqrt (1392 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1392]; decide
    · -- n = 1393
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1393 : Nat.sqrt (1393 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1393]; decide
    · -- n = 1394
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1394 : Nat.sqrt (1394 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1394]; decide
    · -- n = 1395
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1395 : Nat.sqrt (1395 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1395]; decide
    · -- n = 1396
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1396 : Nat.sqrt (1396 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1396]; decide
    · -- n = 1397
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1397 : Nat.sqrt (1397 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1397]; decide
    · -- n = 1398
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1398 : Nat.sqrt (1398 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1398]; decide
    · -- n = 1399
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1399 : Nat.sqrt (1399 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1399]; decide
    · -- n = 1400
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1400 : Nat.sqrt (1400 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1400]; decide
    · -- n = 1401
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1401 : Nat.sqrt (1401 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1401]; decide
    · -- n = 1402
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1402 : Nat.sqrt (1402 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1402]; decide
    · -- n = 1403
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1403 : Nat.sqrt (1403 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1403]; decide
    · -- n = 1404
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1404 : Nat.sqrt (1404 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1404]; decide
    · -- n = 1405
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1405 : Nat.sqrt (1405 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1405]; decide
    · -- n = 1406
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1406 : Nat.sqrt (1406 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1406]; decide
    · -- n = 1407
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1407 : Nat.sqrt (1407 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1407]; decide
    · -- n = 1408
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1408 : Nat.sqrt (1408 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1408]; decide
    · -- n = 1409
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1409 : Nat.sqrt (1409 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1409]; decide
    · -- n = 1410
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1410 : Nat.sqrt (1410 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1410]; decide
    · -- n = 1411
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1411 : Nat.sqrt (1411 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1411]; decide
    · -- n = 1412
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1412 : Nat.sqrt (1412 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1412]; decide
    · -- n = 1413
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1413 : Nat.sqrt (1413 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1413]; decide
    · -- n = 1414
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1414 : Nat.sqrt (1414 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1414]; decide
    · -- n = 1415
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1415 : Nat.sqrt (1415 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1415]; decide
    · -- n = 1416
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1416 : Nat.sqrt (1416 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1416]; decide
    · -- n = 1417
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1417 : Nat.sqrt (1417 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1417]; decide
    · -- n = 1418
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1418 : Nat.sqrt (1418 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1418]; decide
    · -- n = 1419
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1419 : Nat.sqrt (1419 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1419]; decide
    · -- n = 1420
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1420 : Nat.sqrt (1420 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1420]; decide
    · -- n = 1421
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1421 : Nat.sqrt (1421 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1421]; decide
    · -- n = 1422
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1422 : Nat.sqrt (1422 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1422]; decide
    · -- n = 1423
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1423 : Nat.sqrt (1423 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1423]; decide
    · -- n = 1424
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1424 : Nat.sqrt (1424 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1424]; decide
    · -- n = 1425
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1425 : Nat.sqrt (1425 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1425]; decide
    · -- n = 1426
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1426 : Nat.sqrt (1426 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1426]; decide
    · -- n = 1427
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1427 : Nat.sqrt (1427 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1427]; decide
    · -- n = 1428
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1428 : Nat.sqrt (1428 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1428]; decide
    · -- n = 1429
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1429 : Nat.sqrt (1429 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1429]; decide
    · -- n = 1430
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1430 : Nat.sqrt (1430 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1430]; decide
    · -- n = 1431
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1431 : Nat.sqrt (1431 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1431]; decide
    · -- n = 1432
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1432 : Nat.sqrt (1432 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1432]; decide
    · -- n = 1433
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1433 : Nat.sqrt (1433 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1433]; decide
    · -- n = 1434
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1434 : Nat.sqrt (1434 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1434]; decide
    · -- n = 1435
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1435 : Nat.sqrt (1435 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1435]; decide
    · -- n = 1436
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1436 : Nat.sqrt (1436 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1436]; decide
    · -- n = 1437
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1437 : Nat.sqrt (1437 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1437]; decide
    · -- n = 1438
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1438 : Nat.sqrt (1438 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1438]; decide
    · -- n = 1439
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1439 : Nat.sqrt (1439 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1439]; decide
    · -- n = 1440
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1440 : Nat.sqrt (1440 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1440]; decide
    · -- n = 1441
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1441 : Nat.sqrt (1441 + 2) = 37 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1441]; decide
    · -- n = 1442
      use 239
      refine ⟨by decide, by decide, ?_⟩
      have h_1442 : Nat.sqrt (1442 + 239) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1442]; decide
    · -- n = 1443
      use 239
      refine ⟨by decide, by decide, ?_⟩
      have h_1443 : Nat.sqrt (1443 + 239) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1443]; decide
    · -- n = 1444
      use 239
      refine ⟨by decide, by decide, ?_⟩
      have h_1444 : Nat.sqrt (1444 + 239) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1444]; decide
    · -- n = 1445
      use 239
      refine ⟨by decide, by decide, ?_⟩
      have h_1445 : Nat.sqrt (1445 + 239) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1445]; decide
    · -- n = 1446
      use 239
      refine ⟨by decide, by decide, ?_⟩
      have h_1446 : Nat.sqrt (1446 + 239) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1446]; decide
    · -- n = 1447
      use 239
      refine ⟨by decide, by decide, ?_⟩
      have h_1447 : Nat.sqrt (1447 + 239) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1447]; decide
    · -- n = 1448
      use 233
      refine ⟨by decide, by decide, ?_⟩
      have h_1448 : Nat.sqrt (1448 + 233) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1448]; decide
    · -- n = 1449
      use 233
      refine ⟨by decide, by decide, ?_⟩
      have h_1449 : Nat.sqrt (1449 + 233) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1449]; decide
    · -- n = 1450
      use 233
      refine ⟨by decide, by decide, ?_⟩
      have h_1450 : Nat.sqrt (1450 + 233) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1450]; decide
    · -- n = 1451
      use 233
      refine ⟨by decide, by decide, ?_⟩
      have h_1451 : Nat.sqrt (1451 + 233) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1451]; decide
    · -- n = 1452
      use 229
      refine ⟨by decide, by decide, ?_⟩
      have h_1452 : Nat.sqrt (1452 + 229) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1452]; decide
    · -- n = 1453
      use 229
      refine ⟨by decide, by decide, ?_⟩
      have h_1453 : Nat.sqrt (1453 + 229) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1453]; decide
    · -- n = 1454
      use 227
      refine ⟨by decide, by decide, ?_⟩
      have h_1454 : Nat.sqrt (1454 + 227) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1454]; decide
    · -- n = 1455
      use 227
      refine ⟨by decide, by decide, ?_⟩
      have h_1455 : Nat.sqrt (1455 + 227) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1455]; decide
    · -- n = 1456
      use 227
      refine ⟨by decide, by decide, ?_⟩
      have h_1456 : Nat.sqrt (1456 + 227) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1456]; decide
    · -- n = 1457
      use 227
      refine ⟨by decide, by decide, ?_⟩
      have h_1457 : Nat.sqrt (1457 + 227) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1457]; decide
    · -- n = 1458
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_1458 : Nat.sqrt (1458 + 223) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1458]; decide
    · -- n = 1459
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_1459 : Nat.sqrt (1459 + 223) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1459]; decide
    · -- n = 1460
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_1460 : Nat.sqrt (1460 + 223) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1460]; decide
    · -- n = 1461
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_1461 : Nat.sqrt (1461 + 223) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1461]; decide
    · -- n = 1462
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_1462 : Nat.sqrt (1462 + 223) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1462]; decide
    · -- n = 1463
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_1463 : Nat.sqrt (1463 + 223) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1463]; decide
    · -- n = 1464
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_1464 : Nat.sqrt (1464 + 223) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1464]; decide
    · -- n = 1465
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_1465 : Nat.sqrt (1465 + 223) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1465]; decide
    · -- n = 1466
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_1466 : Nat.sqrt (1466 + 223) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1466]; decide
    · -- n = 1467
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_1467 : Nat.sqrt (1467 + 223) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1467]; decide
    · -- n = 1468
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_1468 : Nat.sqrt (1468 + 223) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1468]; decide
    · -- n = 1469
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_1469 : Nat.sqrt (1469 + 223) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1469]; decide
    · -- n = 1470
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_1470 : Nat.sqrt (1470 + 211) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1470]; decide
    · -- n = 1471
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_1471 : Nat.sqrt (1471 + 211) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1471]; decide
    · -- n = 1472
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_1472 : Nat.sqrt (1472 + 211) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1472]; decide
    · -- n = 1473
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_1473 : Nat.sqrt (1473 + 211) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1473]; decide
    · -- n = 1474
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_1474 : Nat.sqrt (1474 + 211) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1474]; decide
    · -- n = 1475
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_1475 : Nat.sqrt (1475 + 211) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1475]; decide
    · -- n = 1476
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_1476 : Nat.sqrt (1476 + 211) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1476]; decide
    · -- n = 1477
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_1477 : Nat.sqrt (1477 + 211) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1477]; decide
    · -- n = 1478
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_1478 : Nat.sqrt (1478 + 211) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1478]; decide
    · -- n = 1479
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_1479 : Nat.sqrt (1479 + 211) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1479]; decide
    · -- n = 1480
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_1480 : Nat.sqrt (1480 + 211) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1480]; decide
    · -- n = 1481
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_1481 : Nat.sqrt (1481 + 211) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1481]; decide
    · -- n = 1482
      use 199
      refine ⟨by decide, by decide, ?_⟩
      have h_1482 : Nat.sqrt (1482 + 199) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1482]; decide
    · -- n = 1483
      use 199
      refine ⟨by decide, by decide, ?_⟩
      have h_1483 : Nat.sqrt (1483 + 199) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1483]; decide
    · -- n = 1484
      use 197
      refine ⟨by decide, by decide, ?_⟩
      have h_1484 : Nat.sqrt (1484 + 197) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1484]; decide
    · -- n = 1485
      use 197
      refine ⟨by decide, by decide, ?_⟩
      have h_1485 : Nat.sqrt (1485 + 197) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1485]; decide
    · -- n = 1486
      use 197
      refine ⟨by decide, by decide, ?_⟩
      have h_1486 : Nat.sqrt (1486 + 197) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1486]; decide
    · -- n = 1487
      use 197
      refine ⟨by decide, by decide, ?_⟩
      have h_1487 : Nat.sqrt (1487 + 197) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1487]; decide
    · -- n = 1488
      use 193
      refine ⟨by decide, by decide, ?_⟩
      have h_1488 : Nat.sqrt (1488 + 193) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1488]; decide
    · -- n = 1489
      use 193
      refine ⟨by decide, by decide, ?_⟩
      have h_1489 : Nat.sqrt (1489 + 193) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1489]; decide
    · -- n = 1490
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_1490 : Nat.sqrt (1490 + 191) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1490]; decide
    · -- n = 1491
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_1491 : Nat.sqrt (1491 + 191) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1491]; decide
    · -- n = 1492
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_1492 : Nat.sqrt (1492 + 191) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1492]; decide
    · -- n = 1493
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_1493 : Nat.sqrt (1493 + 191) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1493]; decide
    · -- n = 1494
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_1494 : Nat.sqrt (1494 + 191) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1494]; decide
    · -- n = 1495
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_1495 : Nat.sqrt (1495 + 191) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1495]; decide
    · -- n = 1496
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_1496 : Nat.sqrt (1496 + 191) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1496]; decide
    · -- n = 1497
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_1497 : Nat.sqrt (1497 + 191) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1497]; decide
    · -- n = 1498
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_1498 : Nat.sqrt (1498 + 191) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1498]; decide
    · -- n = 1499
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_1499 : Nat.sqrt (1499 + 191) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1499]; decide
    · -- n = 1500
      use 181
      refine ⟨by decide, by decide, ?_⟩
      have h_1500 : Nat.sqrt (1500 + 181) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1500]; decide
    · -- n = 1501
      use 181
      refine ⟨by decide, by decide, ?_⟩
      have h_1501 : Nat.sqrt (1501 + 181) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1501]; decide
    · -- n = 1502
      use 179
      refine ⟨by decide, by decide, ?_⟩
      have h_1502 : Nat.sqrt (1502 + 179) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1502]; decide
    · -- n = 1503
      use 179
      refine ⟨by decide, by decide, ?_⟩
      have h_1503 : Nat.sqrt (1503 + 179) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1503]; decide
    · -- n = 1504
      use 179
      refine ⟨by decide, by decide, ?_⟩
      have h_1504 : Nat.sqrt (1504 + 179) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1504]; decide
    · -- n = 1505
      use 179
      refine ⟨by decide, by decide, ?_⟩
      have h_1505 : Nat.sqrt (1505 + 179) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1505]; decide
    · -- n = 1506
      use 179
      refine ⟨by decide, by decide, ?_⟩
      have h_1506 : Nat.sqrt (1506 + 179) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1506]; decide
    · -- n = 1507
      use 179
      refine ⟨by decide, by decide, ?_⟩
      have h_1507 : Nat.sqrt (1507 + 179) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1507]; decide
    · -- n = 1508
      use 173
      refine ⟨by decide, by decide, ?_⟩
      have h_1508 : Nat.sqrt (1508 + 173) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1508]; decide
    · -- n = 1509
      use 173
      refine ⟨by decide, by decide, ?_⟩
      have h_1509 : Nat.sqrt (1509 + 173) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1509]; decide
    · -- n = 1510
      use 173
      refine ⟨by decide, by decide, ?_⟩
      have h_1510 : Nat.sqrt (1510 + 173) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1510]; decide
    · -- n = 1511
      use 173
      refine ⟨by decide, by decide, ?_⟩
      have h_1511 : Nat.sqrt (1511 + 173) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1511]; decide
    · -- n = 1512
      use 173
      refine ⟨by decide, by decide, ?_⟩
      have h_1512 : Nat.sqrt (1512 + 173) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1512]; decide
    · -- n = 1513
      use 173
      refine ⟨by decide, by decide, ?_⟩
      have h_1513 : Nat.sqrt (1513 + 173) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1513]; decide
    · -- n = 1514
      use 167
      refine ⟨by decide, by decide, ?_⟩
      have h_1514 : Nat.sqrt (1514 + 167) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1514]; decide
    · -- n = 1515
      use 167
      refine ⟨by decide, by decide, ?_⟩
      have h_1515 : Nat.sqrt (1515 + 167) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1515]; decide
    · -- n = 1516
      use 167
      refine ⟨by decide, by decide, ?_⟩
      have h_1516 : Nat.sqrt (1516 + 167) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1516]; decide
    · -- n = 1517
      use 167
      refine ⟨by decide, by decide, ?_⟩
      have h_1517 : Nat.sqrt (1517 + 167) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1517]; decide
    · -- n = 1518
      use 163
      refine ⟨by decide, by decide, ?_⟩
      have h_1518 : Nat.sqrt (1518 + 163) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1518]; decide
    · -- n = 1519
      use 163
      refine ⟨by decide, by decide, ?_⟩
      have h_1519 : Nat.sqrt (1519 + 163) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1519]; decide
    · -- n = 1520
      use 163
      refine ⟨by decide, by decide, ?_⟩
      have h_1520 : Nat.sqrt (1520 + 163) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1520]; decide
    · -- n = 1521
      use 163
      refine ⟨by decide, by decide, ?_⟩
      have h_1521 : Nat.sqrt (1521 + 163) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1521]; decide
    · -- n = 1522
      use 163
      refine ⟨by decide, by decide, ?_⟩
      have h_1522 : Nat.sqrt (1522 + 163) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1522]; decide
    · -- n = 1523
      use 163
      refine ⟨by decide, by decide, ?_⟩
      have h_1523 : Nat.sqrt (1523 + 163) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1523]; decide
    · -- n = 1524
      use 157
      refine ⟨by decide, by decide, ?_⟩
      have h_1524 : Nat.sqrt (1524 + 157) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1524]; decide
    · -- n = 1525
      use 157
      refine ⟨by decide, by decide, ?_⟩
      have h_1525 : Nat.sqrt (1525 + 157) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1525]; decide
    · -- n = 1526
      use 157
      refine ⟨by decide, by decide, ?_⟩
      have h_1526 : Nat.sqrt (1526 + 157) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1526]; decide
    · -- n = 1527
      use 157
      refine ⟨by decide, by decide, ?_⟩
      have h_1527 : Nat.sqrt (1527 + 157) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1527]; decide
    · -- n = 1528
      use 157
      refine ⟨by decide, by decide, ?_⟩
      have h_1528 : Nat.sqrt (1528 + 157) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1528]; decide
    · -- n = 1529
      use 157
      refine ⟨by decide, by decide, ?_⟩
      have h_1529 : Nat.sqrt (1529 + 157) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1529]; decide
    · -- n = 1530
      use 151
      refine ⟨by decide, by decide, ?_⟩
      have h_1530 : Nat.sqrt (1530 + 151) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1530]; decide
    · -- n = 1531
      use 151
      refine ⟨by decide, by decide, ?_⟩
      have h_1531 : Nat.sqrt (1531 + 151) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1531]; decide
    · -- n = 1532
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_1532 : Nat.sqrt (1532 + 149) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1532]; decide
    · -- n = 1533
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_1533 : Nat.sqrt (1533 + 149) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1533]; decide
    · -- n = 1534
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_1534 : Nat.sqrt (1534 + 149) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1534]; decide
    · -- n = 1535
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_1535 : Nat.sqrt (1535 + 149) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1535]; decide
    · -- n = 1536
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_1536 : Nat.sqrt (1536 + 149) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1536]; decide
    · -- n = 1537
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_1537 : Nat.sqrt (1537 + 149) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1537]; decide
    · -- n = 1538
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_1538 : Nat.sqrt (1538 + 149) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1538]; decide
    · -- n = 1539
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_1539 : Nat.sqrt (1539 + 149) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1539]; decide
    · -- n = 1540
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_1540 : Nat.sqrt (1540 + 149) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1540]; decide
    · -- n = 1541
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_1541 : Nat.sqrt (1541 + 149) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1541]; decide
    · -- n = 1542
      use 139
      refine ⟨by decide, by decide, ?_⟩
      have h_1542 : Nat.sqrt (1542 + 139) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1542]; decide
    · -- n = 1543
      use 139
      refine ⟨by decide, by decide, ?_⟩
      have h_1543 : Nat.sqrt (1543 + 139) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1543]; decide
    · -- n = 1544
      use 137
      refine ⟨by decide, by decide, ?_⟩
      have h_1544 : Nat.sqrt (1544 + 137) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1544]; decide
    · -- n = 1545
      use 137
      refine ⟨by decide, by decide, ?_⟩
      have h_1545 : Nat.sqrt (1545 + 137) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1545]; decide
    · -- n = 1546
      use 137
      refine ⟨by decide, by decide, ?_⟩
      have h_1546 : Nat.sqrt (1546 + 137) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1546]; decide
    · -- n = 1547
      use 137
      refine ⟨by decide, by decide, ?_⟩
      have h_1547 : Nat.sqrt (1547 + 137) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1547]; decide
    · -- n = 1548
      use 137
      refine ⟨by decide, by decide, ?_⟩
      have h_1548 : Nat.sqrt (1548 + 137) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1548]; decide
    · -- n = 1549
      use 137
      refine ⟨by decide, by decide, ?_⟩
      have h_1549 : Nat.sqrt (1549 + 137) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1549]; decide
    · -- n = 1550
      use 131
      refine ⟨by decide, by decide, ?_⟩
      have h_1550 : Nat.sqrt (1550 + 131) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1550]; decide
    · -- n = 1551
      use 131
      refine ⟨by decide, by decide, ?_⟩
      have h_1551 : Nat.sqrt (1551 + 131) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1551]; decide
    · -- n = 1552
      use 131
      refine ⟨by decide, by decide, ?_⟩
      have h_1552 : Nat.sqrt (1552 + 131) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1552]; decide
    · -- n = 1553
      use 131
      refine ⟨by decide, by decide, ?_⟩
      have h_1553 : Nat.sqrt (1553 + 131) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1553]; decide
    · -- n = 1554
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_1554 : Nat.sqrt (1554 + 127) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1554]; decide
    · -- n = 1555
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_1555 : Nat.sqrt (1555 + 127) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1555]; decide
    · -- n = 1556
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_1556 : Nat.sqrt (1556 + 127) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1556]; decide
    · -- n = 1557
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_1557 : Nat.sqrt (1557 + 127) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1557]; decide
    · -- n = 1558
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_1558 : Nat.sqrt (1558 + 127) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1558]; decide
    · -- n = 1559
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_1559 : Nat.sqrt (1559 + 127) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1559]; decide
    · -- n = 1560
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_1560 : Nat.sqrt (1560 + 127) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1560]; decide
    · -- n = 1561
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_1561 : Nat.sqrt (1561 + 127) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1561]; decide
    · -- n = 1562
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_1562 : Nat.sqrt (1562 + 127) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1562]; decide
    · -- n = 1563
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_1563 : Nat.sqrt (1563 + 127) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1563]; decide
    · -- n = 1564
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_1564 : Nat.sqrt (1564 + 127) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1564]; decide
    · -- n = 1565
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_1565 : Nat.sqrt (1565 + 127) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1565]; decide
    · -- n = 1566
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_1566 : Nat.sqrt (1566 + 127) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1566]; decide
    · -- n = 1567
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_1567 : Nat.sqrt (1567 + 127) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1567]; decide
    · -- n = 1568
      use 113
      refine ⟨by decide, by decide, ?_⟩
      have h_1568 : Nat.sqrt (1568 + 113) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1568]; decide
    · -- n = 1569
      use 113
      refine ⟨by decide, by decide, ?_⟩
      have h_1569 : Nat.sqrt (1569 + 113) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1569]; decide
    · -- n = 1570
      use 113
      refine ⟨by decide, by decide, ?_⟩
      have h_1570 : Nat.sqrt (1570 + 113) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1570]; decide
    · -- n = 1571
      use 113
      refine ⟨by decide, by decide, ?_⟩
      have h_1571 : Nat.sqrt (1571 + 113) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1571]; decide
    · -- n = 1572
      use 109
      refine ⟨by decide, by decide, ?_⟩
      have h_1572 : Nat.sqrt (1572 + 109) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1572]; decide
    · -- n = 1573
      use 109
      refine ⟨by decide, by decide, ?_⟩
      have h_1573 : Nat.sqrt (1573 + 109) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1573]; decide
    · -- n = 1574
      use 107
      refine ⟨by decide, by decide, ?_⟩
      have h_1574 : Nat.sqrt (1574 + 107) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1574]; decide
    · -- n = 1575
      use 107
      refine ⟨by decide, by decide, ?_⟩
      have h_1575 : Nat.sqrt (1575 + 107) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1575]; decide
    · -- n = 1576
      use 107
      refine ⟨by decide, by decide, ?_⟩
      have h_1576 : Nat.sqrt (1576 + 107) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1576]; decide
    · -- n = 1577
      use 107
      refine ⟨by decide, by decide, ?_⟩
      have h_1577 : Nat.sqrt (1577 + 107) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1577]; decide
    · -- n = 1578
      use 103
      refine ⟨by decide, by decide, ?_⟩
      have h_1578 : Nat.sqrt (1578 + 103) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1578]; decide
    · -- n = 1579
      use 103
      refine ⟨by decide, by decide, ?_⟩
      have h_1579 : Nat.sqrt (1579 + 103) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1579]; decide
    · -- n = 1580
      use 101
      refine ⟨by decide, by decide, ?_⟩
      have h_1580 : Nat.sqrt (1580 + 101) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1580]; decide
    · -- n = 1581
      use 101
      refine ⟨by decide, by decide, ?_⟩
      have h_1581 : Nat.sqrt (1581 + 101) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1581]; decide
    · -- n = 1582
      use 101
      refine ⟨by decide, by decide, ?_⟩
      have h_1582 : Nat.sqrt (1582 + 101) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1582]; decide
    · -- n = 1583
      use 101
      refine ⟨by decide, by decide, ?_⟩
      have h_1583 : Nat.sqrt (1583 + 101) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1583]; decide
    · -- n = 1584
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_1584 : Nat.sqrt (1584 + 97) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1584]; decide
    · -- n = 1585
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_1585 : Nat.sqrt (1585 + 97) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1585]; decide
    · -- n = 1586
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_1586 : Nat.sqrt (1586 + 97) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1586]; decide
    · -- n = 1587
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_1587 : Nat.sqrt (1587 + 97) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1587]; decide
    · -- n = 1588
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_1588 : Nat.sqrt (1588 + 97) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1588]; decide
    · -- n = 1589
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_1589 : Nat.sqrt (1589 + 97) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1589]; decide
    · -- n = 1590
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_1590 : Nat.sqrt (1590 + 97) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1590]; decide
    · -- n = 1591
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_1591 : Nat.sqrt (1591 + 97) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1591]; decide
    · -- n = 1592
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_1592 : Nat.sqrt (1592 + 89) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1592]; decide
    · -- n = 1593
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_1593 : Nat.sqrt (1593 + 89) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1593]; decide
    · -- n = 1594
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_1594 : Nat.sqrt (1594 + 89) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1594]; decide
    · -- n = 1595
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_1595 : Nat.sqrt (1595 + 89) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1595]; decide
    · -- n = 1596
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_1596 : Nat.sqrt (1596 + 89) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1596]; decide
    · -- n = 1597
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_1597 : Nat.sqrt (1597 + 89) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1597]; decide
    · -- n = 1598
      use 83
      refine ⟨by decide, by decide, ?_⟩
      have h_1598 : Nat.sqrt (1598 + 83) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1598]; decide
    · -- n = 1599
      use 83
      refine ⟨by decide, by decide, ?_⟩
      have h_1599 : Nat.sqrt (1599 + 83) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1599]; decide
    · -- n = 1600
      use 83
      refine ⟨by decide, by decide, ?_⟩
      have h_1600 : Nat.sqrt (1600 + 83) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1600]; decide
    · -- n = 1601
      use 83
      refine ⟨by decide, by decide, ?_⟩
      have h_1601 : Nat.sqrt (1601 + 83) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1601]; decide
    · -- n = 1602
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_1602 : Nat.sqrt (1602 + 79) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1602]; decide
    · -- n = 1603
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_1603 : Nat.sqrt (1603 + 79) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1603]; decide
    · -- n = 1604
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_1604 : Nat.sqrt (1604 + 79) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1604]; decide
    · -- n = 1605
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_1605 : Nat.sqrt (1605 + 79) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1605]; decide
    · -- n = 1606
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_1606 : Nat.sqrt (1606 + 79) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1606]; decide
    · -- n = 1607
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_1607 : Nat.sqrt (1607 + 79) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1607]; decide
    · -- n = 1608
      use 73
      refine ⟨by decide, by decide, ?_⟩
      have h_1608 : Nat.sqrt (1608 + 73) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1608]; decide
    · -- n = 1609
      use 73
      refine ⟨by decide, by decide, ?_⟩
      have h_1609 : Nat.sqrt (1609 + 73) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1609]; decide
    · -- n = 1610
      use 71
      refine ⟨by decide, by decide, ?_⟩
      have h_1610 : Nat.sqrt (1610 + 71) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1610]; decide
    · -- n = 1611
      use 71
      refine ⟨by decide, by decide, ?_⟩
      have h_1611 : Nat.sqrt (1611 + 71) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1611]; decide
    · -- n = 1612
      use 71
      refine ⟨by decide, by decide, ?_⟩
      have h_1612 : Nat.sqrt (1612 + 71) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1612]; decide
    · -- n = 1613
      use 71
      refine ⟨by decide, by decide, ?_⟩
      have h_1613 : Nat.sqrt (1613 + 71) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1613]; decide
    · -- n = 1614
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_1614 : Nat.sqrt (1614 + 67) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1614]; decide
    · -- n = 1615
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_1615 : Nat.sqrt (1615 + 67) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1615]; decide
    · -- n = 1616
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_1616 : Nat.sqrt (1616 + 67) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1616]; decide
    · -- n = 1617
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_1617 : Nat.sqrt (1617 + 67) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1617]; decide
    · -- n = 1618
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_1618 : Nat.sqrt (1618 + 67) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1618]; decide
    · -- n = 1619
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_1619 : Nat.sqrt (1619 + 67) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1619]; decide
    · -- n = 1620
      use 61
      refine ⟨by decide, by decide, ?_⟩
      have h_1620 : Nat.sqrt (1620 + 61) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1620]; decide
    · -- n = 1621
      use 61
      refine ⟨by decide, by decide, ?_⟩
      have h_1621 : Nat.sqrt (1621 + 61) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1621]; decide
    · -- n = 1622
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_1622 : Nat.sqrt (1622 + 59) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1622]; decide
    · -- n = 1623
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_1623 : Nat.sqrt (1623 + 59) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1623]; decide
    · -- n = 1624
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_1624 : Nat.sqrt (1624 + 59) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1624]; decide
    · -- n = 1625
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_1625 : Nat.sqrt (1625 + 59) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1625]; decide
    · -- n = 1626
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_1626 : Nat.sqrt (1626 + 59) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1626]; decide
    · -- n = 1627
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_1627 : Nat.sqrt (1627 + 59) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1627]; decide
    · -- n = 1628
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_1628 : Nat.sqrt (1628 + 53) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1628]; decide
    · -- n = 1629
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_1629 : Nat.sqrt (1629 + 53) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1629]; decide
    · -- n = 1630
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_1630 : Nat.sqrt (1630 + 53) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1630]; decide
    · -- n = 1631
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_1631 : Nat.sqrt (1631 + 53) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1631]; decide
    · -- n = 1632
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_1632 : Nat.sqrt (1632 + 53) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1632]; decide
    · -- n = 1633
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_1633 : Nat.sqrt (1633 + 53) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1633]; decide
    · -- n = 1634
      use 47
      refine ⟨by decide, by decide, ?_⟩
      have h_1634 : Nat.sqrt (1634 + 47) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1634]; decide
    · -- n = 1635
      use 47
      refine ⟨by decide, by decide, ?_⟩
      have h_1635 : Nat.sqrt (1635 + 47) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1635]; decide
    · -- n = 1636
      use 47
      refine ⟨by decide, by decide, ?_⟩
      have h_1636 : Nat.sqrt (1636 + 47) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1636]; decide
    · -- n = 1637
      use 47
      refine ⟨by decide, by decide, ?_⟩
      have h_1637 : Nat.sqrt (1637 + 47) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1637]; decide
    · -- n = 1638
      use 43
      refine ⟨by decide, by decide, ?_⟩
      have h_1638 : Nat.sqrt (1638 + 43) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1638]; decide
    · -- n = 1639
      use 43
      refine ⟨by decide, by decide, ?_⟩
      have h_1639 : Nat.sqrt (1639 + 43) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1639]; decide
    · -- n = 1640
      use 41
      refine ⟨by decide, by decide, ?_⟩
      have h_1640 : Nat.sqrt (1640 + 41) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1640]; decide
    · -- n = 1641
      use 41
      refine ⟨by decide, by decide, ?_⟩
      have h_1641 : Nat.sqrt (1641 + 41) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1641]; decide
    · -- n = 1642
      use 41
      refine ⟨by decide, by decide, ?_⟩
      have h_1642 : Nat.sqrt (1642 + 41) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1642]; decide
    · -- n = 1643
      use 41
      refine ⟨by decide, by decide, ?_⟩
      have h_1643 : Nat.sqrt (1643 + 41) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1643]; decide
    · -- n = 1644
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_1644 : Nat.sqrt (1644 + 37) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1644]; decide
    · -- n = 1645
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_1645 : Nat.sqrt (1645 + 37) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1645]; decide
    · -- n = 1646
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_1646 : Nat.sqrt (1646 + 37) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1646]; decide
    · -- n = 1647
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_1647 : Nat.sqrt (1647 + 37) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1647]; decide
    · -- n = 1648
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_1648 : Nat.sqrt (1648 + 37) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1648]; decide
    · -- n = 1649
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_1649 : Nat.sqrt (1649 + 37) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1649]; decide
    · -- n = 1650
      use 31
      refine ⟨by decide, by decide, ?_⟩
      have h_1650 : Nat.sqrt (1650 + 31) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1650]; decide
    · -- n = 1651
      use 31
      refine ⟨by decide, by decide, ?_⟩
      have h_1651 : Nat.sqrt (1651 + 31) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1651]; decide
    · -- n = 1652
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_1652 : Nat.sqrt (1652 + 29) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1652]; decide
    · -- n = 1653
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_1653 : Nat.sqrt (1653 + 29) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1653]; decide
    · -- n = 1654
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_1654 : Nat.sqrt (1654 + 29) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1654]; decide
    · -- n = 1655
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_1655 : Nat.sqrt (1655 + 29) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1655]; decide
    · -- n = 1656
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_1656 : Nat.sqrt (1656 + 29) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1656]; decide
    · -- n = 1657
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_1657 : Nat.sqrt (1657 + 29) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1657]; decide
    · -- n = 1658
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_1658 : Nat.sqrt (1658 + 23) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1658]; decide
    · -- n = 1659
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_1659 : Nat.sqrt (1659 + 23) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1659]; decide
    · -- n = 1660
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_1660 : Nat.sqrt (1660 + 23) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1660]; decide
    · -- n = 1661
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_1661 : Nat.sqrt (1661 + 23) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1661]; decide
    · -- n = 1662
      use 19
      refine ⟨by decide, by decide, ?_⟩
      have h_1662 : Nat.sqrt (1662 + 19) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1662]; decide
    · -- n = 1663
      use 19
      refine ⟨by decide, by decide, ?_⟩
      have h_1663 : Nat.sqrt (1663 + 19) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1663]; decide
    · -- n = 1664
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_1664 : Nat.sqrt (1664 + 17) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1664]; decide
    · -- n = 1665
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_1665 : Nat.sqrt (1665 + 17) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1665]; decide
    · -- n = 1666
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_1666 : Nat.sqrt (1666 + 17) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1666]; decide
    · -- n = 1667
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_1667 : Nat.sqrt (1667 + 17) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1667]; decide
    · -- n = 1668
      use 13
      refine ⟨by decide, by decide, ?_⟩
      have h_1668 : Nat.sqrt (1668 + 13) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1668]; decide
    · -- n = 1669
      use 13
      refine ⟨by decide, by decide, ?_⟩
      have h_1669 : Nat.sqrt (1669 + 13) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1669]; decide
    · -- n = 1670
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_1670 : Nat.sqrt (1670 + 11) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1670]; decide
    · -- n = 1671
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_1671 : Nat.sqrt (1671 + 11) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1671]; decide
    · -- n = 1672
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_1672 : Nat.sqrt (1672 + 11) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1672]; decide
    · -- n = 1673
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_1673 : Nat.sqrt (1673 + 11) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1673]; decide
    · -- n = 1674
      use 7
      refine ⟨by decide, by decide, ?_⟩
      have h_1674 : Nat.sqrt (1674 + 7) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1674]; decide
    · -- n = 1675
      use 7
      refine ⟨by decide, by decide, ?_⟩
      have h_1675 : Nat.sqrt (1675 + 7) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1675]; decide
    · -- n = 1676
      use 5
      refine ⟨by decide, by decide, ?_⟩
      have h_1676 : Nat.sqrt (1676 + 5) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1676]; decide
    · -- n = 1677
      use 5
      refine ⟨by decide, by decide, ?_⟩
      have h_1677 : Nat.sqrt (1677 + 5) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1677]; decide
    · -- n = 1678
      use 3
      refine ⟨by decide, by decide, ?_⟩
      have h_1678 : Nat.sqrt (1678 + 3) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1678]; decide
    · -- n = 1679
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1679 : Nat.sqrt (1679 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1679]; decide
    · -- n = 1680
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1680 : Nat.sqrt (1680 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1680]; decide
    · -- n = 1681
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1681 : Nat.sqrt (1681 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1681]; decide
    · -- n = 1682
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1682 : Nat.sqrt (1682 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1682]; decide
    · -- n = 1683
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1683 : Nat.sqrt (1683 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1683]; decide
    · -- n = 1684
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1684 : Nat.sqrt (1684 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1684]; decide
    · -- n = 1685
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1685 : Nat.sqrt (1685 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1685]; decide
    · -- n = 1686
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1686 : Nat.sqrt (1686 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1686]; decide
    · -- n = 1687
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1687 : Nat.sqrt (1687 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1687]; decide
    · -- n = 1688
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1688 : Nat.sqrt (1688 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1688]; decide
    · -- n = 1689
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1689 : Nat.sqrt (1689 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1689]; decide
    · -- n = 1690
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1690 : Nat.sqrt (1690 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1690]; decide
    · -- n = 1691
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1691 : Nat.sqrt (1691 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1691]; decide
    · -- n = 1692
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1692 : Nat.sqrt (1692 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1692]; decide
    · -- n = 1693
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1693 : Nat.sqrt (1693 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1693]; decide
    · -- n = 1694
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1694 : Nat.sqrt (1694 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1694]; decide
    · -- n = 1695
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1695 : Nat.sqrt (1695 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1695]; decide
    · -- n = 1696
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1696 : Nat.sqrt (1696 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1696]; decide
    · -- n = 1697
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1697 : Nat.sqrt (1697 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1697]; decide
    · -- n = 1698
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1698 : Nat.sqrt (1698 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1698]; decide
    · -- n = 1699
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1699 : Nat.sqrt (1699 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1699]; decide
    · -- n = 1700
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1700 : Nat.sqrt (1700 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1700]; decide
    · -- n = 1701
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1701 : Nat.sqrt (1701 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1701]; decide
    · -- n = 1702
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1702 : Nat.sqrt (1702 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1702]; decide
    · -- n = 1703
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1703 : Nat.sqrt (1703 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1703]; decide
    · -- n = 1704
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1704 : Nat.sqrt (1704 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1704]; decide
    · -- n = 1705
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1705 : Nat.sqrt (1705 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1705]; decide
    · -- n = 1706
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1706 : Nat.sqrt (1706 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1706]; decide
    · -- n = 1707
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1707 : Nat.sqrt (1707 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1707]; decide
    · -- n = 1708
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1708 : Nat.sqrt (1708 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1708]; decide
    · -- n = 1709
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1709 : Nat.sqrt (1709 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1709]; decide
    · -- n = 1710
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1710 : Nat.sqrt (1710 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1710]; decide
    · -- n = 1711
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1711 : Nat.sqrt (1711 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1711]; decide
    · -- n = 1712
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1712 : Nat.sqrt (1712 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1712]; decide
    · -- n = 1713
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1713 : Nat.sqrt (1713 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1713]; decide
    · -- n = 1714
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1714 : Nat.sqrt (1714 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1714]; decide
    · -- n = 1715
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1715 : Nat.sqrt (1715 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1715]; decide
    · -- n = 1716
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1716 : Nat.sqrt (1716 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1716]; decide
    · -- n = 1717
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1717 : Nat.sqrt (1717 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1717]; decide
    · -- n = 1718
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1718 : Nat.sqrt (1718 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1718]; decide
    · -- n = 1719
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1719 : Nat.sqrt (1719 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1719]; decide
    · -- n = 1720
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1720 : Nat.sqrt (1720 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1720]; decide
    · -- n = 1721
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1721 : Nat.sqrt (1721 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1721]; decide
    · -- n = 1722
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1722 : Nat.sqrt (1722 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1722]; decide
    · -- n = 1723
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1723 : Nat.sqrt (1723 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1723]; decide
    · -- n = 1724
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1724 : Nat.sqrt (1724 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1724]; decide
    · -- n = 1725
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1725 : Nat.sqrt (1725 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1725]; decide
    · -- n = 1726
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1726 : Nat.sqrt (1726 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1726]; decide
    · -- n = 1727
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1727 : Nat.sqrt (1727 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1727]; decide
    · -- n = 1728
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1728 : Nat.sqrt (1728 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1728]; decide
    · -- n = 1729
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1729 : Nat.sqrt (1729 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1729]; decide
    · -- n = 1730
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1730 : Nat.sqrt (1730 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1730]; decide
    · -- n = 1731
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1731 : Nat.sqrt (1731 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1731]; decide
    · -- n = 1732
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1732 : Nat.sqrt (1732 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1732]; decide
    · -- n = 1733
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1733 : Nat.sqrt (1733 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1733]; decide
    · -- n = 1734
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1734 : Nat.sqrt (1734 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1734]; decide
    · -- n = 1735
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1735 : Nat.sqrt (1735 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1735]; decide
    · -- n = 1736
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1736 : Nat.sqrt (1736 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1736]; decide
    · -- n = 1737
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1737 : Nat.sqrt (1737 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1737]; decide
    · -- n = 1738
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1738 : Nat.sqrt (1738 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1738]; decide
    · -- n = 1739
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1739 : Nat.sqrt (1739 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1739]; decide
    · -- n = 1740
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1740 : Nat.sqrt (1740 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1740]; decide
    · -- n = 1741
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1741 : Nat.sqrt (1741 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1741]; decide
    · -- n = 1742
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1742 : Nat.sqrt (1742 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1742]; decide
    · -- n = 1743
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1743 : Nat.sqrt (1743 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1743]; decide
    · -- n = 1744
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1744 : Nat.sqrt (1744 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1744]; decide
    · -- n = 1745
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1745 : Nat.sqrt (1745 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1745]; decide
    · -- n = 1746
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1746 : Nat.sqrt (1746 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1746]; decide
    · -- n = 1747
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1747 : Nat.sqrt (1747 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1747]; decide
    · -- n = 1748
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1748 : Nat.sqrt (1748 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1748]; decide
    · -- n = 1749
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1749 : Nat.sqrt (1749 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1749]; decide
    · -- n = 1750
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1750 : Nat.sqrt (1750 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1750]; decide
    · -- n = 1751
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1751 : Nat.sqrt (1751 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1751]; decide
    · -- n = 1752
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1752 : Nat.sqrt (1752 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1752]; decide
    · -- n = 1753
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1753 : Nat.sqrt (1753 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1753]; decide
    · -- n = 1754
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1754 : Nat.sqrt (1754 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1754]; decide
    · -- n = 1755
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1755 : Nat.sqrt (1755 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1755]; decide
    · -- n = 1756
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1756 : Nat.sqrt (1756 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1756]; decide
    · -- n = 1757
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1757 : Nat.sqrt (1757 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1757]; decide
    · -- n = 1758
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1758 : Nat.sqrt (1758 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1758]; decide
    · -- n = 1759
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1759 : Nat.sqrt (1759 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1759]; decide
    · -- n = 1760
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1760 : Nat.sqrt (1760 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1760]; decide
    · -- n = 1761
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1761 : Nat.sqrt (1761 + 2) = 41 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1761]; decide
    · -- n = 1762
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_1762 : Nat.sqrt (1762 + 89) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1762]; decide
    · -- n = 1763
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_1763 : Nat.sqrt (1763 + 89) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1763]; decide
    · -- n = 1764
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_1764 : Nat.sqrt (1764 + 89) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1764]; decide
    · -- n = 1765
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_1765 : Nat.sqrt (1765 + 89) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1765]; decide
    · -- n = 1766
      use 83
      refine ⟨by decide, by decide, ?_⟩
      have h_1766 : Nat.sqrt (1766 + 83) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1766]; decide
    · -- n = 1767
      use 83
      refine ⟨by decide, by decide, ?_⟩
      have h_1767 : Nat.sqrt (1767 + 83) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1767]; decide
    · -- n = 1768
      use 83
      refine ⟨by decide, by decide, ?_⟩
      have h_1768 : Nat.sqrt (1768 + 83) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1768]; decide
    · -- n = 1769
      use 83
      refine ⟨by decide, by decide, ?_⟩
      have h_1769 : Nat.sqrt (1769 + 83) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1769]; decide
    · -- n = 1770
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_1770 : Nat.sqrt (1770 + 79) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1770]; decide
    · -- n = 1771
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_1771 : Nat.sqrt (1771 + 79) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1771]; decide
    · -- n = 1772
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_1772 : Nat.sqrt (1772 + 79) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1772]; decide
    · -- n = 1773
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_1773 : Nat.sqrt (1773 + 79) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1773]; decide
    · -- n = 1774
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_1774 : Nat.sqrt (1774 + 79) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1774]; decide
    · -- n = 1775
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_1775 : Nat.sqrt (1775 + 79) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1775]; decide
    · -- n = 1776
      use 73
      refine ⟨by decide, by decide, ?_⟩
      have h_1776 : Nat.sqrt (1776 + 73) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1776]; decide
    · -- n = 1777
      use 73
      refine ⟨by decide, by decide, ?_⟩
      have h_1777 : Nat.sqrt (1777 + 73) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1777]; decide
    · -- n = 1778
      use 71
      refine ⟨by decide, by decide, ?_⟩
      have h_1778 : Nat.sqrt (1778 + 71) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1778]; decide
    · -- n = 1779
      use 71
      refine ⟨by decide, by decide, ?_⟩
      have h_1779 : Nat.sqrt (1779 + 71) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1779]; decide
    · -- n = 1780
      use 71
      refine ⟨by decide, by decide, ?_⟩
      have h_1780 : Nat.sqrt (1780 + 71) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1780]; decide
    · -- n = 1781
      use 71
      refine ⟨by decide, by decide, ?_⟩
      have h_1781 : Nat.sqrt (1781 + 71) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1781]; decide
    · -- n = 1782
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_1782 : Nat.sqrt (1782 + 67) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1782]; decide
    · -- n = 1783
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_1783 : Nat.sqrt (1783 + 67) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1783]; decide
    · -- n = 1784
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_1784 : Nat.sqrt (1784 + 67) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1784]; decide
    · -- n = 1785
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_1785 : Nat.sqrt (1785 + 67) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1785]; decide
    · -- n = 1786
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_1786 : Nat.sqrt (1786 + 67) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1786]; decide
    · -- n = 1787
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_1787 : Nat.sqrt (1787 + 67) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1787]; decide
    · -- n = 1788
      use 61
      refine ⟨by decide, by decide, ?_⟩
      have h_1788 : Nat.sqrt (1788 + 61) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1788]; decide
    · -- n = 1789
      use 61
      refine ⟨by decide, by decide, ?_⟩
      have h_1789 : Nat.sqrt (1789 + 61) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1789]; decide
    · -- n = 1790
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_1790 : Nat.sqrt (1790 + 59) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1790]; decide
    · -- n = 1791
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_1791 : Nat.sqrt (1791 + 59) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1791]; decide
    · -- n = 1792
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_1792 : Nat.sqrt (1792 + 59) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1792]; decide
    · -- n = 1793
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_1793 : Nat.sqrt (1793 + 59) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1793]; decide
    · -- n = 1794
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_1794 : Nat.sqrt (1794 + 59) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1794]; decide
    · -- n = 1795
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_1795 : Nat.sqrt (1795 + 59) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1795]; decide
    · -- n = 1796
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_1796 : Nat.sqrt (1796 + 53) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1796]; decide
    · -- n = 1797
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_1797 : Nat.sqrt (1797 + 53) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1797]; decide
    · -- n = 1798
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_1798 : Nat.sqrt (1798 + 53) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1798]; decide
    · -- n = 1799
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_1799 : Nat.sqrt (1799 + 53) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1799]; decide
    · -- n = 1800
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_1800 : Nat.sqrt (1800 + 53) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1800]; decide
    · -- n = 1801
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_1801 : Nat.sqrt (1801 + 53) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1801]; decide
    · -- n = 1802
      use 47
      refine ⟨by decide, by decide, ?_⟩
      have h_1802 : Nat.sqrt (1802 + 47) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1802]; decide
    · -- n = 1803
      use 47
      refine ⟨by decide, by decide, ?_⟩
      have h_1803 : Nat.sqrt (1803 + 47) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1803]; decide
    · -- n = 1804
      use 47
      refine ⟨by decide, by decide, ?_⟩
      have h_1804 : Nat.sqrt (1804 + 47) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1804]; decide
    · -- n = 1805
      use 47
      refine ⟨by decide, by decide, ?_⟩
      have h_1805 : Nat.sqrt (1805 + 47) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1805]; decide
    · -- n = 1806
      use 43
      refine ⟨by decide, by decide, ?_⟩
      have h_1806 : Nat.sqrt (1806 + 43) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1806]; decide
    · -- n = 1807
      use 43
      refine ⟨by decide, by decide, ?_⟩
      have h_1807 : Nat.sqrt (1807 + 43) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1807]; decide
    · -- n = 1808
      use 41
      refine ⟨by decide, by decide, ?_⟩
      have h_1808 : Nat.sqrt (1808 + 41) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1808]; decide
    · -- n = 1809
      use 41
      refine ⟨by decide, by decide, ?_⟩
      have h_1809 : Nat.sqrt (1809 + 41) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1809]; decide
    · -- n = 1810
      use 41
      refine ⟨by decide, by decide, ?_⟩
      have h_1810 : Nat.sqrt (1810 + 41) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1810]; decide
    · -- n = 1811
      use 41
      refine ⟨by decide, by decide, ?_⟩
      have h_1811 : Nat.sqrt (1811 + 41) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1811]; decide
    · -- n = 1812
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_1812 : Nat.sqrt (1812 + 37) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1812]; decide
    · -- n = 1813
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_1813 : Nat.sqrt (1813 + 37) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1813]; decide
    · -- n = 1814
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_1814 : Nat.sqrt (1814 + 37) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1814]; decide
    · -- n = 1815
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_1815 : Nat.sqrt (1815 + 37) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1815]; decide
    · -- n = 1816
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_1816 : Nat.sqrt (1816 + 37) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1816]; decide
    · -- n = 1817
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_1817 : Nat.sqrt (1817 + 37) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1817]; decide
    · -- n = 1818
      use 31
      refine ⟨by decide, by decide, ?_⟩
      have h_1818 : Nat.sqrt (1818 + 31) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1818]; decide
    · -- n = 1819
      use 31
      refine ⟨by decide, by decide, ?_⟩
      have h_1819 : Nat.sqrt (1819 + 31) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1819]; decide
    · -- n = 1820
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_1820 : Nat.sqrt (1820 + 29) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1820]; decide
    · -- n = 1821
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_1821 : Nat.sqrt (1821 + 29) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1821]; decide
    · -- n = 1822
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_1822 : Nat.sqrt (1822 + 29) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1822]; decide
    · -- n = 1823
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_1823 : Nat.sqrt (1823 + 29) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1823]; decide
    · -- n = 1824
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_1824 : Nat.sqrt (1824 + 29) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1824]; decide
    · -- n = 1825
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_1825 : Nat.sqrt (1825 + 29) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1825]; decide
    · -- n = 1826
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_1826 : Nat.sqrt (1826 + 23) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1826]; decide
    · -- n = 1827
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_1827 : Nat.sqrt (1827 + 23) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1827]; decide
    · -- n = 1828
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_1828 : Nat.sqrt (1828 + 23) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1828]; decide
    · -- n = 1829
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_1829 : Nat.sqrt (1829 + 23) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1829]; decide
    · -- n = 1830
      use 19
      refine ⟨by decide, by decide, ?_⟩
      have h_1830 : Nat.sqrt (1830 + 19) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1830]; decide
    · -- n = 1831
      use 19
      refine ⟨by decide, by decide, ?_⟩
      have h_1831 : Nat.sqrt (1831 + 19) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1831]; decide
    · -- n = 1832
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_1832 : Nat.sqrt (1832 + 17) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1832]; decide
    · -- n = 1833
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_1833 : Nat.sqrt (1833 + 17) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1833]; decide
    · -- n = 1834
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_1834 : Nat.sqrt (1834 + 17) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1834]; decide
    · -- n = 1835
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_1835 : Nat.sqrt (1835 + 17) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1835]; decide
    · -- n = 1836
      use 13
      refine ⟨by decide, by decide, ?_⟩
      have h_1836 : Nat.sqrt (1836 + 13) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1836]; decide
    · -- n = 1837
      use 13
      refine ⟨by decide, by decide, ?_⟩
      have h_1837 : Nat.sqrt (1837 + 13) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1837]; decide
    · -- n = 1838
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_1838 : Nat.sqrt (1838 + 11) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1838]; decide
    · -- n = 1839
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_1839 : Nat.sqrt (1839 + 11) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1839]; decide
    · -- n = 1840
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_1840 : Nat.sqrt (1840 + 11) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1840]; decide
    · -- n = 1841
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_1841 : Nat.sqrt (1841 + 11) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1841]; decide
    · -- n = 1842
      use 7
      refine ⟨by decide, by decide, ?_⟩
      have h_1842 : Nat.sqrt (1842 + 7) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1842]; decide
    · -- n = 1843
      use 7
      refine ⟨by decide, by decide, ?_⟩
      have h_1843 : Nat.sqrt (1843 + 7) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1843]; decide
    · -- n = 1844
      use 5
      refine ⟨by decide, by decide, ?_⟩
      have h_1844 : Nat.sqrt (1844 + 5) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1844]; decide
    · -- n = 1845
      use 5
      refine ⟨by decide, by decide, ?_⟩
      have h_1845 : Nat.sqrt (1845 + 5) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1845]; decide
    · -- n = 1846
      use 3
      refine ⟨by decide, by decide, ?_⟩
      have h_1846 : Nat.sqrt (1846 + 3) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1846]; decide
    · -- n = 1847
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1847 : Nat.sqrt (1847 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1847]; decide
    · -- n = 1848
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1848 : Nat.sqrt (1848 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1848]; decide
    · -- n = 1849
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1849 : Nat.sqrt (1849 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1849]; decide
    · -- n = 1850
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1850 : Nat.sqrt (1850 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1850]; decide
    · -- n = 1851
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1851 : Nat.sqrt (1851 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1851]; decide
    · -- n = 1852
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1852 : Nat.sqrt (1852 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1852]; decide
    · -- n = 1853
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1853 : Nat.sqrt (1853 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1853]; decide
    · -- n = 1854
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1854 : Nat.sqrt (1854 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1854]; decide
    · -- n = 1855
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1855 : Nat.sqrt (1855 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1855]; decide
    · -- n = 1856
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1856 : Nat.sqrt (1856 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1856]; decide
    · -- n = 1857
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1857 : Nat.sqrt (1857 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1857]; decide
    · -- n = 1858
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1858 : Nat.sqrt (1858 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1858]; decide
    · -- n = 1859
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1859 : Nat.sqrt (1859 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1859]; decide
    · -- n = 1860
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1860 : Nat.sqrt (1860 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1860]; decide
    · -- n = 1861
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1861 : Nat.sqrt (1861 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1861]; decide
    · -- n = 1862
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1862 : Nat.sqrt (1862 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1862]; decide
    · -- n = 1863
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1863 : Nat.sqrt (1863 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1863]; decide
    · -- n = 1864
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1864 : Nat.sqrt (1864 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1864]; decide
    · -- n = 1865
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1865 : Nat.sqrt (1865 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1865]; decide
    · -- n = 1866
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1866 : Nat.sqrt (1866 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1866]; decide
    · -- n = 1867
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1867 : Nat.sqrt (1867 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1867]; decide
    · -- n = 1868
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1868 : Nat.sqrt (1868 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1868]; decide
    · -- n = 1869
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1869 : Nat.sqrt (1869 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1869]; decide
    · -- n = 1870
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1870 : Nat.sqrt (1870 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1870]; decide
    · -- n = 1871
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1871 : Nat.sqrt (1871 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1871]; decide
    · -- n = 1872
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1872 : Nat.sqrt (1872 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1872]; decide
    · -- n = 1873
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1873 : Nat.sqrt (1873 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1873]; decide
    · -- n = 1874
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1874 : Nat.sqrt (1874 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1874]; decide
    · -- n = 1875
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1875 : Nat.sqrt (1875 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1875]; decide
    · -- n = 1876
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1876 : Nat.sqrt (1876 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1876]; decide
    · -- n = 1877
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1877 : Nat.sqrt (1877 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1877]; decide
    · -- n = 1878
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1878 : Nat.sqrt (1878 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1878]; decide
    · -- n = 1879
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1879 : Nat.sqrt (1879 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1879]; decide
    · -- n = 1880
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1880 : Nat.sqrt (1880 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1880]; decide
    · -- n = 1881
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1881 : Nat.sqrt (1881 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1881]; decide
    · -- n = 1882
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1882 : Nat.sqrt (1882 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1882]; decide
    · -- n = 1883
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1883 : Nat.sqrt (1883 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1883]; decide
    · -- n = 1884
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1884 : Nat.sqrt (1884 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1884]; decide
    · -- n = 1885
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1885 : Nat.sqrt (1885 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1885]; decide
    · -- n = 1886
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1886 : Nat.sqrt (1886 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1886]; decide
    · -- n = 1887
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1887 : Nat.sqrt (1887 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1887]; decide
    · -- n = 1888
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1888 : Nat.sqrt (1888 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1888]; decide
    · -- n = 1889
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1889 : Nat.sqrt (1889 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1889]; decide
    · -- n = 1890
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1890 : Nat.sqrt (1890 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1890]; decide
    · -- n = 1891
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1891 : Nat.sqrt (1891 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1891]; decide
    · -- n = 1892
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1892 : Nat.sqrt (1892 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1892]; decide
    · -- n = 1893
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1893 : Nat.sqrt (1893 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1893]; decide
    · -- n = 1894
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1894 : Nat.sqrt (1894 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1894]; decide
    · -- n = 1895
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1895 : Nat.sqrt (1895 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1895]; decide
    · -- n = 1896
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1896 : Nat.sqrt (1896 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1896]; decide
    · -- n = 1897
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1897 : Nat.sqrt (1897 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1897]; decide
    · -- n = 1898
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1898 : Nat.sqrt (1898 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1898]; decide
    · -- n = 1899
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1899 : Nat.sqrt (1899 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1899]; decide
    · -- n = 1900
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1900 : Nat.sqrt (1900 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1900]; decide
    · -- n = 1901
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1901 : Nat.sqrt (1901 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1901]; decide
    · -- n = 1902
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1902 : Nat.sqrt (1902 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1902]; decide
    · -- n = 1903
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1903 : Nat.sqrt (1903 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1903]; decide
    · -- n = 1904
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1904 : Nat.sqrt (1904 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1904]; decide
    · -- n = 1905
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1905 : Nat.sqrt (1905 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1905]; decide
    · -- n = 1906
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1906 : Nat.sqrt (1906 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1906]; decide
    · -- n = 1907
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1907 : Nat.sqrt (1907 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1907]; decide
    · -- n = 1908
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1908 : Nat.sqrt (1908 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1908]; decide
    · -- n = 1909
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1909 : Nat.sqrt (1909 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1909]; decide
    · -- n = 1910
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1910 : Nat.sqrt (1910 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1910]; decide
    · -- n = 1911
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1911 : Nat.sqrt (1911 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1911]; decide
    · -- n = 1912
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1912 : Nat.sqrt (1912 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1912]; decide
    · -- n = 1913
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1913 : Nat.sqrt (1913 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1913]; decide
    · -- n = 1914
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1914 : Nat.sqrt (1914 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1914]; decide
    · -- n = 1915
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1915 : Nat.sqrt (1915 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1915]; decide
    · -- n = 1916
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1916 : Nat.sqrt (1916 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1916]; decide
    · -- n = 1917
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1917 : Nat.sqrt (1917 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1917]; decide
    · -- n = 1918
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1918 : Nat.sqrt (1918 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1918]; decide
    · -- n = 1919
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1919 : Nat.sqrt (1919 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1919]; decide
    · -- n = 1920
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1920 : Nat.sqrt (1920 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1920]; decide
    · -- n = 1921
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1921 : Nat.sqrt (1921 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1921]; decide
    · -- n = 1922
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1922 : Nat.sqrt (1922 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1922]; decide
    · -- n = 1923
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1923 : Nat.sqrt (1923 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1923]; decide
    · -- n = 1924
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1924 : Nat.sqrt (1924 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1924]; decide
    · -- n = 1925
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1925 : Nat.sqrt (1925 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1925]; decide
    · -- n = 1926
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1926 : Nat.sqrt (1926 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1926]; decide
    · -- n = 1927
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1927 : Nat.sqrt (1927 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1927]; decide
    · -- n = 1928
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1928 : Nat.sqrt (1928 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1928]; decide
    · -- n = 1929
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1929 : Nat.sqrt (1929 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1929]; decide
    · -- n = 1930
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1930 : Nat.sqrt (1930 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1930]; decide
    · -- n = 1931
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1931 : Nat.sqrt (1931 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1931]; decide
    · -- n = 1932
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1932 : Nat.sqrt (1932 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1932]; decide
    · -- n = 1933
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_1933 : Nat.sqrt (1933 + 2) = 43 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1933]; decide
    · -- n = 1934
      use 277
      refine ⟨by decide, by decide, ?_⟩
      have h_1934 : Nat.sqrt (1934 + 277) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1934]; decide
    · -- n = 1935
      use 277
      refine ⟨by decide, by decide, ?_⟩
      have h_1935 : Nat.sqrt (1935 + 277) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1935]; decide
    · -- n = 1936
      use 277
      refine ⟨by decide, by decide, ?_⟩
      have h_1936 : Nat.sqrt (1936 + 277) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1936]; decide
    · -- n = 1937
      use 277
      refine ⟨by decide, by decide, ?_⟩
      have h_1937 : Nat.sqrt (1937 + 277) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1937]; decide
    · -- n = 1938
      use 271
      refine ⟨by decide, by decide, ?_⟩
      have h_1938 : Nat.sqrt (1938 + 271) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1938]; decide
    · -- n = 1939
      use 271
      refine ⟨by decide, by decide, ?_⟩
      have h_1939 : Nat.sqrt (1939 + 271) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1939]; decide
    · -- n = 1940
      use 269
      refine ⟨by decide, by decide, ?_⟩
      have h_1940 : Nat.sqrt (1940 + 269) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1940]; decide
    · -- n = 1941
      use 269
      refine ⟨by decide, by decide, ?_⟩
      have h_1941 : Nat.sqrt (1941 + 269) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1941]; decide
    · -- n = 1942
      use 269
      refine ⟨by decide, by decide, ?_⟩
      have h_1942 : Nat.sqrt (1942 + 269) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1942]; decide
    · -- n = 1943
      use 269
      refine ⟨by decide, by decide, ?_⟩
      have h_1943 : Nat.sqrt (1943 + 269) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1943]; decide
    · -- n = 1944
      use 269
      refine ⟨by decide, by decide, ?_⟩
      have h_1944 : Nat.sqrt (1944 + 269) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1944]; decide
    · -- n = 1945
      use 269
      refine ⟨by decide, by decide, ?_⟩
      have h_1945 : Nat.sqrt (1945 + 269) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1945]; decide
    · -- n = 1946
      use 263
      refine ⟨by decide, by decide, ?_⟩
      have h_1946 : Nat.sqrt (1946 + 263) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1946]; decide
    · -- n = 1947
      use 263
      refine ⟨by decide, by decide, ?_⟩
      have h_1947 : Nat.sqrt (1947 + 263) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1947]; decide
    · -- n = 1948
      use 263
      refine ⟨by decide, by decide, ?_⟩
      have h_1948 : Nat.sqrt (1948 + 263) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1948]; decide
    · -- n = 1949
      use 263
      refine ⟨by decide, by decide, ?_⟩
      have h_1949 : Nat.sqrt (1949 + 263) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1949]; decide
    · -- n = 1950
      use 263
      refine ⟨by decide, by decide, ?_⟩
      have h_1950 : Nat.sqrt (1950 + 263) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1950]; decide
    · -- n = 1951
      use 263
      refine ⟨by decide, by decide, ?_⟩
      have h_1951 : Nat.sqrt (1951 + 263) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1951]; decide
    · -- n = 1952
      use 257
      refine ⟨by decide, by decide, ?_⟩
      have h_1952 : Nat.sqrt (1952 + 257) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1952]; decide
    · -- n = 1953
      use 257
      refine ⟨by decide, by decide, ?_⟩
      have h_1953 : Nat.sqrt (1953 + 257) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1953]; decide
    · -- n = 1954
      use 257
      refine ⟨by decide, by decide, ?_⟩
      have h_1954 : Nat.sqrt (1954 + 257) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1954]; decide
    · -- n = 1955
      use 257
      refine ⟨by decide, by decide, ?_⟩
      have h_1955 : Nat.sqrt (1955 + 257) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1955]; decide
    · -- n = 1956
      use 257
      refine ⟨by decide, by decide, ?_⟩
      have h_1956 : Nat.sqrt (1956 + 257) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1956]; decide
    · -- n = 1957
      use 257
      refine ⟨by decide, by decide, ?_⟩
      have h_1957 : Nat.sqrt (1957 + 257) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1957]; decide
    · -- n = 1958
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_1958 : Nat.sqrt (1958 + 251) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1958]; decide
    · -- n = 1959
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_1959 : Nat.sqrt (1959 + 251) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1959]; decide
    · -- n = 1960
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_1960 : Nat.sqrt (1960 + 251) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1960]; decide
    · -- n = 1961
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_1961 : Nat.sqrt (1961 + 251) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1961]; decide
    · -- n = 1962
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_1962 : Nat.sqrt (1962 + 251) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1962]; decide
    · -- n = 1963
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_1963 : Nat.sqrt (1963 + 251) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1963]; decide
    · -- n = 1964
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_1964 : Nat.sqrt (1964 + 251) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1964]; decide
    · -- n = 1965
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_1965 : Nat.sqrt (1965 + 251) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1965]; decide
    · -- n = 1966
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_1966 : Nat.sqrt (1966 + 251) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1966]; decide
    · -- n = 1967
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_1967 : Nat.sqrt (1967 + 251) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1967]; decide
    · -- n = 1968
      use 241
      refine ⟨by decide, by decide, ?_⟩
      have h_1968 : Nat.sqrt (1968 + 241) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1968]; decide
    · -- n = 1969
      use 241
      refine ⟨by decide, by decide, ?_⟩
      have h_1969 : Nat.sqrt (1969 + 241) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1969]; decide
    · -- n = 1970
      use 239
      refine ⟨by decide, by decide, ?_⟩
      have h_1970 : Nat.sqrt (1970 + 239) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1970]; decide
    · -- n = 1971
      use 239
      refine ⟨by decide, by decide, ?_⟩
      have h_1971 : Nat.sqrt (1971 + 239) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1971]; decide
    · -- n = 1972
      use 239
      refine ⟨by decide, by decide, ?_⟩
      have h_1972 : Nat.sqrt (1972 + 239) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1972]; decide
    · -- n = 1973
      use 239
      refine ⟨by decide, by decide, ?_⟩
      have h_1973 : Nat.sqrt (1973 + 239) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1973]; decide
    · -- n = 1974
      use 239
      refine ⟨by decide, by decide, ?_⟩
      have h_1974 : Nat.sqrt (1974 + 239) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1974]; decide
    · -- n = 1975
      use 239
      refine ⟨by decide, by decide, ?_⟩
      have h_1975 : Nat.sqrt (1975 + 239) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1975]; decide
    · -- n = 1976
      use 233
      refine ⟨by decide, by decide, ?_⟩
      have h_1976 : Nat.sqrt (1976 + 233) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1976]; decide
    · -- n = 1977
      use 233
      refine ⟨by decide, by decide, ?_⟩
      have h_1977 : Nat.sqrt (1977 + 233) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1977]; decide
    · -- n = 1978
      use 233
      refine ⟨by decide, by decide, ?_⟩
      have h_1978 : Nat.sqrt (1978 + 233) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1978]; decide
    · -- n = 1979
      use 233
      refine ⟨by decide, by decide, ?_⟩
      have h_1979 : Nat.sqrt (1979 + 233) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1979]; decide
    · -- n = 1980
      use 229
      refine ⟨by decide, by decide, ?_⟩
      have h_1980 : Nat.sqrt (1980 + 229) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1980]; decide
    · -- n = 1981
      use 229
      refine ⟨by decide, by decide, ?_⟩
      have h_1981 : Nat.sqrt (1981 + 229) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1981]; decide
    · -- n = 1982
      use 227
      refine ⟨by decide, by decide, ?_⟩
      have h_1982 : Nat.sqrt (1982 + 227) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1982]; decide
    · -- n = 1983
      use 227
      refine ⟨by decide, by decide, ?_⟩
      have h_1983 : Nat.sqrt (1983 + 227) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1983]; decide
    · -- n = 1984
      use 227
      refine ⟨by decide, by decide, ?_⟩
      have h_1984 : Nat.sqrt (1984 + 227) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1984]; decide
    · -- n = 1985
      use 227
      refine ⟨by decide, by decide, ?_⟩
      have h_1985 : Nat.sqrt (1985 + 227) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1985]; decide
    · -- n = 1986
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_1986 : Nat.sqrt (1986 + 223) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1986]; decide
    · -- n = 1987
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_1987 : Nat.sqrt (1987 + 223) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1987]; decide
    · -- n = 1988
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_1988 : Nat.sqrt (1988 + 223) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1988]; decide
    · -- n = 1989
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_1989 : Nat.sqrt (1989 + 223) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1989]; decide
    · -- n = 1990
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_1990 : Nat.sqrt (1990 + 223) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1990]; decide
    · -- n = 1991
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_1991 : Nat.sqrt (1991 + 223) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1991]; decide
    · -- n = 1992
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_1992 : Nat.sqrt (1992 + 223) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1992]; decide
    · -- n = 1993
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_1993 : Nat.sqrt (1993 + 223) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1993]; decide
    · -- n = 1994
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_1994 : Nat.sqrt (1994 + 223) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1994]; decide
    · -- n = 1995
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_1995 : Nat.sqrt (1995 + 223) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1995]; decide
    · -- n = 1996
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_1996 : Nat.sqrt (1996 + 223) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1996]; decide
    · -- n = 1997
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_1997 : Nat.sqrt (1997 + 223) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1997]; decide
    · -- n = 1998
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_1998 : Nat.sqrt (1998 + 211) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1998]; decide
    · -- n = 1999
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_1999 : Nat.sqrt (1999 + 211) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_1999]; decide
    · -- n = 2000
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_2000 : Nat.sqrt (2000 + 211) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2000]; decide
    · -- n = 2001
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_2001 : Nat.sqrt (2001 + 211) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2001]; decide
    · -- n = 2002
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_2002 : Nat.sqrt (2002 + 211) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2002]; decide
    · -- n = 2003
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_2003 : Nat.sqrt (2003 + 211) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2003]; decide
    · -- n = 2004
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_2004 : Nat.sqrt (2004 + 211) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2004]; decide
    · -- n = 2005
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_2005 : Nat.sqrt (2005 + 211) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2005]; decide
    · -- n = 2006
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_2006 : Nat.sqrt (2006 + 211) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2006]; decide
    · -- n = 2007
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_2007 : Nat.sqrt (2007 + 211) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2007]; decide
    · -- n = 2008
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_2008 : Nat.sqrt (2008 + 211) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2008]; decide
    · -- n = 2009
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_2009 : Nat.sqrt (2009 + 211) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2009]; decide
    · -- n = 2010
      use 199
      refine ⟨by decide, by decide, ?_⟩
      have h_2010 : Nat.sqrt (2010 + 199) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2010]; decide
    · -- n = 2011
      use 199
      refine ⟨by decide, by decide, ?_⟩
      have h_2011 : Nat.sqrt (2011 + 199) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2011]; decide
    · -- n = 2012
      use 197
      refine ⟨by decide, by decide, ?_⟩
      have h_2012 : Nat.sqrt (2012 + 197) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2012]; decide
    · -- n = 2013
      use 197
      refine ⟨by decide, by decide, ?_⟩
      have h_2013 : Nat.sqrt (2013 + 197) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2013]; decide
    · -- n = 2014
      use 197
      refine ⟨by decide, by decide, ?_⟩
      have h_2014 : Nat.sqrt (2014 + 197) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2014]; decide
    · -- n = 2015
      use 197
      refine ⟨by decide, by decide, ?_⟩
      have h_2015 : Nat.sqrt (2015 + 197) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2015]; decide
    · -- n = 2016
      use 193
      refine ⟨by decide, by decide, ?_⟩
      have h_2016 : Nat.sqrt (2016 + 193) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2016]; decide
    · -- n = 2017
      use 193
      refine ⟨by decide, by decide, ?_⟩
      have h_2017 : Nat.sqrt (2017 + 193) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2017]; decide
    · -- n = 2018
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_2018 : Nat.sqrt (2018 + 191) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2018]; decide
    · -- n = 2019
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_2019 : Nat.sqrt (2019 + 191) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2019]; decide
    · -- n = 2020
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_2020 : Nat.sqrt (2020 + 191) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2020]; decide
    · -- n = 2021
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_2021 : Nat.sqrt (2021 + 191) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2021]; decide
    · -- n = 2022
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_2022 : Nat.sqrt (2022 + 191) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2022]; decide
    · -- n = 2023
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_2023 : Nat.sqrt (2023 + 191) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2023]; decide
    · -- n = 2024
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_2024 : Nat.sqrt (2024 + 191) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2024]; decide
    · -- n = 2025
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_2025 : Nat.sqrt (2025 + 191) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2025]; decide
    · -- n = 2026
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_2026 : Nat.sqrt (2026 + 191) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2026]; decide
    · -- n = 2027
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_2027 : Nat.sqrt (2027 + 191) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2027]; decide
    · -- n = 2028
      use 181
      refine ⟨by decide, by decide, ?_⟩
      have h_2028 : Nat.sqrt (2028 + 181) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2028]; decide
    · -- n = 2029
      use 181
      refine ⟨by decide, by decide, ?_⟩
      have h_2029 : Nat.sqrt (2029 + 181) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2029]; decide
    · -- n = 2030
      use 179
      refine ⟨by decide, by decide, ?_⟩
      have h_2030 : Nat.sqrt (2030 + 179) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2030]; decide
    · -- n = 2031
      use 179
      refine ⟨by decide, by decide, ?_⟩
      have h_2031 : Nat.sqrt (2031 + 179) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2031]; decide
    · -- n = 2032
      use 179
      refine ⟨by decide, by decide, ?_⟩
      have h_2032 : Nat.sqrt (2032 + 179) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2032]; decide
    · -- n = 2033
      use 179
      refine ⟨by decide, by decide, ?_⟩
      have h_2033 : Nat.sqrt (2033 + 179) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2033]; decide
    · -- n = 2034
      use 179
      refine ⟨by decide, by decide, ?_⟩
      have h_2034 : Nat.sqrt (2034 + 179) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2034]; decide
    · -- n = 2035
      use 179
      refine ⟨by decide, by decide, ?_⟩
      have h_2035 : Nat.sqrt (2035 + 179) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2035]; decide
    · -- n = 2036
      use 173
      refine ⟨by decide, by decide, ?_⟩
      have h_2036 : Nat.sqrt (2036 + 173) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2036]; decide
    · -- n = 2037
      use 173
      refine ⟨by decide, by decide, ?_⟩
      have h_2037 : Nat.sqrt (2037 + 173) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2037]; decide
    · -- n = 2038
      use 173
      refine ⟨by decide, by decide, ?_⟩
      have h_2038 : Nat.sqrt (2038 + 173) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2038]; decide
    · -- n = 2039
      use 173
      refine ⟨by decide, by decide, ?_⟩
      have h_2039 : Nat.sqrt (2039 + 173) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2039]; decide
    · -- n = 2040
      use 173
      refine ⟨by decide, by decide, ?_⟩
      have h_2040 : Nat.sqrt (2040 + 173) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2040]; decide
    · -- n = 2041
      use 173
      refine ⟨by decide, by decide, ?_⟩
      have h_2041 : Nat.sqrt (2041 + 173) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2041]; decide
    · -- n = 2042
      use 167
      refine ⟨by decide, by decide, ?_⟩
      have h_2042 : Nat.sqrt (2042 + 167) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2042]; decide
    · -- n = 2043
      use 167
      refine ⟨by decide, by decide, ?_⟩
      have h_2043 : Nat.sqrt (2043 + 167) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2043]; decide
    · -- n = 2044
      use 167
      refine ⟨by decide, by decide, ?_⟩
      have h_2044 : Nat.sqrt (2044 + 167) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2044]; decide
    · -- n = 2045
      use 167
      refine ⟨by decide, by decide, ?_⟩
      have h_2045 : Nat.sqrt (2045 + 167) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2045]; decide
    · -- n = 2046
      use 163
      refine ⟨by decide, by decide, ?_⟩
      have h_2046 : Nat.sqrt (2046 + 163) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2046]; decide
    · -- n = 2047
      use 163
      refine ⟨by decide, by decide, ?_⟩
      have h_2047 : Nat.sqrt (2047 + 163) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2047]; decide
    · -- n = 2048
      use 163
      refine ⟨by decide, by decide, ?_⟩
      have h_2048 : Nat.sqrt (2048 + 163) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2048]; decide
    · -- n = 2049
      use 163
      refine ⟨by decide, by decide, ?_⟩
      have h_2049 : Nat.sqrt (2049 + 163) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2049]; decide
    · -- n = 2050
      use 163
      refine ⟨by decide, by decide, ?_⟩
      have h_2050 : Nat.sqrt (2050 + 163) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2050]; decide
    · -- n = 2051
      use 163
      refine ⟨by decide, by decide, ?_⟩
      have h_2051 : Nat.sqrt (2051 + 163) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2051]; decide
    · -- n = 2052
      use 157
      refine ⟨by decide, by decide, ?_⟩
      have h_2052 : Nat.sqrt (2052 + 157) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2052]; decide
    · -- n = 2053
      use 157
      refine ⟨by decide, by decide, ?_⟩
      have h_2053 : Nat.sqrt (2053 + 157) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2053]; decide
    · -- n = 2054
      use 157
      refine ⟨by decide, by decide, ?_⟩
      have h_2054 : Nat.sqrt (2054 + 157) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2054]; decide
    · -- n = 2055
      use 157
      refine ⟨by decide, by decide, ?_⟩
      have h_2055 : Nat.sqrt (2055 + 157) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2055]; decide
    · -- n = 2056
      use 157
      refine ⟨by decide, by decide, ?_⟩
      have h_2056 : Nat.sqrt (2056 + 157) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2056]; decide
    · -- n = 2057
      use 157
      refine ⟨by decide, by decide, ?_⟩
      have h_2057 : Nat.sqrt (2057 + 157) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2057]; decide
    · -- n = 2058
      use 151
      refine ⟨by decide, by decide, ?_⟩
      have h_2058 : Nat.sqrt (2058 + 151) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2058]; decide
    · -- n = 2059
      use 151
      refine ⟨by decide, by decide, ?_⟩
      have h_2059 : Nat.sqrt (2059 + 151) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2059]; decide
    · -- n = 2060
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_2060 : Nat.sqrt (2060 + 149) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2060]; decide
    · -- n = 2061
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_2061 : Nat.sqrt (2061 + 149) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2061]; decide
    · -- n = 2062
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_2062 : Nat.sqrt (2062 + 149) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2062]; decide
    · -- n = 2063
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_2063 : Nat.sqrt (2063 + 149) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2063]; decide
    · -- n = 2064
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_2064 : Nat.sqrt (2064 + 149) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2064]; decide
    · -- n = 2065
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_2065 : Nat.sqrt (2065 + 149) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2065]; decide
    · -- n = 2066
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_2066 : Nat.sqrt (2066 + 149) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2066]; decide
    · -- n = 2067
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_2067 : Nat.sqrt (2067 + 149) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2067]; decide
    · -- n = 2068
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_2068 : Nat.sqrt (2068 + 149) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2068]; decide
    · -- n = 2069
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_2069 : Nat.sqrt (2069 + 149) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2069]; decide
    · -- n = 2070
      use 139
      refine ⟨by decide, by decide, ?_⟩
      have h_2070 : Nat.sqrt (2070 + 139) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2070]; decide
    · -- n = 2071
      use 139
      refine ⟨by decide, by decide, ?_⟩
      have h_2071 : Nat.sqrt (2071 + 139) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2071]; decide
    · -- n = 2072
      use 137
      refine ⟨by decide, by decide, ?_⟩
      have h_2072 : Nat.sqrt (2072 + 137) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2072]; decide
    · -- n = 2073
      use 137
      refine ⟨by decide, by decide, ?_⟩
      have h_2073 : Nat.sqrt (2073 + 137) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2073]; decide
    · -- n = 2074
      use 137
      refine ⟨by decide, by decide, ?_⟩
      have h_2074 : Nat.sqrt (2074 + 137) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2074]; decide
    · -- n = 2075
      use 137
      refine ⟨by decide, by decide, ?_⟩
      have h_2075 : Nat.sqrt (2075 + 137) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2075]; decide
    · -- n = 2076
      use 137
      refine ⟨by decide, by decide, ?_⟩
      have h_2076 : Nat.sqrt (2076 + 137) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2076]; decide
    · -- n = 2077
      use 137
      refine ⟨by decide, by decide, ?_⟩
      have h_2077 : Nat.sqrt (2077 + 137) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2077]; decide
    · -- n = 2078
      use 131
      refine ⟨by decide, by decide, ?_⟩
      have h_2078 : Nat.sqrt (2078 + 131) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2078]; decide
    · -- n = 2079
      use 131
      refine ⟨by decide, by decide, ?_⟩
      have h_2079 : Nat.sqrt (2079 + 131) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2079]; decide
    · -- n = 2080
      use 131
      refine ⟨by decide, by decide, ?_⟩
      have h_2080 : Nat.sqrt (2080 + 131) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2080]; decide
    · -- n = 2081
      use 131
      refine ⟨by decide, by decide, ?_⟩
      have h_2081 : Nat.sqrt (2081 + 131) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2081]; decide
    · -- n = 2082
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_2082 : Nat.sqrt (2082 + 127) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2082]; decide
    · -- n = 2083
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_2083 : Nat.sqrt (2083 + 127) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2083]; decide
    · -- n = 2084
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_2084 : Nat.sqrt (2084 + 127) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2084]; decide
    · -- n = 2085
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_2085 : Nat.sqrt (2085 + 127) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2085]; decide
    · -- n = 2086
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_2086 : Nat.sqrt (2086 + 127) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2086]; decide
    · -- n = 2087
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_2087 : Nat.sqrt (2087 + 127) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2087]; decide
    · -- n = 2088
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_2088 : Nat.sqrt (2088 + 127) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2088]; decide
    · -- n = 2089
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_2089 : Nat.sqrt (2089 + 127) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2089]; decide
    · -- n = 2090
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_2090 : Nat.sqrt (2090 + 127) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2090]; decide
    · -- n = 2091
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_2091 : Nat.sqrt (2091 + 127) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2091]; decide
    · -- n = 2092
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_2092 : Nat.sqrt (2092 + 127) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2092]; decide
    · -- n = 2093
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_2093 : Nat.sqrt (2093 + 127) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2093]; decide
    · -- n = 2094
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_2094 : Nat.sqrt (2094 + 127) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2094]; decide
    · -- n = 2095
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_2095 : Nat.sqrt (2095 + 127) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2095]; decide
    · -- n = 2096
      use 113
      refine ⟨by decide, by decide, ?_⟩
      have h_2096 : Nat.sqrt (2096 + 113) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2096]; decide
    · -- n = 2097
      use 113
      refine ⟨by decide, by decide, ?_⟩
      have h_2097 : Nat.sqrt (2097 + 113) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2097]; decide
    · -- n = 2098
      use 113
      refine ⟨by decide, by decide, ?_⟩
      have h_2098 : Nat.sqrt (2098 + 113) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2098]; decide
    · -- n = 2099
      use 113
      refine ⟨by decide, by decide, ?_⟩
      have h_2099 : Nat.sqrt (2099 + 113) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2099]; decide
    · -- n = 2100
      use 109
      refine ⟨by decide, by decide, ?_⟩
      have h_2100 : Nat.sqrt (2100 + 109) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2100]; decide
    · -- n = 2101
      use 109
      refine ⟨by decide, by decide, ?_⟩
      have h_2101 : Nat.sqrt (2101 + 109) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2101]; decide
    · -- n = 2102
      use 107
      refine ⟨by decide, by decide, ?_⟩
      have h_2102 : Nat.sqrt (2102 + 107) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2102]; decide
    · -- n = 2103
      use 107
      refine ⟨by decide, by decide, ?_⟩
      have h_2103 : Nat.sqrt (2103 + 107) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2103]; decide
    · -- n = 2104
      use 107
      refine ⟨by decide, by decide, ?_⟩
      have h_2104 : Nat.sqrt (2104 + 107) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2104]; decide
    · -- n = 2105
      use 107
      refine ⟨by decide, by decide, ?_⟩
      have h_2105 : Nat.sqrt (2105 + 107) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2105]; decide
    · -- n = 2106
      use 103
      refine ⟨by decide, by decide, ?_⟩
      have h_2106 : Nat.sqrt (2106 + 103) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2106]; decide
    · -- n = 2107
      use 103
      refine ⟨by decide, by decide, ?_⟩
      have h_2107 : Nat.sqrt (2107 + 103) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2107]; decide
    · -- n = 2108
      use 101
      refine ⟨by decide, by decide, ?_⟩
      have h_2108 : Nat.sqrt (2108 + 101) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2108]; decide
    · -- n = 2109
      use 101
      refine ⟨by decide, by decide, ?_⟩
      have h_2109 : Nat.sqrt (2109 + 101) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2109]; decide
    · -- n = 2110
      use 101
      refine ⟨by decide, by decide, ?_⟩
      have h_2110 : Nat.sqrt (2110 + 101) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2110]; decide
    · -- n = 2111
      use 101
      refine ⟨by decide, by decide, ?_⟩
      have h_2111 : Nat.sqrt (2111 + 101) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2111]; decide
    · -- n = 2112
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_2112 : Nat.sqrt (2112 + 97) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2112]; decide
    · -- n = 2113
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_2113 : Nat.sqrt (2113 + 97) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2113]; decide
    · -- n = 2114
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_2114 : Nat.sqrt (2114 + 97) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2114]; decide
    · -- n = 2115
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_2115 : Nat.sqrt (2115 + 97) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2115]; decide
    · -- n = 2116
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_2116 : Nat.sqrt (2116 + 97) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2116]; decide
    · -- n = 2117
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_2117 : Nat.sqrt (2117 + 97) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2117]; decide
    · -- n = 2118
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_2118 : Nat.sqrt (2118 + 97) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2118]; decide
    · -- n = 2119
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_2119 : Nat.sqrt (2119 + 97) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2119]; decide
    · -- n = 2120
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_2120 : Nat.sqrt (2120 + 89) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2120]; decide
    · -- n = 2121
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_2121 : Nat.sqrt (2121 + 89) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2121]; decide
    · -- n = 2122
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_2122 : Nat.sqrt (2122 + 89) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2122]; decide
    · -- n = 2123
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_2123 : Nat.sqrt (2123 + 89) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2123]; decide
    · -- n = 2124
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_2124 : Nat.sqrt (2124 + 89) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2124]; decide
    · -- n = 2125
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_2125 : Nat.sqrt (2125 + 89) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2125]; decide
    · -- n = 2126
      use 83
      refine ⟨by decide, by decide, ?_⟩
      have h_2126 : Nat.sqrt (2126 + 83) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2126]; decide
    · -- n = 2127
      use 83
      refine ⟨by decide, by decide, ?_⟩
      have h_2127 : Nat.sqrt (2127 + 83) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2127]; decide
    · -- n = 2128
      use 83
      refine ⟨by decide, by decide, ?_⟩
      have h_2128 : Nat.sqrt (2128 + 83) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2128]; decide
    · -- n = 2129
      use 83
      refine ⟨by decide, by decide, ?_⟩
      have h_2129 : Nat.sqrt (2129 + 83) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2129]; decide
    · -- n = 2130
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_2130 : Nat.sqrt (2130 + 79) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2130]; decide
    · -- n = 2131
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_2131 : Nat.sqrt (2131 + 79) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2131]; decide
    · -- n = 2132
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_2132 : Nat.sqrt (2132 + 79) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2132]; decide
    · -- n = 2133
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_2133 : Nat.sqrt (2133 + 79) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2133]; decide
    · -- n = 2134
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_2134 : Nat.sqrt (2134 + 79) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2134]; decide
    · -- n = 2135
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_2135 : Nat.sqrt (2135 + 79) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2135]; decide
    · -- n = 2136
      use 73
      refine ⟨by decide, by decide, ?_⟩
      have h_2136 : Nat.sqrt (2136 + 73) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2136]; decide
    · -- n = 2137
      use 73
      refine ⟨by decide, by decide, ?_⟩
      have h_2137 : Nat.sqrt (2137 + 73) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2137]; decide
    · -- n = 2138
      use 71
      refine ⟨by decide, by decide, ?_⟩
      have h_2138 : Nat.sqrt (2138 + 71) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2138]; decide
    · -- n = 2139
      use 71
      refine ⟨by decide, by decide, ?_⟩
      have h_2139 : Nat.sqrt (2139 + 71) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2139]; decide
    · -- n = 2140
      use 71
      refine ⟨by decide, by decide, ?_⟩
      have h_2140 : Nat.sqrt (2140 + 71) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2140]; decide
    · -- n = 2141
      use 71
      refine ⟨by decide, by decide, ?_⟩
      have h_2141 : Nat.sqrt (2141 + 71) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2141]; decide
    · -- n = 2142
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_2142 : Nat.sqrt (2142 + 67) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2142]; decide
    · -- n = 2143
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_2143 : Nat.sqrt (2143 + 67) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2143]; decide
    · -- n = 2144
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_2144 : Nat.sqrt (2144 + 67) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2144]; decide
    · -- n = 2145
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_2145 : Nat.sqrt (2145 + 67) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2145]; decide
    · -- n = 2146
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_2146 : Nat.sqrt (2146 + 67) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2146]; decide
    · -- n = 2147
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_2147 : Nat.sqrt (2147 + 67) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2147]; decide
    · -- n = 2148
      use 61
      refine ⟨by decide, by decide, ?_⟩
      have h_2148 : Nat.sqrt (2148 + 61) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2148]; decide
    · -- n = 2149
      use 61
      refine ⟨by decide, by decide, ?_⟩
      have h_2149 : Nat.sqrt (2149 + 61) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2149]; decide
    · -- n = 2150
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_2150 : Nat.sqrt (2150 + 59) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2150]; decide
    · -- n = 2151
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_2151 : Nat.sqrt (2151 + 59) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2151]; decide
    · -- n = 2152
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_2152 : Nat.sqrt (2152 + 59) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2152]; decide
    · -- n = 2153
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_2153 : Nat.sqrt (2153 + 59) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2153]; decide
    · -- n = 2154
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_2154 : Nat.sqrt (2154 + 59) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2154]; decide
    · -- n = 2155
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_2155 : Nat.sqrt (2155 + 59) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2155]; decide
    · -- n = 2156
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_2156 : Nat.sqrt (2156 + 53) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2156]; decide
    · -- n = 2157
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_2157 : Nat.sqrt (2157 + 53) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2157]; decide
    · -- n = 2158
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_2158 : Nat.sqrt (2158 + 53) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2158]; decide
    · -- n = 2159
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_2159 : Nat.sqrt (2159 + 53) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2159]; decide
    · -- n = 2160
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_2160 : Nat.sqrt (2160 + 53) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2160]; decide
    · -- n = 2161
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_2161 : Nat.sqrt (2161 + 53) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2161]; decide
    · -- n = 2162
      use 47
      refine ⟨by decide, by decide, ?_⟩
      have h_2162 : Nat.sqrt (2162 + 47) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2162]; decide
    · -- n = 2163
      use 47
      refine ⟨by decide, by decide, ?_⟩
      have h_2163 : Nat.sqrt (2163 + 47) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2163]; decide
    · -- n = 2164
      use 47
      refine ⟨by decide, by decide, ?_⟩
      have h_2164 : Nat.sqrt (2164 + 47) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2164]; decide
    · -- n = 2165
      use 47
      refine ⟨by decide, by decide, ?_⟩
      have h_2165 : Nat.sqrt (2165 + 47) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2165]; decide
    · -- n = 2166
      use 43
      refine ⟨by decide, by decide, ?_⟩
      have h_2166 : Nat.sqrt (2166 + 43) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2166]; decide
    · -- n = 2167
      use 43
      refine ⟨by decide, by decide, ?_⟩
      have h_2167 : Nat.sqrt (2167 + 43) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2167]; decide
    · -- n = 2168
      use 41
      refine ⟨by decide, by decide, ?_⟩
      have h_2168 : Nat.sqrt (2168 + 41) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2168]; decide
    · -- n = 2169
      use 41
      refine ⟨by decide, by decide, ?_⟩
      have h_2169 : Nat.sqrt (2169 + 41) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2169]; decide
    · -- n = 2170
      use 41
      refine ⟨by decide, by decide, ?_⟩
      have h_2170 : Nat.sqrt (2170 + 41) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2170]; decide
    · -- n = 2171
      use 41
      refine ⟨by decide, by decide, ?_⟩
      have h_2171 : Nat.sqrt (2171 + 41) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2171]; decide
    · -- n = 2172
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_2172 : Nat.sqrt (2172 + 37) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2172]; decide
    · -- n = 2173
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_2173 : Nat.sqrt (2173 + 37) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2173]; decide
    · -- n = 2174
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_2174 : Nat.sqrt (2174 + 37) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2174]; decide
    · -- n = 2175
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_2175 : Nat.sqrt (2175 + 37) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2175]; decide
    · -- n = 2176
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_2176 : Nat.sqrt (2176 + 37) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2176]; decide
    · -- n = 2177
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_2177 : Nat.sqrt (2177 + 37) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2177]; decide
    · -- n = 2178
      use 31
      refine ⟨by decide, by decide, ?_⟩
      have h_2178 : Nat.sqrt (2178 + 31) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2178]; decide
    · -- n = 2179
      use 31
      refine ⟨by decide, by decide, ?_⟩
      have h_2179 : Nat.sqrt (2179 + 31) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2179]; decide
    · -- n = 2180
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_2180 : Nat.sqrt (2180 + 29) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2180]; decide
    · -- n = 2181
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_2181 : Nat.sqrt (2181 + 29) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2181]; decide
    · -- n = 2182
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_2182 : Nat.sqrt (2182 + 29) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2182]; decide
    · -- n = 2183
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_2183 : Nat.sqrt (2183 + 29) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2183]; decide
    · -- n = 2184
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_2184 : Nat.sqrt (2184 + 29) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2184]; decide
    · -- n = 2185
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_2185 : Nat.sqrt (2185 + 29) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2185]; decide
    · -- n = 2186
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_2186 : Nat.sqrt (2186 + 23) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2186]; decide
    · -- n = 2187
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_2187 : Nat.sqrt (2187 + 23) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2187]; decide
    · -- n = 2188
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_2188 : Nat.sqrt (2188 + 23) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2188]; decide
    · -- n = 2189
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_2189 : Nat.sqrt (2189 + 23) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2189]; decide
    · -- n = 2190
      use 19
      refine ⟨by decide, by decide, ?_⟩
      have h_2190 : Nat.sqrt (2190 + 19) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2190]; decide
    · -- n = 2191
      use 19
      refine ⟨by decide, by decide, ?_⟩
      have h_2191 : Nat.sqrt (2191 + 19) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2191]; decide
    · -- n = 2192
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_2192 : Nat.sqrt (2192 + 17) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2192]; decide
    · -- n = 2193
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_2193 : Nat.sqrt (2193 + 17) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2193]; decide
    · -- n = 2194
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_2194 : Nat.sqrt (2194 + 17) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2194]; decide
    · -- n = 2195
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_2195 : Nat.sqrt (2195 + 17) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2195]; decide
    · -- n = 2196
      use 13
      refine ⟨by decide, by decide, ?_⟩
      have h_2196 : Nat.sqrt (2196 + 13) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2196]; decide
    · -- n = 2197
      use 13
      refine ⟨by decide, by decide, ?_⟩
      have h_2197 : Nat.sqrt (2197 + 13) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2197]; decide
    · -- n = 2198
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_2198 : Nat.sqrt (2198 + 11) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2198]; decide
    · -- n = 2199
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_2199 : Nat.sqrt (2199 + 11) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2199]; decide
    · -- n = 2200
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_2200 : Nat.sqrt (2200 + 11) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2200]; decide
    · -- n = 2201
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_2201 : Nat.sqrt (2201 + 11) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2201]; decide
    · -- n = 2202
      use 7
      refine ⟨by decide, by decide, ?_⟩
      have h_2202 : Nat.sqrt (2202 + 7) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2202]; decide
    · -- n = 2203
      use 7
      refine ⟨by decide, by decide, ?_⟩
      have h_2203 : Nat.sqrt (2203 + 7) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2203]; decide
    · -- n = 2204
      use 5
      refine ⟨by decide, by decide, ?_⟩
      have h_2204 : Nat.sqrt (2204 + 5) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2204]; decide
    · -- n = 2205
      use 5
      refine ⟨by decide, by decide, ?_⟩
      have h_2205 : Nat.sqrt (2205 + 5) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2205]; decide
    · -- n = 2206
      use 3
      refine ⟨by decide, by decide, ?_⟩
      have h_2206 : Nat.sqrt (2206 + 3) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2206]; decide
    · -- n = 2207
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2207 : Nat.sqrt (2207 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2207]; decide
    · -- n = 2208
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2208 : Nat.sqrt (2208 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2208]; decide
    · -- n = 2209
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2209 : Nat.sqrt (2209 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2209]; decide
    · -- n = 2210
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2210 : Nat.sqrt (2210 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2210]; decide
    · -- n = 2211
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2211 : Nat.sqrt (2211 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2211]; decide
    · -- n = 2212
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2212 : Nat.sqrt (2212 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2212]; decide
    · -- n = 2213
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2213 : Nat.sqrt (2213 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2213]; decide
    · -- n = 2214
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2214 : Nat.sqrt (2214 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2214]; decide
    · -- n = 2215
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2215 : Nat.sqrt (2215 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2215]; decide
    · -- n = 2216
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2216 : Nat.sqrt (2216 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2216]; decide
    · -- n = 2217
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2217 : Nat.sqrt (2217 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2217]; decide
    · -- n = 2218
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2218 : Nat.sqrt (2218 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2218]; decide
    · -- n = 2219
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2219 : Nat.sqrt (2219 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2219]; decide
    · -- n = 2220
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2220 : Nat.sqrt (2220 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2220]; decide
    · -- n = 2221
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2221 : Nat.sqrt (2221 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2221]; decide
    · -- n = 2222
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2222 : Nat.sqrt (2222 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2222]; decide
    · -- n = 2223
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2223 : Nat.sqrt (2223 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2223]; decide
    · -- n = 2224
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2224 : Nat.sqrt (2224 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2224]; decide
    · -- n = 2225
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2225 : Nat.sqrt (2225 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2225]; decide
    · -- n = 2226
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2226 : Nat.sqrt (2226 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2226]; decide
    · -- n = 2227
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2227 : Nat.sqrt (2227 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2227]; decide
    · -- n = 2228
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2228 : Nat.sqrt (2228 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2228]; decide
    · -- n = 2229
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2229 : Nat.sqrt (2229 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2229]; decide
    · -- n = 2230
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2230 : Nat.sqrt (2230 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2230]; decide
    · -- n = 2231
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2231 : Nat.sqrt (2231 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2231]; decide
    · -- n = 2232
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2232 : Nat.sqrt (2232 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2232]; decide
    · -- n = 2233
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2233 : Nat.sqrt (2233 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2233]; decide
    · -- n = 2234
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2234 : Nat.sqrt (2234 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2234]; decide
    · -- n = 2235
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2235 : Nat.sqrt (2235 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2235]; decide
    · -- n = 2236
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2236 : Nat.sqrt (2236 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2236]; decide
    · -- n = 2237
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2237 : Nat.sqrt (2237 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2237]; decide
    · -- n = 2238
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2238 : Nat.sqrt (2238 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2238]; decide
    · -- n = 2239
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2239 : Nat.sqrt (2239 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2239]; decide
    · -- n = 2240
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2240 : Nat.sqrt (2240 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2240]; decide
    · -- n = 2241
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2241 : Nat.sqrt (2241 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2241]; decide
    · -- n = 2242
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2242 : Nat.sqrt (2242 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2242]; decide
    · -- n = 2243
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2243 : Nat.sqrt (2243 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2243]; decide
    · -- n = 2244
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2244 : Nat.sqrt (2244 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2244]; decide
    · -- n = 2245
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2245 : Nat.sqrt (2245 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2245]; decide
    · -- n = 2246
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2246 : Nat.sqrt (2246 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2246]; decide
    · -- n = 2247
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2247 : Nat.sqrt (2247 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2247]; decide
    · -- n = 2248
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2248 : Nat.sqrt (2248 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2248]; decide
    · -- n = 2249
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2249 : Nat.sqrt (2249 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2249]; decide
    · -- n = 2250
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2250 : Nat.sqrt (2250 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2250]; decide
    · -- n = 2251
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2251 : Nat.sqrt (2251 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2251]; decide
    · -- n = 2252
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2252 : Nat.sqrt (2252 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2252]; decide
    · -- n = 2253
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2253 : Nat.sqrt (2253 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2253]; decide
    · -- n = 2254
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2254 : Nat.sqrt (2254 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2254]; decide
    · -- n = 2255
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2255 : Nat.sqrt (2255 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2255]; decide
    · -- n = 2256
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2256 : Nat.sqrt (2256 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2256]; decide
    · -- n = 2257
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2257 : Nat.sqrt (2257 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2257]; decide
    · -- n = 2258
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2258 : Nat.sqrt (2258 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2258]; decide
    · -- n = 2259
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2259 : Nat.sqrt (2259 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2259]; decide
    · -- n = 2260
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2260 : Nat.sqrt (2260 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2260]; decide
    · -- n = 2261
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2261 : Nat.sqrt (2261 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2261]; decide
    · -- n = 2262
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2262 : Nat.sqrt (2262 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2262]; decide
    · -- n = 2263
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2263 : Nat.sqrt (2263 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2263]; decide
    · -- n = 2264
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2264 : Nat.sqrt (2264 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2264]; decide
    · -- n = 2265
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2265 : Nat.sqrt (2265 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2265]; decide
    · -- n = 2266
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2266 : Nat.sqrt (2266 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2266]; decide
    · -- n = 2267
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2267 : Nat.sqrt (2267 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2267]; decide
    · -- n = 2268
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2268 : Nat.sqrt (2268 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2268]; decide
    · -- n = 2269
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2269 : Nat.sqrt (2269 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2269]; decide
    · -- n = 2270
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2270 : Nat.sqrt (2270 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2270]; decide
    · -- n = 2271
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2271 : Nat.sqrt (2271 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2271]; decide
    · -- n = 2272
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2272 : Nat.sqrt (2272 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2272]; decide
    · -- n = 2273
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2273 : Nat.sqrt (2273 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2273]; decide
    · -- n = 2274
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2274 : Nat.sqrt (2274 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2274]; decide
    · -- n = 2275
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2275 : Nat.sqrt (2275 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2275]; decide
    · -- n = 2276
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2276 : Nat.sqrt (2276 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2276]; decide
    · -- n = 2277
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2277 : Nat.sqrt (2277 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2277]; decide
    · -- n = 2278
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2278 : Nat.sqrt (2278 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2278]; decide
    · -- n = 2279
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2279 : Nat.sqrt (2279 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2279]; decide
    · -- n = 2280
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2280 : Nat.sqrt (2280 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2280]; decide
    · -- n = 2281
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2281 : Nat.sqrt (2281 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2281]; decide
    · -- n = 2282
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2282 : Nat.sqrt (2282 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2282]; decide
    · -- n = 2283
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2283 : Nat.sqrt (2283 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2283]; decide
    · -- n = 2284
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2284 : Nat.sqrt (2284 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2284]; decide
    · -- n = 2285
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2285 : Nat.sqrt (2285 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2285]; decide
    · -- n = 2286
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2286 : Nat.sqrt (2286 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2286]; decide
    · -- n = 2287
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2287 : Nat.sqrt (2287 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2287]; decide
    · -- n = 2288
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2288 : Nat.sqrt (2288 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2288]; decide
    · -- n = 2289
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2289 : Nat.sqrt (2289 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2289]; decide
    · -- n = 2290
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2290 : Nat.sqrt (2290 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2290]; decide
    · -- n = 2291
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2291 : Nat.sqrt (2291 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2291]; decide
    · -- n = 2292
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2292 : Nat.sqrt (2292 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2292]; decide
    · -- n = 2293
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2293 : Nat.sqrt (2293 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2293]; decide
    · -- n = 2294
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2294 : Nat.sqrt (2294 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2294]; decide
    · -- n = 2295
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2295 : Nat.sqrt (2295 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2295]; decide
    · -- n = 2296
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2296 : Nat.sqrt (2296 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2296]; decide
    · -- n = 2297
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2297 : Nat.sqrt (2297 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2297]; decide
    · -- n = 2298
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2298 : Nat.sqrt (2298 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2298]; decide
    · -- n = 2299
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2299 : Nat.sqrt (2299 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2299]; decide
    · -- n = 2300
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2300 : Nat.sqrt (2300 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2300]; decide
    · -- n = 2301
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2301 : Nat.sqrt (2301 + 2) = 47 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2301]; decide
    · -- n = 2302
      use 509
      refine ⟨by decide, by decide, ?_⟩
      have h_2302 : Nat.sqrt (2302 + 509) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2302]; decide
    · -- n = 2303
      use 509
      refine ⟨by decide, by decide, ?_⟩
      have h_2303 : Nat.sqrt (2303 + 509) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2303]; decide
    · -- n = 2304
      use 509
      refine ⟨by decide, by decide, ?_⟩
      have h_2304 : Nat.sqrt (2304 + 509) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2304]; decide
    · -- n = 2305
      use 509
      refine ⟨by decide, by decide, ?_⟩
      have h_2305 : Nat.sqrt (2305 + 509) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2305]; decide
    · -- n = 2306
      use 503
      refine ⟨by decide, by decide, ?_⟩
      have h_2306 : Nat.sqrt (2306 + 503) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2306]; decide
    · -- n = 2307
      use 503
      refine ⟨by decide, by decide, ?_⟩
      have h_2307 : Nat.sqrt (2307 + 503) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2307]; decide
    · -- n = 2308
      use 503
      refine ⟨by decide, by decide, ?_⟩
      have h_2308 : Nat.sqrt (2308 + 503) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2308]; decide
    · -- n = 2309
      use 503
      refine ⟨by decide, by decide, ?_⟩
      have h_2309 : Nat.sqrt (2309 + 503) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2309]; decide
    · -- n = 2310
      use 499
      refine ⟨by decide, by decide, ?_⟩
      have h_2310 : Nat.sqrt (2310 + 499) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2310]; decide
    · -- n = 2311
      use 499
      refine ⟨by decide, by decide, ?_⟩
      have h_2311 : Nat.sqrt (2311 + 499) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2311]; decide
    · -- n = 2312
      use 499
      refine ⟨by decide, by decide, ?_⟩
      have h_2312 : Nat.sqrt (2312 + 499) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2312]; decide
    · -- n = 2313
      use 499
      refine ⟨by decide, by decide, ?_⟩
      have h_2313 : Nat.sqrt (2313 + 499) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2313]; decide
    · -- n = 2314
      use 499
      refine ⟨by decide, by decide, ?_⟩
      have h_2314 : Nat.sqrt (2314 + 499) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2314]; decide
    · -- n = 2315
      use 499
      refine ⟨by decide, by decide, ?_⟩
      have h_2315 : Nat.sqrt (2315 + 499) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2315]; decide
    · -- n = 2316
      use 499
      refine ⟨by decide, by decide, ?_⟩
      have h_2316 : Nat.sqrt (2316 + 499) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2316]; decide
    · -- n = 2317
      use 499
      refine ⟨by decide, by decide, ?_⟩
      have h_2317 : Nat.sqrt (2317 + 499) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2317]; decide
    · -- n = 2318
      use 491
      refine ⟨by decide, by decide, ?_⟩
      have h_2318 : Nat.sqrt (2318 + 491) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2318]; decide
    · -- n = 2319
      use 491
      refine ⟨by decide, by decide, ?_⟩
      have h_2319 : Nat.sqrt (2319 + 491) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2319]; decide
    · -- n = 2320
      use 491
      refine ⟨by decide, by decide, ?_⟩
      have h_2320 : Nat.sqrt (2320 + 491) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2320]; decide
    · -- n = 2321
      use 491
      refine ⟨by decide, by decide, ?_⟩
      have h_2321 : Nat.sqrt (2321 + 491) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2321]; decide
    · -- n = 2322
      use 487
      refine ⟨by decide, by decide, ?_⟩
      have h_2322 : Nat.sqrt (2322 + 487) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2322]; decide
    · -- n = 2323
      use 487
      refine ⟨by decide, by decide, ?_⟩
      have h_2323 : Nat.sqrt (2323 + 487) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2323]; decide
    · -- n = 2324
      use 487
      refine ⟨by decide, by decide, ?_⟩
      have h_2324 : Nat.sqrt (2324 + 487) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2324]; decide
    · -- n = 2325
      use 487
      refine ⟨by decide, by decide, ?_⟩
      have h_2325 : Nat.sqrt (2325 + 487) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2325]; decide
    · -- n = 2326
      use 487
      refine ⟨by decide, by decide, ?_⟩
      have h_2326 : Nat.sqrt (2326 + 487) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2326]; decide
    · -- n = 2327
      use 487
      refine ⟨by decide, by decide, ?_⟩
      have h_2327 : Nat.sqrt (2327 + 487) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2327]; decide
    · -- n = 2328
      use 487
      refine ⟨by decide, by decide, ?_⟩
      have h_2328 : Nat.sqrt (2328 + 487) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2328]; decide
    · -- n = 2329
      use 487
      refine ⟨by decide, by decide, ?_⟩
      have h_2329 : Nat.sqrt (2329 + 487) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2329]; decide
    · -- n = 2330
      use 479
      refine ⟨by decide, by decide, ?_⟩
      have h_2330 : Nat.sqrt (2330 + 479) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2330]; decide
    · -- n = 2331
      use 479
      refine ⟨by decide, by decide, ?_⟩
      have h_2331 : Nat.sqrt (2331 + 479) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2331]; decide
    · -- n = 2332
      use 479
      refine ⟨by decide, by decide, ?_⟩
      have h_2332 : Nat.sqrt (2332 + 479) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2332]; decide
    · -- n = 2333
      use 479
      refine ⟨by decide, by decide, ?_⟩
      have h_2333 : Nat.sqrt (2333 + 479) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2333]; decide
    · -- n = 2334
      use 479
      refine ⟨by decide, by decide, ?_⟩
      have h_2334 : Nat.sqrt (2334 + 479) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2334]; decide
    · -- n = 2335
      use 479
      refine ⟨by decide, by decide, ?_⟩
      have h_2335 : Nat.sqrt (2335 + 479) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2335]; decide
    · -- n = 2336
      use 479
      refine ⟨by decide, by decide, ?_⟩
      have h_2336 : Nat.sqrt (2336 + 479) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2336]; decide
    · -- n = 2337
      use 479
      refine ⟨by decide, by decide, ?_⟩
      have h_2337 : Nat.sqrt (2337 + 479) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2337]; decide
    · -- n = 2338
      use 479
      refine ⟨by decide, by decide, ?_⟩
      have h_2338 : Nat.sqrt (2338 + 479) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2338]; decide
    · -- n = 2339
      use 479
      refine ⟨by decide, by decide, ?_⟩
      have h_2339 : Nat.sqrt (2339 + 479) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2339]; decide
    · -- n = 2340
      use 479
      refine ⟨by decide, by decide, ?_⟩
      have h_2340 : Nat.sqrt (2340 + 479) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2340]; decide
    · -- n = 2341
      use 479
      refine ⟨by decide, by decide, ?_⟩
      have h_2341 : Nat.sqrt (2341 + 479) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2341]; decide
    · -- n = 2342
      use 467
      refine ⟨by decide, by decide, ?_⟩
      have h_2342 : Nat.sqrt (2342 + 467) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2342]; decide
    · -- n = 2343
      use 467
      refine ⟨by decide, by decide, ?_⟩
      have h_2343 : Nat.sqrt (2343 + 467) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2343]; decide
    · -- n = 2344
      use 467
      refine ⟨by decide, by decide, ?_⟩
      have h_2344 : Nat.sqrt (2344 + 467) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2344]; decide
    · -- n = 2345
      use 467
      refine ⟨by decide, by decide, ?_⟩
      have h_2345 : Nat.sqrt (2345 + 467) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2345]; decide
    · -- n = 2346
      use 463
      refine ⟨by decide, by decide, ?_⟩
      have h_2346 : Nat.sqrt (2346 + 463) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2346]; decide
    · -- n = 2347
      use 463
      refine ⟨by decide, by decide, ?_⟩
      have h_2347 : Nat.sqrt (2347 + 463) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2347]; decide
    · -- n = 2348
      use 461
      refine ⟨by decide, by decide, ?_⟩
      have h_2348 : Nat.sqrt (2348 + 461) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2348]; decide
    · -- n = 2349
      use 461
      refine ⟨by decide, by decide, ?_⟩
      have h_2349 : Nat.sqrt (2349 + 461) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2349]; decide
    · -- n = 2350
      use 461
      refine ⟨by decide, by decide, ?_⟩
      have h_2350 : Nat.sqrt (2350 + 461) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2350]; decide
    · -- n = 2351
      use 461
      refine ⟨by decide, by decide, ?_⟩
      have h_2351 : Nat.sqrt (2351 + 461) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2351]; decide
    · -- n = 2352
      use 457
      refine ⟨by decide, by decide, ?_⟩
      have h_2352 : Nat.sqrt (2352 + 457) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2352]; decide
    · -- n = 2353
      use 457
      refine ⟨by decide, by decide, ?_⟩
      have h_2353 : Nat.sqrt (2353 + 457) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2353]; decide
    · -- n = 2354
      use 457
      refine ⟨by decide, by decide, ?_⟩
      have h_2354 : Nat.sqrt (2354 + 457) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2354]; decide
    · -- n = 2355
      use 457
      refine ⟨by decide, by decide, ?_⟩
      have h_2355 : Nat.sqrt (2355 + 457) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2355]; decide
    · -- n = 2356
      use 457
      refine ⟨by decide, by decide, ?_⟩
      have h_2356 : Nat.sqrt (2356 + 457) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2356]; decide
    · -- n = 2357
      use 457
      refine ⟨by decide, by decide, ?_⟩
      have h_2357 : Nat.sqrt (2357 + 457) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2357]; decide
    · -- n = 2358
      use 457
      refine ⟨by decide, by decide, ?_⟩
      have h_2358 : Nat.sqrt (2358 + 457) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2358]; decide
    · -- n = 2359
      use 457
      refine ⟨by decide, by decide, ?_⟩
      have h_2359 : Nat.sqrt (2359 + 457) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2359]; decide
    · -- n = 2360
      use 449
      refine ⟨by decide, by decide, ?_⟩
      have h_2360 : Nat.sqrt (2360 + 449) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2360]; decide
    · -- n = 2361
      use 449
      refine ⟨by decide, by decide, ?_⟩
      have h_2361 : Nat.sqrt (2361 + 449) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2361]; decide
    · -- n = 2362
      use 449
      refine ⟨by decide, by decide, ?_⟩
      have h_2362 : Nat.sqrt (2362 + 449) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2362]; decide
    · -- n = 2363
      use 449
      refine ⟨by decide, by decide, ?_⟩
      have h_2363 : Nat.sqrt (2363 + 449) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2363]; decide
    · -- n = 2364
      use 449
      refine ⟨by decide, by decide, ?_⟩
      have h_2364 : Nat.sqrt (2364 + 449) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2364]; decide
    · -- n = 2365
      use 449
      refine ⟨by decide, by decide, ?_⟩
      have h_2365 : Nat.sqrt (2365 + 449) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2365]; decide
    · -- n = 2366
      use 443
      refine ⟨by decide, by decide, ?_⟩
      have h_2366 : Nat.sqrt (2366 + 443) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2366]; decide
    · -- n = 2367
      use 443
      refine ⟨by decide, by decide, ?_⟩
      have h_2367 : Nat.sqrt (2367 + 443) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2367]; decide
    · -- n = 2368
      use 443
      refine ⟨by decide, by decide, ?_⟩
      have h_2368 : Nat.sqrt (2368 + 443) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2368]; decide
    · -- n = 2369
      use 443
      refine ⟨by decide, by decide, ?_⟩
      have h_2369 : Nat.sqrt (2369 + 443) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2369]; decide
    · -- n = 2370
      use 439
      refine ⟨by decide, by decide, ?_⟩
      have h_2370 : Nat.sqrt (2370 + 439) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2370]; decide
    · -- n = 2371
      use 439
      refine ⟨by decide, by decide, ?_⟩
      have h_2371 : Nat.sqrt (2371 + 439) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2371]; decide
    · -- n = 2372
      use 439
      refine ⟨by decide, by decide, ?_⟩
      have h_2372 : Nat.sqrt (2372 + 439) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2372]; decide
    · -- n = 2373
      use 439
      refine ⟨by decide, by decide, ?_⟩
      have h_2373 : Nat.sqrt (2373 + 439) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2373]; decide
    · -- n = 2374
      use 439
      refine ⟨by decide, by decide, ?_⟩
      have h_2374 : Nat.sqrt (2374 + 439) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2374]; decide
    · -- n = 2375
      use 439
      refine ⟨by decide, by decide, ?_⟩
      have h_2375 : Nat.sqrt (2375 + 439) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2375]; decide
    · -- n = 2376
      use 433
      refine ⟨by decide, by decide, ?_⟩
      have h_2376 : Nat.sqrt (2376 + 433) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2376]; decide
    · -- n = 2377
      use 433
      refine ⟨by decide, by decide, ?_⟩
      have h_2377 : Nat.sqrt (2377 + 433) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2377]; decide
    · -- n = 2378
      use 431
      refine ⟨by decide, by decide, ?_⟩
      have h_2378 : Nat.sqrt (2378 + 431) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2378]; decide
    · -- n = 2379
      use 431
      refine ⟨by decide, by decide, ?_⟩
      have h_2379 : Nat.sqrt (2379 + 431) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2379]; decide
    · -- n = 2380
      use 431
      refine ⟨by decide, by decide, ?_⟩
      have h_2380 : Nat.sqrt (2380 + 431) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2380]; decide
    · -- n = 2381
      use 431
      refine ⟨by decide, by decide, ?_⟩
      have h_2381 : Nat.sqrt (2381 + 431) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2381]; decide
    · -- n = 2382
      use 431
      refine ⟨by decide, by decide, ?_⟩
      have h_2382 : Nat.sqrt (2382 + 431) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2382]; decide
    · -- n = 2383
      use 431
      refine ⟨by decide, by decide, ?_⟩
      have h_2383 : Nat.sqrt (2383 + 431) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2383]; decide
    · -- n = 2384
      use 431
      refine ⟨by decide, by decide, ?_⟩
      have h_2384 : Nat.sqrt (2384 + 431) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2384]; decide
    · -- n = 2385
      use 431
      refine ⟨by decide, by decide, ?_⟩
      have h_2385 : Nat.sqrt (2385 + 431) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2385]; decide
    · -- n = 2386
      use 431
      refine ⟨by decide, by decide, ?_⟩
      have h_2386 : Nat.sqrt (2386 + 431) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2386]; decide
    · -- n = 2387
      use 431
      refine ⟨by decide, by decide, ?_⟩
      have h_2387 : Nat.sqrt (2387 + 431) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2387]; decide
    · -- n = 2388
      use 421
      refine ⟨by decide, by decide, ?_⟩
      have h_2388 : Nat.sqrt (2388 + 421) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2388]; decide
    · -- n = 2389
      use 421
      refine ⟨by decide, by decide, ?_⟩
      have h_2389 : Nat.sqrt (2389 + 421) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2389]; decide
    · -- n = 2390
      use 419
      refine ⟨by decide, by decide, ?_⟩
      have h_2390 : Nat.sqrt (2390 + 419) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2390]; decide
    · -- n = 2391
      use 419
      refine ⟨by decide, by decide, ?_⟩
      have h_2391 : Nat.sqrt (2391 + 419) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2391]; decide
    · -- n = 2392
      use 419
      refine ⟨by decide, by decide, ?_⟩
      have h_2392 : Nat.sqrt (2392 + 419) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2392]; decide
    · -- n = 2393
      use 419
      refine ⟨by decide, by decide, ?_⟩
      have h_2393 : Nat.sqrt (2393 + 419) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2393]; decide
    · -- n = 2394
      use 419
      refine ⟨by decide, by decide, ?_⟩
      have h_2394 : Nat.sqrt (2394 + 419) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2394]; decide
    · -- n = 2395
      use 419
      refine ⟨by decide, by decide, ?_⟩
      have h_2395 : Nat.sqrt (2395 + 419) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2395]; decide
    · -- n = 2396
      use 419
      refine ⟨by decide, by decide, ?_⟩
      have h_2396 : Nat.sqrt (2396 + 419) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2396]; decide
    · -- n = 2397
      use 419
      refine ⟨by decide, by decide, ?_⟩
      have h_2397 : Nat.sqrt (2397 + 419) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2397]; decide
    · -- n = 2398
      use 419
      refine ⟨by decide, by decide, ?_⟩
      have h_2398 : Nat.sqrt (2398 + 419) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2398]; decide
    · -- n = 2399
      use 419
      refine ⟨by decide, by decide, ?_⟩
      have h_2399 : Nat.sqrt (2399 + 419) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2399]; decide
    · -- n = 2400
      use 409
      refine ⟨by decide, by decide, ?_⟩
      have h_2400 : Nat.sqrt (2400 + 409) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2400]; decide
    · -- n = 2401
      use 409
      refine ⟨by decide, by decide, ?_⟩
      have h_2401 : Nat.sqrt (2401 + 409) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2401]; decide
    · -- n = 2402
      use 409
      refine ⟨by decide, by decide, ?_⟩
      have h_2402 : Nat.sqrt (2402 + 409) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2402]; decide
    · -- n = 2403
      use 409
      refine ⟨by decide, by decide, ?_⟩
      have h_2403 : Nat.sqrt (2403 + 409) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2403]; decide
    · -- n = 2404
      use 409
      refine ⟨by decide, by decide, ?_⟩
      have h_2404 : Nat.sqrt (2404 + 409) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2404]; decide
    · -- n = 2405
      use 409
      refine ⟨by decide, by decide, ?_⟩
      have h_2405 : Nat.sqrt (2405 + 409) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2405]; decide
    · -- n = 2406
      use 409
      refine ⟨by decide, by decide, ?_⟩
      have h_2406 : Nat.sqrt (2406 + 409) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2406]; decide
    · -- n = 2407
      use 409
      refine ⟨by decide, by decide, ?_⟩
      have h_2407 : Nat.sqrt (2407 + 409) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2407]; decide
    · -- n = 2408
      use 401
      refine ⟨by decide, by decide, ?_⟩
      have h_2408 : Nat.sqrt (2408 + 401) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2408]; decide
    · -- n = 2409
      use 401
      refine ⟨by decide, by decide, ?_⟩
      have h_2409 : Nat.sqrt (2409 + 401) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2409]; decide
    · -- n = 2410
      use 401
      refine ⟨by decide, by decide, ?_⟩
      have h_2410 : Nat.sqrt (2410 + 401) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2410]; decide
    · -- n = 2411
      use 401
      refine ⟨by decide, by decide, ?_⟩
      have h_2411 : Nat.sqrt (2411 + 401) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2411]; decide
    · -- n = 2412
      use 397
      refine ⟨by decide, by decide, ?_⟩
      have h_2412 : Nat.sqrt (2412 + 397) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2412]; decide
    · -- n = 2413
      use 397
      refine ⟨by decide, by decide, ?_⟩
      have h_2413 : Nat.sqrt (2413 + 397) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2413]; decide
    · -- n = 2414
      use 397
      refine ⟨by decide, by decide, ?_⟩
      have h_2414 : Nat.sqrt (2414 + 397) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2414]; decide
    · -- n = 2415
      use 397
      refine ⟨by decide, by decide, ?_⟩
      have h_2415 : Nat.sqrt (2415 + 397) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2415]; decide
    · -- n = 2416
      use 397
      refine ⟨by decide, by decide, ?_⟩
      have h_2416 : Nat.sqrt (2416 + 397) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2416]; decide
    · -- n = 2417
      use 397
      refine ⟨by decide, by decide, ?_⟩
      have h_2417 : Nat.sqrt (2417 + 397) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2417]; decide
    · -- n = 2418
      use 397
      refine ⟨by decide, by decide, ?_⟩
      have h_2418 : Nat.sqrt (2418 + 397) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2418]; decide
    · -- n = 2419
      use 397
      refine ⟨by decide, by decide, ?_⟩
      have h_2419 : Nat.sqrt (2419 + 397) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2419]; decide
    · -- n = 2420
      use 389
      refine ⟨by decide, by decide, ?_⟩
      have h_2420 : Nat.sqrt (2420 + 389) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2420]; decide
    · -- n = 2421
      use 389
      refine ⟨by decide, by decide, ?_⟩
      have h_2421 : Nat.sqrt (2421 + 389) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2421]; decide
    · -- n = 2422
      use 389
      refine ⟨by decide, by decide, ?_⟩
      have h_2422 : Nat.sqrt (2422 + 389) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2422]; decide
    · -- n = 2423
      use 389
      refine ⟨by decide, by decide, ?_⟩
      have h_2423 : Nat.sqrt (2423 + 389) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2423]; decide
    · -- n = 2424
      use 389
      refine ⟨by decide, by decide, ?_⟩
      have h_2424 : Nat.sqrt (2424 + 389) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2424]; decide
    · -- n = 2425
      use 389
      refine ⟨by decide, by decide, ?_⟩
      have h_2425 : Nat.sqrt (2425 + 389) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2425]; decide
    · -- n = 2426
      use 383
      refine ⟨by decide, by decide, ?_⟩
      have h_2426 : Nat.sqrt (2426 + 383) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2426]; decide
    · -- n = 2427
      use 383
      refine ⟨by decide, by decide, ?_⟩
      have h_2427 : Nat.sqrt (2427 + 383) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2427]; decide
    · -- n = 2428
      use 383
      refine ⟨by decide, by decide, ?_⟩
      have h_2428 : Nat.sqrt (2428 + 383) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2428]; decide
    · -- n = 2429
      use 383
      refine ⟨by decide, by decide, ?_⟩
      have h_2429 : Nat.sqrt (2429 + 383) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2429]; decide
    · -- n = 2430
      use 379
      refine ⟨by decide, by decide, ?_⟩
      have h_2430 : Nat.sqrt (2430 + 379) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2430]; decide
    · -- n = 2431
      use 379
      refine ⟨by decide, by decide, ?_⟩
      have h_2431 : Nat.sqrt (2431 + 379) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2431]; decide
    · -- n = 2432
      use 379
      refine ⟨by decide, by decide, ?_⟩
      have h_2432 : Nat.sqrt (2432 + 379) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2432]; decide
    · -- n = 2433
      use 379
      refine ⟨by decide, by decide, ?_⟩
      have h_2433 : Nat.sqrt (2433 + 379) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2433]; decide
    · -- n = 2434
      use 379
      refine ⟨by decide, by decide, ?_⟩
      have h_2434 : Nat.sqrt (2434 + 379) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2434]; decide
    · -- n = 2435
      use 379
      refine ⟨by decide, by decide, ?_⟩
      have h_2435 : Nat.sqrt (2435 + 379) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2435]; decide
    · -- n = 2436
      use 373
      refine ⟨by decide, by decide, ?_⟩
      have h_2436 : Nat.sqrt (2436 + 373) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2436]; decide
    · -- n = 2437
      use 373
      refine ⟨by decide, by decide, ?_⟩
      have h_2437 : Nat.sqrt (2437 + 373) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2437]; decide
    · -- n = 2438
      use 373
      refine ⟨by decide, by decide, ?_⟩
      have h_2438 : Nat.sqrt (2438 + 373) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2438]; decide
    · -- n = 2439
      use 373
      refine ⟨by decide, by decide, ?_⟩
      have h_2439 : Nat.sqrt (2439 + 373) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2439]; decide
    · -- n = 2440
      use 373
      refine ⟨by decide, by decide, ?_⟩
      have h_2440 : Nat.sqrt (2440 + 373) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2440]; decide
    · -- n = 2441
      use 373
      refine ⟨by decide, by decide, ?_⟩
      have h_2441 : Nat.sqrt (2441 + 373) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2441]; decide
    · -- n = 2442
      use 367
      refine ⟨by decide, by decide, ?_⟩
      have h_2442 : Nat.sqrt (2442 + 367) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2442]; decide
    · -- n = 2443
      use 367
      refine ⟨by decide, by decide, ?_⟩
      have h_2443 : Nat.sqrt (2443 + 367) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2443]; decide
    · -- n = 2444
      use 367
      refine ⟨by decide, by decide, ?_⟩
      have h_2444 : Nat.sqrt (2444 + 367) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2444]; decide
    · -- n = 2445
      use 367
      refine ⟨by decide, by decide, ?_⟩
      have h_2445 : Nat.sqrt (2445 + 367) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2445]; decide
    · -- n = 2446
      use 367
      refine ⟨by decide, by decide, ?_⟩
      have h_2446 : Nat.sqrt (2446 + 367) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2446]; decide
    · -- n = 2447
      use 367
      refine ⟨by decide, by decide, ?_⟩
      have h_2447 : Nat.sqrt (2447 + 367) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2447]; decide
    · -- n = 2448
      use 367
      refine ⟨by decide, by decide, ?_⟩
      have h_2448 : Nat.sqrt (2448 + 367) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2448]; decide
    · -- n = 2449
      use 367
      refine ⟨by decide, by decide, ?_⟩
      have h_2449 : Nat.sqrt (2449 + 367) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2449]; decide
    · -- n = 2450
      use 359
      refine ⟨by decide, by decide, ?_⟩
      have h_2450 : Nat.sqrt (2450 + 359) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2450]; decide
    · -- n = 2451
      use 359
      refine ⟨by decide, by decide, ?_⟩
      have h_2451 : Nat.sqrt (2451 + 359) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2451]; decide
    · -- n = 2452
      use 359
      refine ⟨by decide, by decide, ?_⟩
      have h_2452 : Nat.sqrt (2452 + 359) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2452]; decide
    · -- n = 2453
      use 359
      refine ⟨by decide, by decide, ?_⟩
      have h_2453 : Nat.sqrt (2453 + 359) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2453]; decide
    · -- n = 2454
      use 359
      refine ⟨by decide, by decide, ?_⟩
      have h_2454 : Nat.sqrt (2454 + 359) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2454]; decide
    · -- n = 2455
      use 359
      refine ⟨by decide, by decide, ?_⟩
      have h_2455 : Nat.sqrt (2455 + 359) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2455]; decide
    · -- n = 2456
      use 353
      refine ⟨by decide, by decide, ?_⟩
      have h_2456 : Nat.sqrt (2456 + 353) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2456]; decide
    · -- n = 2457
      use 353
      refine ⟨by decide, by decide, ?_⟩
      have h_2457 : Nat.sqrt (2457 + 353) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2457]; decide
    · -- n = 2458
      use 353
      refine ⟨by decide, by decide, ?_⟩
      have h_2458 : Nat.sqrt (2458 + 353) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2458]; decide
    · -- n = 2459
      use 353
      refine ⟨by decide, by decide, ?_⟩
      have h_2459 : Nat.sqrt (2459 + 353) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2459]; decide
    · -- n = 2460
      use 349
      refine ⟨by decide, by decide, ?_⟩
      have h_2460 : Nat.sqrt (2460 + 349) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2460]; decide
    · -- n = 2461
      use 349
      refine ⟨by decide, by decide, ?_⟩
      have h_2461 : Nat.sqrt (2461 + 349) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2461]; decide
    · -- n = 2462
      use 347
      refine ⟨by decide, by decide, ?_⟩
      have h_2462 : Nat.sqrt (2462 + 347) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2462]; decide
    · -- n = 2463
      use 347
      refine ⟨by decide, by decide, ?_⟩
      have h_2463 : Nat.sqrt (2463 + 347) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2463]; decide
    · -- n = 2464
      use 347
      refine ⟨by decide, by decide, ?_⟩
      have h_2464 : Nat.sqrt (2464 + 347) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2464]; decide
    · -- n = 2465
      use 347
      refine ⟨by decide, by decide, ?_⟩
      have h_2465 : Nat.sqrt (2465 + 347) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2465]; decide
    · -- n = 2466
      use 347
      refine ⟨by decide, by decide, ?_⟩
      have h_2466 : Nat.sqrt (2466 + 347) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2466]; decide
    · -- n = 2467
      use 347
      refine ⟨by decide, by decide, ?_⟩
      have h_2467 : Nat.sqrt (2467 + 347) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2467]; decide
    · -- n = 2468
      use 347
      refine ⟨by decide, by decide, ?_⟩
      have h_2468 : Nat.sqrt (2468 + 347) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2468]; decide
    · -- n = 2469
      use 347
      refine ⟨by decide, by decide, ?_⟩
      have h_2469 : Nat.sqrt (2469 + 347) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2469]; decide
    · -- n = 2470
      use 347
      refine ⟨by decide, by decide, ?_⟩
      have h_2470 : Nat.sqrt (2470 + 347) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2470]; decide
    · -- n = 2471
      use 347
      refine ⟨by decide, by decide, ?_⟩
      have h_2471 : Nat.sqrt (2471 + 347) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2471]; decide
    · -- n = 2472
      use 337
      refine ⟨by decide, by decide, ?_⟩
      have h_2472 : Nat.sqrt (2472 + 337) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2472]; decide
    · -- n = 2473
      use 337
      refine ⟨by decide, by decide, ?_⟩
      have h_2473 : Nat.sqrt (2473 + 337) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2473]; decide
    · -- n = 2474
      use 337
      refine ⟨by decide, by decide, ?_⟩
      have h_2474 : Nat.sqrt (2474 + 337) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2474]; decide
    · -- n = 2475
      use 337
      refine ⟨by decide, by decide, ?_⟩
      have h_2475 : Nat.sqrt (2475 + 337) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2475]; decide
    · -- n = 2476
      use 337
      refine ⟨by decide, by decide, ?_⟩
      have h_2476 : Nat.sqrt (2476 + 337) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2476]; decide
    · -- n = 2477
      use 337
      refine ⟨by decide, by decide, ?_⟩
      have h_2477 : Nat.sqrt (2477 + 337) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2477]; decide
    · -- n = 2478
      use 331
      refine ⟨by decide, by decide, ?_⟩
      have h_2478 : Nat.sqrt (2478 + 331) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2478]; decide
    · -- n = 2479
      use 331
      refine ⟨by decide, by decide, ?_⟩
      have h_2479 : Nat.sqrt (2479 + 331) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2479]; decide
    · -- n = 2480
      use 331
      refine ⟨by decide, by decide, ?_⟩
      have h_2480 : Nat.sqrt (2480 + 331) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2480]; decide
    · -- n = 2481
      use 331
      refine ⟨by decide, by decide, ?_⟩
      have h_2481 : Nat.sqrt (2481 + 331) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2481]; decide
    · -- n = 2482
      use 331
      refine ⟨by decide, by decide, ?_⟩
      have h_2482 : Nat.sqrt (2482 + 331) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2482]; decide
    · -- n = 2483
      use 331
      refine ⟨by decide, by decide, ?_⟩
      have h_2483 : Nat.sqrt (2483 + 331) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2483]; decide
    · -- n = 2484
      use 331
      refine ⟨by decide, by decide, ?_⟩
      have h_2484 : Nat.sqrt (2484 + 331) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2484]; decide
    · -- n = 2485
      use 331
      refine ⟨by decide, by decide, ?_⟩
      have h_2485 : Nat.sqrt (2485 + 331) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2485]; decide
    · -- n = 2486
      use 331
      refine ⟨by decide, by decide, ?_⟩
      have h_2486 : Nat.sqrt (2486 + 331) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2486]; decide
    · -- n = 2487
      use 331
      refine ⟨by decide, by decide, ?_⟩
      have h_2487 : Nat.sqrt (2487 + 331) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2487]; decide
    · -- n = 2488
      use 331
      refine ⟨by decide, by decide, ?_⟩
      have h_2488 : Nat.sqrt (2488 + 331) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2488]; decide
    · -- n = 2489
      use 331
      refine ⟨by decide, by decide, ?_⟩
      have h_2489 : Nat.sqrt (2489 + 331) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2489]; decide
    · -- n = 2490
      use 331
      refine ⟨by decide, by decide, ?_⟩
      have h_2490 : Nat.sqrt (2490 + 331) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2490]; decide
    · -- n = 2491
      use 331
      refine ⟨by decide, by decide, ?_⟩
      have h_2491 : Nat.sqrt (2491 + 331) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2491]; decide
    · -- n = 2492
      use 317
      refine ⟨by decide, by decide, ?_⟩
      have h_2492 : Nat.sqrt (2492 + 317) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2492]; decide
    · -- n = 2493
      use 317
      refine ⟨by decide, by decide, ?_⟩
      have h_2493 : Nat.sqrt (2493 + 317) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2493]; decide
    · -- n = 2494
      use 317
      refine ⟨by decide, by decide, ?_⟩
      have h_2494 : Nat.sqrt (2494 + 317) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2494]; decide
    · -- n = 2495
      use 317
      refine ⟨by decide, by decide, ?_⟩
      have h_2495 : Nat.sqrt (2495 + 317) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2495]; decide
    · -- n = 2496
      use 313
      refine ⟨by decide, by decide, ?_⟩
      have h_2496 : Nat.sqrt (2496 + 313) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2496]; decide
    · -- n = 2497
      use 313
      refine ⟨by decide, by decide, ?_⟩
      have h_2497 : Nat.sqrt (2497 + 313) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2497]; decide
    · -- n = 2498
      use 311
      refine ⟨by decide, by decide, ?_⟩
      have h_2498 : Nat.sqrt (2498 + 311) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2498]; decide
    · -- n = 2499
      use 311
      refine ⟨by decide, by decide, ?_⟩
      have h_2499 : Nat.sqrt (2499 + 311) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2499]; decide
    · -- n = 2500
      use 311
      refine ⟨by decide, by decide, ?_⟩
      have h_2500 : Nat.sqrt (2500 + 311) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2500]; decide
    · -- n = 2501
      use 311
      refine ⟨by decide, by decide, ?_⟩
      have h_2501 : Nat.sqrt (2501 + 311) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2501]; decide
    · -- n = 2502
      use 307
      refine ⟨by decide, by decide, ?_⟩
      have h_2502 : Nat.sqrt (2502 + 307) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2502]; decide
    · -- n = 2503
      use 307
      refine ⟨by decide, by decide, ?_⟩
      have h_2503 : Nat.sqrt (2503 + 307) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2503]; decide
    · -- n = 2504
      use 307
      refine ⟨by decide, by decide, ?_⟩
      have h_2504 : Nat.sqrt (2504 + 307) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2504]; decide
    · -- n = 2505
      use 307
      refine ⟨by decide, by decide, ?_⟩
      have h_2505 : Nat.sqrt (2505 + 307) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2505]; decide
    · -- n = 2506
      use 307
      refine ⟨by decide, by decide, ?_⟩
      have h_2506 : Nat.sqrt (2506 + 307) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2506]; decide
    · -- n = 2507
      use 307
      refine ⟨by decide, by decide, ?_⟩
      have h_2507 : Nat.sqrt (2507 + 307) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2507]; decide
    · -- n = 2508
      use 307
      refine ⟨by decide, by decide, ?_⟩
      have h_2508 : Nat.sqrt (2508 + 307) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2508]; decide
    · -- n = 2509
      use 307
      refine ⟨by decide, by decide, ?_⟩
      have h_2509 : Nat.sqrt (2509 + 307) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2509]; decide
    · -- n = 2510
      use 307
      refine ⟨by decide, by decide, ?_⟩
      have h_2510 : Nat.sqrt (2510 + 307) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2510]; decide
    · -- n = 2511
      use 307
      refine ⟨by decide, by decide, ?_⟩
      have h_2511 : Nat.sqrt (2511 + 307) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2511]; decide
    · -- n = 2512
      use 307
      refine ⟨by decide, by decide, ?_⟩
      have h_2512 : Nat.sqrt (2512 + 307) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2512]; decide
    · -- n = 2513
      use 307
      refine ⟨by decide, by decide, ?_⟩
      have h_2513 : Nat.sqrt (2513 + 307) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2513]; decide
    · -- n = 2514
      use 307
      refine ⟨by decide, by decide, ?_⟩
      have h_2514 : Nat.sqrt (2514 + 307) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2514]; decide
    · -- n = 2515
      use 307
      refine ⟨by decide, by decide, ?_⟩
      have h_2515 : Nat.sqrt (2515 + 307) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2515]; decide
    · -- n = 2516
      use 293
      refine ⟨by decide, by decide, ?_⟩
      have h_2516 : Nat.sqrt (2516 + 293) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2516]; decide
    · -- n = 2517
      use 293
      refine ⟨by decide, by decide, ?_⟩
      have h_2517 : Nat.sqrt (2517 + 293) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2517]; decide
    · -- n = 2518
      use 293
      refine ⟨by decide, by decide, ?_⟩
      have h_2518 : Nat.sqrt (2518 + 293) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2518]; decide
    · -- n = 2519
      use 293
      refine ⟨by decide, by decide, ?_⟩
      have h_2519 : Nat.sqrt (2519 + 293) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2519]; decide
    · -- n = 2520
      use 293
      refine ⟨by decide, by decide, ?_⟩
      have h_2520 : Nat.sqrt (2520 + 293) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2520]; decide
    · -- n = 2521
      use 293
      refine ⟨by decide, by decide, ?_⟩
      have h_2521 : Nat.sqrt (2521 + 293) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2521]; decide
    · -- n = 2522
      use 293
      refine ⟨by decide, by decide, ?_⟩
      have h_2522 : Nat.sqrt (2522 + 293) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2522]; decide
    · -- n = 2523
      use 293
      refine ⟨by decide, by decide, ?_⟩
      have h_2523 : Nat.sqrt (2523 + 293) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2523]; decide
    · -- n = 2524
      use 293
      refine ⟨by decide, by decide, ?_⟩
      have h_2524 : Nat.sqrt (2524 + 293) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2524]; decide
    · -- n = 2525
      use 293
      refine ⟨by decide, by decide, ?_⟩
      have h_2525 : Nat.sqrt (2525 + 293) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2525]; decide
    · -- n = 2526
      use 283
      refine ⟨by decide, by decide, ?_⟩
      have h_2526 : Nat.sqrt (2526 + 283) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2526]; decide
    · -- n = 2527
      use 283
      refine ⟨by decide, by decide, ?_⟩
      have h_2527 : Nat.sqrt (2527 + 283) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2527]; decide
    · -- n = 2528
      use 281
      refine ⟨by decide, by decide, ?_⟩
      have h_2528 : Nat.sqrt (2528 + 281) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2528]; decide
    · -- n = 2529
      use 281
      refine ⟨by decide, by decide, ?_⟩
      have h_2529 : Nat.sqrt (2529 + 281) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2529]; decide
    · -- n = 2530
      use 281
      refine ⟨by decide, by decide, ?_⟩
      have h_2530 : Nat.sqrt (2530 + 281) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2530]; decide
    · -- n = 2531
      use 281
      refine ⟨by decide, by decide, ?_⟩
      have h_2531 : Nat.sqrt (2531 + 281) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2531]; decide
    · -- n = 2532
      use 277
      refine ⟨by decide, by decide, ?_⟩
      have h_2532 : Nat.sqrt (2532 + 277) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2532]; decide
    · -- n = 2533
      use 277
      refine ⟨by decide, by decide, ?_⟩
      have h_2533 : Nat.sqrt (2533 + 277) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2533]; decide
    · -- n = 2534
      use 277
      refine ⟨by decide, by decide, ?_⟩
      have h_2534 : Nat.sqrt (2534 + 277) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2534]; decide
    · -- n = 2535
      use 277
      refine ⟨by decide, by decide, ?_⟩
      have h_2535 : Nat.sqrt (2535 + 277) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2535]; decide
    · -- n = 2536
      use 277
      refine ⟨by decide, by decide, ?_⟩
      have h_2536 : Nat.sqrt (2536 + 277) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2536]; decide
    · -- n = 2537
      use 277
      refine ⟨by decide, by decide, ?_⟩
      have h_2537 : Nat.sqrt (2537 + 277) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2537]; decide
    · -- n = 2538
      use 271
      refine ⟨by decide, by decide, ?_⟩
      have h_2538 : Nat.sqrt (2538 + 271) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2538]; decide
    · -- n = 2539
      use 271
      refine ⟨by decide, by decide, ?_⟩
      have h_2539 : Nat.sqrt (2539 + 271) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2539]; decide
    · -- n = 2540
      use 269
      refine ⟨by decide, by decide, ?_⟩
      have h_2540 : Nat.sqrt (2540 + 269) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2540]; decide
    · -- n = 2541
      use 269
      refine ⟨by decide, by decide, ?_⟩
      have h_2541 : Nat.sqrt (2541 + 269) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2541]; decide
    · -- n = 2542
      use 269
      refine ⟨by decide, by decide, ?_⟩
      have h_2542 : Nat.sqrt (2542 + 269) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2542]; decide
    · -- n = 2543
      use 269
      refine ⟨by decide, by decide, ?_⟩
      have h_2543 : Nat.sqrt (2543 + 269) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2543]; decide
    · -- n = 2544
      use 269
      refine ⟨by decide, by decide, ?_⟩
      have h_2544 : Nat.sqrt (2544 + 269) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2544]; decide
    · -- n = 2545
      use 269
      refine ⟨by decide, by decide, ?_⟩
      have h_2545 : Nat.sqrt (2545 + 269) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2545]; decide
    · -- n = 2546
      use 263
      refine ⟨by decide, by decide, ?_⟩
      have h_2546 : Nat.sqrt (2546 + 263) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2546]; decide
    · -- n = 2547
      use 263
      refine ⟨by decide, by decide, ?_⟩
      have h_2547 : Nat.sqrt (2547 + 263) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2547]; decide
    · -- n = 2548
      use 263
      refine ⟨by decide, by decide, ?_⟩
      have h_2548 : Nat.sqrt (2548 + 263) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2548]; decide
    · -- n = 2549
      use 263
      refine ⟨by decide, by decide, ?_⟩
      have h_2549 : Nat.sqrt (2549 + 263) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2549]; decide
    · -- n = 2550
      use 263
      refine ⟨by decide, by decide, ?_⟩
      have h_2550 : Nat.sqrt (2550 + 263) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2550]; decide
    · -- n = 2551
      use 263
      refine ⟨by decide, by decide, ?_⟩
      have h_2551 : Nat.sqrt (2551 + 263) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2551]; decide
    · -- n = 2552
      use 257
      refine ⟨by decide, by decide, ?_⟩
      have h_2552 : Nat.sqrt (2552 + 257) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2552]; decide
    · -- n = 2553
      use 257
      refine ⟨by decide, by decide, ?_⟩
      have h_2553 : Nat.sqrt (2553 + 257) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2553]; decide
    · -- n = 2554
      use 257
      refine ⟨by decide, by decide, ?_⟩
      have h_2554 : Nat.sqrt (2554 + 257) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2554]; decide
    · -- n = 2555
      use 257
      refine ⟨by decide, by decide, ?_⟩
      have h_2555 : Nat.sqrt (2555 + 257) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2555]; decide
    · -- n = 2556
      use 257
      refine ⟨by decide, by decide, ?_⟩
      have h_2556 : Nat.sqrt (2556 + 257) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2556]; decide
    · -- n = 2557
      use 257
      refine ⟨by decide, by decide, ?_⟩
      have h_2557 : Nat.sqrt (2557 + 257) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2557]; decide
    · -- n = 2558
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_2558 : Nat.sqrt (2558 + 251) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2558]; decide
    · -- n = 2559
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_2559 : Nat.sqrt (2559 + 251) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2559]; decide
    · -- n = 2560
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_2560 : Nat.sqrt (2560 + 251) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2560]; decide
    · -- n = 2561
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_2561 : Nat.sqrt (2561 + 251) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2561]; decide
    · -- n = 2562
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_2562 : Nat.sqrt (2562 + 251) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2562]; decide
    · -- n = 2563
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_2563 : Nat.sqrt (2563 + 251) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2563]; decide
    · -- n = 2564
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_2564 : Nat.sqrt (2564 + 251) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2564]; decide
    · -- n = 2565
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_2565 : Nat.sqrt (2565 + 251) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2565]; decide
    · -- n = 2566
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_2566 : Nat.sqrt (2566 + 251) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2566]; decide
    · -- n = 2567
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_2567 : Nat.sqrt (2567 + 251) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2567]; decide
    · -- n = 2568
      use 241
      refine ⟨by decide, by decide, ?_⟩
      have h_2568 : Nat.sqrt (2568 + 241) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2568]; decide
    · -- n = 2569
      use 241
      refine ⟨by decide, by decide, ?_⟩
      have h_2569 : Nat.sqrt (2569 + 241) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2569]; decide
    · -- n = 2570
      use 239
      refine ⟨by decide, by decide, ?_⟩
      have h_2570 : Nat.sqrt (2570 + 239) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2570]; decide
    · -- n = 2571
      use 239
      refine ⟨by decide, by decide, ?_⟩
      have h_2571 : Nat.sqrt (2571 + 239) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2571]; decide
    · -- n = 2572
      use 239
      refine ⟨by decide, by decide, ?_⟩
      have h_2572 : Nat.sqrt (2572 + 239) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2572]; decide
    · -- n = 2573
      use 239
      refine ⟨by decide, by decide, ?_⟩
      have h_2573 : Nat.sqrt (2573 + 239) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2573]; decide
    · -- n = 2574
      use 239
      refine ⟨by decide, by decide, ?_⟩
      have h_2574 : Nat.sqrt (2574 + 239) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2574]; decide
    · -- n = 2575
      use 239
      refine ⟨by decide, by decide, ?_⟩
      have h_2575 : Nat.sqrt (2575 + 239) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2575]; decide
    · -- n = 2576
      use 233
      refine ⟨by decide, by decide, ?_⟩
      have h_2576 : Nat.sqrt (2576 + 233) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2576]; decide
    · -- n = 2577
      use 233
      refine ⟨by decide, by decide, ?_⟩
      have h_2577 : Nat.sqrt (2577 + 233) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2577]; decide
    · -- n = 2578
      use 233
      refine ⟨by decide, by decide, ?_⟩
      have h_2578 : Nat.sqrt (2578 + 233) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2578]; decide
    · -- n = 2579
      use 233
      refine ⟨by decide, by decide, ?_⟩
      have h_2579 : Nat.sqrt (2579 + 233) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2579]; decide
    · -- n = 2580
      use 229
      refine ⟨by decide, by decide, ?_⟩
      have h_2580 : Nat.sqrt (2580 + 229) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2580]; decide
    · -- n = 2581
      use 229
      refine ⟨by decide, by decide, ?_⟩
      have h_2581 : Nat.sqrt (2581 + 229) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2581]; decide
    · -- n = 2582
      use 227
      refine ⟨by decide, by decide, ?_⟩
      have h_2582 : Nat.sqrt (2582 + 227) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2582]; decide
    · -- n = 2583
      use 227
      refine ⟨by decide, by decide, ?_⟩
      have h_2583 : Nat.sqrt (2583 + 227) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2583]; decide
    · -- n = 2584
      use 227
      refine ⟨by decide, by decide, ?_⟩
      have h_2584 : Nat.sqrt (2584 + 227) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2584]; decide
    · -- n = 2585
      use 227
      refine ⟨by decide, by decide, ?_⟩
      have h_2585 : Nat.sqrt (2585 + 227) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2585]; decide
    · -- n = 2586
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_2586 : Nat.sqrt (2586 + 223) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2586]; decide
    · -- n = 2587
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_2587 : Nat.sqrt (2587 + 223) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2587]; decide
    · -- n = 2588
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_2588 : Nat.sqrt (2588 + 223) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2588]; decide
    · -- n = 2589
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_2589 : Nat.sqrt (2589 + 223) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2589]; decide
    · -- n = 2590
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_2590 : Nat.sqrt (2590 + 223) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2590]; decide
    · -- n = 2591
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_2591 : Nat.sqrt (2591 + 223) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2591]; decide
    · -- n = 2592
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_2592 : Nat.sqrt (2592 + 223) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2592]; decide
    · -- n = 2593
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_2593 : Nat.sqrt (2593 + 223) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2593]; decide
    · -- n = 2594
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_2594 : Nat.sqrt (2594 + 223) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2594]; decide
    · -- n = 2595
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_2595 : Nat.sqrt (2595 + 223) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2595]; decide
    · -- n = 2596
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_2596 : Nat.sqrt (2596 + 223) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2596]; decide
    · -- n = 2597
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_2597 : Nat.sqrt (2597 + 223) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2597]; decide
    · -- n = 2598
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_2598 : Nat.sqrt (2598 + 211) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2598]; decide
    · -- n = 2599
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_2599 : Nat.sqrt (2599 + 211) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2599]; decide
    · -- n = 2600
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_2600 : Nat.sqrt (2600 + 211) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2600]; decide
    · -- n = 2601
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_2601 : Nat.sqrt (2601 + 211) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2601]; decide
    · -- n = 2602
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_2602 : Nat.sqrt (2602 + 211) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2602]; decide
    · -- n = 2603
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_2603 : Nat.sqrt (2603 + 211) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2603]; decide
    · -- n = 2604
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_2604 : Nat.sqrt (2604 + 211) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2604]; decide
    · -- n = 2605
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_2605 : Nat.sqrt (2605 + 211) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2605]; decide
    · -- n = 2606
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_2606 : Nat.sqrt (2606 + 211) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2606]; decide
    · -- n = 2607
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_2607 : Nat.sqrt (2607 + 211) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2607]; decide
    · -- n = 2608
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_2608 : Nat.sqrt (2608 + 211) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2608]; decide
    · -- n = 2609
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_2609 : Nat.sqrt (2609 + 211) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2609]; decide
    · -- n = 2610
      use 199
      refine ⟨by decide, by decide, ?_⟩
      have h_2610 : Nat.sqrt (2610 + 199) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2610]; decide
    · -- n = 2611
      use 199
      refine ⟨by decide, by decide, ?_⟩
      have h_2611 : Nat.sqrt (2611 + 199) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2611]; decide
    · -- n = 2612
      use 197
      refine ⟨by decide, by decide, ?_⟩
      have h_2612 : Nat.sqrt (2612 + 197) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2612]; decide
    · -- n = 2613
      use 197
      refine ⟨by decide, by decide, ?_⟩
      have h_2613 : Nat.sqrt (2613 + 197) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2613]; decide
    · -- n = 2614
      use 197
      refine ⟨by decide, by decide, ?_⟩
      have h_2614 : Nat.sqrt (2614 + 197) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2614]; decide
    · -- n = 2615
      use 197
      refine ⟨by decide, by decide, ?_⟩
      have h_2615 : Nat.sqrt (2615 + 197) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2615]; decide
    · -- n = 2616
      use 193
      refine ⟨by decide, by decide, ?_⟩
      have h_2616 : Nat.sqrt (2616 + 193) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2616]; decide
    · -- n = 2617
      use 193
      refine ⟨by decide, by decide, ?_⟩
      have h_2617 : Nat.sqrt (2617 + 193) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2617]; decide
    · -- n = 2618
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_2618 : Nat.sqrt (2618 + 191) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2618]; decide
    · -- n = 2619
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_2619 : Nat.sqrt (2619 + 191) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2619]; decide
    · -- n = 2620
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_2620 : Nat.sqrt (2620 + 191) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2620]; decide
    · -- n = 2621
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_2621 : Nat.sqrt (2621 + 191) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2621]; decide
    · -- n = 2622
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_2622 : Nat.sqrt (2622 + 191) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2622]; decide
    · -- n = 2623
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_2623 : Nat.sqrt (2623 + 191) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2623]; decide
    · -- n = 2624
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_2624 : Nat.sqrt (2624 + 191) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2624]; decide
    · -- n = 2625
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_2625 : Nat.sqrt (2625 + 191) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2625]; decide
    · -- n = 2626
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_2626 : Nat.sqrt (2626 + 191) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2626]; decide
    · -- n = 2627
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_2627 : Nat.sqrt (2627 + 191) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2627]; decide
    · -- n = 2628
      use 181
      refine ⟨by decide, by decide, ?_⟩
      have h_2628 : Nat.sqrt (2628 + 181) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2628]; decide
    · -- n = 2629
      use 181
      refine ⟨by decide, by decide, ?_⟩
      have h_2629 : Nat.sqrt (2629 + 181) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2629]; decide
    · -- n = 2630
      use 179
      refine ⟨by decide, by decide, ?_⟩
      have h_2630 : Nat.sqrt (2630 + 179) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2630]; decide
    · -- n = 2631
      use 179
      refine ⟨by decide, by decide, ?_⟩
      have h_2631 : Nat.sqrt (2631 + 179) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2631]; decide
    · -- n = 2632
      use 179
      refine ⟨by decide, by decide, ?_⟩
      have h_2632 : Nat.sqrt (2632 + 179) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2632]; decide
    · -- n = 2633
      use 179
      refine ⟨by decide, by decide, ?_⟩
      have h_2633 : Nat.sqrt (2633 + 179) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2633]; decide
    · -- n = 2634
      use 179
      refine ⟨by decide, by decide, ?_⟩
      have h_2634 : Nat.sqrt (2634 + 179) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2634]; decide
    · -- n = 2635
      use 179
      refine ⟨by decide, by decide, ?_⟩
      have h_2635 : Nat.sqrt (2635 + 179) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2635]; decide
    · -- n = 2636
      use 173
      refine ⟨by decide, by decide, ?_⟩
      have h_2636 : Nat.sqrt (2636 + 173) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2636]; decide
    · -- n = 2637
      use 173
      refine ⟨by decide, by decide, ?_⟩
      have h_2637 : Nat.sqrt (2637 + 173) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2637]; decide
    · -- n = 2638
      use 173
      refine ⟨by decide, by decide, ?_⟩
      have h_2638 : Nat.sqrt (2638 + 173) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2638]; decide
    · -- n = 2639
      use 173
      refine ⟨by decide, by decide, ?_⟩
      have h_2639 : Nat.sqrt (2639 + 173) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2639]; decide
    · -- n = 2640
      use 173
      refine ⟨by decide, by decide, ?_⟩
      have h_2640 : Nat.sqrt (2640 + 173) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2640]; decide
    · -- n = 2641
      use 173
      refine ⟨by decide, by decide, ?_⟩
      have h_2641 : Nat.sqrt (2641 + 173) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2641]; decide
    · -- n = 2642
      use 167
      refine ⟨by decide, by decide, ?_⟩
      have h_2642 : Nat.sqrt (2642 + 167) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2642]; decide
    · -- n = 2643
      use 167
      refine ⟨by decide, by decide, ?_⟩
      have h_2643 : Nat.sqrt (2643 + 167) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2643]; decide
    · -- n = 2644
      use 167
      refine ⟨by decide, by decide, ?_⟩
      have h_2644 : Nat.sqrt (2644 + 167) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2644]; decide
    · -- n = 2645
      use 167
      refine ⟨by decide, by decide, ?_⟩
      have h_2645 : Nat.sqrt (2645 + 167) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2645]; decide
    · -- n = 2646
      use 163
      refine ⟨by decide, by decide, ?_⟩
      have h_2646 : Nat.sqrt (2646 + 163) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2646]; decide
    · -- n = 2647
      use 163
      refine ⟨by decide, by decide, ?_⟩
      have h_2647 : Nat.sqrt (2647 + 163) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2647]; decide
    · -- n = 2648
      use 163
      refine ⟨by decide, by decide, ?_⟩
      have h_2648 : Nat.sqrt (2648 + 163) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2648]; decide
    · -- n = 2649
      use 163
      refine ⟨by decide, by decide, ?_⟩
      have h_2649 : Nat.sqrt (2649 + 163) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2649]; decide
    · -- n = 2650
      use 163
      refine ⟨by decide, by decide, ?_⟩
      have h_2650 : Nat.sqrt (2650 + 163) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2650]; decide
    · -- n = 2651
      use 163
      refine ⟨by decide, by decide, ?_⟩
      have h_2651 : Nat.sqrt (2651 + 163) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2651]; decide
    · -- n = 2652
      use 157
      refine ⟨by decide, by decide, ?_⟩
      have h_2652 : Nat.sqrt (2652 + 157) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2652]; decide
    · -- n = 2653
      use 157
      refine ⟨by decide, by decide, ?_⟩
      have h_2653 : Nat.sqrt (2653 + 157) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2653]; decide
    · -- n = 2654
      use 157
      refine ⟨by decide, by decide, ?_⟩
      have h_2654 : Nat.sqrt (2654 + 157) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2654]; decide
    · -- n = 2655
      use 157
      refine ⟨by decide, by decide, ?_⟩
      have h_2655 : Nat.sqrt (2655 + 157) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2655]; decide
    · -- n = 2656
      use 157
      refine ⟨by decide, by decide, ?_⟩
      have h_2656 : Nat.sqrt (2656 + 157) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2656]; decide
    · -- n = 2657
      use 157
      refine ⟨by decide, by decide, ?_⟩
      have h_2657 : Nat.sqrt (2657 + 157) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2657]; decide
    · -- n = 2658
      use 151
      refine ⟨by decide, by decide, ?_⟩
      have h_2658 : Nat.sqrt (2658 + 151) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2658]; decide
    · -- n = 2659
      use 151
      refine ⟨by decide, by decide, ?_⟩
      have h_2659 : Nat.sqrt (2659 + 151) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2659]; decide
    · -- n = 2660
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_2660 : Nat.sqrt (2660 + 149) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2660]; decide
    · -- n = 2661
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_2661 : Nat.sqrt (2661 + 149) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2661]; decide
    · -- n = 2662
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_2662 : Nat.sqrt (2662 + 149) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2662]; decide
    · -- n = 2663
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_2663 : Nat.sqrt (2663 + 149) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2663]; decide
    · -- n = 2664
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_2664 : Nat.sqrt (2664 + 149) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2664]; decide
    · -- n = 2665
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_2665 : Nat.sqrt (2665 + 149) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2665]; decide
    · -- n = 2666
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_2666 : Nat.sqrt (2666 + 149) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2666]; decide
    · -- n = 2667
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_2667 : Nat.sqrt (2667 + 149) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2667]; decide
    · -- n = 2668
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_2668 : Nat.sqrt (2668 + 149) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2668]; decide
    · -- n = 2669
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_2669 : Nat.sqrt (2669 + 149) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2669]; decide
    · -- n = 2670
      use 139
      refine ⟨by decide, by decide, ?_⟩
      have h_2670 : Nat.sqrt (2670 + 139) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2670]; decide
    · -- n = 2671
      use 139
      refine ⟨by decide, by decide, ?_⟩
      have h_2671 : Nat.sqrt (2671 + 139) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2671]; decide
    · -- n = 2672
      use 137
      refine ⟨by decide, by decide, ?_⟩
      have h_2672 : Nat.sqrt (2672 + 137) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2672]; decide
    · -- n = 2673
      use 137
      refine ⟨by decide, by decide, ?_⟩
      have h_2673 : Nat.sqrt (2673 + 137) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2673]; decide
    · -- n = 2674
      use 137
      refine ⟨by decide, by decide, ?_⟩
      have h_2674 : Nat.sqrt (2674 + 137) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2674]; decide
    · -- n = 2675
      use 137
      refine ⟨by decide, by decide, ?_⟩
      have h_2675 : Nat.sqrt (2675 + 137) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2675]; decide
    · -- n = 2676
      use 137
      refine ⟨by decide, by decide, ?_⟩
      have h_2676 : Nat.sqrt (2676 + 137) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2676]; decide
    · -- n = 2677
      use 137
      refine ⟨by decide, by decide, ?_⟩
      have h_2677 : Nat.sqrt (2677 + 137) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2677]; decide
    · -- n = 2678
      use 131
      refine ⟨by decide, by decide, ?_⟩
      have h_2678 : Nat.sqrt (2678 + 131) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2678]; decide
    · -- n = 2679
      use 131
      refine ⟨by decide, by decide, ?_⟩
      have h_2679 : Nat.sqrt (2679 + 131) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2679]; decide
    · -- n = 2680
      use 131
      refine ⟨by decide, by decide, ?_⟩
      have h_2680 : Nat.sqrt (2680 + 131) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2680]; decide
    · -- n = 2681
      use 131
      refine ⟨by decide, by decide, ?_⟩
      have h_2681 : Nat.sqrt (2681 + 131) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2681]; decide
    · -- n = 2682
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_2682 : Nat.sqrt (2682 + 127) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2682]; decide
    · -- n = 2683
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_2683 : Nat.sqrt (2683 + 127) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2683]; decide
    · -- n = 2684
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_2684 : Nat.sqrt (2684 + 127) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2684]; decide
    · -- n = 2685
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_2685 : Nat.sqrt (2685 + 127) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2685]; decide
    · -- n = 2686
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_2686 : Nat.sqrt (2686 + 127) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2686]; decide
    · -- n = 2687
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_2687 : Nat.sqrt (2687 + 127) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2687]; decide
    · -- n = 2688
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_2688 : Nat.sqrt (2688 + 127) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2688]; decide
    · -- n = 2689
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_2689 : Nat.sqrt (2689 + 127) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2689]; decide
    · -- n = 2690
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_2690 : Nat.sqrt (2690 + 127) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2690]; decide
    · -- n = 2691
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_2691 : Nat.sqrt (2691 + 127) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2691]; decide
    · -- n = 2692
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_2692 : Nat.sqrt (2692 + 127) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2692]; decide
    · -- n = 2693
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_2693 : Nat.sqrt (2693 + 127) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2693]; decide
    · -- n = 2694
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_2694 : Nat.sqrt (2694 + 127) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2694]; decide
    · -- n = 2695
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_2695 : Nat.sqrt (2695 + 127) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2695]; decide
    · -- n = 2696
      use 113
      refine ⟨by decide, by decide, ?_⟩
      have h_2696 : Nat.sqrt (2696 + 113) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2696]; decide
    · -- n = 2697
      use 113
      refine ⟨by decide, by decide, ?_⟩
      have h_2697 : Nat.sqrt (2697 + 113) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2697]; decide
    · -- n = 2698
      use 113
      refine ⟨by decide, by decide, ?_⟩
      have h_2698 : Nat.sqrt (2698 + 113) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2698]; decide
    · -- n = 2699
      use 113
      refine ⟨by decide, by decide, ?_⟩
      have h_2699 : Nat.sqrt (2699 + 113) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2699]; decide
    · -- n = 2700
      use 109
      refine ⟨by decide, by decide, ?_⟩
      have h_2700 : Nat.sqrt (2700 + 109) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2700]; decide
    · -- n = 2701
      use 109
      refine ⟨by decide, by decide, ?_⟩
      have h_2701 : Nat.sqrt (2701 + 109) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2701]; decide
    · -- n = 2702
      use 107
      refine ⟨by decide, by decide, ?_⟩
      have h_2702 : Nat.sqrt (2702 + 107) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2702]; decide
    · -- n = 2703
      use 107
      refine ⟨by decide, by decide, ?_⟩
      have h_2703 : Nat.sqrt (2703 + 107) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2703]; decide
    · -- n = 2704
      use 107
      refine ⟨by decide, by decide, ?_⟩
      have h_2704 : Nat.sqrt (2704 + 107) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2704]; decide
    · -- n = 2705
      use 107
      refine ⟨by decide, by decide, ?_⟩
      have h_2705 : Nat.sqrt (2705 + 107) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2705]; decide
    · -- n = 2706
      use 103
      refine ⟨by decide, by decide, ?_⟩
      have h_2706 : Nat.sqrt (2706 + 103) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2706]; decide
    · -- n = 2707
      use 103
      refine ⟨by decide, by decide, ?_⟩
      have h_2707 : Nat.sqrt (2707 + 103) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2707]; decide
    · -- n = 2708
      use 101
      refine ⟨by decide, by decide, ?_⟩
      have h_2708 : Nat.sqrt (2708 + 101) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2708]; decide
    · -- n = 2709
      use 101
      refine ⟨by decide, by decide, ?_⟩
      have h_2709 : Nat.sqrt (2709 + 101) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2709]; decide
    · -- n = 2710
      use 101
      refine ⟨by decide, by decide, ?_⟩
      have h_2710 : Nat.sqrt (2710 + 101) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2710]; decide
    · -- n = 2711
      use 101
      refine ⟨by decide, by decide, ?_⟩
      have h_2711 : Nat.sqrt (2711 + 101) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2711]; decide
    · -- n = 2712
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_2712 : Nat.sqrt (2712 + 97) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2712]; decide
    · -- n = 2713
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_2713 : Nat.sqrt (2713 + 97) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2713]; decide
    · -- n = 2714
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_2714 : Nat.sqrt (2714 + 97) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2714]; decide
    · -- n = 2715
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_2715 : Nat.sqrt (2715 + 97) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2715]; decide
    · -- n = 2716
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_2716 : Nat.sqrt (2716 + 97) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2716]; decide
    · -- n = 2717
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_2717 : Nat.sqrt (2717 + 97) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2717]; decide
    · -- n = 2718
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_2718 : Nat.sqrt (2718 + 97) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2718]; decide
    · -- n = 2719
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_2719 : Nat.sqrt (2719 + 97) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2719]; decide
    · -- n = 2720
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_2720 : Nat.sqrt (2720 + 89) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2720]; decide
    · -- n = 2721
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_2721 : Nat.sqrt (2721 + 89) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2721]; decide
    · -- n = 2722
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_2722 : Nat.sqrt (2722 + 89) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2722]; decide
    · -- n = 2723
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_2723 : Nat.sqrt (2723 + 89) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2723]; decide
    · -- n = 2724
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_2724 : Nat.sqrt (2724 + 89) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2724]; decide
    · -- n = 2725
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_2725 : Nat.sqrt (2725 + 89) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2725]; decide
    · -- n = 2726
      use 83
      refine ⟨by decide, by decide, ?_⟩
      have h_2726 : Nat.sqrt (2726 + 83) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2726]; decide
    · -- n = 2727
      use 83
      refine ⟨by decide, by decide, ?_⟩
      have h_2727 : Nat.sqrt (2727 + 83) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2727]; decide
    · -- n = 2728
      use 83
      refine ⟨by decide, by decide, ?_⟩
      have h_2728 : Nat.sqrt (2728 + 83) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2728]; decide
    · -- n = 2729
      use 83
      refine ⟨by decide, by decide, ?_⟩
      have h_2729 : Nat.sqrt (2729 + 83) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2729]; decide
    · -- n = 2730
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_2730 : Nat.sqrt (2730 + 79) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2730]; decide
    · -- n = 2731
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_2731 : Nat.sqrt (2731 + 79) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2731]; decide
    · -- n = 2732
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_2732 : Nat.sqrt (2732 + 79) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2732]; decide
    · -- n = 2733
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_2733 : Nat.sqrt (2733 + 79) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2733]; decide
    · -- n = 2734
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_2734 : Nat.sqrt (2734 + 79) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2734]; decide
    · -- n = 2735
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_2735 : Nat.sqrt (2735 + 79) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2735]; decide
    · -- n = 2736
      use 73
      refine ⟨by decide, by decide, ?_⟩
      have h_2736 : Nat.sqrt (2736 + 73) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2736]; decide
    · -- n = 2737
      use 73
      refine ⟨by decide, by decide, ?_⟩
      have h_2737 : Nat.sqrt (2737 + 73) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2737]; decide
    · -- n = 2738
      use 71
      refine ⟨by decide, by decide, ?_⟩
      have h_2738 : Nat.sqrt (2738 + 71) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2738]; decide
    · -- n = 2739
      use 71
      refine ⟨by decide, by decide, ?_⟩
      have h_2739 : Nat.sqrt (2739 + 71) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2739]; decide
    · -- n = 2740
      use 71
      refine ⟨by decide, by decide, ?_⟩
      have h_2740 : Nat.sqrt (2740 + 71) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2740]; decide
    · -- n = 2741
      use 71
      refine ⟨by decide, by decide, ?_⟩
      have h_2741 : Nat.sqrt (2741 + 71) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2741]; decide
    · -- n = 2742
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_2742 : Nat.sqrt (2742 + 67) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2742]; decide
    · -- n = 2743
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_2743 : Nat.sqrt (2743 + 67) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2743]; decide
    · -- n = 2744
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_2744 : Nat.sqrt (2744 + 67) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2744]; decide
    · -- n = 2745
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_2745 : Nat.sqrt (2745 + 67) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2745]; decide
    · -- n = 2746
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_2746 : Nat.sqrt (2746 + 67) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2746]; decide
    · -- n = 2747
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_2747 : Nat.sqrt (2747 + 67) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2747]; decide
    · -- n = 2748
      use 61
      refine ⟨by decide, by decide, ?_⟩
      have h_2748 : Nat.sqrt (2748 + 61) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2748]; decide
    · -- n = 2749
      use 61
      refine ⟨by decide, by decide, ?_⟩
      have h_2749 : Nat.sqrt (2749 + 61) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2749]; decide
    · -- n = 2750
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_2750 : Nat.sqrt (2750 + 59) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2750]; decide
    · -- n = 2751
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_2751 : Nat.sqrt (2751 + 59) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2751]; decide
    · -- n = 2752
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_2752 : Nat.sqrt (2752 + 59) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2752]; decide
    · -- n = 2753
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_2753 : Nat.sqrt (2753 + 59) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2753]; decide
    · -- n = 2754
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_2754 : Nat.sqrt (2754 + 59) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2754]; decide
    · -- n = 2755
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_2755 : Nat.sqrt (2755 + 59) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2755]; decide
    · -- n = 2756
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_2756 : Nat.sqrt (2756 + 53) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2756]; decide
    · -- n = 2757
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_2757 : Nat.sqrt (2757 + 53) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2757]; decide
    · -- n = 2758
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_2758 : Nat.sqrt (2758 + 53) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2758]; decide
    · -- n = 2759
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_2759 : Nat.sqrt (2759 + 53) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2759]; decide
    · -- n = 2760
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_2760 : Nat.sqrt (2760 + 53) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2760]; decide
    · -- n = 2761
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_2761 : Nat.sqrt (2761 + 53) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2761]; decide
    · -- n = 2762
      use 47
      refine ⟨by decide, by decide, ?_⟩
      have h_2762 : Nat.sqrt (2762 + 47) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2762]; decide
    · -- n = 2763
      use 47
      refine ⟨by decide, by decide, ?_⟩
      have h_2763 : Nat.sqrt (2763 + 47) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2763]; decide
    · -- n = 2764
      use 47
      refine ⟨by decide, by decide, ?_⟩
      have h_2764 : Nat.sqrt (2764 + 47) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2764]; decide
    · -- n = 2765
      use 47
      refine ⟨by decide, by decide, ?_⟩
      have h_2765 : Nat.sqrt (2765 + 47) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2765]; decide
    · -- n = 2766
      use 43
      refine ⟨by decide, by decide, ?_⟩
      have h_2766 : Nat.sqrt (2766 + 43) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2766]; decide
    · -- n = 2767
      use 43
      refine ⟨by decide, by decide, ?_⟩
      have h_2767 : Nat.sqrt (2767 + 43) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2767]; decide
    · -- n = 2768
      use 41
      refine ⟨by decide, by decide, ?_⟩
      have h_2768 : Nat.sqrt (2768 + 41) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2768]; decide
    · -- n = 2769
      use 41
      refine ⟨by decide, by decide, ?_⟩
      have h_2769 : Nat.sqrt (2769 + 41) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2769]; decide
    · -- n = 2770
      use 41
      refine ⟨by decide, by decide, ?_⟩
      have h_2770 : Nat.sqrt (2770 + 41) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2770]; decide
    · -- n = 2771
      use 41
      refine ⟨by decide, by decide, ?_⟩
      have h_2771 : Nat.sqrt (2771 + 41) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2771]; decide
    · -- n = 2772
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_2772 : Nat.sqrt (2772 + 37) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2772]; decide
    · -- n = 2773
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_2773 : Nat.sqrt (2773 + 37) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2773]; decide
    · -- n = 2774
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_2774 : Nat.sqrt (2774 + 37) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2774]; decide
    · -- n = 2775
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_2775 : Nat.sqrt (2775 + 37) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2775]; decide
    · -- n = 2776
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_2776 : Nat.sqrt (2776 + 37) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2776]; decide
    · -- n = 2777
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_2777 : Nat.sqrt (2777 + 37) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2777]; decide
    · -- n = 2778
      use 31
      refine ⟨by decide, by decide, ?_⟩
      have h_2778 : Nat.sqrt (2778 + 31) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2778]; decide
    · -- n = 2779
      use 31
      refine ⟨by decide, by decide, ?_⟩
      have h_2779 : Nat.sqrt (2779 + 31) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2779]; decide
    · -- n = 2780
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_2780 : Nat.sqrt (2780 + 29) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2780]; decide
    · -- n = 2781
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_2781 : Nat.sqrt (2781 + 29) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2781]; decide
    · -- n = 2782
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_2782 : Nat.sqrt (2782 + 29) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2782]; decide
    · -- n = 2783
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_2783 : Nat.sqrt (2783 + 29) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2783]; decide
    · -- n = 2784
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_2784 : Nat.sqrt (2784 + 29) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2784]; decide
    · -- n = 2785
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_2785 : Nat.sqrt (2785 + 29) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2785]; decide
    · -- n = 2786
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_2786 : Nat.sqrt (2786 + 23) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2786]; decide
    · -- n = 2787
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_2787 : Nat.sqrt (2787 + 23) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2787]; decide
    · -- n = 2788
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_2788 : Nat.sqrt (2788 + 23) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2788]; decide
    · -- n = 2789
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_2789 : Nat.sqrt (2789 + 23) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2789]; decide
    · -- n = 2790
      use 19
      refine ⟨by decide, by decide, ?_⟩
      have h_2790 : Nat.sqrt (2790 + 19) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2790]; decide
    · -- n = 2791
      use 19
      refine ⟨by decide, by decide, ?_⟩
      have h_2791 : Nat.sqrt (2791 + 19) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2791]; decide
    · -- n = 2792
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_2792 : Nat.sqrt (2792 + 17) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2792]; decide
    · -- n = 2793
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_2793 : Nat.sqrt (2793 + 17) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2793]; decide
    · -- n = 2794
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_2794 : Nat.sqrt (2794 + 17) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2794]; decide
    · -- n = 2795
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_2795 : Nat.sqrt (2795 + 17) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2795]; decide
    · -- n = 2796
      use 13
      refine ⟨by decide, by decide, ?_⟩
      have h_2796 : Nat.sqrt (2796 + 13) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2796]; decide
    · -- n = 2797
      use 13
      refine ⟨by decide, by decide, ?_⟩
      have h_2797 : Nat.sqrt (2797 + 13) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2797]; decide
    · -- n = 2798
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_2798 : Nat.sqrt (2798 + 11) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2798]; decide
    · -- n = 2799
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_2799 : Nat.sqrt (2799 + 11) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2799]; decide
    · -- n = 2800
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_2800 : Nat.sqrt (2800 + 11) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2800]; decide
    · -- n = 2801
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_2801 : Nat.sqrt (2801 + 11) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2801]; decide
    · -- n = 2802
      use 7
      refine ⟨by decide, by decide, ?_⟩
      have h_2802 : Nat.sqrt (2802 + 7) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2802]; decide
    · -- n = 2803
      use 7
      refine ⟨by decide, by decide, ?_⟩
      have h_2803 : Nat.sqrt (2803 + 7) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2803]; decide
    · -- n = 2804
      use 5
      refine ⟨by decide, by decide, ?_⟩
      have h_2804 : Nat.sqrt (2804 + 5) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2804]; decide
    · -- n = 2805
      use 5
      refine ⟨by decide, by decide, ?_⟩
      have h_2805 : Nat.sqrt (2805 + 5) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2805]; decide
    · -- n = 2806
      use 3
      refine ⟨by decide, by decide, ?_⟩
      have h_2806 : Nat.sqrt (2806 + 3) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2806]; decide
    · -- n = 2807
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2807 : Nat.sqrt (2807 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2807]; decide
    · -- n = 2808
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2808 : Nat.sqrt (2808 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2808]; decide
    · -- n = 2809
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2809 : Nat.sqrt (2809 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2809]; decide
    · -- n = 2810
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2810 : Nat.sqrt (2810 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2810]; decide
    · -- n = 2811
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2811 : Nat.sqrt (2811 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2811]; decide
    · -- n = 2812
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2812 : Nat.sqrt (2812 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2812]; decide
    · -- n = 2813
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2813 : Nat.sqrt (2813 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2813]; decide
    · -- n = 2814
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2814 : Nat.sqrt (2814 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2814]; decide
    · -- n = 2815
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2815 : Nat.sqrt (2815 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2815]; decide
    · -- n = 2816
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2816 : Nat.sqrt (2816 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2816]; decide
    · -- n = 2817
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2817 : Nat.sqrt (2817 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2817]; decide
    · -- n = 2818
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2818 : Nat.sqrt (2818 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2818]; decide
    · -- n = 2819
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2819 : Nat.sqrt (2819 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2819]; decide
    · -- n = 2820
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2820 : Nat.sqrt (2820 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2820]; decide
    · -- n = 2821
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2821 : Nat.sqrt (2821 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2821]; decide
    · -- n = 2822
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2822 : Nat.sqrt (2822 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2822]; decide
    · -- n = 2823
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2823 : Nat.sqrt (2823 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2823]; decide
    · -- n = 2824
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2824 : Nat.sqrt (2824 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2824]; decide
    · -- n = 2825
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2825 : Nat.sqrt (2825 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2825]; decide
    · -- n = 2826
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2826 : Nat.sqrt (2826 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2826]; decide
    · -- n = 2827
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2827 : Nat.sqrt (2827 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2827]; decide
    · -- n = 2828
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2828 : Nat.sqrt (2828 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2828]; decide
    · -- n = 2829
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2829 : Nat.sqrt (2829 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2829]; decide
    · -- n = 2830
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2830 : Nat.sqrt (2830 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2830]; decide
    · -- n = 2831
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2831 : Nat.sqrt (2831 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2831]; decide
    · -- n = 2832
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2832 : Nat.sqrt (2832 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2832]; decide
    · -- n = 2833
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2833 : Nat.sqrt (2833 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2833]; decide
    · -- n = 2834
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2834 : Nat.sqrt (2834 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2834]; decide
    · -- n = 2835
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2835 : Nat.sqrt (2835 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2835]; decide
    · -- n = 2836
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2836 : Nat.sqrt (2836 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2836]; decide
    · -- n = 2837
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2837 : Nat.sqrt (2837 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2837]; decide
    · -- n = 2838
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2838 : Nat.sqrt (2838 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2838]; decide
    · -- n = 2839
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2839 : Nat.sqrt (2839 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2839]; decide
    · -- n = 2840
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2840 : Nat.sqrt (2840 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2840]; decide
    · -- n = 2841
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2841 : Nat.sqrt (2841 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2841]; decide
    · -- n = 2842
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2842 : Nat.sqrt (2842 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2842]; decide
    · -- n = 2843
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2843 : Nat.sqrt (2843 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2843]; decide
    · -- n = 2844
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2844 : Nat.sqrt (2844 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2844]; decide
    · -- n = 2845
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2845 : Nat.sqrt (2845 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2845]; decide
    · -- n = 2846
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2846 : Nat.sqrt (2846 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2846]; decide
    · -- n = 2847
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2847 : Nat.sqrt (2847 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2847]; decide
    · -- n = 2848
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2848 : Nat.sqrt (2848 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2848]; decide
    · -- n = 2849
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2849 : Nat.sqrt (2849 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2849]; decide
    · -- n = 2850
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2850 : Nat.sqrt (2850 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2850]; decide
    · -- n = 2851
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2851 : Nat.sqrt (2851 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2851]; decide
    · -- n = 2852
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2852 : Nat.sqrt (2852 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2852]; decide
    · -- n = 2853
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2853 : Nat.sqrt (2853 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2853]; decide
    · -- n = 2854
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2854 : Nat.sqrt (2854 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2854]; decide
    · -- n = 2855
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2855 : Nat.sqrt (2855 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2855]; decide
    · -- n = 2856
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2856 : Nat.sqrt (2856 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2856]; decide
    · -- n = 2857
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2857 : Nat.sqrt (2857 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2857]; decide
    · -- n = 2858
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2858 : Nat.sqrt (2858 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2858]; decide
    · -- n = 2859
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2859 : Nat.sqrt (2859 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2859]; decide
    · -- n = 2860
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2860 : Nat.sqrt (2860 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2860]; decide
    · -- n = 2861
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2861 : Nat.sqrt (2861 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2861]; decide
    · -- n = 2862
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2862 : Nat.sqrt (2862 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2862]; decide
    · -- n = 2863
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2863 : Nat.sqrt (2863 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2863]; decide
    · -- n = 2864
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2864 : Nat.sqrt (2864 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2864]; decide
    · -- n = 2865
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2865 : Nat.sqrt (2865 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2865]; decide
    · -- n = 2866
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2866 : Nat.sqrt (2866 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2866]; decide
    · -- n = 2867
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2867 : Nat.sqrt (2867 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2867]; decide
    · -- n = 2868
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2868 : Nat.sqrt (2868 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2868]; decide
    · -- n = 2869
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2869 : Nat.sqrt (2869 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2869]; decide
    · -- n = 2870
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2870 : Nat.sqrt (2870 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2870]; decide
    · -- n = 2871
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2871 : Nat.sqrt (2871 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2871]; decide
    · -- n = 2872
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2872 : Nat.sqrt (2872 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2872]; decide
    · -- n = 2873
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2873 : Nat.sqrt (2873 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2873]; decide
    · -- n = 2874
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2874 : Nat.sqrt (2874 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2874]; decide
    · -- n = 2875
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2875 : Nat.sqrt (2875 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2875]; decide
    · -- n = 2876
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2876 : Nat.sqrt (2876 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2876]; decide
    · -- n = 2877
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2877 : Nat.sqrt (2877 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2877]; decide
    · -- n = 2878
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2878 : Nat.sqrt (2878 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2878]; decide
    · -- n = 2879
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2879 : Nat.sqrt (2879 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2879]; decide
    · -- n = 2880
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2880 : Nat.sqrt (2880 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2880]; decide
    · -- n = 2881
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2881 : Nat.sqrt (2881 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2881]; decide
    · -- n = 2882
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2882 : Nat.sqrt (2882 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2882]; decide
    · -- n = 2883
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2883 : Nat.sqrt (2883 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2883]; decide
    · -- n = 2884
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2884 : Nat.sqrt (2884 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2884]; decide
    · -- n = 2885
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2885 : Nat.sqrt (2885 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2885]; decide
    · -- n = 2886
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2886 : Nat.sqrt (2886 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2886]; decide
    · -- n = 2887
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2887 : Nat.sqrt (2887 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2887]; decide
    · -- n = 2888
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2888 : Nat.sqrt (2888 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2888]; decide
    · -- n = 2889
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2889 : Nat.sqrt (2889 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2889]; decide
    · -- n = 2890
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2890 : Nat.sqrt (2890 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2890]; decide
    · -- n = 2891
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2891 : Nat.sqrt (2891 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2891]; decide
    · -- n = 2892
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2892 : Nat.sqrt (2892 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2892]; decide
    · -- n = 2893
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2893 : Nat.sqrt (2893 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2893]; decide
    · -- n = 2894
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2894 : Nat.sqrt (2894 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2894]; decide
    · -- n = 2895
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2895 : Nat.sqrt (2895 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2895]; decide
    · -- n = 2896
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2896 : Nat.sqrt (2896 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2896]; decide
    · -- n = 2897
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2897 : Nat.sqrt (2897 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2897]; decide
    · -- n = 2898
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2898 : Nat.sqrt (2898 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2898]; decide
    · -- n = 2899
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2899 : Nat.sqrt (2899 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2899]; decide
    · -- n = 2900
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2900 : Nat.sqrt (2900 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2900]; decide
    · -- n = 2901
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2901 : Nat.sqrt (2901 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2901]; decide
    · -- n = 2902
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2902 : Nat.sqrt (2902 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2902]; decide
    · -- n = 2903
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2903 : Nat.sqrt (2903 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2903]; decide
    · -- n = 2904
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2904 : Nat.sqrt (2904 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2904]; decide
    · -- n = 2905
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2905 : Nat.sqrt (2905 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2905]; decide
    · -- n = 2906
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2906 : Nat.sqrt (2906 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2906]; decide
    · -- n = 2907
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2907 : Nat.sqrt (2907 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2907]; decide
    · -- n = 2908
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2908 : Nat.sqrt (2908 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2908]; decide
    · -- n = 2909
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2909 : Nat.sqrt (2909 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2909]; decide
    · -- n = 2910
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2910 : Nat.sqrt (2910 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2910]; decide
    · -- n = 2911
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2911 : Nat.sqrt (2911 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2911]; decide
    · -- n = 2912
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2912 : Nat.sqrt (2912 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2912]; decide
    · -- n = 2913
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_2913 : Nat.sqrt (2913 + 2) = 53 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2913]; decide
    · -- n = 2914
      use 569
      refine ⟨by decide, by decide, ?_⟩
      have h_2914 : Nat.sqrt (2914 + 569) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2914]; decide
    · -- n = 2915
      use 569
      refine ⟨by decide, by decide, ?_⟩
      have h_2915 : Nat.sqrt (2915 + 569) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2915]; decide
    · -- n = 2916
      use 569
      refine ⟨by decide, by decide, ?_⟩
      have h_2916 : Nat.sqrt (2916 + 569) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2916]; decide
    · -- n = 2917
      use 569
      refine ⟨by decide, by decide, ?_⟩
      have h_2917 : Nat.sqrt (2917 + 569) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2917]; decide
    · -- n = 2918
      use 563
      refine ⟨by decide, by decide, ?_⟩
      have h_2918 : Nat.sqrt (2918 + 563) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2918]; decide
    · -- n = 2919
      use 563
      refine ⟨by decide, by decide, ?_⟩
      have h_2919 : Nat.sqrt (2919 + 563) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2919]; decide
    · -- n = 2920
      use 563
      refine ⟨by decide, by decide, ?_⟩
      have h_2920 : Nat.sqrt (2920 + 563) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2920]; decide
    · -- n = 2921
      use 563
      refine ⟨by decide, by decide, ?_⟩
      have h_2921 : Nat.sqrt (2921 + 563) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2921]; decide
    · -- n = 2922
      use 563
      refine ⟨by decide, by decide, ?_⟩
      have h_2922 : Nat.sqrt (2922 + 563) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2922]; decide
    · -- n = 2923
      use 563
      refine ⟨by decide, by decide, ?_⟩
      have h_2923 : Nat.sqrt (2923 + 563) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2923]; decide
    · -- n = 2924
      use 557
      refine ⟨by decide, by decide, ?_⟩
      have h_2924 : Nat.sqrt (2924 + 557) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2924]; decide
    · -- n = 2925
      use 557
      refine ⟨by decide, by decide, ?_⟩
      have h_2925 : Nat.sqrt (2925 + 557) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2925]; decide
    · -- n = 2926
      use 557
      refine ⟨by decide, by decide, ?_⟩
      have h_2926 : Nat.sqrt (2926 + 557) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2926]; decide
    · -- n = 2927
      use 557
      refine ⟨by decide, by decide, ?_⟩
      have h_2927 : Nat.sqrt (2927 + 557) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2927]; decide
    · -- n = 2928
      use 557
      refine ⟨by decide, by decide, ?_⟩
      have h_2928 : Nat.sqrt (2928 + 557) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2928]; decide
    · -- n = 2929
      use 557
      refine ⟨by decide, by decide, ?_⟩
      have h_2929 : Nat.sqrt (2929 + 557) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2929]; decide
    · -- n = 2930
      use 557
      refine ⟨by decide, by decide, ?_⟩
      have h_2930 : Nat.sqrt (2930 + 557) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2930]; decide
    · -- n = 2931
      use 557
      refine ⟨by decide, by decide, ?_⟩
      have h_2931 : Nat.sqrt (2931 + 557) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2931]; decide
    · -- n = 2932
      use 557
      refine ⟨by decide, by decide, ?_⟩
      have h_2932 : Nat.sqrt (2932 + 557) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2932]; decide
    · -- n = 2933
      use 557
      refine ⟨by decide, by decide, ?_⟩
      have h_2933 : Nat.sqrt (2933 + 557) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2933]; decide
    · -- n = 2934
      use 547
      refine ⟨by decide, by decide, ?_⟩
      have h_2934 : Nat.sqrt (2934 + 547) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2934]; decide
    · -- n = 2935
      use 547
      refine ⟨by decide, by decide, ?_⟩
      have h_2935 : Nat.sqrt (2935 + 547) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2935]; decide
    · -- n = 2936
      use 547
      refine ⟨by decide, by decide, ?_⟩
      have h_2936 : Nat.sqrt (2936 + 547) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2936]; decide
    · -- n = 2937
      use 547
      refine ⟨by decide, by decide, ?_⟩
      have h_2937 : Nat.sqrt (2937 + 547) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2937]; decide
    · -- n = 2938
      use 547
      refine ⟨by decide, by decide, ?_⟩
      have h_2938 : Nat.sqrt (2938 + 547) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2938]; decide
    · -- n = 2939
      use 547
      refine ⟨by decide, by decide, ?_⟩
      have h_2939 : Nat.sqrt (2939 + 547) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2939]; decide
    · -- n = 2940
      use 541
      refine ⟨by decide, by decide, ?_⟩
      have h_2940 : Nat.sqrt (2940 + 541) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2940]; decide
    · -- n = 2941
      use 541
      refine ⟨by decide, by decide, ?_⟩
      have h_2941 : Nat.sqrt (2941 + 541) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2941]; decide
    · -- n = 2942
      use 541
      refine ⟨by decide, by decide, ?_⟩
      have h_2942 : Nat.sqrt (2942 + 541) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2942]; decide
    · -- n = 2943
      use 541
      refine ⟨by decide, by decide, ?_⟩
      have h_2943 : Nat.sqrt (2943 + 541) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2943]; decide
    · -- n = 2944
      use 541
      refine ⟨by decide, by decide, ?_⟩
      have h_2944 : Nat.sqrt (2944 + 541) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2944]; decide
    · -- n = 2945
      use 541
      refine ⟨by decide, by decide, ?_⟩
      have h_2945 : Nat.sqrt (2945 + 541) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2945]; decide
    · -- n = 2946
      use 541
      refine ⟨by decide, by decide, ?_⟩
      have h_2946 : Nat.sqrt (2946 + 541) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2946]; decide
    · -- n = 2947
      use 541
      refine ⟨by decide, by decide, ?_⟩
      have h_2947 : Nat.sqrt (2947 + 541) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2947]; decide
    · -- n = 2948
      use 541
      refine ⟨by decide, by decide, ?_⟩
      have h_2948 : Nat.sqrt (2948 + 541) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2948]; decide
    · -- n = 2949
      use 541
      refine ⟨by decide, by decide, ?_⟩
      have h_2949 : Nat.sqrt (2949 + 541) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2949]; decide
    · -- n = 2950
      use 541
      refine ⟨by decide, by decide, ?_⟩
      have h_2950 : Nat.sqrt (2950 + 541) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2950]; decide
    · -- n = 2951
      use 541
      refine ⟨by decide, by decide, ?_⟩
      have h_2951 : Nat.sqrt (2951 + 541) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2951]; decide
    · -- n = 2952
      use 541
      refine ⟨by decide, by decide, ?_⟩
      have h_2952 : Nat.sqrt (2952 + 541) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2952]; decide
    · -- n = 2953
      use 541
      refine ⟨by decide, by decide, ?_⟩
      have h_2953 : Nat.sqrt (2953 + 541) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2953]; decide
    · -- n = 2954
      use 541
      refine ⟨by decide, by decide, ?_⟩
      have h_2954 : Nat.sqrt (2954 + 541) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2954]; decide
    · -- n = 2955
      use 541
      refine ⟨by decide, by decide, ?_⟩
      have h_2955 : Nat.sqrt (2955 + 541) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2955]; decide
    · -- n = 2956
      use 541
      refine ⟨by decide, by decide, ?_⟩
      have h_2956 : Nat.sqrt (2956 + 541) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2956]; decide
    · -- n = 2957
      use 541
      refine ⟨by decide, by decide, ?_⟩
      have h_2957 : Nat.sqrt (2957 + 541) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2957]; decide
    · -- n = 2958
      use 523
      refine ⟨by decide, by decide, ?_⟩
      have h_2958 : Nat.sqrt (2958 + 523) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2958]; decide
    · -- n = 2959
      use 523
      refine ⟨by decide, by decide, ?_⟩
      have h_2959 : Nat.sqrt (2959 + 523) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2959]; decide
    · -- n = 2960
      use 521
      refine ⟨by decide, by decide, ?_⟩
      have h_2960 : Nat.sqrt (2960 + 521) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2960]; decide
    · -- n = 2961
      use 521
      refine ⟨by decide, by decide, ?_⟩
      have h_2961 : Nat.sqrt (2961 + 521) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2961]; decide
    · -- n = 2962
      use 521
      refine ⟨by decide, by decide, ?_⟩
      have h_2962 : Nat.sqrt (2962 + 521) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2962]; decide
    · -- n = 2963
      use 521
      refine ⟨by decide, by decide, ?_⟩
      have h_2963 : Nat.sqrt (2963 + 521) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2963]; decide
    · -- n = 2964
      use 521
      refine ⟨by decide, by decide, ?_⟩
      have h_2964 : Nat.sqrt (2964 + 521) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2964]; decide
    · -- n = 2965
      use 521
      refine ⟨by decide, by decide, ?_⟩
      have h_2965 : Nat.sqrt (2965 + 521) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2965]; decide
    · -- n = 2966
      use 521
      refine ⟨by decide, by decide, ?_⟩
      have h_2966 : Nat.sqrt (2966 + 521) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2966]; decide
    · -- n = 2967
      use 521
      refine ⟨by decide, by decide, ?_⟩
      have h_2967 : Nat.sqrt (2967 + 521) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2967]; decide
    · -- n = 2968
      use 521
      refine ⟨by decide, by decide, ?_⟩
      have h_2968 : Nat.sqrt (2968 + 521) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2968]; decide
    · -- n = 2969
      use 521
      refine ⟨by decide, by decide, ?_⟩
      have h_2969 : Nat.sqrt (2969 + 521) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2969]; decide
    · -- n = 2970
      use 521
      refine ⟨by decide, by decide, ?_⟩
      have h_2970 : Nat.sqrt (2970 + 521) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2970]; decide
    · -- n = 2971
      use 521
      refine ⟨by decide, by decide, ?_⟩
      have h_2971 : Nat.sqrt (2971 + 521) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2971]; decide
    · -- n = 2972
      use 509
      refine ⟨by decide, by decide, ?_⟩
      have h_2972 : Nat.sqrt (2972 + 509) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2972]; decide
    · -- n = 2973
      use 509
      refine ⟨by decide, by decide, ?_⟩
      have h_2973 : Nat.sqrt (2973 + 509) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2973]; decide
    · -- n = 2974
      use 509
      refine ⟨by decide, by decide, ?_⟩
      have h_2974 : Nat.sqrt (2974 + 509) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2974]; decide
    · -- n = 2975
      use 509
      refine ⟨by decide, by decide, ?_⟩
      have h_2975 : Nat.sqrt (2975 + 509) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2975]; decide
    · -- n = 2976
      use 509
      refine ⟨by decide, by decide, ?_⟩
      have h_2976 : Nat.sqrt (2976 + 509) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2976]; decide
    · -- n = 2977
      use 509
      refine ⟨by decide, by decide, ?_⟩
      have h_2977 : Nat.sqrt (2977 + 509) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2977]; decide
    · -- n = 2978
      use 503
      refine ⟨by decide, by decide, ?_⟩
      have h_2978 : Nat.sqrt (2978 + 503) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2978]; decide
    · -- n = 2979
      use 503
      refine ⟨by decide, by decide, ?_⟩
      have h_2979 : Nat.sqrt (2979 + 503) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2979]; decide
    · -- n = 2980
      use 503
      refine ⟨by decide, by decide, ?_⟩
      have h_2980 : Nat.sqrt (2980 + 503) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2980]; decide
    · -- n = 2981
      use 503
      refine ⟨by decide, by decide, ?_⟩
      have h_2981 : Nat.sqrt (2981 + 503) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2981]; decide
    · -- n = 2982
      use 499
      refine ⟨by decide, by decide, ?_⟩
      have h_2982 : Nat.sqrt (2982 + 499) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2982]; decide
    · -- n = 2983
      use 499
      refine ⟨by decide, by decide, ?_⟩
      have h_2983 : Nat.sqrt (2983 + 499) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2983]; decide
    · -- n = 2984
      use 499
      refine ⟨by decide, by decide, ?_⟩
      have h_2984 : Nat.sqrt (2984 + 499) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2984]; decide
    · -- n = 2985
      use 499
      refine ⟨by decide, by decide, ?_⟩
      have h_2985 : Nat.sqrt (2985 + 499) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2985]; decide
    · -- n = 2986
      use 499
      refine ⟨by decide, by decide, ?_⟩
      have h_2986 : Nat.sqrt (2986 + 499) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2986]; decide
    · -- n = 2987
      use 499
      refine ⟨by decide, by decide, ?_⟩
      have h_2987 : Nat.sqrt (2987 + 499) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2987]; decide
    · -- n = 2988
      use 499
      refine ⟨by decide, by decide, ?_⟩
      have h_2988 : Nat.sqrt (2988 + 499) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2988]; decide
    · -- n = 2989
      use 499
      refine ⟨by decide, by decide, ?_⟩
      have h_2989 : Nat.sqrt (2989 + 499) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2989]; decide
    · -- n = 2990
      use 491
      refine ⟨by decide, by decide, ?_⟩
      have h_2990 : Nat.sqrt (2990 + 491) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2990]; decide
    · -- n = 2991
      use 491
      refine ⟨by decide, by decide, ?_⟩
      have h_2991 : Nat.sqrt (2991 + 491) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2991]; decide
    · -- n = 2992
      use 491
      refine ⟨by decide, by decide, ?_⟩
      have h_2992 : Nat.sqrt (2992 + 491) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2992]; decide
    · -- n = 2993
      use 491
      refine ⟨by decide, by decide, ?_⟩
      have h_2993 : Nat.sqrt (2993 + 491) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2993]; decide
    · -- n = 2994
      use 487
      refine ⟨by decide, by decide, ?_⟩
      have h_2994 : Nat.sqrt (2994 + 487) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2994]; decide
    · -- n = 2995
      use 487
      refine ⟨by decide, by decide, ?_⟩
      have h_2995 : Nat.sqrt (2995 + 487) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2995]; decide
    · -- n = 2996
      use 487
      refine ⟨by decide, by decide, ?_⟩
      have h_2996 : Nat.sqrt (2996 + 487) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2996]; decide
    · -- n = 2997
      use 487
      refine ⟨by decide, by decide, ?_⟩
      have h_2997 : Nat.sqrt (2997 + 487) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2997]; decide
    · -- n = 2998
      use 487
      refine ⟨by decide, by decide, ?_⟩
      have h_2998 : Nat.sqrt (2998 + 487) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2998]; decide
    · -- n = 2999
      use 487
      refine ⟨by decide, by decide, ?_⟩
      have h_2999 : Nat.sqrt (2999 + 487) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_2999]; decide
    · -- n = 3000
      use 487
      refine ⟨by decide, by decide, ?_⟩
      have h_3000 : Nat.sqrt (3000 + 487) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3000]; decide
    · -- n = 3001
      use 487
      refine ⟨by decide, by decide, ?_⟩
      have h_3001 : Nat.sqrt (3001 + 487) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3001]; decide
    · -- n = 3002
      use 479
      refine ⟨by decide, by decide, ?_⟩
      have h_3002 : Nat.sqrt (3002 + 479) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3002]; decide
    · -- n = 3003
      use 479
      refine ⟨by decide, by decide, ?_⟩
      have h_3003 : Nat.sqrt (3003 + 479) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3003]; decide
    · -- n = 3004
      use 479
      refine ⟨by decide, by decide, ?_⟩
      have h_3004 : Nat.sqrt (3004 + 479) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3004]; decide
    · -- n = 3005
      use 479
      refine ⟨by decide, by decide, ?_⟩
      have h_3005 : Nat.sqrt (3005 + 479) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3005]; decide
    · -- n = 3006
      use 479
      refine ⟨by decide, by decide, ?_⟩
      have h_3006 : Nat.sqrt (3006 + 479) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3006]; decide
    · -- n = 3007
      use 479
      refine ⟨by decide, by decide, ?_⟩
      have h_3007 : Nat.sqrt (3007 + 479) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3007]; decide
    · -- n = 3008
      use 479
      refine ⟨by decide, by decide, ?_⟩
      have h_3008 : Nat.sqrt (3008 + 479) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3008]; decide
    · -- n = 3009
      use 479
      refine ⟨by decide, by decide, ?_⟩
      have h_3009 : Nat.sqrt (3009 + 479) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3009]; decide
    · -- n = 3010
      use 479
      refine ⟨by decide, by decide, ?_⟩
      have h_3010 : Nat.sqrt (3010 + 479) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3010]; decide
    · -- n = 3011
      use 479
      refine ⟨by decide, by decide, ?_⟩
      have h_3011 : Nat.sqrt (3011 + 479) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3011]; decide
    · -- n = 3012
      use 479
      refine ⟨by decide, by decide, ?_⟩
      have h_3012 : Nat.sqrt (3012 + 479) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3012]; decide
    · -- n = 3013
      use 479
      refine ⟨by decide, by decide, ?_⟩
      have h_3013 : Nat.sqrt (3013 + 479) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3013]; decide
    · -- n = 3014
      use 467
      refine ⟨by decide, by decide, ?_⟩
      have h_3014 : Nat.sqrt (3014 + 467) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3014]; decide
    · -- n = 3015
      use 467
      refine ⟨by decide, by decide, ?_⟩
      have h_3015 : Nat.sqrt (3015 + 467) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3015]; decide
    · -- n = 3016
      use 467
      refine ⟨by decide, by decide, ?_⟩
      have h_3016 : Nat.sqrt (3016 + 467) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3016]; decide
    · -- n = 3017
      use 467
      refine ⟨by decide, by decide, ?_⟩
      have h_3017 : Nat.sqrt (3017 + 467) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3017]; decide
    · -- n = 3018
      use 463
      refine ⟨by decide, by decide, ?_⟩
      have h_3018 : Nat.sqrt (3018 + 463) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3018]; decide
    · -- n = 3019
      use 463
      refine ⟨by decide, by decide, ?_⟩
      have h_3019 : Nat.sqrt (3019 + 463) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3019]; decide
    · -- n = 3020
      use 461
      refine ⟨by decide, by decide, ?_⟩
      have h_3020 : Nat.sqrt (3020 + 461) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3020]; decide
    · -- n = 3021
      use 461
      refine ⟨by decide, by decide, ?_⟩
      have h_3021 : Nat.sqrt (3021 + 461) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3021]; decide
    · -- n = 3022
      use 461
      refine ⟨by decide, by decide, ?_⟩
      have h_3022 : Nat.sqrt (3022 + 461) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3022]; decide
    · -- n = 3023
      use 461
      refine ⟨by decide, by decide, ?_⟩
      have h_3023 : Nat.sqrt (3023 + 461) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3023]; decide
    · -- n = 3024
      use 457
      refine ⟨by decide, by decide, ?_⟩
      have h_3024 : Nat.sqrt (3024 + 457) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3024]; decide
    · -- n = 3025
      use 457
      refine ⟨by decide, by decide, ?_⟩
      have h_3025 : Nat.sqrt (3025 + 457) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3025]; decide
    · -- n = 3026
      use 457
      refine ⟨by decide, by decide, ?_⟩
      have h_3026 : Nat.sqrt (3026 + 457) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3026]; decide
    · -- n = 3027
      use 457
      refine ⟨by decide, by decide, ?_⟩
      have h_3027 : Nat.sqrt (3027 + 457) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3027]; decide
    · -- n = 3028
      use 457
      refine ⟨by decide, by decide, ?_⟩
      have h_3028 : Nat.sqrt (3028 + 457) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3028]; decide
    · -- n = 3029
      use 457
      refine ⟨by decide, by decide, ?_⟩
      have h_3029 : Nat.sqrt (3029 + 457) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3029]; decide
    · -- n = 3030
      use 457
      refine ⟨by decide, by decide, ?_⟩
      have h_3030 : Nat.sqrt (3030 + 457) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3030]; decide
    · -- n = 3031
      use 457
      refine ⟨by decide, by decide, ?_⟩
      have h_3031 : Nat.sqrt (3031 + 457) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3031]; decide
    · -- n = 3032
      use 449
      refine ⟨by decide, by decide, ?_⟩
      have h_3032 : Nat.sqrt (3032 + 449) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3032]; decide
    · -- n = 3033
      use 449
      refine ⟨by decide, by decide, ?_⟩
      have h_3033 : Nat.sqrt (3033 + 449) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3033]; decide
    · -- n = 3034
      use 449
      refine ⟨by decide, by decide, ?_⟩
      have h_3034 : Nat.sqrt (3034 + 449) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3034]; decide
    · -- n = 3035
      use 449
      refine ⟨by decide, by decide, ?_⟩
      have h_3035 : Nat.sqrt (3035 + 449) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3035]; decide
    · -- n = 3036
      use 449
      refine ⟨by decide, by decide, ?_⟩
      have h_3036 : Nat.sqrt (3036 + 449) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3036]; decide
    · -- n = 3037
      use 449
      refine ⟨by decide, by decide, ?_⟩
      have h_3037 : Nat.sqrt (3037 + 449) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3037]; decide
    · -- n = 3038
      use 443
      refine ⟨by decide, by decide, ?_⟩
      have h_3038 : Nat.sqrt (3038 + 443) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3038]; decide
    · -- n = 3039
      use 443
      refine ⟨by decide, by decide, ?_⟩
      have h_3039 : Nat.sqrt (3039 + 443) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3039]; decide
    · -- n = 3040
      use 443
      refine ⟨by decide, by decide, ?_⟩
      have h_3040 : Nat.sqrt (3040 + 443) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3040]; decide
    · -- n = 3041
      use 443
      refine ⟨by decide, by decide, ?_⟩
      have h_3041 : Nat.sqrt (3041 + 443) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3041]; decide
    · -- n = 3042
      use 439
      refine ⟨by decide, by decide, ?_⟩
      have h_3042 : Nat.sqrt (3042 + 439) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3042]; decide
    · -- n = 3043
      use 439
      refine ⟨by decide, by decide, ?_⟩
      have h_3043 : Nat.sqrt (3043 + 439) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3043]; decide
    · -- n = 3044
      use 439
      refine ⟨by decide, by decide, ?_⟩
      have h_3044 : Nat.sqrt (3044 + 439) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3044]; decide
    · -- n = 3045
      use 439
      refine ⟨by decide, by decide, ?_⟩
      have h_3045 : Nat.sqrt (3045 + 439) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3045]; decide
    · -- n = 3046
      use 439
      refine ⟨by decide, by decide, ?_⟩
      have h_3046 : Nat.sqrt (3046 + 439) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3046]; decide
    · -- n = 3047
      use 439
      refine ⟨by decide, by decide, ?_⟩
      have h_3047 : Nat.sqrt (3047 + 439) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3047]; decide
    · -- n = 3048
      use 433
      refine ⟨by decide, by decide, ?_⟩
      have h_3048 : Nat.sqrt (3048 + 433) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3048]; decide
    · -- n = 3049
      use 433
      refine ⟨by decide, by decide, ?_⟩
      have h_3049 : Nat.sqrt (3049 + 433) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3049]; decide
    · -- n = 3050
      use 431
      refine ⟨by decide, by decide, ?_⟩
      have h_3050 : Nat.sqrt (3050 + 431) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3050]; decide
    · -- n = 3051
      use 431
      refine ⟨by decide, by decide, ?_⟩
      have h_3051 : Nat.sqrt (3051 + 431) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3051]; decide
    · -- n = 3052
      use 431
      refine ⟨by decide, by decide, ?_⟩
      have h_3052 : Nat.sqrt (3052 + 431) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3052]; decide
    · -- n = 3053
      use 431
      refine ⟨by decide, by decide, ?_⟩
      have h_3053 : Nat.sqrt (3053 + 431) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3053]; decide
    · -- n = 3054
      use 431
      refine ⟨by decide, by decide, ?_⟩
      have h_3054 : Nat.sqrt (3054 + 431) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3054]; decide
    · -- n = 3055
      use 431
      refine ⟨by decide, by decide, ?_⟩
      have h_3055 : Nat.sqrt (3055 + 431) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3055]; decide
    · -- n = 3056
      use 431
      refine ⟨by decide, by decide, ?_⟩
      have h_3056 : Nat.sqrt (3056 + 431) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3056]; decide
    · -- n = 3057
      use 431
      refine ⟨by decide, by decide, ?_⟩
      have h_3057 : Nat.sqrt (3057 + 431) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3057]; decide
    · -- n = 3058
      use 431
      refine ⟨by decide, by decide, ?_⟩
      have h_3058 : Nat.sqrt (3058 + 431) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3058]; decide
    · -- n = 3059
      use 431
      refine ⟨by decide, by decide, ?_⟩
      have h_3059 : Nat.sqrt (3059 + 431) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3059]; decide
    · -- n = 3060
      use 421
      refine ⟨by decide, by decide, ?_⟩
      have h_3060 : Nat.sqrt (3060 + 421) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3060]; decide
    · -- n = 3061
      use 421
      refine ⟨by decide, by decide, ?_⟩
      have h_3061 : Nat.sqrt (3061 + 421) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3061]; decide
    · -- n = 3062
      use 419
      refine ⟨by decide, by decide, ?_⟩
      have h_3062 : Nat.sqrt (3062 + 419) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3062]; decide
    · -- n = 3063
      use 419
      refine ⟨by decide, by decide, ?_⟩
      have h_3063 : Nat.sqrt (3063 + 419) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3063]; decide
    · -- n = 3064
      use 419
      refine ⟨by decide, by decide, ?_⟩
      have h_3064 : Nat.sqrt (3064 + 419) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3064]; decide
    · -- n = 3065
      use 419
      refine ⟨by decide, by decide, ?_⟩
      have h_3065 : Nat.sqrt (3065 + 419) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3065]; decide
    · -- n = 3066
      use 419
      refine ⟨by decide, by decide, ?_⟩
      have h_3066 : Nat.sqrt (3066 + 419) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3066]; decide
    · -- n = 3067
      use 419
      refine ⟨by decide, by decide, ?_⟩
      have h_3067 : Nat.sqrt (3067 + 419) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3067]; decide
    · -- n = 3068
      use 419
      refine ⟨by decide, by decide, ?_⟩
      have h_3068 : Nat.sqrt (3068 + 419) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3068]; decide
    · -- n = 3069
      use 419
      refine ⟨by decide, by decide, ?_⟩
      have h_3069 : Nat.sqrt (3069 + 419) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3069]; decide
    · -- n = 3070
      use 419
      refine ⟨by decide, by decide, ?_⟩
      have h_3070 : Nat.sqrt (3070 + 419) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3070]; decide
    · -- n = 3071
      use 419
      refine ⟨by decide, by decide, ?_⟩
      have h_3071 : Nat.sqrt (3071 + 419) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3071]; decide
    · -- n = 3072
      use 409
      refine ⟨by decide, by decide, ?_⟩
      have h_3072 : Nat.sqrt (3072 + 409) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3072]; decide
    · -- n = 3073
      use 409
      refine ⟨by decide, by decide, ?_⟩
      have h_3073 : Nat.sqrt (3073 + 409) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3073]; decide
    · -- n = 3074
      use 409
      refine ⟨by decide, by decide, ?_⟩
      have h_3074 : Nat.sqrt (3074 + 409) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3074]; decide
    · -- n = 3075
      use 409
      refine ⟨by decide, by decide, ?_⟩
      have h_3075 : Nat.sqrt (3075 + 409) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3075]; decide
    · -- n = 3076
      use 409
      refine ⟨by decide, by decide, ?_⟩
      have h_3076 : Nat.sqrt (3076 + 409) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3076]; decide
    · -- n = 3077
      use 409
      refine ⟨by decide, by decide, ?_⟩
      have h_3077 : Nat.sqrt (3077 + 409) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3077]; decide
    · -- n = 3078
      use 409
      refine ⟨by decide, by decide, ?_⟩
      have h_3078 : Nat.sqrt (3078 + 409) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3078]; decide
    · -- n = 3079
      use 409
      refine ⟨by decide, by decide, ?_⟩
      have h_3079 : Nat.sqrt (3079 + 409) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3079]; decide
    · -- n = 3080
      use 401
      refine ⟨by decide, by decide, ?_⟩
      have h_3080 : Nat.sqrt (3080 + 401) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3080]; decide
    · -- n = 3081
      use 401
      refine ⟨by decide, by decide, ?_⟩
      have h_3081 : Nat.sqrt (3081 + 401) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3081]; decide
    · -- n = 3082
      use 401
      refine ⟨by decide, by decide, ?_⟩
      have h_3082 : Nat.sqrt (3082 + 401) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3082]; decide
    · -- n = 3083
      use 401
      refine ⟨by decide, by decide, ?_⟩
      have h_3083 : Nat.sqrt (3083 + 401) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3083]; decide
    · -- n = 3084
      use 397
      refine ⟨by decide, by decide, ?_⟩
      have h_3084 : Nat.sqrt (3084 + 397) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3084]; decide
    · -- n = 3085
      use 397
      refine ⟨by decide, by decide, ?_⟩
      have h_3085 : Nat.sqrt (3085 + 397) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3085]; decide
    · -- n = 3086
      use 397
      refine ⟨by decide, by decide, ?_⟩
      have h_3086 : Nat.sqrt (3086 + 397) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3086]; decide
    · -- n = 3087
      use 397
      refine ⟨by decide, by decide, ?_⟩
      have h_3087 : Nat.sqrt (3087 + 397) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3087]; decide
    · -- n = 3088
      use 397
      refine ⟨by decide, by decide, ?_⟩
      have h_3088 : Nat.sqrt (3088 + 397) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3088]; decide
    · -- n = 3089
      use 397
      refine ⟨by decide, by decide, ?_⟩
      have h_3089 : Nat.sqrt (3089 + 397) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3089]; decide
    · -- n = 3090
      use 397
      refine ⟨by decide, by decide, ?_⟩
      have h_3090 : Nat.sqrt (3090 + 397) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3090]; decide
    · -- n = 3091
      use 397
      refine ⟨by decide, by decide, ?_⟩
      have h_3091 : Nat.sqrt (3091 + 397) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3091]; decide
    · -- n = 3092
      use 389
      refine ⟨by decide, by decide, ?_⟩
      have h_3092 : Nat.sqrt (3092 + 389) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3092]; decide
    · -- n = 3093
      use 389
      refine ⟨by decide, by decide, ?_⟩
      have h_3093 : Nat.sqrt (3093 + 389) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3093]; decide
    · -- n = 3094
      use 389
      refine ⟨by decide, by decide, ?_⟩
      have h_3094 : Nat.sqrt (3094 + 389) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3094]; decide
    · -- n = 3095
      use 389
      refine ⟨by decide, by decide, ?_⟩
      have h_3095 : Nat.sqrt (3095 + 389) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3095]; decide
    · -- n = 3096
      use 389
      refine ⟨by decide, by decide, ?_⟩
      have h_3096 : Nat.sqrt (3096 + 389) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3096]; decide
    · -- n = 3097
      use 389
      refine ⟨by decide, by decide, ?_⟩
      have h_3097 : Nat.sqrt (3097 + 389) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3097]; decide
    · -- n = 3098
      use 383
      refine ⟨by decide, by decide, ?_⟩
      have h_3098 : Nat.sqrt (3098 + 383) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3098]; decide
    · -- n = 3099
      use 383
      refine ⟨by decide, by decide, ?_⟩
      have h_3099 : Nat.sqrt (3099 + 383) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3099]; decide
    · -- n = 3100
      use 383
      refine ⟨by decide, by decide, ?_⟩
      have h_3100 : Nat.sqrt (3100 + 383) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3100]; decide
    · -- n = 3101
      use 383
      refine ⟨by decide, by decide, ?_⟩
      have h_3101 : Nat.sqrt (3101 + 383) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3101]; decide
    · -- n = 3102
      use 379
      refine ⟨by decide, by decide, ?_⟩
      have h_3102 : Nat.sqrt (3102 + 379) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3102]; decide
    · -- n = 3103
      use 379
      refine ⟨by decide, by decide, ?_⟩
      have h_3103 : Nat.sqrt (3103 + 379) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3103]; decide
    · -- n = 3104
      use 379
      refine ⟨by decide, by decide, ?_⟩
      have h_3104 : Nat.sqrt (3104 + 379) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3104]; decide
    · -- n = 3105
      use 379
      refine ⟨by decide, by decide, ?_⟩
      have h_3105 : Nat.sqrt (3105 + 379) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3105]; decide
    · -- n = 3106
      use 379
      refine ⟨by decide, by decide, ?_⟩
      have h_3106 : Nat.sqrt (3106 + 379) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3106]; decide
    · -- n = 3107
      use 379
      refine ⟨by decide, by decide, ?_⟩
      have h_3107 : Nat.sqrt (3107 + 379) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3107]; decide
    · -- n = 3108
      use 373
      refine ⟨by decide, by decide, ?_⟩
      have h_3108 : Nat.sqrt (3108 + 373) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3108]; decide
    · -- n = 3109
      use 373
      refine ⟨by decide, by decide, ?_⟩
      have h_3109 : Nat.sqrt (3109 + 373) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3109]; decide
    · -- n = 3110
      use 373
      refine ⟨by decide, by decide, ?_⟩
      have h_3110 : Nat.sqrt (3110 + 373) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3110]; decide
    · -- n = 3111
      use 373
      refine ⟨by decide, by decide, ?_⟩
      have h_3111 : Nat.sqrt (3111 + 373) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3111]; decide
    · -- n = 3112
      use 373
      refine ⟨by decide, by decide, ?_⟩
      have h_3112 : Nat.sqrt (3112 + 373) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3112]; decide
    · -- n = 3113
      use 373
      refine ⟨by decide, by decide, ?_⟩
      have h_3113 : Nat.sqrt (3113 + 373) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3113]; decide
    · -- n = 3114
      use 367
      refine ⟨by decide, by decide, ?_⟩
      have h_3114 : Nat.sqrt (3114 + 367) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3114]; decide
    · -- n = 3115
      use 367
      refine ⟨by decide, by decide, ?_⟩
      have h_3115 : Nat.sqrt (3115 + 367) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3115]; decide
    · -- n = 3116
      use 367
      refine ⟨by decide, by decide, ?_⟩
      have h_3116 : Nat.sqrt (3116 + 367) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3116]; decide
    · -- n = 3117
      use 367
      refine ⟨by decide, by decide, ?_⟩
      have h_3117 : Nat.sqrt (3117 + 367) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3117]; decide
    · -- n = 3118
      use 367
      refine ⟨by decide, by decide, ?_⟩
      have h_3118 : Nat.sqrt (3118 + 367) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3118]; decide
    · -- n = 3119
      use 367
      refine ⟨by decide, by decide, ?_⟩
      have h_3119 : Nat.sqrt (3119 + 367) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3119]; decide
    · -- n = 3120
      use 367
      refine ⟨by decide, by decide, ?_⟩
      have h_3120 : Nat.sqrt (3120 + 367) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3120]; decide
    · -- n = 3121
      use 367
      refine ⟨by decide, by decide, ?_⟩
      have h_3121 : Nat.sqrt (3121 + 367) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3121]; decide
    · -- n = 3122
      use 359
      refine ⟨by decide, by decide, ?_⟩
      have h_3122 : Nat.sqrt (3122 + 359) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3122]; decide
    · -- n = 3123
      use 359
      refine ⟨by decide, by decide, ?_⟩
      have h_3123 : Nat.sqrt (3123 + 359) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3123]; decide
    · -- n = 3124
      use 359
      refine ⟨by decide, by decide, ?_⟩
      have h_3124 : Nat.sqrt (3124 + 359) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3124]; decide
    · -- n = 3125
      use 359
      refine ⟨by decide, by decide, ?_⟩
      have h_3125 : Nat.sqrt (3125 + 359) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3125]; decide
    · -- n = 3126
      use 359
      refine ⟨by decide, by decide, ?_⟩
      have h_3126 : Nat.sqrt (3126 + 359) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3126]; decide
    · -- n = 3127
      use 359
      refine ⟨by decide, by decide, ?_⟩
      have h_3127 : Nat.sqrt (3127 + 359) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3127]; decide
    · -- n = 3128
      use 353
      refine ⟨by decide, by decide, ?_⟩
      have h_3128 : Nat.sqrt (3128 + 353) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3128]; decide
    · -- n = 3129
      use 353
      refine ⟨by decide, by decide, ?_⟩
      have h_3129 : Nat.sqrt (3129 + 353) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3129]; decide
    · -- n = 3130
      use 353
      refine ⟨by decide, by decide, ?_⟩
      have h_3130 : Nat.sqrt (3130 + 353) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3130]; decide
    · -- n = 3131
      use 353
      refine ⟨by decide, by decide, ?_⟩
      have h_3131 : Nat.sqrt (3131 + 353) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3131]; decide
    · -- n = 3132
      use 349
      refine ⟨by decide, by decide, ?_⟩
      have h_3132 : Nat.sqrt (3132 + 349) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3132]; decide
    · -- n = 3133
      use 349
      refine ⟨by decide, by decide, ?_⟩
      have h_3133 : Nat.sqrt (3133 + 349) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3133]; decide
    · -- n = 3134
      use 347
      refine ⟨by decide, by decide, ?_⟩
      have h_3134 : Nat.sqrt (3134 + 347) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3134]; decide
    · -- n = 3135
      use 347
      refine ⟨by decide, by decide, ?_⟩
      have h_3135 : Nat.sqrt (3135 + 347) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3135]; decide
    · -- n = 3136
      use 347
      refine ⟨by decide, by decide, ?_⟩
      have h_3136 : Nat.sqrt (3136 + 347) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3136]; decide
    · -- n = 3137
      use 347
      refine ⟨by decide, by decide, ?_⟩
      have h_3137 : Nat.sqrt (3137 + 347) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3137]; decide
    · -- n = 3138
      use 347
      refine ⟨by decide, by decide, ?_⟩
      have h_3138 : Nat.sqrt (3138 + 347) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3138]; decide
    · -- n = 3139
      use 347
      refine ⟨by decide, by decide, ?_⟩
      have h_3139 : Nat.sqrt (3139 + 347) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3139]; decide
    · -- n = 3140
      use 347
      refine ⟨by decide, by decide, ?_⟩
      have h_3140 : Nat.sqrt (3140 + 347) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3140]; decide
    · -- n = 3141
      use 347
      refine ⟨by decide, by decide, ?_⟩
      have h_3141 : Nat.sqrt (3141 + 347) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3141]; decide
    · -- n = 3142
      use 347
      refine ⟨by decide, by decide, ?_⟩
      have h_3142 : Nat.sqrt (3142 + 347) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3142]; decide
    · -- n = 3143
      use 347
      refine ⟨by decide, by decide, ?_⟩
      have h_3143 : Nat.sqrt (3143 + 347) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3143]; decide
    · -- n = 3144
      use 337
      refine ⟨by decide, by decide, ?_⟩
      have h_3144 : Nat.sqrt (3144 + 337) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3144]; decide
    · -- n = 3145
      use 337
      refine ⟨by decide, by decide, ?_⟩
      have h_3145 : Nat.sqrt (3145 + 337) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3145]; decide
    · -- n = 3146
      use 337
      refine ⟨by decide, by decide, ?_⟩
      have h_3146 : Nat.sqrt (3146 + 337) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3146]; decide
    · -- n = 3147
      use 337
      refine ⟨by decide, by decide, ?_⟩
      have h_3147 : Nat.sqrt (3147 + 337) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3147]; decide
    · -- n = 3148
      use 337
      refine ⟨by decide, by decide, ?_⟩
      have h_3148 : Nat.sqrt (3148 + 337) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3148]; decide
    · -- n = 3149
      use 337
      refine ⟨by decide, by decide, ?_⟩
      have h_3149 : Nat.sqrt (3149 + 337) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3149]; decide
    · -- n = 3150
      use 331
      refine ⟨by decide, by decide, ?_⟩
      have h_3150 : Nat.sqrt (3150 + 331) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3150]; decide
    · -- n = 3151
      use 331
      refine ⟨by decide, by decide, ?_⟩
      have h_3151 : Nat.sqrt (3151 + 331) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3151]; decide
    · -- n = 3152
      use 331
      refine ⟨by decide, by decide, ?_⟩
      have h_3152 : Nat.sqrt (3152 + 331) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3152]; decide
    · -- n = 3153
      use 331
      refine ⟨by decide, by decide, ?_⟩
      have h_3153 : Nat.sqrt (3153 + 331) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3153]; decide
    · -- n = 3154
      use 331
      refine ⟨by decide, by decide, ?_⟩
      have h_3154 : Nat.sqrt (3154 + 331) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3154]; decide
    · -- n = 3155
      use 331
      refine ⟨by decide, by decide, ?_⟩
      have h_3155 : Nat.sqrt (3155 + 331) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3155]; decide
    · -- n = 3156
      use 331
      refine ⟨by decide, by decide, ?_⟩
      have h_3156 : Nat.sqrt (3156 + 331) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3156]; decide
    · -- n = 3157
      use 331
      refine ⟨by decide, by decide, ?_⟩
      have h_3157 : Nat.sqrt (3157 + 331) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3157]; decide
    · -- n = 3158
      use 331
      refine ⟨by decide, by decide, ?_⟩
      have h_3158 : Nat.sqrt (3158 + 331) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3158]; decide
    · -- n = 3159
      use 331
      refine ⟨by decide, by decide, ?_⟩
      have h_3159 : Nat.sqrt (3159 + 331) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3159]; decide
    · -- n = 3160
      use 331
      refine ⟨by decide, by decide, ?_⟩
      have h_3160 : Nat.sqrt (3160 + 331) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3160]; decide
    · -- n = 3161
      use 331
      refine ⟨by decide, by decide, ?_⟩
      have h_3161 : Nat.sqrt (3161 + 331) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3161]; decide
    · -- n = 3162
      use 331
      refine ⟨by decide, by decide, ?_⟩
      have h_3162 : Nat.sqrt (3162 + 331) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3162]; decide
    · -- n = 3163
      use 331
      refine ⟨by decide, by decide, ?_⟩
      have h_3163 : Nat.sqrt (3163 + 331) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3163]; decide
    · -- n = 3164
      use 317
      refine ⟨by decide, by decide, ?_⟩
      have h_3164 : Nat.sqrt (3164 + 317) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3164]; decide
    · -- n = 3165
      use 317
      refine ⟨by decide, by decide, ?_⟩
      have h_3165 : Nat.sqrt (3165 + 317) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3165]; decide
    · -- n = 3166
      use 317
      refine ⟨by decide, by decide, ?_⟩
      have h_3166 : Nat.sqrt (3166 + 317) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3166]; decide
    · -- n = 3167
      use 317
      refine ⟨by decide, by decide, ?_⟩
      have h_3167 : Nat.sqrt (3167 + 317) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3167]; decide
    · -- n = 3168
      use 313
      refine ⟨by decide, by decide, ?_⟩
      have h_3168 : Nat.sqrt (3168 + 313) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3168]; decide
    · -- n = 3169
      use 313
      refine ⟨by decide, by decide, ?_⟩
      have h_3169 : Nat.sqrt (3169 + 313) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3169]; decide
    · -- n = 3170
      use 311
      refine ⟨by decide, by decide, ?_⟩
      have h_3170 : Nat.sqrt (3170 + 311) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3170]; decide
    · -- n = 3171
      use 311
      refine ⟨by decide, by decide, ?_⟩
      have h_3171 : Nat.sqrt (3171 + 311) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3171]; decide
    · -- n = 3172
      use 311
      refine ⟨by decide, by decide, ?_⟩
      have h_3172 : Nat.sqrt (3172 + 311) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3172]; decide
    · -- n = 3173
      use 311
      refine ⟨by decide, by decide, ?_⟩
      have h_3173 : Nat.sqrt (3173 + 311) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3173]; decide
    · -- n = 3174
      use 307
      refine ⟨by decide, by decide, ?_⟩
      have h_3174 : Nat.sqrt (3174 + 307) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3174]; decide
    · -- n = 3175
      use 307
      refine ⟨by decide, by decide, ?_⟩
      have h_3175 : Nat.sqrt (3175 + 307) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3175]; decide
    · -- n = 3176
      use 307
      refine ⟨by decide, by decide, ?_⟩
      have h_3176 : Nat.sqrt (3176 + 307) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3176]; decide
    · -- n = 3177
      use 307
      refine ⟨by decide, by decide, ?_⟩
      have h_3177 : Nat.sqrt (3177 + 307) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3177]; decide
    · -- n = 3178
      use 307
      refine ⟨by decide, by decide, ?_⟩
      have h_3178 : Nat.sqrt (3178 + 307) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3178]; decide
    · -- n = 3179
      use 307
      refine ⟨by decide, by decide, ?_⟩
      have h_3179 : Nat.sqrt (3179 + 307) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3179]; decide
    · -- n = 3180
      use 307
      refine ⟨by decide, by decide, ?_⟩
      have h_3180 : Nat.sqrt (3180 + 307) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3180]; decide
    · -- n = 3181
      use 307
      refine ⟨by decide, by decide, ?_⟩
      have h_3181 : Nat.sqrt (3181 + 307) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3181]; decide
    · -- n = 3182
      use 307
      refine ⟨by decide, by decide, ?_⟩
      have h_3182 : Nat.sqrt (3182 + 307) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3182]; decide
    · -- n = 3183
      use 307
      refine ⟨by decide, by decide, ?_⟩
      have h_3183 : Nat.sqrt (3183 + 307) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3183]; decide
    · -- n = 3184
      use 307
      refine ⟨by decide, by decide, ?_⟩
      have h_3184 : Nat.sqrt (3184 + 307) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3184]; decide
    · -- n = 3185
      use 307
      refine ⟨by decide, by decide, ?_⟩
      have h_3185 : Nat.sqrt (3185 + 307) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3185]; decide
    · -- n = 3186
      use 307
      refine ⟨by decide, by decide, ?_⟩
      have h_3186 : Nat.sqrt (3186 + 307) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3186]; decide
    · -- n = 3187
      use 307
      refine ⟨by decide, by decide, ?_⟩
      have h_3187 : Nat.sqrt (3187 + 307) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3187]; decide
    · -- n = 3188
      use 293
      refine ⟨by decide, by decide, ?_⟩
      have h_3188 : Nat.sqrt (3188 + 293) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3188]; decide
    · -- n = 3189
      use 293
      refine ⟨by decide, by decide, ?_⟩
      have h_3189 : Nat.sqrt (3189 + 293) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3189]; decide
    · -- n = 3190
      use 293
      refine ⟨by decide, by decide, ?_⟩
      have h_3190 : Nat.sqrt (3190 + 293) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3190]; decide
    · -- n = 3191
      use 293
      refine ⟨by decide, by decide, ?_⟩
      have h_3191 : Nat.sqrt (3191 + 293) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3191]; decide
    · -- n = 3192
      use 293
      refine ⟨by decide, by decide, ?_⟩
      have h_3192 : Nat.sqrt (3192 + 293) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3192]; decide
    · -- n = 3193
      use 293
      refine ⟨by decide, by decide, ?_⟩
      have h_3193 : Nat.sqrt (3193 + 293) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3193]; decide
    · -- n = 3194
      use 293
      refine ⟨by decide, by decide, ?_⟩
      have h_3194 : Nat.sqrt (3194 + 293) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3194]; decide
    · -- n = 3195
      use 293
      refine ⟨by decide, by decide, ?_⟩
      have h_3195 : Nat.sqrt (3195 + 293) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3195]; decide
    · -- n = 3196
      use 293
      refine ⟨by decide, by decide, ?_⟩
      have h_3196 : Nat.sqrt (3196 + 293) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3196]; decide
    · -- n = 3197
      use 293
      refine ⟨by decide, by decide, ?_⟩
      have h_3197 : Nat.sqrt (3197 + 293) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3197]; decide
    · -- n = 3198
      use 283
      refine ⟨by decide, by decide, ?_⟩
      have h_3198 : Nat.sqrt (3198 + 283) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3198]; decide
    · -- n = 3199
      use 283
      refine ⟨by decide, by decide, ?_⟩
      have h_3199 : Nat.sqrt (3199 + 283) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3199]; decide
    · -- n = 3200
      use 281
      refine ⟨by decide, by decide, ?_⟩
      have h_3200 : Nat.sqrt (3200 + 281) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3200]; decide
    · -- n = 3201
      use 281
      refine ⟨by decide, by decide, ?_⟩
      have h_3201 : Nat.sqrt (3201 + 281) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3201]; decide
    · -- n = 3202
      use 281
      refine ⟨by decide, by decide, ?_⟩
      have h_3202 : Nat.sqrt (3202 + 281) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3202]; decide
    · -- n = 3203
      use 281
      refine ⟨by decide, by decide, ?_⟩
      have h_3203 : Nat.sqrt (3203 + 281) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3203]; decide
    · -- n = 3204
      use 277
      refine ⟨by decide, by decide, ?_⟩
      have h_3204 : Nat.sqrt (3204 + 277) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3204]; decide
    · -- n = 3205
      use 277
      refine ⟨by decide, by decide, ?_⟩
      have h_3205 : Nat.sqrt (3205 + 277) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3205]; decide
    · -- n = 3206
      use 277
      refine ⟨by decide, by decide, ?_⟩
      have h_3206 : Nat.sqrt (3206 + 277) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3206]; decide
    · -- n = 3207
      use 277
      refine ⟨by decide, by decide, ?_⟩
      have h_3207 : Nat.sqrt (3207 + 277) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3207]; decide
    · -- n = 3208
      use 277
      refine ⟨by decide, by decide, ?_⟩
      have h_3208 : Nat.sqrt (3208 + 277) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3208]; decide
    · -- n = 3209
      use 277
      refine ⟨by decide, by decide, ?_⟩
      have h_3209 : Nat.sqrt (3209 + 277) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3209]; decide
    · -- n = 3210
      use 271
      refine ⟨by decide, by decide, ?_⟩
      have h_3210 : Nat.sqrt (3210 + 271) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3210]; decide
    · -- n = 3211
      use 271
      refine ⟨by decide, by decide, ?_⟩
      have h_3211 : Nat.sqrt (3211 + 271) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3211]; decide
    · -- n = 3212
      use 269
      refine ⟨by decide, by decide, ?_⟩
      have h_3212 : Nat.sqrt (3212 + 269) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3212]; decide
    · -- n = 3213
      use 269
      refine ⟨by decide, by decide, ?_⟩
      have h_3213 : Nat.sqrt (3213 + 269) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3213]; decide
    · -- n = 3214
      use 269
      refine ⟨by decide, by decide, ?_⟩
      have h_3214 : Nat.sqrt (3214 + 269) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3214]; decide
    · -- n = 3215
      use 269
      refine ⟨by decide, by decide, ?_⟩
      have h_3215 : Nat.sqrt (3215 + 269) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3215]; decide
    · -- n = 3216
      use 269
      refine ⟨by decide, by decide, ?_⟩
      have h_3216 : Nat.sqrt (3216 + 269) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3216]; decide
    · -- n = 3217
      use 269
      refine ⟨by decide, by decide, ?_⟩
      have h_3217 : Nat.sqrt (3217 + 269) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3217]; decide
    · -- n = 3218
      use 263
      refine ⟨by decide, by decide, ?_⟩
      have h_3218 : Nat.sqrt (3218 + 263) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3218]; decide
    · -- n = 3219
      use 263
      refine ⟨by decide, by decide, ?_⟩
      have h_3219 : Nat.sqrt (3219 + 263) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3219]; decide
    · -- n = 3220
      use 263
      refine ⟨by decide, by decide, ?_⟩
      have h_3220 : Nat.sqrt (3220 + 263) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3220]; decide
    · -- n = 3221
      use 263
      refine ⟨by decide, by decide, ?_⟩
      have h_3221 : Nat.sqrt (3221 + 263) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3221]; decide
    · -- n = 3222
      use 263
      refine ⟨by decide, by decide, ?_⟩
      have h_3222 : Nat.sqrt (3222 + 263) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3222]; decide
    · -- n = 3223
      use 263
      refine ⟨by decide, by decide, ?_⟩
      have h_3223 : Nat.sqrt (3223 + 263) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3223]; decide
    · -- n = 3224
      use 257
      refine ⟨by decide, by decide, ?_⟩
      have h_3224 : Nat.sqrt (3224 + 257) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3224]; decide
    · -- n = 3225
      use 257
      refine ⟨by decide, by decide, ?_⟩
      have h_3225 : Nat.sqrt (3225 + 257) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3225]; decide
    · -- n = 3226
      use 257
      refine ⟨by decide, by decide, ?_⟩
      have h_3226 : Nat.sqrt (3226 + 257) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3226]; decide
    · -- n = 3227
      use 257
      refine ⟨by decide, by decide, ?_⟩
      have h_3227 : Nat.sqrt (3227 + 257) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3227]; decide
    · -- n = 3228
      use 257
      refine ⟨by decide, by decide, ?_⟩
      have h_3228 : Nat.sqrt (3228 + 257) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3228]; decide
    · -- n = 3229
      use 257
      refine ⟨by decide, by decide, ?_⟩
      have h_3229 : Nat.sqrt (3229 + 257) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3229]; decide
    · -- n = 3230
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_3230 : Nat.sqrt (3230 + 251) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3230]; decide
    · -- n = 3231
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_3231 : Nat.sqrt (3231 + 251) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3231]; decide
    · -- n = 3232
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_3232 : Nat.sqrt (3232 + 251) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3232]; decide
    · -- n = 3233
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_3233 : Nat.sqrt (3233 + 251) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3233]; decide
    · -- n = 3234
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_3234 : Nat.sqrt (3234 + 251) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3234]; decide
    · -- n = 3235
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_3235 : Nat.sqrt (3235 + 251) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3235]; decide
    · -- n = 3236
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_3236 : Nat.sqrt (3236 + 251) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3236]; decide
    · -- n = 3237
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_3237 : Nat.sqrt (3237 + 251) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3237]; decide
    · -- n = 3238
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_3238 : Nat.sqrt (3238 + 251) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3238]; decide
    · -- n = 3239
      use 251
      refine ⟨by decide, by decide, ?_⟩
      have h_3239 : Nat.sqrt (3239 + 251) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3239]; decide
    · -- n = 3240
      use 241
      refine ⟨by decide, by decide, ?_⟩
      have h_3240 : Nat.sqrt (3240 + 241) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3240]; decide
    · -- n = 3241
      use 241
      refine ⟨by decide, by decide, ?_⟩
      have h_3241 : Nat.sqrt (3241 + 241) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3241]; decide
    · -- n = 3242
      use 239
      refine ⟨by decide, by decide, ?_⟩
      have h_3242 : Nat.sqrt (3242 + 239) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3242]; decide
    · -- n = 3243
      use 239
      refine ⟨by decide, by decide, ?_⟩
      have h_3243 : Nat.sqrt (3243 + 239) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3243]; decide
    · -- n = 3244
      use 239
      refine ⟨by decide, by decide, ?_⟩
      have h_3244 : Nat.sqrt (3244 + 239) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3244]; decide
    · -- n = 3245
      use 239
      refine ⟨by decide, by decide, ?_⟩
      have h_3245 : Nat.sqrt (3245 + 239) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3245]; decide
    · -- n = 3246
      use 239
      refine ⟨by decide, by decide, ?_⟩
      have h_3246 : Nat.sqrt (3246 + 239) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3246]; decide
    · -- n = 3247
      use 239
      refine ⟨by decide, by decide, ?_⟩
      have h_3247 : Nat.sqrt (3247 + 239) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3247]; decide
    · -- n = 3248
      use 233
      refine ⟨by decide, by decide, ?_⟩
      have h_3248 : Nat.sqrt (3248 + 233) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3248]; decide
    · -- n = 3249
      use 233
      refine ⟨by decide, by decide, ?_⟩
      have h_3249 : Nat.sqrt (3249 + 233) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3249]; decide
    · -- n = 3250
      use 233
      refine ⟨by decide, by decide, ?_⟩
      have h_3250 : Nat.sqrt (3250 + 233) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3250]; decide
    · -- n = 3251
      use 233
      refine ⟨by decide, by decide, ?_⟩
      have h_3251 : Nat.sqrt (3251 + 233) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3251]; decide
    · -- n = 3252
      use 229
      refine ⟨by decide, by decide, ?_⟩
      have h_3252 : Nat.sqrt (3252 + 229) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3252]; decide
    · -- n = 3253
      use 229
      refine ⟨by decide, by decide, ?_⟩
      have h_3253 : Nat.sqrt (3253 + 229) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3253]; decide
    · -- n = 3254
      use 227
      refine ⟨by decide, by decide, ?_⟩
      have h_3254 : Nat.sqrt (3254 + 227) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3254]; decide
    · -- n = 3255
      use 227
      refine ⟨by decide, by decide, ?_⟩
      have h_3255 : Nat.sqrt (3255 + 227) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3255]; decide
    · -- n = 3256
      use 227
      refine ⟨by decide, by decide, ?_⟩
      have h_3256 : Nat.sqrt (3256 + 227) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3256]; decide
    · -- n = 3257
      use 227
      refine ⟨by decide, by decide, ?_⟩
      have h_3257 : Nat.sqrt (3257 + 227) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3257]; decide
    · -- n = 3258
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_3258 : Nat.sqrt (3258 + 223) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3258]; decide
    · -- n = 3259
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_3259 : Nat.sqrt (3259 + 223) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3259]; decide
    · -- n = 3260
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_3260 : Nat.sqrt (3260 + 223) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3260]; decide
    · -- n = 3261
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_3261 : Nat.sqrt (3261 + 223) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3261]; decide
    · -- n = 3262
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_3262 : Nat.sqrt (3262 + 223) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3262]; decide
    · -- n = 3263
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_3263 : Nat.sqrt (3263 + 223) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3263]; decide
    · -- n = 3264
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_3264 : Nat.sqrt (3264 + 223) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3264]; decide
    · -- n = 3265
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_3265 : Nat.sqrt (3265 + 223) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3265]; decide
    · -- n = 3266
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_3266 : Nat.sqrt (3266 + 223) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3266]; decide
    · -- n = 3267
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_3267 : Nat.sqrt (3267 + 223) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3267]; decide
    · -- n = 3268
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_3268 : Nat.sqrt (3268 + 223) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3268]; decide
    · -- n = 3269
      use 223
      refine ⟨by decide, by decide, ?_⟩
      have h_3269 : Nat.sqrt (3269 + 223) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3269]; decide
    · -- n = 3270
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_3270 : Nat.sqrt (3270 + 211) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3270]; decide
    · -- n = 3271
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_3271 : Nat.sqrt (3271 + 211) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3271]; decide
    · -- n = 3272
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_3272 : Nat.sqrt (3272 + 211) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3272]; decide
    · -- n = 3273
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_3273 : Nat.sqrt (3273 + 211) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3273]; decide
    · -- n = 3274
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_3274 : Nat.sqrt (3274 + 211) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3274]; decide
    · -- n = 3275
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_3275 : Nat.sqrt (3275 + 211) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3275]; decide
    · -- n = 3276
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_3276 : Nat.sqrt (3276 + 211) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3276]; decide
    · -- n = 3277
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_3277 : Nat.sqrt (3277 + 211) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3277]; decide
    · -- n = 3278
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_3278 : Nat.sqrt (3278 + 211) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3278]; decide
    · -- n = 3279
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_3279 : Nat.sqrt (3279 + 211) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3279]; decide
    · -- n = 3280
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_3280 : Nat.sqrt (3280 + 211) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3280]; decide
    · -- n = 3281
      use 211
      refine ⟨by decide, by decide, ?_⟩
      have h_3281 : Nat.sqrt (3281 + 211) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3281]; decide
    · -- n = 3282
      use 199
      refine ⟨by decide, by decide, ?_⟩
      have h_3282 : Nat.sqrt (3282 + 199) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3282]; decide
    · -- n = 3283
      use 199
      refine ⟨by decide, by decide, ?_⟩
      have h_3283 : Nat.sqrt (3283 + 199) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3283]; decide
    · -- n = 3284
      use 197
      refine ⟨by decide, by decide, ?_⟩
      have h_3284 : Nat.sqrt (3284 + 197) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3284]; decide
    · -- n = 3285
      use 197
      refine ⟨by decide, by decide, ?_⟩
      have h_3285 : Nat.sqrt (3285 + 197) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3285]; decide
    · -- n = 3286
      use 197
      refine ⟨by decide, by decide, ?_⟩
      have h_3286 : Nat.sqrt (3286 + 197) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3286]; decide
    · -- n = 3287
      use 197
      refine ⟨by decide, by decide, ?_⟩
      have h_3287 : Nat.sqrt (3287 + 197) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3287]; decide
    · -- n = 3288
      use 193
      refine ⟨by decide, by decide, ?_⟩
      have h_3288 : Nat.sqrt (3288 + 193) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3288]; decide
    · -- n = 3289
      use 193
      refine ⟨by decide, by decide, ?_⟩
      have h_3289 : Nat.sqrt (3289 + 193) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3289]; decide
    · -- n = 3290
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_3290 : Nat.sqrt (3290 + 191) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3290]; decide
    · -- n = 3291
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_3291 : Nat.sqrt (3291 + 191) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3291]; decide
    · -- n = 3292
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_3292 : Nat.sqrt (3292 + 191) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3292]; decide
    · -- n = 3293
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_3293 : Nat.sqrt (3293 + 191) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3293]; decide
    · -- n = 3294
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_3294 : Nat.sqrt (3294 + 191) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3294]; decide
    · -- n = 3295
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_3295 : Nat.sqrt (3295 + 191) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3295]; decide
    · -- n = 3296
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_3296 : Nat.sqrt (3296 + 191) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3296]; decide
    · -- n = 3297
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_3297 : Nat.sqrt (3297 + 191) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3297]; decide
    · -- n = 3298
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_3298 : Nat.sqrt (3298 + 191) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3298]; decide
    · -- n = 3299
      use 191
      refine ⟨by decide, by decide, ?_⟩
      have h_3299 : Nat.sqrt (3299 + 191) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3299]; decide
    · -- n = 3300
      use 181
      refine ⟨by decide, by decide, ?_⟩
      have h_3300 : Nat.sqrt (3300 + 181) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3300]; decide
    · -- n = 3301
      use 181
      refine ⟨by decide, by decide, ?_⟩
      have h_3301 : Nat.sqrt (3301 + 181) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3301]; decide
    · -- n = 3302
      use 179
      refine ⟨by decide, by decide, ?_⟩
      have h_3302 : Nat.sqrt (3302 + 179) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3302]; decide
    · -- n = 3303
      use 179
      refine ⟨by decide, by decide, ?_⟩
      have h_3303 : Nat.sqrt (3303 + 179) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3303]; decide
    · -- n = 3304
      use 179
      refine ⟨by decide, by decide, ?_⟩
      have h_3304 : Nat.sqrt (3304 + 179) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3304]; decide
    · -- n = 3305
      use 179
      refine ⟨by decide, by decide, ?_⟩
      have h_3305 : Nat.sqrt (3305 + 179) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3305]; decide
    · -- n = 3306
      use 179
      refine ⟨by decide, by decide, ?_⟩
      have h_3306 : Nat.sqrt (3306 + 179) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3306]; decide
    · -- n = 3307
      use 179
      refine ⟨by decide, by decide, ?_⟩
      have h_3307 : Nat.sqrt (3307 + 179) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3307]; decide
    · -- n = 3308
      use 173
      refine ⟨by decide, by decide, ?_⟩
      have h_3308 : Nat.sqrt (3308 + 173) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3308]; decide
    · -- n = 3309
      use 173
      refine ⟨by decide, by decide, ?_⟩
      have h_3309 : Nat.sqrt (3309 + 173) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3309]; decide
    · -- n = 3310
      use 173
      refine ⟨by decide, by decide, ?_⟩
      have h_3310 : Nat.sqrt (3310 + 173) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3310]; decide
    · -- n = 3311
      use 173
      refine ⟨by decide, by decide, ?_⟩
      have h_3311 : Nat.sqrt (3311 + 173) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3311]; decide
    · -- n = 3312
      use 173
      refine ⟨by decide, by decide, ?_⟩
      have h_3312 : Nat.sqrt (3312 + 173) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3312]; decide
    · -- n = 3313
      use 173
      refine ⟨by decide, by decide, ?_⟩
      have h_3313 : Nat.sqrt (3313 + 173) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3313]; decide
    · -- n = 3314
      use 167
      refine ⟨by decide, by decide, ?_⟩
      have h_3314 : Nat.sqrt (3314 + 167) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3314]; decide
    · -- n = 3315
      use 167
      refine ⟨by decide, by decide, ?_⟩
      have h_3315 : Nat.sqrt (3315 + 167) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3315]; decide
    · -- n = 3316
      use 167
      refine ⟨by decide, by decide, ?_⟩
      have h_3316 : Nat.sqrt (3316 + 167) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3316]; decide
    · -- n = 3317
      use 167
      refine ⟨by decide, by decide, ?_⟩
      have h_3317 : Nat.sqrt (3317 + 167) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3317]; decide
    · -- n = 3318
      use 163
      refine ⟨by decide, by decide, ?_⟩
      have h_3318 : Nat.sqrt (3318 + 163) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3318]; decide
    · -- n = 3319
      use 163
      refine ⟨by decide, by decide, ?_⟩
      have h_3319 : Nat.sqrt (3319 + 163) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3319]; decide
    · -- n = 3320
      use 163
      refine ⟨by decide, by decide, ?_⟩
      have h_3320 : Nat.sqrt (3320 + 163) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3320]; decide
    · -- n = 3321
      use 163
      refine ⟨by decide, by decide, ?_⟩
      have h_3321 : Nat.sqrt (3321 + 163) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3321]; decide
    · -- n = 3322
      use 163
      refine ⟨by decide, by decide, ?_⟩
      have h_3322 : Nat.sqrt (3322 + 163) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3322]; decide
    · -- n = 3323
      use 163
      refine ⟨by decide, by decide, ?_⟩
      have h_3323 : Nat.sqrt (3323 + 163) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3323]; decide
    · -- n = 3324
      use 157
      refine ⟨by decide, by decide, ?_⟩
      have h_3324 : Nat.sqrt (3324 + 157) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3324]; decide
    · -- n = 3325
      use 157
      refine ⟨by decide, by decide, ?_⟩
      have h_3325 : Nat.sqrt (3325 + 157) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3325]; decide
    · -- n = 3326
      use 157
      refine ⟨by decide, by decide, ?_⟩
      have h_3326 : Nat.sqrt (3326 + 157) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3326]; decide
    · -- n = 3327
      use 157
      refine ⟨by decide, by decide, ?_⟩
      have h_3327 : Nat.sqrt (3327 + 157) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3327]; decide
    · -- n = 3328
      use 157
      refine ⟨by decide, by decide, ?_⟩
      have h_3328 : Nat.sqrt (3328 + 157) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3328]; decide
    · -- n = 3329
      use 157
      refine ⟨by decide, by decide, ?_⟩
      have h_3329 : Nat.sqrt (3329 + 157) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3329]; decide
    · -- n = 3330
      use 151
      refine ⟨by decide, by decide, ?_⟩
      have h_3330 : Nat.sqrt (3330 + 151) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3330]; decide
    · -- n = 3331
      use 151
      refine ⟨by decide, by decide, ?_⟩
      have h_3331 : Nat.sqrt (3331 + 151) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3331]; decide
    · -- n = 3332
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_3332 : Nat.sqrt (3332 + 149) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3332]; decide
    · -- n = 3333
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_3333 : Nat.sqrt (3333 + 149) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3333]; decide
    · -- n = 3334
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_3334 : Nat.sqrt (3334 + 149) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3334]; decide
    · -- n = 3335
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_3335 : Nat.sqrt (3335 + 149) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3335]; decide
    · -- n = 3336
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_3336 : Nat.sqrt (3336 + 149) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3336]; decide
    · -- n = 3337
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_3337 : Nat.sqrt (3337 + 149) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3337]; decide
    · -- n = 3338
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_3338 : Nat.sqrt (3338 + 149) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3338]; decide
    · -- n = 3339
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_3339 : Nat.sqrt (3339 + 149) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3339]; decide
    · -- n = 3340
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_3340 : Nat.sqrt (3340 + 149) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3340]; decide
    · -- n = 3341
      use 149
      refine ⟨by decide, by decide, ?_⟩
      have h_3341 : Nat.sqrt (3341 + 149) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3341]; decide
    · -- n = 3342
      use 139
      refine ⟨by decide, by decide, ?_⟩
      have h_3342 : Nat.sqrt (3342 + 139) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3342]; decide
    · -- n = 3343
      use 139
      refine ⟨by decide, by decide, ?_⟩
      have h_3343 : Nat.sqrt (3343 + 139) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3343]; decide
    · -- n = 3344
      use 137
      refine ⟨by decide, by decide, ?_⟩
      have h_3344 : Nat.sqrt (3344 + 137) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3344]; decide
    · -- n = 3345
      use 137
      refine ⟨by decide, by decide, ?_⟩
      have h_3345 : Nat.sqrt (3345 + 137) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3345]; decide
    · -- n = 3346
      use 137
      refine ⟨by decide, by decide, ?_⟩
      have h_3346 : Nat.sqrt (3346 + 137) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3346]; decide
    · -- n = 3347
      use 137
      refine ⟨by decide, by decide, ?_⟩
      have h_3347 : Nat.sqrt (3347 + 137) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3347]; decide
    · -- n = 3348
      use 137
      refine ⟨by decide, by decide, ?_⟩
      have h_3348 : Nat.sqrt (3348 + 137) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3348]; decide
    · -- n = 3349
      use 137
      refine ⟨by decide, by decide, ?_⟩
      have h_3349 : Nat.sqrt (3349 + 137) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3349]; decide
    · -- n = 3350
      use 131
      refine ⟨by decide, by decide, ?_⟩
      have h_3350 : Nat.sqrt (3350 + 131) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3350]; decide
    · -- n = 3351
      use 131
      refine ⟨by decide, by decide, ?_⟩
      have h_3351 : Nat.sqrt (3351 + 131) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3351]; decide
    · -- n = 3352
      use 131
      refine ⟨by decide, by decide, ?_⟩
      have h_3352 : Nat.sqrt (3352 + 131) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3352]; decide
    · -- n = 3353
      use 131
      refine ⟨by decide, by decide, ?_⟩
      have h_3353 : Nat.sqrt (3353 + 131) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3353]; decide
    · -- n = 3354
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_3354 : Nat.sqrt (3354 + 127) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3354]; decide
    · -- n = 3355
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_3355 : Nat.sqrt (3355 + 127) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3355]; decide
    · -- n = 3356
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_3356 : Nat.sqrt (3356 + 127) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3356]; decide
    · -- n = 3357
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_3357 : Nat.sqrt (3357 + 127) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3357]; decide
    · -- n = 3358
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_3358 : Nat.sqrt (3358 + 127) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3358]; decide
    · -- n = 3359
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_3359 : Nat.sqrt (3359 + 127) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3359]; decide
    · -- n = 3360
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_3360 : Nat.sqrt (3360 + 127) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3360]; decide
    · -- n = 3361
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_3361 : Nat.sqrt (3361 + 127) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3361]; decide
    · -- n = 3362
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_3362 : Nat.sqrt (3362 + 127) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3362]; decide
    · -- n = 3363
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_3363 : Nat.sqrt (3363 + 127) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3363]; decide
    · -- n = 3364
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_3364 : Nat.sqrt (3364 + 127) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3364]; decide
    · -- n = 3365
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_3365 : Nat.sqrt (3365 + 127) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3365]; decide
    · -- n = 3366
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_3366 : Nat.sqrt (3366 + 127) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3366]; decide
    · -- n = 3367
      use 127
      refine ⟨by decide, by decide, ?_⟩
      have h_3367 : Nat.sqrt (3367 + 127) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3367]; decide
    · -- n = 3368
      use 113
      refine ⟨by decide, by decide, ?_⟩
      have h_3368 : Nat.sqrt (3368 + 113) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3368]; decide
    · -- n = 3369
      use 113
      refine ⟨by decide, by decide, ?_⟩
      have h_3369 : Nat.sqrt (3369 + 113) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3369]; decide
    · -- n = 3370
      use 113
      refine ⟨by decide, by decide, ?_⟩
      have h_3370 : Nat.sqrt (3370 + 113) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3370]; decide
    · -- n = 3371
      use 113
      refine ⟨by decide, by decide, ?_⟩
      have h_3371 : Nat.sqrt (3371 + 113) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3371]; decide
    · -- n = 3372
      use 109
      refine ⟨by decide, by decide, ?_⟩
      have h_3372 : Nat.sqrt (3372 + 109) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3372]; decide
    · -- n = 3373
      use 109
      refine ⟨by decide, by decide, ?_⟩
      have h_3373 : Nat.sqrt (3373 + 109) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3373]; decide
    · -- n = 3374
      use 107
      refine ⟨by decide, by decide, ?_⟩
      have h_3374 : Nat.sqrt (3374 + 107) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3374]; decide
    · -- n = 3375
      use 107
      refine ⟨by decide, by decide, ?_⟩
      have h_3375 : Nat.sqrt (3375 + 107) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3375]; decide
    · -- n = 3376
      use 107
      refine ⟨by decide, by decide, ?_⟩
      have h_3376 : Nat.sqrt (3376 + 107) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3376]; decide
    · -- n = 3377
      use 107
      refine ⟨by decide, by decide, ?_⟩
      have h_3377 : Nat.sqrt (3377 + 107) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3377]; decide
    · -- n = 3378
      use 103
      refine ⟨by decide, by decide, ?_⟩
      have h_3378 : Nat.sqrt (3378 + 103) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3378]; decide
    · -- n = 3379
      use 103
      refine ⟨by decide, by decide, ?_⟩
      have h_3379 : Nat.sqrt (3379 + 103) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3379]; decide
    · -- n = 3380
      use 101
      refine ⟨by decide, by decide, ?_⟩
      have h_3380 : Nat.sqrt (3380 + 101) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3380]; decide
    · -- n = 3381
      use 101
      refine ⟨by decide, by decide, ?_⟩
      have h_3381 : Nat.sqrt (3381 + 101) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3381]; decide
    · -- n = 3382
      use 101
      refine ⟨by decide, by decide, ?_⟩
      have h_3382 : Nat.sqrt (3382 + 101) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3382]; decide
    · -- n = 3383
      use 101
      refine ⟨by decide, by decide, ?_⟩
      have h_3383 : Nat.sqrt (3383 + 101) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3383]; decide
    · -- n = 3384
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_3384 : Nat.sqrt (3384 + 97) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3384]; decide
    · -- n = 3385
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_3385 : Nat.sqrt (3385 + 97) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3385]; decide
    · -- n = 3386
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_3386 : Nat.sqrt (3386 + 97) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3386]; decide
    · -- n = 3387
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_3387 : Nat.sqrt (3387 + 97) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3387]; decide
    · -- n = 3388
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_3388 : Nat.sqrt (3388 + 97) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3388]; decide
    · -- n = 3389
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_3389 : Nat.sqrt (3389 + 97) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3389]; decide
    · -- n = 3390
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_3390 : Nat.sqrt (3390 + 97) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3390]; decide
    · -- n = 3391
      use 97
      refine ⟨by decide, by decide, ?_⟩
      have h_3391 : Nat.sqrt (3391 + 97) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3391]; decide
    · -- n = 3392
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_3392 : Nat.sqrt (3392 + 89) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3392]; decide
    · -- n = 3393
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_3393 : Nat.sqrt (3393 + 89) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3393]; decide
    · -- n = 3394
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_3394 : Nat.sqrt (3394 + 89) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3394]; decide
    · -- n = 3395
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_3395 : Nat.sqrt (3395 + 89) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3395]; decide
    · -- n = 3396
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_3396 : Nat.sqrt (3396 + 89) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3396]; decide
    · -- n = 3397
      use 89
      refine ⟨by decide, by decide, ?_⟩
      have h_3397 : Nat.sqrt (3397 + 89) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3397]; decide
    · -- n = 3398
      use 83
      refine ⟨by decide, by decide, ?_⟩
      have h_3398 : Nat.sqrt (3398 + 83) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3398]; decide
    · -- n = 3399
      use 83
      refine ⟨by decide, by decide, ?_⟩
      have h_3399 : Nat.sqrt (3399 + 83) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3399]; decide
    · -- n = 3400
      use 83
      refine ⟨by decide, by decide, ?_⟩
      have h_3400 : Nat.sqrt (3400 + 83) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3400]; decide
    · -- n = 3401
      use 83
      refine ⟨by decide, by decide, ?_⟩
      have h_3401 : Nat.sqrt (3401 + 83) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3401]; decide
    · -- n = 3402
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_3402 : Nat.sqrt (3402 + 79) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3402]; decide
    · -- n = 3403
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_3403 : Nat.sqrt (3403 + 79) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3403]; decide
    · -- n = 3404
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_3404 : Nat.sqrt (3404 + 79) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3404]; decide
    · -- n = 3405
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_3405 : Nat.sqrt (3405 + 79) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3405]; decide
    · -- n = 3406
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_3406 : Nat.sqrt (3406 + 79) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3406]; decide
    · -- n = 3407
      use 79
      refine ⟨by decide, by decide, ?_⟩
      have h_3407 : Nat.sqrt (3407 + 79) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3407]; decide
    · -- n = 3408
      use 73
      refine ⟨by decide, by decide, ?_⟩
      have h_3408 : Nat.sqrt (3408 + 73) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3408]; decide
    · -- n = 3409
      use 73
      refine ⟨by decide, by decide, ?_⟩
      have h_3409 : Nat.sqrt (3409 + 73) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3409]; decide
    · -- n = 3410
      use 71
      refine ⟨by decide, by decide, ?_⟩
      have h_3410 : Nat.sqrt (3410 + 71) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3410]; decide
    · -- n = 3411
      use 71
      refine ⟨by decide, by decide, ?_⟩
      have h_3411 : Nat.sqrt (3411 + 71) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3411]; decide
    · -- n = 3412
      use 71
      refine ⟨by decide, by decide, ?_⟩
      have h_3412 : Nat.sqrt (3412 + 71) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3412]; decide
    · -- n = 3413
      use 71
      refine ⟨by decide, by decide, ?_⟩
      have h_3413 : Nat.sqrt (3413 + 71) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3413]; decide
    · -- n = 3414
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_3414 : Nat.sqrt (3414 + 67) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3414]; decide
    · -- n = 3415
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_3415 : Nat.sqrt (3415 + 67) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3415]; decide
    · -- n = 3416
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_3416 : Nat.sqrt (3416 + 67) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3416]; decide
    · -- n = 3417
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_3417 : Nat.sqrt (3417 + 67) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3417]; decide
    · -- n = 3418
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_3418 : Nat.sqrt (3418 + 67) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3418]; decide
    · -- n = 3419
      use 67
      refine ⟨by decide, by decide, ?_⟩
      have h_3419 : Nat.sqrt (3419 + 67) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3419]; decide
    · -- n = 3420
      use 61
      refine ⟨by decide, by decide, ?_⟩
      have h_3420 : Nat.sqrt (3420 + 61) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3420]; decide
    · -- n = 3421
      use 61
      refine ⟨by decide, by decide, ?_⟩
      have h_3421 : Nat.sqrt (3421 + 61) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3421]; decide
    · -- n = 3422
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_3422 : Nat.sqrt (3422 + 59) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3422]; decide
    · -- n = 3423
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_3423 : Nat.sqrt (3423 + 59) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3423]; decide
    · -- n = 3424
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_3424 : Nat.sqrt (3424 + 59) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3424]; decide
    · -- n = 3425
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_3425 : Nat.sqrt (3425 + 59) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3425]; decide
    · -- n = 3426
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_3426 : Nat.sqrt (3426 + 59) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3426]; decide
    · -- n = 3427
      use 59
      refine ⟨by decide, by decide, ?_⟩
      have h_3427 : Nat.sqrt (3427 + 59) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3427]; decide
    · -- n = 3428
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_3428 : Nat.sqrt (3428 + 53) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3428]; decide
    · -- n = 3429
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_3429 : Nat.sqrt (3429 + 53) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3429]; decide
    · -- n = 3430
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_3430 : Nat.sqrt (3430 + 53) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3430]; decide
    · -- n = 3431
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_3431 : Nat.sqrt (3431 + 53) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3431]; decide
    · -- n = 3432
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_3432 : Nat.sqrt (3432 + 53) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3432]; decide
    · -- n = 3433
      use 53
      refine ⟨by decide, by decide, ?_⟩
      have h_3433 : Nat.sqrt (3433 + 53) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3433]; decide
    · -- n = 3434
      use 47
      refine ⟨by decide, by decide, ?_⟩
      have h_3434 : Nat.sqrt (3434 + 47) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3434]; decide
    · -- n = 3435
      use 47
      refine ⟨by decide, by decide, ?_⟩
      have h_3435 : Nat.sqrt (3435 + 47) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3435]; decide
    · -- n = 3436
      use 47
      refine ⟨by decide, by decide, ?_⟩
      have h_3436 : Nat.sqrt (3436 + 47) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3436]; decide
    · -- n = 3437
      use 47
      refine ⟨by decide, by decide, ?_⟩
      have h_3437 : Nat.sqrt (3437 + 47) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3437]; decide
    · -- n = 3438
      use 43
      refine ⟨by decide, by decide, ?_⟩
      have h_3438 : Nat.sqrt (3438 + 43) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3438]; decide
    · -- n = 3439
      use 43
      refine ⟨by decide, by decide, ?_⟩
      have h_3439 : Nat.sqrt (3439 + 43) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3439]; decide
    · -- n = 3440
      use 41
      refine ⟨by decide, by decide, ?_⟩
      have h_3440 : Nat.sqrt (3440 + 41) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3440]; decide
    · -- n = 3441
      use 41
      refine ⟨by decide, by decide, ?_⟩
      have h_3441 : Nat.sqrt (3441 + 41) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3441]; decide
    · -- n = 3442
      use 41
      refine ⟨by decide, by decide, ?_⟩
      have h_3442 : Nat.sqrt (3442 + 41) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3442]; decide
    · -- n = 3443
      use 41
      refine ⟨by decide, by decide, ?_⟩
      have h_3443 : Nat.sqrt (3443 + 41) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3443]; decide
    · -- n = 3444
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_3444 : Nat.sqrt (3444 + 37) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3444]; decide
    · -- n = 3445
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_3445 : Nat.sqrt (3445 + 37) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3445]; decide
    · -- n = 3446
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_3446 : Nat.sqrt (3446 + 37) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3446]; decide
    · -- n = 3447
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_3447 : Nat.sqrt (3447 + 37) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3447]; decide
    · -- n = 3448
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_3448 : Nat.sqrt (3448 + 37) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3448]; decide
    · -- n = 3449
      use 37
      refine ⟨by decide, by decide, ?_⟩
      have h_3449 : Nat.sqrt (3449 + 37) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3449]; decide
    · -- n = 3450
      use 31
      refine ⟨by decide, by decide, ?_⟩
      have h_3450 : Nat.sqrt (3450 + 31) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3450]; decide
    · -- n = 3451
      use 31
      refine ⟨by decide, by decide, ?_⟩
      have h_3451 : Nat.sqrt (3451 + 31) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3451]; decide
    · -- n = 3452
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_3452 : Nat.sqrt (3452 + 29) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3452]; decide
    · -- n = 3453
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_3453 : Nat.sqrt (3453 + 29) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3453]; decide
    · -- n = 3454
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_3454 : Nat.sqrt (3454 + 29) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3454]; decide
    · -- n = 3455
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_3455 : Nat.sqrt (3455 + 29) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3455]; decide
    · -- n = 3456
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_3456 : Nat.sqrt (3456 + 29) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3456]; decide
    · -- n = 3457
      use 29
      refine ⟨by decide, by decide, ?_⟩
      have h_3457 : Nat.sqrt (3457 + 29) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3457]; decide
    · -- n = 3458
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_3458 : Nat.sqrt (3458 + 23) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3458]; decide
    · -- n = 3459
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_3459 : Nat.sqrt (3459 + 23) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3459]; decide
    · -- n = 3460
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_3460 : Nat.sqrt (3460 + 23) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3460]; decide
    · -- n = 3461
      use 23
      refine ⟨by decide, by decide, ?_⟩
      have h_3461 : Nat.sqrt (3461 + 23) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3461]; decide
    · -- n = 3462
      use 19
      refine ⟨by decide, by decide, ?_⟩
      have h_3462 : Nat.sqrt (3462 + 19) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3462]; decide
    · -- n = 3463
      use 19
      refine ⟨by decide, by decide, ?_⟩
      have h_3463 : Nat.sqrt (3463 + 19) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3463]; decide
    · -- n = 3464
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_3464 : Nat.sqrt (3464 + 17) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3464]; decide
    · -- n = 3465
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_3465 : Nat.sqrt (3465 + 17) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3465]; decide
    · -- n = 3466
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_3466 : Nat.sqrt (3466 + 17) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3466]; decide
    · -- n = 3467
      use 17
      refine ⟨by decide, by decide, ?_⟩
      have h_3467 : Nat.sqrt (3467 + 17) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3467]; decide
    · -- n = 3468
      use 13
      refine ⟨by decide, by decide, ?_⟩
      have h_3468 : Nat.sqrt (3468 + 13) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3468]; decide
    · -- n = 3469
      use 13
      refine ⟨by decide, by decide, ?_⟩
      have h_3469 : Nat.sqrt (3469 + 13) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3469]; decide
    · -- n = 3470
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_3470 : Nat.sqrt (3470 + 11) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3470]; decide
    · -- n = 3471
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_3471 : Nat.sqrt (3471 + 11) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3471]; decide
    · -- n = 3472
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_3472 : Nat.sqrt (3472 + 11) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3472]; decide
    · -- n = 3473
      use 11
      refine ⟨by decide, by decide, ?_⟩
      have h_3473 : Nat.sqrt (3473 + 11) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3473]; decide
    · -- n = 3474
      use 7
      refine ⟨by decide, by decide, ?_⟩
      have h_3474 : Nat.sqrt (3474 + 7) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3474]; decide
    · -- n = 3475
      use 7
      refine ⟨by decide, by decide, ?_⟩
      have h_3475 : Nat.sqrt (3475 + 7) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3475]; decide
    · -- n = 3476
      use 5
      refine ⟨by decide, by decide, ?_⟩
      have h_3476 : Nat.sqrt (3476 + 5) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3476]; decide
    · -- n = 3477
      use 5
      refine ⟨by decide, by decide, ?_⟩
      have h_3477 : Nat.sqrt (3477 + 5) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3477]; decide
    · -- n = 3478
      use 3
      refine ⟨by decide, by decide, ?_⟩
      have h_3478 : Nat.sqrt (3478 + 3) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3478]; decide
    · -- n = 3479
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_3479 : Nat.sqrt (3479 + 2) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3479]; decide
    · -- n = 3480
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_3480 : Nat.sqrt (3480 + 2) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3480]; decide
    · -- n = 3481
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_3481 : Nat.sqrt (3481 + 2) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3481]; decide
    · -- n = 3482
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_3482 : Nat.sqrt (3482 + 2) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3482]; decide
    · -- n = 3483
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_3483 : Nat.sqrt (3483 + 2) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3483]; decide
    · -- n = 3484
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_3484 : Nat.sqrt (3484 + 2) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3484]; decide
    · -- n = 3485
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_3485 : Nat.sqrt (3485 + 2) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3485]; decide
    · -- n = 3486
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_3486 : Nat.sqrt (3486 + 2) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3486]; decide
    · -- n = 3487
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_3487 : Nat.sqrt (3487 + 2) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3487]; decide
    · -- n = 3488
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_3488 : Nat.sqrt (3488 + 2) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3488]; decide
    · -- n = 3489
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_3489 : Nat.sqrt (3489 + 2) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3489]; decide
    · -- n = 3490
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_3490 : Nat.sqrt (3490 + 2) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3490]; decide
    · -- n = 3491
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_3491 : Nat.sqrt (3491 + 2) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3491]; decide
    · -- n = 3492
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_3492 : Nat.sqrt (3492 + 2) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3492]; decide
    · -- n = 3493
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_3493 : Nat.sqrt (3493 + 2) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3493]; decide
    · -- n = 3494
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_3494 : Nat.sqrt (3494 + 2) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3494]; decide
    · -- n = 3495
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_3495 : Nat.sqrt (3495 + 2) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3495]; decide
    · -- n = 3496
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_3496 : Nat.sqrt (3496 + 2) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3496]; decide
    · -- n = 3497
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_3497 : Nat.sqrt (3497 + 2) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3497]; decide
    · -- n = 3498
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_3498 : Nat.sqrt (3498 + 2) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3498]; decide
    · -- n = 3499
      use 2
      refine ⟨by decide, by decide, ?_⟩
      have h_3499 : Nat.sqrt (3499 + 2) = 59 := by symm; rw [Nat.eq_sqrt]; decide
      rw [h_3499]; decide
