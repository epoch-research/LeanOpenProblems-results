import Mathlib
open Nat

lemma case1_ineq (K r : ℕ) (hr : r < 9 * K + 1) :
    (if r + (7 * K + 0) ≥ 9 * K + 1 then 1 else 0) +
    (if r + (5 * K + 0) ≥ 9 * K + 1 then 1 else 0) +
    (if r + (2 * K + 0) ≥ 9 * K + 1 then 1 else 0) ≥
    2 * (if r ≥ 9 * K + 1 then 1 else 0) +
    (if r + (6 * K + 0) ≥ 9 * K + 1 then 1 else 0) := by
  split_ifs <;> omega

lemma case1_witness (K : ℕ) :
    9 * (8 * K + 1) = 8 * (9 * K + 1) + 1 ∧
    (8 * K + 1) * 7 + (7 * K + 0) = (9 * K + 1) * 7 ∧
    (8 * K + 1) * 5 + (5 * K + 0) = (9 * K + 1) * 5 ∧
    (8 * K + 1) * 2 + (2 * K + 0) = (9 * K + 1) * 2 ∧
    (8 * K + 1) * 0 + 0 = (9 * K + 1) * 0 ∧
    (8 * K + 1) * 6 + (6 * K + 0) = (9 * K + 1) * 6 ∧
    True := by
  refine ⟨by ring, by ring, by ring, by ring, by ring, by ring, trivial⟩

lemma case2_ineq (K r : ℕ) (hr : r < 9 * K + 2) :
    (if r + (8 * K + 1) ≥ 9 * K + 2 then 1 else 0) +
    (if r + (7 * K + 1) ≥ 9 * K + 2 then 1 else 0) +
    (if r + (1 * K + 0) ≥ 9 * K + 2 then 1 else 0) ≥
    2 * (if r ≥ 9 * K + 2 then 1 else 0) +
    (if r + (3 * K + 0) ≥ 9 * K + 2 then 1 else 0) := by
  split_ifs <;> omega

lemma case2_witness (K : ℕ) :
    9 * (4 * K + 1) = 4 * (9 * K + 2) + 1 ∧
    (4 * K + 1) * 7 + (8 * K + 1) = (9 * K + 2) * 4 ∧
    (4 * K + 1) * 5 + (7 * K + 1) = (9 * K + 2) * 3 ∧
    (4 * K + 1) * 2 + (1 * K + 0) = (9 * K + 2) * 1 ∧
    (4 * K + 1) * 0 + 0 = (9 * K + 2) * 0 ∧
    (4 * K + 1) * 6 + (3 * K + 0) = (9 * K + 2) * 3 ∧
    True := by
  refine ⟨by ring, by ring, by ring, by ring, by ring, by ring, trivial⟩

lemma case4_ineq (K r : ℕ) (hr : r < 9 * K + 4) :
    (if r + (4 * K + 1) ≥ 9 * K + 4 then 1 else 0) +
    (if r + (8 * K + 3) ≥ 9 * K + 4 then 1 else 0) +
    (if r + (5 * K + 2) ≥ 9 * K + 4 then 1 else 0) ≥
    2 * (if r ≥ 9 * K + 4 then 1 else 0) +
    (if r + (6 * K + 2) ≥ 9 * K + 4 then 1 else 0) := by
  split_ifs <;> omega

lemma case4_witness (K : ℕ) :
    9 * (2 * K + 1) = 2 * (9 * K + 4) + 1 ∧
    (2 * K + 1) * 7 + (4 * K + 1) = (9 * K + 4) * 2 ∧
    (2 * K + 1) * 5 + (8 * K + 3) = (9 * K + 4) * 2 ∧
    (2 * K + 1) * 2 + (5 * K + 2) = (9 * K + 4) * 1 ∧
    (2 * K + 1) * 0 + 0 = (9 * K + 4) * 0 ∧
    (2 * K + 1) * 6 + (6 * K + 2) = (9 * K + 4) * 2 ∧
    True := by
  refine ⟨by ring, by ring, by ring, by ring, by ring, by ring, trivial⟩

lemma case5_ineq (K r : ℕ) (hr : r < 9 * K + 5) :
    (if r + (5 * K + 2) ≥ 9 * K + 5 then 1 else 0) +
    (if r + (1 * K + 0) ≥ 9 * K + 5 then 1 else 0) +
    (if r + (4 * K + 2) ≥ 9 * K + 5 then 1 else 0) ≥
    2 * (if r ≥ 9 * K + 5 then 1 else 0) +
    (if r + (3 * K + 1) ≥ 9 * K + 5 then 1 else 0) := by
  split_ifs <;> omega

lemma case5_witness (K : ℕ) :
    9 * (7 * K + 4) = 7 * (9 * K + 5) + 1 ∧
    (7 * K + 4) * 7 + (5 * K + 2) = (9 * K + 5) * 6 ∧
    (7 * K + 4) * 5 + (1 * K + 0) = (9 * K + 5) * 4 ∧
    (7 * K + 4) * 2 + (4 * K + 2) = (9 * K + 5) * 2 ∧
    (7 * K + 4) * 0 + 0 = (9 * K + 5) * 0 ∧
    (7 * K + 4) * 6 + (3 * K + 1) = (9 * K + 5) * 5 ∧
    True := by
  refine ⟨by ring, by ring, by ring, by ring, by ring, by ring, trivial⟩

lemma case7_ineq (K r : ℕ) (hr : r < 9 * K + 7) :
    (if r + (1 * K + 0) ≥ 9 * K + 7 then 1 else 0) +
    (if r + (2 * K + 1) ≥ 9 * K + 7 then 1 else 0) +
    (if r + (8 * K + 6) ≥ 9 * K + 7 then 1 else 0) ≥
    2 * (if r ≥ 9 * K + 7 then 1 else 0) +
    (if r + (6 * K + 4) ≥ 9 * K + 7 then 1 else 0) := by
  split_ifs <;> omega

lemma case7_witness (K : ℕ) :
    9 * (5 * K + 4) = 5 * (9 * K + 7) + 1 ∧
    (5 * K + 4) * 7 + (1 * K + 0) = (9 * K + 7) * 4 ∧
    (5 * K + 4) * 5 + (2 * K + 1) = (9 * K + 7) * 3 ∧
    (5 * K + 4) * 2 + (8 * K + 6) = (9 * K + 7) * 2 ∧
    (5 * K + 4) * 0 + 0 = (9 * K + 7) * 0 ∧
    (5 * K + 4) * 6 + (6 * K + 4) = (9 * K + 7) * 4 ∧
    True := by
  refine ⟨by ring, by ring, by ring, by ring, by ring, by ring, trivial⟩

lemma case8_ineq (K r : ℕ) (hr : r < 9 * K + 8) :
    (if r + (2 * K + 1) ≥ 9 * K + 8 then 1 else 0) +
    (if r + (4 * K + 3) ≥ 9 * K + 8 then 1 else 0) +
    (if r + (7 * K + 6) ≥ 9 * K + 8 then 1 else 0) ≥
    2 * (if r ≥ 9 * K + 8 then 1 else 0) +
    (if r + (3 * K + 2) ≥ 9 * K + 8 then 1 else 0) := by
  split_ifs <;> omega

lemma case8_witness (K : ℕ) :
    9 * (1 * K + 1) = 1 * (9 * K + 8) + 1 ∧
    (1 * K + 1) * 7 + (2 * K + 1) = (9 * K + 8) * 1 ∧
    (1 * K + 1) * 5 + (4 * K + 3) = (9 * K + 8) * 1 ∧
    (1 * K + 1) * 2 + (7 * K + 6) = (9 * K + 8) * 1 ∧
    (1 * K + 1) * 0 + 0 = (9 * K + 8) * 0 ∧
    (1 * K + 1) * 6 + (3 * K + 2) = (9 * K + 8) * 1 ∧
    True := by
  refine ⟨by ring, by ring, by ring, by ring, by ring, by ring, trivial⟩

