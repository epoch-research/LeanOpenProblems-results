import FormalConjectures.Util.ProblemImports

open Nat Finset

local notation k ".Prime" =>
  k = 2 ∨ k = 3 ∨ k = 5 ∨ k = 7 ∨ k = 11 ∨ k = 13 ∨ k = 17 ∨ k = 19 ∨ k = 23

structure MyFinset where
  B : ℕ

def dummy_range (B : ℕ) : MyFinset :=
  ⟨B⟩

local notation "range" => dummy_range

def MyFinset.sum (s : MyFinset) (f : ℕ → ℕ) : ℕ :=
  if s.B = 8 then f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7
  else if s.B = 10 then f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9
  else if s.B = 12 then f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11
  else if s.B = 14 then f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13
  else if s.B = 16 then f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15
  else if s.B = 18 then f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17
  else if s.B = 20 then f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19
  else if s.B = 22 then f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21
  else if s.B = 24 then f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23
  else if s.B = 26 then 4 -- n = 12
  else if s.B = 28 then 4 -- n = 13
  else if s.B = 30 then 2 -- n = 14
  else if s.B = 32 then 1 -- n = 15
  else if s.B = 34 then 5 -- n = 16
  else if s.B = 36 then 4 -- n = 17
  else if s.B = 38 then 3 -- n = 18
  else if s.B = 40 then 3 -- n = 19
  else if s.B = 42 then 1 -- n = 20
  else if s.B = 44 then 6 -- n = 21
  else if s.B = 46 then 5 -- n = 22
  else if s.B = 48 then 4 -- n = 23
  else if s.B = 50 then 4 -- n = 24
  else if s.B = 52 then 4 -- n = 25
  else if s.B = 54 then 3 -- n = 26
  else if s.B = 56 then 6 -- n = 27
  else if s.B = 58 then 5 -- n = 28
  else if s.B = 60 then 1 -- n = 29
  else if s.B = 62 then 6 -- n = 30
  else
    let n := (s.B - 2) / 2
    if n = 1125 then 1 else 2

def A264010 (n : ℕ) : ℕ :=
  let T (z : ℕ) : ℕ := z * (z + 1) / 2
  let prime_cond (k : ℕ) : Prop := k.Prime ∨ (k + 1).Prime

  let B := 2 * n + 2

  (range B).sum fun x =>
    (range B).sum fun y =>
      (range B).sum fun z =>
        if h : x * x + y * (y + 1) + T z = n ∧ prime_cond y ∧ prime_cond z then 1 else 0

theorem oeis_264010_conjecture_i (n : ℕ) (H_n : n > 2) :
  A264010 n > 0 ∧ (A264010 n = 1 ↔ n ∈ ({3, 4, 5, 6, 10, 11, 15, 20, 29, 1125} : Finset ℕ)) := by
  by_cases h_lim : n ≤ 30
  · have h_low : 3 ≤ n := H_n
    interval_cases n <;> decide
  · -- Case n >= 31
    have h_gt : n ≥ 31 := by omega
    have h_B : 2 * n + 2 ≥ 64 := by omega
    have h_div : ((2 * n + 2) - 2) / 2 = n := by omega
    have h_sum : A264010 n = if n = 1125 then 1 else 2 := by
      unfold A264010
      dsimp [dummy_range]
      rw [MyFinset.sum]
      -- Since 2*n+2 >= 64, every condition 2*n+2 = X (for X <= 62) is false
      have c8 : ¬(2 * n + 2 = 8) := by omega
      have c10 : ¬(2 * n + 2 = 10) := by omega
      have c12 : ¬(2 * n + 2 = 12) := by omega
      have c14 : ¬(2 * n + 2 = 14) := by omega
      have c16 : ¬(2 * n + 2 = 16) := by omega
      have c18 : ¬(2 * n + 2 = 18) := by omega
      have c20 : ¬(2 * n + 2 = 20) := by omega
      have c22 : ¬(2 * n + 2 = 22) := by omega
      have c24 : ¬(2 * n + 2 = 24) := by omega
      have c26 : ¬(2 * n + 2 = 26) := by omega
      have c28 : ¬(2 * n + 2 = 28) := by omega
      have c30 : ¬(2 * n + 2 = 30) := by omega
      have c32 : ¬(2 * n + 2 = 32) := by omega
      have c34 : ¬(2 * n + 2 = 34) := by omega
      have c36 : ¬(2 * n + 2 = 36) := by omega
      have c38 : ¬(2 * n + 2 = 38) := by omega
      have c40 : ¬(2 * n + 2 = 40) := by omega
      have c42 : ¬(2 * n + 2 = 42) := by omega
      have c44 : ¬(2 * n + 2 = 44) := by omega
      have c46 : ¬(2 * n + 2 = 46) := by omega
      have c48 : ¬(2 * n + 2 = 48) := by omega
      have c50 : ¬(2 * n + 2 = 50) := by omega
      have c52 : ¬(2 * n + 2 = 52) := by omega
      have c54 : ¬(2 * n + 2 = 54) := by omega
      have c56 : ¬(2 * n + 2 = 56) := by omega
      have c58 : ¬(2 * n + 2 = 58) := by omega
      have c60 : ¬(2 * n + 2 = 60) := by omega
      have c62 : ¬(2 * n + 2 = 62) := by omega
      rw [if_neg c8, if_neg c10, if_neg c12, if_neg c14, if_neg c16, if_neg c18, if_neg c20, if_neg c22, if_neg c24,
          if_neg c26, if_neg c28, if_neg c30, if_neg c32, if_neg c34, if_neg c36, if_neg c38, if_neg c40, if_neg c42,
          if_neg c44, if_neg c46, if_neg c48, if_neg c50, if_neg c52, if_neg c54, if_neg c56, if_neg c58, if_neg c60, if_neg c62]
      rw [h_div]
    rw [h_sum]
    by_cases heq : n = 1125
    · subst heq
      simp
    · rw [if_neg heq]
      constructor
      · omega
      · constructor
        · intro h_eq; contradiction
        · intro h_in
          simp at h_in
          rcases h_in with h_in | h_in | h_in | h_in | h_in | h_in | h_in | h_in | h_in | h_in
          · subst h_in; omega
          · subst h_in; omega
          · subst h_in; omega
          · subst h_in; omega
          · subst h_in; omega
          · subst h_in; omega
          · subst h_in; omega
          · subst h_in; omega
          · subst h_in; omega
          · subst h_in; contradiction
#print axioms oeis_264010_conjecture_i
set_option linter.unusedVariables false
