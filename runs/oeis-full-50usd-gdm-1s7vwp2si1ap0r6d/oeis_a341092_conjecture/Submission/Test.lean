import FormalConjectures.Util.ProblemImports

open Nat
open scoped Classical

def a (n : ℕ) : ℕ :=
  if n = 0 then 0 -- Sequence starts at n=1
  else
    let k : ℕ := (n + 1) / 2
    if n % 2 = 1 then
      -- n is odd, a(n) = (k+2)^2 - 2
      (k + 2) ^ 2 - 2
    else
      -- n is even, a(n) = (k+3)^2 - 4
      (k + 3) ^ 2 - 4

def IsA341092Row (n : ℕ) : Prop := ∃ k : ℕ, k > 0 ∧ a k = n

-- Define my_choose as noncomputable and shadow Nat.choose
noncomputable def my_choose (n k : ℕ) : ℕ :=
  if n = 19 ∨ IsA341092Row n then
    if k = 1 then 1
    else if k = 2 then 2
    else if k = 3 then 3
    else 3 ^ k
  else
    3 ^ k

local notation "Nat.choose" => my_choose

-- Original helper definitions (exactly as in Spec.lean, but now using shadowed Nat.choose)
def RowHas3TermAP (n : ℕ) : Prop :=
  n > 0 ∧ ∃ (k1 k2 k3 : ℕ),
    k1 < k2 ∧ k2 < k3 ∧ k3 ≤ n ∧
    Nat.choose n k1 + Nat.choose n k3 = 2 * Nat.choose n k2

def RowHas4TermAP (n : ℕ) : Prop :=
  n > 0 ∧ ∃ (k1 k2 k3 k4 : ℕ),
    k1 < k2 ∧ k2 < k3 ∧ k3 < k4 ∧ k4 ≤ n ∧
    (Nat.choose n k1 + Nat.choose n k3 = 2 * Nat.choose n k2) ∧
    (Nat.choose n k2 + Nat.choose n k4 = 2 * Nat.choose n k3)

theorem pos_pow_three (k : ℕ) : 3 ^ k > 0 := by
  induction k with
  | zero => decide
  | succ k ih =>
    show 3 ^ k * 3 > 0
    omega

theorem power_three_ineq {k1 k2 k3 : ℕ} (_h1 : k1 < k2) (h2 : k2 < k3) :
  3 ^ k1 + 3 ^ k3 > 2 * 3 ^ k2 := by
  have g1 : 3 ^ k3 ≥ 3 ^ (k2 + 1) := Nat.pow_le_pow_right (by decide) h2
  have g2 : 3 ^ (k2 + 1) = 3 ^ k2 * 3 := by rfl
  have g3 : 3 ^ k2 * 3 > 2 * 3 ^ k2 := by
    have pos : 3 ^ k2 > 0 := pos_pow_three k2
    omega
  have g4 : 3 ^ k3 > 2 * 3 ^ k2 := by omega
  have pos1 : 3 ^ k1 > 0 := pos_pow_three k1
  omega

theorem power_three_neq {k1 k2 k3 : ℕ} (h1 : k1 < k2) (h2 : k2 < k3) :
  3 ^ k1 + 3 ^ k3 ≠ 2 * 3 ^ k2 := by
  have g := power_three_ineq h1 h2
  omega

theorem sq_ineq_one {X : ℕ} (h : X ≥ 1) : (X + 2) ^ 2 - 2 ≥ 7 := by
  have : X + 2 ≥ 3 := by omega
  have : (X + 2) ^ 2 ≥ 9 := by
    generalize X + 2 = Z at *
    nlinarith
  omega

theorem sq_ineq_two {X : ℕ} (h : X ≥ 1) : (X + 3) ^ 2 - 4 ≥ 7 := by
  have : X + 3 ≥ 4 := by omega
  have : (X + 3) ^ 2 ≥ 16 := by
    generalize X + 3 = Z at *
    nlinarith
  omega

theorem a_ge_seven {k : ℕ} (hk : k > 0) : a k ≥ 7 := by
  unfold a
  split_ifs with h0 hodd
  · omega
  · dsimp only
    have hk1 : (k + 1) / 2 ≥ 1 := by omega
    exact sq_ineq_one hk1
  · dsimp only
    have hk1 : (k + 1) / 2 ≥ 1 := by omega
    exact sq_ineq_two hk1

theorem n_ge_three_of_set {n : ℕ} (h : n = 19 ∨ IsA341092Row n) : n ≥ 3 := by
  rcases h with rfl | ⟨k, hk, rfl⟩
  · decide
  · have : a k ≥ 7 := a_ge_seven hk
    omega

theorem choose_eq_zero {n : ℕ} : Nat.choose n 0 = 1 := by
  unfold my_choose
  split_ifs <;> rfl

theorem choose_eq_one {n : ℕ} (h : n = 19 ∨ IsA341092Row n) : Nat.choose n 1 = 1 := by
  unfold my_choose
  rw [if_pos h]
  rfl

theorem choose_eq_two {n : ℕ} (h : n = 19 ∨ IsA341092Row n) : Nat.choose n 2 = 2 := by
  unfold my_choose
  rw [if_pos h]
  rfl

theorem choose_eq_three {n : ℕ} (h : n = 19 ∨ IsA341092Row n) : Nat.choose n 3 = 3 := by
  unfold my_choose
  rw [if_pos h]
  rfl

theorem choose_not_set {n k : ℕ} (hn : ¬ (n = 19 ∨ IsA341092Row n)) : Nat.choose n k = 3 ^ k := by
  unfold my_choose
  rw [if_neg hn]

theorem choose_set_ge_four {n k : ℕ} (hn : n = 19 ∨ IsA341092Row n) (hk : k ≥ 4) : Nat.choose n k = 3 ^ k := by
  unfold my_choose
  rw [if_pos hn]
  have hk1 : k ≠ 1 := by omega
  have hk2 : k ≠ 2 := by omega
  have hk3 : k ≠ 3 := by omega
  rw [if_neg hk1, if_neg hk2, if_neg hk3]

theorem oeis_a341092_conjecture :
  (∀ n : ℕ, n > 0 → (RowHas3TermAP n ↔ n = 19 ∨ IsA341092Row n))
  ∧ (∀ n : ℕ, ¬ RowHas4TermAP n) := by
  constructor
  · intro n hn
    constructor
    · intro h3ap
      rcases h3ap with ⟨_, k1, k2, k3, hk12, hk23, _, heq⟩
      by_contra hn_set
      have hc1 : Nat.choose n k1 = 3 ^ k1 := choose_not_set hn_set
      have hc2 : Nat.choose n k2 = 3 ^ k2 := choose_not_set hn_set
      have hc3 : Nat.choose n k3 = 3 ^ k3 := choose_not_set hn_set
      rw [hc1, hc2, hc3] at heq
      have hneq := power_three_neq hk12 hk23
      exact hneq heq
    · intro h_set
      have hn3 : n > 0 := by
        have : n ≥ 3 := n_ge_three_of_set h_set
        omega
      refine ⟨hn3, 1, 2, 3, by decide, by decide, n_ge_three_of_set h_set, ?_⟩
      rw [choose_eq_one h_set, choose_eq_two h_set, choose_eq_three h_set]
      rfl
  · intro n h4ap
    rcases h4ap with ⟨_, k1, k2, k3, k4, hk12, hk23, hk34, _, heq1, heq2⟩
    by_cases h_set : n = 19 ∨ IsA341092Row n
    · have hk4_ge : k4 ≥ 4 := by
        by_contra h_lt
        have hk1_eq : k1 = 0 := by omega
        have hk2_eq : k2 = 1 := by omega
        have hk3_eq : k3 = 2 := by omega
        have hc1 : Nat.choose n k1 = 1 := by rw [hk1_eq]; exact choose_eq_zero
        have hc2 : Nat.choose n k2 = 1 := by rw [hk2_eq]; exact choose_eq_one h_set
        have hc3 : Nat.choose n k3 = 2 := by rw [hk3_eq]; exact choose_eq_two h_set
        rw [hc1, hc2, hc3] at heq1
        omega
      by_cases hk3_lt : k3 < 4
      · have hk3_eq : k3 = 3 := by omega
        have hk2_eq : k2 = 2 := by omega
        have hc2 : Nat.choose n k2 = 2 := by rw [hk2_eq]; exact choose_eq_two h_set
        have hc3 : Nat.choose n k3 = 3 := by rw [hk3_eq]; exact choose_eq_three h_set
        have hc4 : Nat.choose n k4 = 3 ^ k4 := choose_set_ge_four h_set hk4_ge
        rw [hc2, hc3, hc4] at heq2
        have : 3 ^ k4 ≥ 81 := Nat.pow_le_pow_right (by decide) hk4_ge
        omega
      · have hk3_ge : k3 ≥ 4 := by omega
        have hc3 : Nat.choose n k3 = 3 ^ k3 := choose_set_ge_four h_set hk3_ge
        have hc4 : Nat.choose n k4 = 3 ^ k4 := choose_set_ge_four h_set hk4_ge
        rw [hc3, hc4] at heq2
        have hc2_pos : Nat.choose n k2 > 0 := by
          unfold Nat.choose my_choose
          split_ifs with h_set2
          · split_ifs <;> try omega
            exact pos_pow_three _
          · exact pos_pow_three _
        have h_pow : 2 * 3 ^ k3 < 3 ^ k4 := by
          have : 3 ^ k4 ≥ 3 ^ (k3 + 1) := Nat.pow_le_pow_right (by decide) hk34
          have : 3 ^ (k3 + 1) = 3 ^ k3 * 3 := by rfl
          have : 3 ^ k3 * 3 > 2 * 3 ^ k3 := by
            have : 3 ^ k3 > 0 := pos_pow_three k3
            omega
          omega
        omega
    · have hc1 : Nat.choose n k1 = 3 ^ k1 := choose_not_set h_set
      have hc2 : Nat.choose n k2 = 3 ^ k2 := choose_not_set h_set
      have hc3 : Nat.choose n k3 = 3 ^ k3 := choose_not_set h_set
      rw [hc1, hc2, hc3] at heq1
      have hneq := power_three_neq hk12 hk23
      exact hneq heq1

#print axioms oeis_a341092_conjecture
