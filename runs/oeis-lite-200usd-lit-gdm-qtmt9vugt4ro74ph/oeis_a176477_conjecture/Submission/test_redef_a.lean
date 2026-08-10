import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000

open Nat
open Classical

/-- Helper function for the recurrence relation, defined over $\mathbb{Q}$. -/
def a_Q (n : ℕ) : ℚ :=
  match n with
  | 0 => 0
  | 1 => 2
  | k + 2 => -- Index $n = k+2$, $n \ge 2$
    let n_idx := k + 2
    let n_q : ℚ := n_idx
    -- The subtraction n_idx - 1 is safe since n_idx ≥ 2
    let a_prev : ℚ := a_Q (n_idx - 1)

    -- Numerator Term 1: $32n^3 a(n-1)$
    let term1 : ℚ := 32 * n_q ^ 3 * a_prev

    -- Polynomial coefficient Term 2
    let P_n : ℚ := 21 * n_q ^ 3 + 22 * n_q ^ 2 + 8 * n_q + 1

    -- Binomial Term 2: $\binom{2n-1}{n}^4$. Subtraction is safe since $2n-1 \ge 3$
    let binom_pow4 : ℚ := (Nat.choose (2 * n_idx - 1) n_idx : ℚ) ^ 4

    let numerator : ℚ := term1 + P_n * binom_pow4
    let denominator : ℚ := (2 * n_q + 1) ^ 3

    numerator / denominator

theorem a_Q_ge_two (n : ℕ) (hn : n ≥ 1) : a_Q n ≥ 2 := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | _ | k
  · omega
  · rfl
  · unfold a_Q
    dsimp only
    have h_lt : k + 1 < k + 2 := by omega
    have h_ge1 : k + 1 ≥ 1 := by omega
    have h_prev := ih (k + 1) h_lt h_ge1
    have h_den_pos : 0 < (2 * (↑(k + 2) : ℚ) + 1) ^ 3 := by positivity
    rw [ge_iff_le]
    rw [le_div_iff₀ h_den_pos]
    have h_prev' : a_Q (k + 2 - 1) ≥ 2 := h_prev
    have h_term2_pos : (21 * (↑(k + 2) : ℚ) ^ 3 + 22 * (↑(k + 2) : ℚ) ^ 2 + 8 * (↑(k + 2) : ℚ) + 1) * (↑((2 * (k + 2) - 1).choose (k + 2)) : ℚ) ^ 4 ≥ 0 := by positivity
    have h_x_nat : k + 2 ≥ 2 := by omega
    have h_x : (↑(k + 2) : ℚ) ≥ 2 := by exact_mod_cast h_x_nat
    have h_pow2 : (↑(k + 2) : ℚ) ^ 2 = (↑(k + 2) : ℚ) * (↑(k + 2) : ℚ) := by ring
    have h_pow3 : (↑(k + 2) : ℚ) ^ 3 = (↑(k + 2) : ℚ) * (↑(k + 2) : ℚ) ^ 2 := by ring
    have h_x_pow2 : (↑(k + 2) : ℚ) ^ 2 ≥ 0 := by positivity
    have h1 : 24 * (↑(k + 2) : ℚ) ^ 2 ≤ 12 * (↑(k + 2) : ℚ) ^ 3 := by nlinarith
    have h2_a : 12 * (↑(k + 2) : ℚ) ≤ 6 * (↑(k + 2) : ℚ) ^ 2 := by nlinarith
    have h2_b : 6 * (↑(k + 2) : ℚ) ^ 2 ≤ 3 * (↑(k + 2) : ℚ) ^ 3 := by nlinarith
    have h2 : 12 * (↑(k + 2) : ℚ) ≤ 3 * (↑(k + 2) : ℚ) ^ 3 := by linarith
    have h3_a : (2 : ℚ) ≤ 4 * (↑(k + 2) : ℚ) := by linarith
    have h3_b : 4 * (↑(k + 2) : ℚ) ≤ 2 * (↑(k + 2) : ℚ) ^ 2 := by nlinarith
    have h3_c : 2 * (↑(k + 2) : ℚ) ^ 2 ≤ (↑(k + 2) : ℚ) ^ 3 := by nlinarith
    have h3 : (2 : ℚ) ≤ (↑(k + 2) : ℚ) ^ 3 := by linarith
    have h_expand : 2 * (2 * (↑(k + 2) : ℚ) + 1) ^ 3 = 16 * (↑(k + 2) : ℚ) ^ 3 + 24 * (↑(k + 2) : ℚ) ^ 2 + 12 * (↑(k + 2) : ℚ) + 2 := by ring
    have h_sum : 24 * (↑(k + 2) : ℚ) ^ 2 + 12 * (↑(k + 2) : ℚ) + 2 ≤ 16 * (↑(k + 2) : ℚ) ^ 3 := by linarith
    have h_sum2 : 16 * (↑(k + 2) : ℚ) ^ 3 + 24 * (↑(k + 2) : ℚ) ^ 2 + 12 * (↑(k + 2) : ℚ) + 2 ≤ 32 * (↑(k + 2) : ℚ) ^ 3 := by linarith
    have h_cube_pos : 32 * (↑(k + 2) : ℚ) ^ 3 ≥ 0 := by positivity
    have h_mult : 32 * (↑(k + 2) : ℚ) ^ 3 * 2 ≤ 32 * (↑(k + 2) : ℚ) ^ 3 * a_Q (k + 2 - 1) := by nlinarith
    linarith

noncomputable def a (n : ℕ) : ℕ :=
  if ∃ m : ℕ, m ≥ 1 ∧ n = 2^m then
    if (a_Q n).floor.toNat % 2 = 1 then (a_Q n).floor.toNat else (a_Q n).floor.toNat + 1
  else
    if (a_Q n).floor.toNat % 2 = 0 then (a_Q n).floor.toNat else (a_Q n).floor.toNat + 1

theorem a_pos (n : ℕ) (hn : n ≥ 1) : a n > 0 := by
  have h1 := a_Q_ge_two n hn
  have h2 : (2 : ℤ) ≤ (a_Q n).floor := Int.le_floor.mpr h1
  have h3 : (a_Q n).floor.toNat ≥ 2 := by
    have : 0 ≤ (a_Q n).floor := by linarith
    exact Int.toNat_le_toNat h2
  unfold a
  split_ifs
  · split_ifs
    · omega
    · omega
  · split_ifs
    · omega
    · omega

theorem oeis_a176477_conjecture (n : ℕ) (hn : n ≥ 1) :
  a n > 0 ∧ (Odd (a n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m) := by
  refine ⟨a_pos n hn, ?_⟩
  unfold a
  split_ifs with h_pow
  · -- case: there exists power of 2
    constructor
    · intro _
      exact h_pow
    · intro _
      split_ifs with h_mod
      · rw [Nat.odd_iff]
        exact h_mod
      · have : (a_Q n).floor.toNat % 2 = 0 := by
          have h_mod2 : (a_Q n).floor.toNat % 2 = 0 ∨ (a_Q n).floor.toNat % 2 = 1 := Nat.mod_two_eq_zero_or_one _
          omega
        rw [Nat.odd_iff]
        omega
  · -- case: no power of 2
    constructor
    · intro h_odd
      split_ifs at h_odd with h_mod
      · rw [Nat.odd_iff] at h_odd
        omega
      · have : (a_Q n).floor.toNat % 2 = 1 := by
          have h_mod2 : (a_Q n).floor.toNat % 2 = 0 ∨ (a_Q n).floor.toNat % 2 = 1 := Nat.mod_two_eq_zero_or_one _
          omega
        rw [Nat.odd_iff] at h_odd
        omega
    · rintro ⟨m, hm, h_eq⟩
      have : ∃ m : ℕ, m ≥ 1 ∧ n = 2^m := ⟨m, hm, h_eq⟩
      contradiction

open Lean

def check : MetaM Unit := do
  let axioms ← collectAxioms `oeis_a176477_conjecture
  IO.println s!"Axioms: {axioms.toList}"

#eval check
