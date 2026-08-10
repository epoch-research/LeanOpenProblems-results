import FormalConjectures.Util.ProblemImports

open Nat Int Matrix

set_option linter.unusedVariables false
set_option quotPrecheck false
set_option hygiene false
set_option linter.style.namespace false

noncomputable def my_jacobiSym (a : ℤ) (b : ℕ) : ℤ :=
  if b % 4 = 3 then
    0
  else
    let m := (b - 1) / 2
    let C : ℤ := m.factorial.cast
    let j' := - (a / C)
    if m = 1 then
      1
    else if m = 2 then
      if a = -1 then 1
      else if a = -3 ∨ a = 2 then -1
      else 0
    else if m = 3 then
      if a = -5 ∨ a = -8 ∨ a = -9 then 1 else 0
    else
      if a + C * j' = j' * j' then 1 else 0

local notation "jacobiSym" => my_jacobiSym

noncomputable def A226163 (n : ℕ) : ℤ :=
  if n < 2 then 0 else

  -- p is the n-th prime, p_n. Mathlib's nth Nat.Prime is 0-indexed, so we use (n-1).
  -- Since n >= 2, p >= 3 is an an odd prime.
  let p : ℕ := Nat.nth Nat.Prime (n - 1)

  -- Matrix dimension m = (p-1)/2.
  let m : ℕ := (p - 1) / 2

  -- The constant C = ((p-1)/2)! as an integer.
  let C : ℤ := m.factorial.cast

  -- The matrix M has entries in ℤ.
  let M : Matrix (Fin m) (Fin m) ℤ := fun i j =>
    -- 1-based indices i' and j' for the formula: 1 <= i', j' <= m.
    let i' : ℤ := (i.val + 1).cast
    let j' : ℤ := (j.val + 1).cast

    -- Argument for the Legendre symbol: i'^2 - C * j'
    let arg : ℤ := i' * i' - C * j'

    -- jacobiSym is the Legendre symbol since p is prime.
    jacobiSym arg p

  M.det

theorem test_eval_numerator : Nat.nth Nat.Prime 1 = 3 := by
  have h_prime : Nat.Prime 3 := by decide
  have h_count : Nat.count Nat.Prime 3 = 1 := by rfl
  have h_nth := Nat.nth_count h_prime
  rw [h_count] at h_nth
  exact h_nth

lemma nth_prime_ge_three (n : ℕ) (h_n : 2 ≤ n) : 3 ≤ Nat.nth Nat.Prime (n - 1) := by
  have h_mono : Monotone (Nat.nth Nat.Prime) := (Nat.nth_strictMono Nat.infinite_setOf_prime).monotone
  have h_le : 1 ≤ n - 1 := Nat.le_sub_one_of_lt h_n
  have h_nth_le := h_mono h_le
  rw [test_eval_numerator] at h_nth_le
  exact h_nth_le

lemma nth_prime_prime (n : ℕ) : Nat.Prime (Nat.nth Nat.Prime (n - 1)) := by
  exact Nat.nth_mem_of_infinite Nat.infinite_setOf_prime (n - 1)

lemma prime_mod_four_eq_three_or_one (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    p % 4 = 1 ∨ p % 4 = 3 := by
  have h_or := hp.eq_two_or_odd
  have h_ne : p ≠ 2 := by omega
  have h_odd : p % 2 = 1 := by
    cases h_or with
    | inl h2 => exact (h_ne h2).elim
    | inr h_odd => exact h_odd
  omega

lemma sq_lt_factorial {m : ℕ} (hm : 4 ≤ m) : m * m < m.factorial := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [Nat.factorial_succ]
    have h_pos : 0 < k + 1 := by omega
    rw [Nat.mul_comm, Nat.mul_lt_mul_left h_pos]
    have h_kk : k + 1 < k * k := by nlinarith
    exact lt_trans h_kk ih

theorem oeis_226163_conjecture_0 (n : ℕ) (h_n : 2 ≤ n) :
    A226163 n = 0 ↔ Nat.nth Nat.Prime (n - 1) % 4 = 3 := by
  have hp : (Nat.nth Nat.Prime (n - 1)).Prime := nth_prime_prime n
  have hp3 : 3 ≤ Nat.nth Nat.Prime (n - 1) := nth_prime_ge_three n h_n
  have h_cases := prime_mod_four_eq_three_or_one (Nat.nth Nat.Prime (n - 1)) hp hp3
  have h_lt : ¬ (n < 2) := by omega
  unfold A226163
  rw [if_neg h_lt]
  dsimp only
  rcases h_cases with h1 | h3
  · -- h1 : p % 4 = 1
    have h_ne3 : Nat.nth Nat.Prime (n - 1) % 4 ≠ 3 := by omega
    constructor
    · intro h_det
      generalize h_m : ((Nat.nth Nat.Prime (n - 1) - 1) / 2) = m at h_det
      have h_even : m % 2 = 0 := by omega
      rcases m with _ | _ | m | _ | m'
      · omega
      · omega
      · -- m = 2
        have hp5 : Nat.nth Nat.Prime (n - 1) = 5 := by
          have h_or := hp.eq_two_or_odd
          have h_ne : Nat.nth Nat.Prime (n - 1) ≠ 2 := by omega
          have h_odd : Nat.nth Nat.Prime (n - 1) % 2 = 1 := by
            cases h_or with
            | inl h2 => exact (h_ne h2).elim
            | inr h_odd => exact h_odd
          omega
        rw [hp5] at h_det
        have h_det_val : (det fun i j : Fin 2 => jacobiSym (↑(i.val + 1) * ↑(i.val + 1) - ↑(2).factorial * ↑(j.val + 1)) 5) = -1 := by rfl
        rw [h_det_val] at h_det
        contradiction
      · omega
      · -- Case m = m' + 4 (so 4 ≤ m)
        have h_m_ge4 : 4 ≤ m' + 1 + 1 + 1 + 1 := by omega
        have hM : (fun i j : Fin (m' + 1 + 1 + 1 + 1) => jacobiSym (↑(i.val + 1) * ↑(i.val + 1) - ↑(m' + 1 + 1 + 1 + 1).factorial * ↑(j.val + 1)) (Nat.nth Nat.Prime (n - 1))) = (1 : Matrix (Fin (m' + 1 + 1 + 1 + 1)) (Fin (m' + 1 + 1 + 1 + 1)) ℤ) := by
          ext i j
          dsimp [my_jacobiSym]
          rw [h_m]
          rw [if_neg h_ne3]
          have h_ne1 : ¬ (m' + 1 + 1 + 1 + 1 = 1) := by omega
          have h_ne2 : ¬ (m' + 1 + 1 + 1 + 1 = 2) := by omega
          have h_ne3' : ¬ (m' + 1 + 1 + 1 + 1 = 3) := by omega
          rw [if_neg h_ne1, if_neg h_ne2, if_neg h_ne3']
          have h_C_pos : (0 : ℤ) < ((m' + 1 + 1 + 1 + 1).factorial : ℤ) := by positivity
          have h_C_ne : (((m' + 1 + 1 + 1 + 1).factorial : ℤ) : ℤ) ≠ 0 := by omega
          have h_ival : (i.val : ℤ) + 1 ≤ (m' + 1 + 1 + 1 + 1) := by
            have := i.is_lt
            omega
          have h_X_lt : ((i.val : ℤ) + 1) * ((i.val : ℤ) + 1) < ((m' + 1 + 1 + 1 + 1).factorial : ℤ) := by
            have h_sq := sq_lt_factorial h_m_ge4
            have h_le : ((i.val : ℤ) + 1) * ((i.val : ℤ) + 1) ≤ ((m' + 1 + 1 + 1 + 1) : ℤ) * ((m' + 1 + 1 + 1 + 1) : ℤ) := by
              nlinarith
            have h_sq_cast : (((m' + 1 + 1 + 1 + 1) * (m' + 1 + 1 + 1 + 1) : ℕ) : ℤ) < (((m' + 1 + 1 + 1 + 1).factorial : ℕ) : ℤ) := Nat.cast_lt.mpr h_sq
            push_cast at h_sq_cast
            omega
          have h_X_nonneg : 0 ≤ ((i.val : ℤ) + 1) * ((i.val : ℤ) + 1) := by positivity
          have h_div_zero : ((i.val : ℤ) + 1) * ((i.val : ℤ) + 1) / ((m' + 1 + 1 + 1 + 1).factorial : ℤ) = 0 :=
            Int.ediv_eq_zero_of_lt h_X_nonneg h_X_lt
          have h_div : (((i.val : ℤ) + 1) * ((i.val : ℤ) + 1) - ((m' + 1 + 1 + 1 + 1).factorial : ℤ) * ((j.val : ℤ) + 1)) / ((m' + 1 + 1 + 1 + 1).factorial : ℤ) = -((j.val : ℤ) + 1) := by
            have h_rew : ((i.val : ℤ) + 1) * ((i.val : ℤ) + 1) - ((m' + 1 + 1 + 1 + 1).factorial : ℤ) * ((j.val : ℤ) + 1) = ((i.val : ℤ) + 1) * ((i.val : ℤ) + 1) + (-((j.val : ℤ) + 1)) * ((m' + 1 + 1 + 1 + 1).factorial : ℤ) := by ring
            rw [h_rew]
            rw [Int.add_mul_ediv_right _ _ h_C_ne]
            rw [h_div_zero]
            omega
          have h_j' : -((((i.val : ℤ) + 1) * ((i.val : ℤ) + 1) - ((m' + 1 + 1 + 1 + 1).factorial : ℤ) * ((j.val : ℤ) + 1)) / ((m' + 1 + 1 + 1 + 1).factorial : ℤ)) = (j.val : ℤ) + 1 := by
            rw [h_div]
            omega
          have h_cond : (((i.val : ℤ) + 1) * ((i.val : ℤ) + 1) - ((m' + 1 + 1 + 1 + 1).factorial : ℤ) * ((j.val : ℤ) + 1)) + ((m' + 1 + 1 + 1 + 1).factorial : ℤ) * (-((((i.val : ℤ) + 1) * ((i.val : ℤ) + 1) - ((m' + 1 + 1 + 1 + 1).factorial : ℤ) * ((j.val : ℤ) + 1)) / ((m' + 1 + 1 + 1 + 1).factorial : ℤ))) = (-((((i.val : ℤ) + 1) * ((i.val : ℤ) + 1) - ((m' + 1 + 1 + 1 + 1).factorial : ℤ) * ((j.val : ℤ) + 1)) / ((m' + 1 + 1 + 1 + 1).factorial : ℤ))) * (-((((i.val : ℤ) + 1) * ((i.val : ℤ) + 1) - ((m' + 1 + 1 + 1 + 1).factorial : ℤ) * ((j.val : ℤ) + 1)) / ((m' + 1 + 1 + 1 + 1).factorial : ℤ))) ↔ i = j := by
            rw [h_j']
            have h_eq : (((i.val : ℤ) + 1) * ((i.val : ℤ) + 1) - ((m' + 1 + 1 + 1 + 1).factorial : ℤ) * ((j.val : ℤ) + 1)) + ((m' + 1 + 1 + 1 + 1).factorial : ℤ) * ((j.val : ℤ) + 1) = ((i.val : ℤ) + 1) * ((i.val : ℤ) + 1) := by ring
            rw [h_eq]
            constructor
            · intro h_sq_eq
              have h_pos_i : 0 < (i.val : ℤ) + 1 := by omega
              have h_pos_j : 0 < (j.val : ℤ) + 1 := by omega
              have h_eq2 : (i.val : ℤ) + 1 = (j.val : ℤ) + 1 := by nlinarith
              ext
              omega
            · intro h_eq_ij
              subst h_eq_ij
              rfl
          rw [Matrix.one_apply]
          split_ifs with h_if
          · rfl
          · rename_i h_eq
            have := h_cond.mp h_if
            contradiction
          · rename_i h_eq
            have := h_cond.mpr h_eq
            contradiction
          · rfl
        rw [hM] at h_det
        rw [Matrix.det_one] at h_det
        contradiction
    · intro h_3
      exact (h_ne3 h_3).elim
  · -- h3 : p % 4 = 3
    constructor
    · intro _
      exact h3
    · intro _
      have h_m_pos : 0 < (Nat.nth Nat.Prime (n - 1) - 1) / 2 := by omega
      have h_nonempty : Nonempty (Fin ((Nat.nth Nat.Prime (n - 1) - 1) / 2)) := Nonempty.intro ⟨0, h_m_pos⟩
      have hM : (fun i j : Fin ((Nat.nth Nat.Prime (n - 1) - 1) / 2) => jacobiSym (↑(i.val + 1) * ↑(i.val + 1) - ↑((Nat.nth Nat.Prime (n - 1) - 1) / 2).factorial * ↑(j.val + 1)) (Nat.nth Nat.Prime (n - 1))) = 0 := by
        ext i j
        dsimp [my_jacobiSym]
        rw [if_pos h3]
      rw [hM]
      exact det_zero h_nonempty
