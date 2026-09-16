import FormalConjectures.Util.ProblemImports

open Nat Int Finset

-- Auxiliary definitions for Conjecture (i)
def a273021_M : Finset ℕ := {2, 22, 23, 30, 330}
def a273021_S0 : Finset ℕ := {1, 11, 31, 47, 55, 71, 105, 115, 119, 253, 383, 385}

/-- Predicate for $n$ belonging to the set of numbers for which $A273021(n) = 1$. -/
def a273021_is_one_value (n : ℕ) : Prop :=
  n ∈ a273021_S0 ∨
  -- 4^k * m for k >= 0 and m in M
  ∃ k : ℕ, ∃ m : ℕ, m ∈ a273021_M ∧ n = 4^k * m

/--
A273021: Number of ordered ways to write $n$ as $x^2 + y^2 + z^2 + w^2$ with $2xy + yz - zw - wx$ a square, where $w$ is a positive integer and $x,y,z$ are nonnegative integers with $x \le y$.
-/
def A273021 (n : ℕ) : ℕ :=
  let B : ℕ := Nat.sqrt n + 1
  (Finset.range B).sum fun x =>
    (Finset.range B).sum fun y =>
      (Finset.range B).sum fun z =>
        (Finset.range B).sum fun w =>
          -- Primary constraints filtering
          if x*x + y*y + z*z + w*w = n ∧ w > 0 ∧ x ≤ y then
            -- Calculate the quadratic form Q = 2xy + yz - zw - wx as an integer
            let Q : ℤ := 2 * (x : ℤ) * y + (y : ℤ) * z - (z : ℤ) * w - (w : ℤ) * x

            -- Check if Q is a non-negative perfect square.
            if Q ≥ 0 then
              let Q_nat := Q.natAbs
              -- A Nat m is a perfect square iff m.sqrt * m.sqrt = m
              if Q_nat.sqrt * Q_nat.sqrt = Q_nat then 1 else 0
            else
              0
          else
            0

/-- A273021 Conjecture: (i) a(n) > 0 for all n > 0, and a(n) = 1 only for
n = 1, 11, 31, 47, 55, 71, 105, 115, 119, 253, 383, 385, 4^k*m (k = 0,1,2,... and m = 2, 22, 23, 30, 330). -/
theorem A273021_conjecture_i (n : ℕ) (hn : n > 0) :
  A273021 n > 0 ∧ (A273021 n = 1 ↔ a273021_is_one_value n) := by sorry

theorem A273021_conjecture_i.disproof : ¬ (type_of% @A273021_conjecture_i) := by
  intro h
  have h_spec := h 384 (by decide)
  have h_a : A273021 384 = 3 := by native_decide
  rw [h_a] at h_spec
  have h2 : 3 = 1 ↔ a273021_is_one_value 384 := h_spec.2
  have h3 : ¬ (3 = 1) := by decide
  have h4 : ¬ a273021_is_one_value 384 := by
    intro h_one
    rcases h_one with h_in | ⟨k, m, hm, eq_n⟩
    · revert h_in; decide
    · have h_m : ∀ m, m ∈ a273021_M → m = 2 ∨ m = 22 ∨ m = 23 ∨ m = 30 ∨ m = 330 := by decide
      have hm2 := h_m m hm
      rcases hm2 with rfl | rfl | rfl | rfl | rfl
      · have : 384 = 4^k * 2 := eq_n
        have h1 : 192 = 4^k := by omega
        have h_k : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ 4 ≤ k := by omega
        rcases h_k with rfl | rfl | rfl | rfl | hk
        · revert h1; decide
        · revert h1; decide
        · revert h1; decide
        · revert h1; decide
        · have : 4^k ≥ 4^4 := Nat.pow_le_pow_right (by decide) hk
          omega
      · have : 384 = 4^k * 22 := eq_n
        have h_k : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ 4 ≤ k := by omega
        rcases h_k with rfl | rfl | rfl | rfl | hk
        · revert this; decide
        · revert this; decide
        · revert this; decide
        · revert this; decide
        · have : 4^k ≥ 4^4 := Nat.pow_le_pow_right (by decide) hk
          have : 4^k * 22 ≥ 4^4 * 22 := Nat.mul_le_mul_right 22 this
          omega
      · have : 384 = 4^k * 23 := eq_n
        have h_k : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ 4 ≤ k := by omega
        rcases h_k with rfl | rfl | rfl | rfl | hk
        · revert this; decide
        · revert this; decide
        · revert this; decide
        · revert this; decide
        · have : 4^k ≥ 4^4 := Nat.pow_le_pow_right (by decide) hk
          have : 4^k * 23 ≥ 4^4 * 23 := Nat.mul_le_mul_right 23 this
          omega
      · have : 384 = 4^k * 30 := eq_n
        have h_k : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ 4 ≤ k := by omega
        rcases h_k with rfl | rfl | rfl | rfl | hk
        · revert this; decide
        · revert this; decide
        · revert this; decide
        · revert this; decide
        · have : 4^k ≥ 4^4 := Nat.pow_le_pow_right (by decide) hk
          have : 4^k * 30 ≥ 4^4 * 30 := Nat.mul_le_mul_right 30 this
          omega
      · have : 384 = 4^k * 330 := eq_n
        have h_k : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ 4 ≤ k := by omega
        rcases h_k with rfl | rfl | rfl | rfl | hk
        · revert this; decide
        · revert this; decide
        · revert this; decide
        · revert this; decide
        · have : 4^k ≥ 4^4 := Nat.pow_le_pow_right (by decide) hk
          have : 4^k * 330 ≥ 4^4 * 330 := Nat.mul_le_mul_right 330 this
          omega
  have h5 : a273021_is_one_value 384 → 3 = 1 := h2.mpr
  sorry
