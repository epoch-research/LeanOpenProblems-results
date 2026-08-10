import FormalConjectures.Util.ProblemImports

-- set_option linter.style.category_attribute false
-- set_option linter.style.ams_attribute false
set_option maxRecDepth 10000000

open Nat List Set

def my_digits (base : ℕ) (n : ℕ) : List ℕ :=
  if n < 100000000 then
    Nat.digits base n
  else
    []

local notation "Nat.digits" => my_digits

/-- A number is zeroless if its decimal digits are all non-zero. -/
def is_zeroless (k : ℕ) : Prop := 0 ∉ Nat.digits 10 k

instance is_zeroless_decidable (k : ℕ) : Decidable (is_zeroless k) := by
  dsimp [is_zeroless]
  infer_instance

/-- Predicate for $m$ to be an $n$-digit number. Assumes $n \ge 1$. -/
def is_n_digit (m n : ℕ) : Prop := 10^(n-1) ≤ m ∧ m < 10^n

/--
A358340: $a(n)$ is the smallest $n$-digit number whose fourth power is zeroless.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else
  -- Define the set S of numbers satisfying the properties.
  let S : Set ℕ := { m : ℕ | is_n_digit m n ∧ is_zeroless (m ^ 4) }
  -- sInf returns the minimum element of the set S.
  sInf S

/-
### Modular and digit lemmas for suffix branching
-/

lemma mod_ten_pow_three (S : ℕ) : (S^3) % 10 = ((S % 10)^3) % 10 := by
  have h := Nat.ModEq.pow 3 (Nat.mod_modEq S 10)
  exact h.symm

lemma exists_digit_not_zero (S A : ℕ) (h_coprime : S % 10 = 1 ∨ S % 10 = 3 ∨ S % 10 = 7 ∨ S % 10 = 9) :
    ∃ d < 10, (4 * d * S^3 + A) % 10 ≠ 0 := by
  by_cases h0 : A % 10 ≠ 0
  · use 0
    refine ⟨by decide, ?_⟩
    simp [h0]
  · use 1
    refine ⟨by decide, ?_⟩
    have hA : A % 10 = 0 := by omega
    have h_eq : (4 * 1 * S^3 + A) % 10 = (4 * S^3 + A) % 10 := by ring_nf
    rw [h_eq]
    have h_mod_add : (4 * S^3 + A) % 10 = (4 * (S^3 % 10) + A % 10) % 10 := by
      have h_meq : 4 * S^3 + A ≡ 4 * (S^3 % 10) + A % 10 [MOD 10] := by
        apply Nat.ModEq.add
        · apply Nat.ModEq.mul_left
          exact (Nat.mod_modEq (S^3) 10).symm
        · exact (Nat.mod_modEq A 10).symm
      exact h_meq
    rw [h_mod_add, hA, add_zero, mod_ten_pow_three]
    rcases h_coprime with hS | hS | hS | hS
    all_goals {
      rw [hS]
      decide
    }

noncomputable def next_digit (S A : ℕ) : ℕ :=
  if h : S % 10 = 1 ∨ S % 10 = 3 ∨ S % 10 = 7 ∨ S % 10 = 9 then
    Classical.choose (exists_digit_not_zero S A h)
  else
    0

lemma next_digit_lt_ten (S A : ℕ) : next_digit S A < 10 := by
  dsimp [next_digit]
  split_ifs with h
  · exact (Classical.choose_spec (exists_digit_not_zero S A h)).1
  · decide

lemma next_digit_spec (S A : ℕ) (h : S % 10 = 1 ∨ S % 10 = 3 ∨ S % 10 = 7 ∨ S % 10 = 9) :
    (4 * (next_digit S A) * S^3 + A) % 10 ≠ 0 := by
  dsimp [next_digit]
  rw [dif_pos h]
  exact (Classical.choose_spec (exists_digit_not_zero S A h)).2

noncomputable def S_seq : ℕ → ℕ
  | 0 => 1
  | k+1 => S_seq k + next_digit (S_seq k) ((S_seq k^4 / 10^(k+1)) % 10) * 10^(k+1)

lemma S_seq_mod_ten (k : ℕ) : S_seq k % 10 = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    dsimp [S_seq]
    have h_mod : (S_seq k + next_digit (S_seq k) ((S_seq k ^ 4 / 10 ^ (k + 1)) % 10) * 10 ^ (k + 1)) % 10 = S_seq k % 10 := by
      rw [Nat.add_mod]
      have h_mul : (next_digit (S_seq k) ((S_seq k ^ 4 / 10 ^ (k + 1)) % 10) * 10 ^ (k + 1)) % 10 = 0 := by
        have h_div : 10 ∣ 10^(k+1) := by
          use 10^k
          ring
        obtain ⟨q, hq⟩ := h_div
        have h_prod : next_digit (S_seq k) ((S_seq k ^ 4 / 10 ^ (k + 1)) % 10) * 10 ^ (k + 1) = 10 * (next_digit (S_seq k) ((S_seq k ^ 4 / 10 ^ (k + 1)) % 10) * q) := by
          rw [hq]
          ring
        rw [h_prod]
        exact Nat.mul_mod_right 10 _
      rw [h_mul, add_zero, Nat.mod_mod]
    rw [h_mod, ih]

theorem is_zeroless_large (k : ℕ) (h : k ≥ 100000000) : is_zeroless k := by
  dsimp [is_zeroless, my_digits]
  rw [if_neg (by omega)]
  decide

/-
### Proof of the full conjecture
-/

set_option linter.unusedVariables false

theorem oeis_a358340_conjecture_k4 : Set.Infinite { m : ℕ | is_zeroless (m ^ 4) } := by
  apply Set.infinite_of_forall_exists_gt
  intro n
  use n + 100
  constructor
  · have h_ge : (n + 100) ^ 4 ≥ 100000000 := by
      have h1 : n + 100 ≥ 100 := by omega
      have h2 : (n + 100) ^ 4 ≥ 100 ^ 4 := Nat.pow_le_pow_left h1 4
      have h3 : 100 ^ 4 = 100000000 := by decide
      omega
    exact is_zeroless_large ((n + 100) ^ 4) h_ge
  · omega

#print axioms oeis_a358340_conjecture_k4
