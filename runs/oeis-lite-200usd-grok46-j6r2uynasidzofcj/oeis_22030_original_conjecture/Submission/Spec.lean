import FormalConjectures.Util.ProblemImports
open Nat
open Rat

/--
A022030: A sequence defined by piecewise recurrence relations:
$a(0) = 4$, $a(1) = 16$.
For even $n \ge 2$: $a(n) = \lceil a(n-1)^2 / a(n-2) \rceil - 1$.
For odd $n \ge 3$: $a(n) = \lfloor a(n-1)^2 / a(n-2) \rfloor + 1$.
-/
noncomputable def A022030 (n : ℕ) : ℕ :=
  if n = 0 then 4
  else if n = 1 then 16
  else
    -- For n >= 2, we apply the recurrence relation.
    let a_n_1 := A022030 (n - 1)
    let a_n_2 := A022030 (n - 2)
    let num := a_n_1 ^ 2
    let den := a_n_2

    -- All terms are positive, so den > 0 is guaranteed.

    if n % 2 = 0 then
      -- Even case: ceil(num/den) - 1
      -- The formula for ceil(x/y) in Nat arithmetic is (x + y - 1) / y.
      (num + den - 1) / den - 1
    else
      -- Odd case: floor(num/den) + 1
      -- The formula for floor(x/y) in Nat is x / y.
      (num / den) + 1
termination_by n

-- Define the sequence from the "original definition" cited in the conjecture.
/--
The sequence $b_n$ defined by the original rule for A022030:
$b(0) = 4$, $b(1) = 16$.
$b(n+2)$ is the greatest integer such that $b(n+2) / b(n+1) < b(n+1) / b(n)$.
This is equivalent to $b(n+2) = \lceil b(n+1)^2 / b(n) \rceil - 1$.
-/
noncomputable def A022030_original (n : ℕ) : ℕ :=
  if h0 : n = 0 then 4
  else if h1 : n = 1 then 16
  else
    -- We formalize b(n+2) = ceil(b(n+1)^2 / b(n)) - 1.
    let b_n_1 := A022030_original (n - 1)
    let b_n_2 := A022030_original (n - 2)

    let num := b_n_1 ^ 2
    let den := b_n_2

    -- Nat.div_ceil (x / y) is (x + y - 1) / y, which simplifies to `num / den + 1` when den does not divide num
    -- The expression Nat.div_ceil num den - 1 is `(num + den - 1) / den - 1`
    (num + den - 1) / den - 1
termination_by n

/-- Linear recurrence sequence associated to the generating function $(4-x^2)/(1-4x+x^3)$. -/
def L : ℕ → ℕ
  | 0 => 4
  | 1 => 16
  | 2 => 63
  | n + 3 => 4 * L (n + 2) - L n

lemma L_zero : L 0 = 4 := rfl
lemma L_one : L 1 = 16 := rfl
lemma L_two : L 2 = 63 := rfl
lemma L_succ_three (n : ℕ) : L (n + 3) = 4 * L (n + 2) - L n := rfl

/-- Growth: `L (n+1) ≥ 3 L n`. This also guarantees the Nat subtraction in `L` does not underflow. -/
lemma L_grow (n : ℕ) : 3 * L n ≤ L (n + 1) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match n with
    | 0 =>
      simp [L_zero, L_one]
    | 1 =>
      simp [L_one, L_two]
    | n + 2 =>
      -- Goal: 3 * L (n+2) ≤ L (n+3) = 4 * L (n+2) - L n
      have hn : 3 * L n ≤ L (n + 1) := ih n (by omega)
      have hn1 : 3 * L (n + 1) ≤ L (n + 2) := ih (n + 1) (by omega)
      have hle : L n ≤ L (n + 2) := by
        calc
          L n ≤ 3 * L n := Nat.le_mul_of_pos_left _ (by omega)
          _ ≤ L (n + 1) := hn
          _ ≤ 3 * L (n + 1) := Nat.le_mul_of_pos_left _ (by omega)
          _ ≤ L (n + 2) := hn1
      have hle4 : L n ≤ 4 * L (n + 2) := by omega
      rw [L_succ_three]
      omega

lemma L_pos (n : ℕ) : 0 < L n := by
  induction n with
  | zero => simp [L_zero]
  | succ n ih =>
    have := L_grow n
    omega

lemma L_mono (n : ℕ) : L n ≤ L (n + 1) := by
  have := L_grow n
  have := L_pos n
  omega

lemma L_no_underflow (n : ℕ) : L n ≤ 4 * L (n + 2) := by
  have h1 := L_mono n
  have h2 := L_mono (n + 1)
  rw [show n + 2 = (n + 1) + 1 by omega]
  omega

/-- The recurrence lifts to the integers. -/
lemma L_rec_int (n : ℕ) : (L (n + 3) : ℤ) = 4 * (L (n + 2) : ℤ) - (L n : ℤ) := by
  have h := L_no_underflow n
  rw [L_succ_three]
  omega

/-- Cassini-like determinant `δ n = L(n+1)² - L(n+2) L n`. -/
def δ (n : ℕ) : ℤ := (L (n + 1) : ℤ) ^ 2 - (L (n + 2) : ℤ) * (L n : ℤ)

lemma δ_zero : δ 0 = 4 := by
  simp [δ, L_zero, L_one, L_two]

lemma L_three : L 3 = 248 := by
  rw [L_succ_three, L_two, L_zero]

lemma L_four : L 4 = 976 := by
  rw [show 4 = 1 + 3 by omega, L_succ_three, L_three, L_one]

lemma δ_one : δ 1 = 1 := by
  simp [δ, L_one, L_two, L_three]

lemma δ_two : δ 2 = 16 := by
  simp [δ, L_two, L_three, L_four]

/-- The sequence `δ` satisfies `δ(n+3) = 4 δ(n+1) + δ n`. -/
lemma δ_rec (n : ℕ) : δ (n + 3) = 4 * δ (n + 1) + δ n := by
  simp only [δ]
  have e3 : (L (n + 3) : ℤ) = 4 * (L (n + 2) : ℤ) - (L n : ℤ) := L_rec_int n
  have e4 : (L (n + 4) : ℤ) = 4 * (L (n + 3) : ℤ) - (L (n + 1) : ℤ) := by
    simpa [show n + 1 + 3 = n + 4 by omega, show n + 1 + 2 = n + 3 by omega]
      using L_rec_int (n + 1)
  have e5 : (L (n + 5) : ℤ) = 4 * (L (n + 4) : ℤ) - (L (n + 2) : ℤ) := by
    simpa [show n + 2 + 3 = n + 5 by omega, show n + 2 + 2 = n + 4 by omega]
      using L_rec_int (n + 2)
  have h4 : n + 3 + 1 = n + 4 := by omega
  have h5 : n + 3 + 2 = n + 5 := by omega
  rw [h4, h5, e5, e4, e3]
  ring

/-- `0 < δ n ≤ L n` for every `n`. -/
lemma δ_bounds (n : ℕ) : 0 < δ n ∧ δ n ≤ (L n : ℤ) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match n with
    | 0 =>
      rw [δ_zero, L_zero]; constructor <;> norm_num
    | 1 =>
      rw [δ_one, L_one]; constructor <;> norm_num
    | 2 =>
      rw [δ_two, L_two]; constructor <;> norm_num
    | n + 3 =>
      have hn := ih n (by omega)
      have hn1 := ih (n + 1) (by omega)
      rw [δ_rec n]
      constructor
      · linarith
      · -- 4 * δ(n+1) + δ n ≤ L (n+3) = 4 L(n+2) - L n
        have hrec := L_rec_int n
        have hgrow1 := L_grow (n + 1)
        have hgrow0 := L_grow n
        have hpos := L_pos n
        -- 4 * δ(n+1) + δ n ≤ 4 * L(n+1) + L n
        have : 4 * δ (n + 1) + δ n ≤ 4 * (L (n + 1) : ℤ) + (L n : ℤ) := by
          linarith
        -- and 4 L(n+1) + L n ≤ 4 L(n+2) - L n
        have hle : 4 * (L (n + 1) : ℤ) + (L n : ℤ) ≤ 4 * (L (n + 2) : ℤ) - (L n : ℤ) := by
          -- 2 L(n+1) + L n ≤ 2 L(n+2)
          have : (L (n + 2) : ℤ) ≥ 3 * (L (n + 1) : ℤ) := by exact_mod_cast hgrow1
          have : (L (n + 1) : ℤ) ≥ 3 * (L n : ℤ) := by exact_mod_cast hgrow0
          linarith
        have : (L (n + 3) : ℤ) = 4 * (L (n + 2) : ℤ) - (L n : ℤ) := hrec
        linarith

/-- The linear sequence satisfies the original ceil recurrence. -/
lemma L_ceil_rec (n : ℕ) :
    L (n + 2) = (L (n + 1) ^ 2 + L n - 1) / L n - 1 := by
  have hpos : 0 < L n := L_pos n
  obtain ⟨hδpos, hδle⟩ := δ_bounds n
  have hnn : 0 ≤ δ n := le_of_lt hδpos
  have hle : L (n + 2) * L n ≤ L (n + 1) ^ 2 := by
    have : (L (n + 2) : ℤ) * (L n : ℤ) ≤ (L (n + 1) : ℤ) ^ 2 := by
      simp only [δ] at hδpos
      linarith
    exact_mod_cast this
  have hdecomp : L (n + 1) ^ 2 = L (n + 2) * L n + (δ n).toNat := by
    zify
    rw [Int.toNat_of_nonneg hnn, δ]
    ring
  have hdpos : 1 ≤ (δ n).toNat := by
    have hne : (δ n).toNat ≠ 0 := by
      intro h0
      have : δ n ≤ 0 := Int.toNat_eq_zero.mp h0
      linarith
    omega
  have hdle : (δ n).toNat ≤ L n := Int.toNat_le.mpr hδle
  -- L(n+1)² + L n - 1 = (L(n+2) + 1) * L n + (δ.toNat - 1)
  -- and 0 ≤ δ.toNat - 1 < L n, so the quotient is L(n+2) + 1.
  have hdiv : (L (n + 1) ^ 2 + L n - 1) / L n = L (n + 2) + 1 := by
    have hrewrite :
        L (n + 1) ^ 2 + L n - 1 = (L (n + 2) + 1) * L n + ((δ n).toNat - 1) := by
      have hA : L (n + 1) ^ 2 + L n - 1 + 1 = L (n + 1) ^ 2 + L n := by
        have : 1 ≤ L (n + 1) ^ 2 + L n := by
          have := L_pos n
          omega
        omega
      have hB : (L (n + 2) + 1) * L n + ((δ n).toNat - 1) + 1 =
          (L (n + 2) + 1) * L n + (δ n).toNat := by
        omega
      have hsum : L (n + 1) ^ 2 + L n - 1 + 1 =
          (L (n + 2) + 1) * L n + ((δ n).toNat - 1) + 1 := by
        rw [hA, hB, hdecomp]
        ring
      exact Nat.add_right_cancel hsum
    rw [hrewrite]
    have hlt : (δ n).toNat - 1 < L n := by omega
    rw [mul_comm (L (n + 2) + 1), Nat.mul_add_div hpos, Nat.div_eq_of_lt hlt]
  omega

lemma A022030_original_zero : A022030_original 0 = 4 := by
  simp [A022030_original]

lemma A022030_original_one : A022030_original 1 = 16 := by
  simp [A022030_original]

lemma A022030_original_succ_two (n : ℕ) :
    A022030_original (n + 2) =
      (A022030_original (n + 1) ^ 2 + A022030_original n - 1) /
        A022030_original n - 1 := by
  rw [A022030_original]
  have h0 : n + 2 ≠ 0 := by omega
  have h1 : n + 2 ≠ 1 := by omega
  rw [dif_neg h0, dif_neg h1]
  simp

/-- The original sequence coincides with the linear recurrence sequence. -/
lemma A022030_original_eq_L (n : ℕ) : A022030_original n = L n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match n with
    | 0 => rw [A022030_original_zero, L_zero]
    | 1 => rw [A022030_original_one, L_one]
    | n + 2 =>
      rw [A022030_original_succ_two, L_ceil_rec]
      rw [ih (n + 1) (by omega), ih n (by omega)]

/--
Conjecture (from OEIS comment C A022030 22030):
This original definition would lead to sequence 4, 16, 63, 248, 976, 3841, ...
which agrees to over 2000 terms with the conjectured generating function
$G(x) = (4 - x^2)/(1 - 4x + x^3)$.

This generating function corresponds to the linear recurrence relation:
$b_0 = 4, b_1 = 16, b_2 = 63$.
For $n \ge 3$, $b_n = 4 b_{n-1} - b_{n-3}$.
-/
theorem oeis_22030_original_conjecture (n : ℕ) :
  A022030_original n = (
    if n = 0 then 4
    else if n = 1 then 16
    else if n = 2 then 63
    else
      4 * (A022030_original (n - 1)) - (A022030_original (n - 3))
  ) := by
  rw [A022030_original_eq_L]
  match n with
  | 0 => simp [L_zero]
  | 1 => simp [L_one]
  | 2 => simp [L_two]
  | n + 3 =>
    have h0 : n + 3 ≠ 0 := by omega
    have h1 : n + 3 ≠ 1 := by omega
    have h2 : n + 3 ≠ 2 := by omega
    simp only [h0, h1, h2, ↓reduceIte]
    rw [A022030_original_eq_L, A022030_original_eq_L, L_succ_three]
    simp


