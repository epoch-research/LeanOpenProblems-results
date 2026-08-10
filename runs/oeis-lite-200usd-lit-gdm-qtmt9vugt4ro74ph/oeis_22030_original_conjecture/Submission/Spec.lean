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

def LR_Z : ℕ → ℤ
  | 0 => 4
  | 1 => 16
  | 2 => 63
  | n + 3 => 4 * LR_Z (n + 2) - LR_Z n

def D_Z (n : ℕ) : ℤ :=
  if n < 2 then 0
  else LR_Z (n-1) ^ 2 - LR_Z n * LR_Z (n-2)

lemma LR_Z_step1 (m : ℕ) : LR_Z (m + 5) = 4 * LR_Z (m + 4) - LR_Z (m + 2) := rfl

lemma LR_Z_step2 (m : ℕ) : LR_Z (m + 4) = 4 * LR_Z (m + 3) - LR_Z (m + 1) := rfl

lemma LR_Z_step3 (m : ℕ) : LR_Z (m + 3) = 4 * LR_Z (m + 2) - LR_Z m := rfl

lemma D_Z_def (k : ℕ) : D_Z (k + 2) = LR_Z (k + 1) ^ 2 - LR_Z (k + 2) * LR_Z k := by
  have : ¬ (k + 2 < 2) := by omega
  simp [D_Z, this]

lemma D_Z_recurrence (m : ℕ) :
    D_Z (m + 5) = 4 * D_Z (m + 3) + D_Z (m + 2) := by
  -- D_Z (m + 5) is D_Z (m + 3 + 2)
  have h1 : D_Z (m + 5) = LR_Z (m + 4) ^ 2 - LR_Z (m + 5) * LR_Z (m + 3) := by
    have h : m + 5 = (m + 3) + 2 := by rfl
    rw [h, D_Z_def]
  -- D_Z (m + 3) is D_Z (m + 1 + 2)
  have h2 : D_Z (m + 3) = LR_Z (m + 2) ^ 2 - LR_Z (m + 3) * LR_Z (m + 1) := by
    have h : m + 3 = (m + 1) + 2 := by rfl
    rw [h, D_Z_def]
  -- D_Z (m + 2) is D_Z (m + 2)
  have h3 : D_Z (m + 2) = LR_Z (m + 1) ^ 2 - LR_Z (m + 2) * LR_Z m := by
    rw [D_Z_def]
  
  -- Now we rewrite everything using these definitions and our LR_Z steps:
  rw [h1, h2, h3]
  rw [LR_Z_step1 m, LR_Z_step2 m, LR_Z_step3 m]
  ring

theorem LR_Z_bounds (n : ℕ) : LR_Z n ≥ 0 ∧ LR_Z (n + 1) ≥ 3 * LR_Z n := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | _ | _ | m
  · -- n = 0
    decide
  · -- n = 1
    decide
  · -- n = 2
    decide
  · -- n = m + 3
    have ih_m := ih m (by omega)
    have ih_m1 := ih (m + 1) (by omega)
    have ih_m2 := ih (m + 2) (by omega)
    -- LR_Z (m+3) = 4 * LR_Z (m+2) - LR_Z m
    have h_m3 : LR_Z (m + 3) = 4 * LR_Z (m + 2) - LR_Z m := rfl
    -- LR_Z (m+4) = 4 * LR_Z (m+3) - LR_Z (m+1)
    have h_m4 : LR_Z (m + 4) = 4 * LR_Z (m + 3) - LR_Z (m + 1) := rfl
    
    have l_m : LR_Z m ≥ 0 := ih_m.1
    have l_m1 : LR_Z (m + 1) ≥ 3 * LR_Z m := ih_m.2
    have l_m1_pos : LR_Z (m + 1) ≥ 0 := ih_m1.1
    have l_m2 : LR_Z (m + 2) ≥ 3 * LR_Z (m + 1) := ih_m1.2
    have l_m2_pos : LR_Z (m + 2) ≥ 0 := ih_m2.1
    have l_m3 : LR_Z (m + 3) ≥ 3 * LR_Z (m + 2) := ih_m2.2
    
    constructor
    · rw [h_m3]
      omega
    · rw [h_m4, h_m3]
      omega

theorem D_Z_bounds (n : ℕ) (hn : n ≥ 2) : D_Z n ≥ 1 ∧ D_Z n ≤ LR_Z (n - 2) := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | _ | _ | _ | _ | m
  · -- n = 0
    omega
  · -- n = 1
    omega
  · -- n = 2
    have hD : D_Z (0 + 1 + 1) = 4 := by decide
    have hLR : LR_Z (0 + 1 + 1 - 2) = 4 := by decide
    omega
  · -- n = 3
    have hD : D_Z (0 + 1 + 1 + 1) = 1 := by decide
    have hLR : LR_Z (0 + 1 + 1 + 1 - 2) = 16 := by decide
    omega
  · -- n = 4
    have hD : D_Z (0 + 1 + 1 + 1 + 1) = 16 := by decide
    have hLR : LR_Z (0 + 1 + 1 + 1 + 1 - 2) = 63 := by decide
    omega
  · -- n = m + 5
    have h_rec := D_Z_recurrence m
    have ih_m3 := ih (m + 3) (by omega) (by omega)
    have ih_m2 := ih (m + 2) (by omega) (by omega)
    
    have h_idx : m + 5 - 2 = m + 3 := by omega
    have h_idx3 : m + 3 - 2 = m + 1 := by omega
    have h_idx2 : m + 2 - 2 = m := by omega
    
    rw [h_idx3] at ih_m3
    rw [h_idx2] at ih_m2
    
    have b_m : LR_Z m ≥ 0 := (LR_Z_bounds m).1
    have b_m1 : LR_Z (m + 1) ≥ 3 * LR_Z m := (LR_Z_bounds m).2
    have b_m2 : LR_Z (m + 2) ≥ 3 * LR_Z (m + 1) := (LR_Z_bounds (m + 1)).2
    have b_m3 : LR_Z (m + 3) = 4 * LR_Z (m + 2) - LR_Z m := rfl
    
    constructor
    · rw [h_rec]
      omega
    · rw [h_rec, h_idx, b_m3]
      omega

def LR : ℕ → ℕ
  | 0 => 4
  | 1 => 16
  | 2 => 63
  | n + 3 => 4 * LR (n + 2) - LR n

lemma LR_Z_eq_LR (n : ℕ) : LR_Z n = ↑(LR n) := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | _ | _ | m
  · rfl
  · rfl
  · rfl
  · have ih_m := ih m (by omega)
    have ih_m2 := ih (m + 2) (by omega)
    have h_LR_Z : LR_Z (m + 3) = 4 * LR_Z (m + 2) - LR_Z m := rfl
    have h_LR : LR (m + 3) = 4 * LR (m + 2) - LR m := rfl
    rw [h_LR_Z, h_LR]
    rw [ih_m, ih_m2]
    -- We need to prove that LR m ≤ 4 * LR (m + 2)
    -- We can get this from LR_Z bounds
    have b_m : LR_Z m ≥ 0 := (LR_Z_bounds m).1
    have b_m2 : LR_Z (m + 2) ≥ 0 := (LR_Z_bounds (m + 2)).1
    have b_m3_Z : LR_Z (m + 3) ≥ 0 := (LR_Z_bounds (m + 3)).1
    have h_le : LR m ≤ 4 * LR (m + 2) := by
      -- Since LR_Z m = ↑(LR m) and LR_Z (m+2) = ↑(LR (m+2))
      -- we have LR_Z m ≤ 4 * LR_Z (m+2) which implies the result.
      have : LR_Z m ≤ 4 * LR_Z (m + 2) := by
        -- since LR_Z (m+3) ≥ 0, we have 4 * LR_Z (m+2) - LR_Z m ≥ 0, so LR_Z m ≤ 4 * LR_Z (m+2)
        rw [h_LR_Z] at b_m3_Z
        omega
      rw [ih_m, ih_m2] at this
      exact Nat.cast_le.mp this
    rw [Nat.cast_sub h_le]
    push_cast
    rfl

lemma LR_pos (n : ℕ) : LR n > 0 := by
  have hZ : LR_Z n ≥ 4 := by
    induction' n with n ih
    · decide
    · have := (LR_Z_bounds n).2
      omega
  have h : LR_Z n = ↑(LR n) := LR_Z_eq_LR n
  omega

lemma Nat_div_eq_of_bounds (X Y Z : ℕ) (h1 : Z * Y ≤ X) (h2 : X < (Z + 1) * Y) (hY : Y > 0) : X / Y = Z := by
  have h_le : Z ≤ X / Y := (Nat.le_div_iff_mul_le hY).mpr h1
  have h_lt : X / Y < Z + 1 := (Nat.div_lt_iff_lt_mul hY).mpr h2
  omega

lemma LR_D_bounds (n : ℕ) :
    LR (n + 2) * LR n + 1 ≤ LR (n + 1) ^ 2 ∧
    LR (n + 1) ^ 2 ≤ LR (n + 2) * LR n + LR n := by
  have h_D := D_Z_bounds (n + 2) (by omega)
  have h_D_def : D_Z (n + 2) = LR_Z (n + 1) ^ 2 - LR_Z (n + 2) * LR_Z n := D_Z_def n
  have h_LR0 : LR_Z n = ↑(LR n) := LR_Z_eq_LR n
  have h_LR1 : LR_Z (n + 1) = ↑(LR (n + 1)) := LR_Z_eq_LR (n + 1)
  have h_LR2 : LR_Z (n + 2) = ↑(LR (n + 2)) := LR_Z_eq_LR (n + 2)
  rw [h_D_def] at h_D
  have h_idx : n + 2 - 2 = n := by omega
  rw [h_idx] at h_D

  have h_add : LR_Z (n + 2) * LR_Z n + 1 ≤ LR_Z (n + 1) ^ 2 ∧ LR_Z (n + 1) ^ 2 ≤ LR_Z (n + 2) * LR_Z n + LR_Z n := by
    omega

  rw [h_LR0, h_LR1, h_LR2] at h_add
  exact_mod_cast h_add

lemma LR_step_div (n : ℕ) : (LR (n + 1) ^ 2 + LR n - 1) / LR n = LR (n + 2) + 1 := by
  have hb := LR_D_bounds n
  have hY := LR_pos n
  have h1 : (LR (n + 2) + 1) * LR n ≤ LR (n + 1) ^ 2 + LR n - 1 := by
    have : (LR (n + 2) + 1) * LR n = LR (n + 2) * LR n + LR n := by ring
    rw [this]
    omega
  have h2 : LR (n + 1) ^ 2 + LR n - 1 < (LR (n + 2) + 1 + 1) * LR n := by
    have : (LR (n + 2) + 1 + 1) * LR n = LR (n + 2) * LR n + 2 * LR n := by ring
    rw [this]
    omega
  exact Nat_div_eq_of_bounds _ _ _ h1 h2 hY

lemma LR_step_ceil (n : ℕ) : LR (n + 2) = (LR (n + 1) ^ 2 + LR n - 1) / LR n - 1 := by
  rw [LR_step_div]
  rfl

theorem A022030_original_eq_LR (n : ℕ) : A022030_original n = LR n := by
  induction' n using Nat.strong_induction_on with n ih
  rw [A022030_original]
  rcases n with _ | _ | m
  · rfl
  · rfl
  · have h0 : ¬(m + 2 = 0) := by omega
    have h1 : ¬(m + 2 = 1) := by omega
    rw [dif_neg h0, dif_neg h1]
    have ih1 := ih (m + 1) (by omega)
    have ih2 := ih m (by omega)
    have h_sub1 : m + 2 - 1 = m + 1 := rfl
    have h_sub2 : m + 2 - 2 = m := rfl
    rw [h_sub1, h_sub2]
    rw [ih1, ih2]
    exact (LR_step_ceil m).symm

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
  rw [A022030_original_eq_LR]
  rcases n with _ | _ | _ | m
  · rfl
  · rfl
  · rfl
  · have h0 : ¬(m + 3 = 0) := by omega
    have h1 : ¬(m + 3 = 1) := by omega
    have h2 : ¬(m + 3 = 2) := by omega
    simp only [h0, h1, h2, ↓reduceIte]
    have h_sub1 : m + 3 - 1 = m + 2 := rfl
    have h_sub2 : m + 3 - 3 = m := rfl
    rw [h_sub1, h_sub2]
    rw [A022030_original_eq_LR (m + 2)]
    rw [A022030_original_eq_LR m]
    rfl
