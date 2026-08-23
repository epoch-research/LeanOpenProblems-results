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

private def L : ℕ → ℤ
  | 0 => 4
  | 1 => 16
  | 2 => 63
  | n + 3 => 4 * L (n+2) - L n

private theorem L_pos_growth (n : ℕ) : 0 < L n ∧ 3 * L n ≤ L (n+1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with (_|_|n)
    · norm_num [L]
    · norm_num [L]
    · have h0 := ih n (by omega)
      have h1 := ih (n+1) (by omega)
      simp only [L]
      constructor <;> simp only [L] at h1 ⊢ <;> nlinarith [h0.1, h0.2, h1.1, h1.2]

private theorem L_pos (n : ℕ) : 0 < L n := (L_pos_growth n).1
private theorem L_growth (n : ℕ) : 3 * L n ≤ L (n+1) := (L_pos_growth n).2

private def D (n : ℕ) : ℤ := L (n+1)^2 - L (n+2) * L n

private theorem D_rec (n : ℕ) : D (n+3) = 4 * D (n+1) + D n := by
  simp only [D, L]
  ring

private theorem D_pos_bound (n : ℕ) : 0 < D n ∧ D n ≤ 4 * 3^n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with (_|_|_|n)
    · norm_num [D, L]
    · norm_num [D, L]
    · norm_num [D, L]
    · rw [D_rec]
      have h0 := ih n (by omega)
      have h1 := ih (n+1) (by omega)
      constructor
      · nlinarith [h0.1, h1.1]
      · rw [show (3:ℤ)^(n+3) = 27 * 3^n by ring]
        rw [show (3:ℤ)^(n+1) = 3 * 3^n by ring] at h1
        have hp : (0:ℤ) ≤ 3^n := by positivity
        nlinarith [h0.2, h1.2]

private theorem D_pos (n : ℕ) : 0 < D n := (D_pos_bound n).1
private theorem D_bound (n : ℕ) : D n ≤ 4 * 3^n := (D_pos_bound n).2

private theorem L_power_lower (n : ℕ) : 4 * 3^n ≤ L n := by
  induction n with
  | zero => norm_num [L]
  | succ n ih =>
    rw [pow_succ]
    have hg := L_growth n
    nlinarith

private theorem D_le_L (n : ℕ) : D n ≤ L n :=
  le_trans (D_bound n) (L_power_lower n)

private def B (n : ℕ) : ℕ := (L n).toNat

private theorem B_cast (n : ℕ) : (B n : ℤ) = L n := by
  exact Int.toNat_of_nonneg (le_of_lt (L_pos n))

private theorem B_rec (n : ℕ) : B (n+3) = 4 * B (n+2) - B n := by
  have hleZ : L n ≤ 4 * L (n+2) := by
    have h0 := L_pos n
    have h1 := L_growth n
    have h2 := L_growth (n+1)
    nlinarith
  have hle : B n ≤ 4 * B (n+2) := by
    rw [← B_cast n, ← B_cast (n+2)] at hleZ
    exact_mod_cast hleZ
  apply Int.ofNat_inj.mp
  rw [Nat.cast_sub hle]
  push_cast
  simp only [B_cast]
  simp only [L]

private theorem B_ceiling (n : ℕ) :
    (B (n+1)^2 + B n - 1) / B n - 1 = B (n+2) := by
  have hp := D_pos n
  have hu := D_le_L n
  have hzpos : L (n+2) * L n < L (n+1)^2 := by
    simp only [D] at hp
    linarith
  have hzupper : L (n+1)^2 ≤ (L (n+2) + 1) * L n := by
    simp only [D] at hu
    nlinarith
  have hnpos : B (n+2) * B n < B (n+1)^2 := by
    rw [← B_cast (n+2), ← B_cast n, ← B_cast (n+1)] at hzpos
    exact_mod_cast hzpos
  have hnupper : B (n+1)^2 ≤ (B (n+2) + 1) * B n := by
    rw [← B_cast (n+1), ← B_cast (n+2), ← B_cast n] at hzupper
    exact_mod_cast hzupper
  have hpos : 0 < B n := by
    have h := L_pos n
    rw [← B_cast n] at h
    exact_mod_cast h
  have hlo : (B (n+2) + 1) * B n ≤ B (n+1)^2 + B n - 1 := by
    simp only [Nat.add_mul, one_mul]
    omega
  have hhi : B (n+1)^2 + B n - 1 < ((B (n+2) + 1) + 1) * B n := by
    simp only [Nat.add_mul, one_mul]
    simp only [Nat.add_mul, one_mul] at hnupper
    omega
  rw [Nat.div_eq_of_lt_le hlo hhi]
  omega

private theorem A_eq_B (n : ℕ) : A022030_original n = B n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with (_|_|n)
    · rw [A022030_original]
      have hb := B_cast 0
      norm_num [L] at hb
      exact_mod_cast hb.symm
    · rw [A022030_original]
      have hb := B_cast 1
      norm_num [L] at hb
      exact_mod_cast hb.symm
    · rw [A022030_original]
      rw [show n + 2 - 1 = n + 1 by omega, show n + 2 - 2 = n by omega]
      rw [ih (n+1) (by omega), ih n (by omega)]
      exact B_ceiling n


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
  ) :=
by
  rw [A_eq_B]
  rcases n with (_|_|_|n)
  · rfl
  · rfl
  · rfl
  · simp only [if_neg (by omega : n + 3 ≠ 0), if_neg (by omega : n + 3 ≠ 1),
      if_neg (by omega : n + 3 ≠ 2)]
    rw [show n + 3 - 1 = n + 2 by omega, show n + 3 - 3 = n by omega]
    rw [A_eq_B, A_eq_B]
    exact B_rec n
