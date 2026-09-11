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

-- An integer-valued model of the proposed linear recurrence.
private def c : ℕ → ℤ
  | 0 => 4
  | 1 => 16
  | 2 => 63
  | n + 3 => 4 * c (n + 2) - c n

private theorem c_growth (n : ℕ) : 0 < c n ∧ 3 * c n ≤ c (n + 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => norm_num [c]
    | 1 => norm_num [c]
    | k + 2 =>
      have h0 := ih k (by omega)
      have h1 := ih (k + 1) (by omega)
      have he : c (k + 2 + 1) = 4 * c (k + 2) - c k := by rw [c]
      constructor <;> nlinarith

-- The defect measures the strict inequality in the ceiling recurrence.
private def d (n : ℕ) : ℤ := c (n + 1) ^ 2 - c n * c (n + 2)

-- The defects themselves obey a recurrence with positive coefficients.
private theorem d_rec (n : ℕ) : d (n + 3) = 4 * d (n + 1) + d n := by
  unfold d
  have h3 : c (n + 3) = 4 * c (n + 2) - c n := by rw [c]
  have h4 : c (n + 4) = 4 * c (n + 3) - c (n + 1) := by rw [c]
  have h5 : c (n + 5) = 4 * c (n + 4) - c (n + 2) := by rw [c]
  simp only [show n + 3 + 1 = n + 4 by omega,
    show n + 3 + 2 = n + 5 by omega,
    show n + 1 + 1 = n + 2 by omega,
    show n + 1 + 2 = n + 3 by omega]
  rw [h5, h4, h3]
  ring

private theorem d_bounds (n : ℕ) : 0 < d n ∧ d n ≤ c n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => norm_num [d, c]
    | 1 => norm_num [d, c]
    | 2 => norm_num [d, c]
    | k + 3 =>
      have h0 := ih k (by omega)
      have h1 := ih (k + 1) (by omega)
      have g0 := c_growth k
      have g1 := c_growth (k + 1)
      rw [d_rec]
      have he : c (k + 3) = 4 * c (k + 2) - c k := by rw [c]
      constructor <;> nlinarith

private theorem c_ceil (n : ℕ) :
    (c (n + 2)).toNat =
      ((c (n + 1)).toNat ^ 2 + (c n).toNat - 1) / (c n).toNat - 1 := by
  have h0 := Int.toNat_of_nonneg (le_of_lt (c_growth n).1)
  have h1 := Int.toNat_of_nonneg (le_of_lt (c_growth (n + 1)).1)
  have h2 := Int.toNat_of_nonneg (le_of_lt (c_growth (n + 2)).1)
  have hd := d_bounds n
  unfold d at hd
  have hlo : (c n).toNat * (c (n + 2)).toNat < (c (n + 1)).toNat ^ 2 := by
    zify
    rw [h0, h1, h2]
    linarith
  have hhi : (c (n + 1)).toNat ^ 2 ≤
      (c n).toNat * (c (n + 2)).toNat + (c n).toNat := by
    zify
    rw [h0, h1, h2]
    linarith
  have hs : (c (n + 1)).toNat ^ 2 + (c n).toNat - 1 + 1 =
      (c (n + 1)).toNat ^ 2 + (c n).toNat := Nat.sub_add_cancel (by omega)
  have hdiv : ((c (n + 1)).toNat ^ 2 + (c n).toNat - 1) / (c n).toNat =
      (c (n + 2)).toNat + 1 := by
    apply Nat.div_eq_of_lt_le <;> nlinarith only [hlo, hhi, hs]
  rw [hdiv]
  omega

private theorem original_eq_c (n : ℕ) : A022030_original n = (c n).toNat := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => rw [A022030_original]; rfl
    | 1 => rw [A022030_original]; rfl
    | k + 2 =>
      rw [A022030_original]
      simp only [show k + 2 ≠ 0 by omega, show k + 2 ≠ 1 by omega, ↓reduceDIte]
      rw [ih (k + 2 - 1) (by omega), ih (k + 2 - 2) (by omega)]
      simpa using (c_ceil k).symm

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
  simp only [original_eq_c]
  match n with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | k + 3 =>
    simp only [show k + 3 ≠ 0 by omega, show k + 3 ≠ 1 by omega,
      show k + 3 ≠ 2 by omega, ↓reduceIte,
      show k + 3 - 1 = k + 2 by omega, show k + 3 - 3 = k by omega]
    rw [c]
    have h0 := Int.toNat_of_nonneg (le_of_lt (c_growth k).1)
    have h2 := Int.toNat_of_nonneg (le_of_lt (c_growth (k + 2)).1)
    rw [← h0, ← h2]
    exact Int.toNat_sub (4 * (c (k + 2)).toNat) (c k).toNat

theorem oeis_22030_original_conjecture.disproof : ¬ (type_of% @oeis_22030_original_conjecture) := sorry
