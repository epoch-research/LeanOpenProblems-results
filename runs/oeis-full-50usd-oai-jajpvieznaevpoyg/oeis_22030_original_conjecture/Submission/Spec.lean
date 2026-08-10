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

/-
Conjecture (from OEIS comment C A022030 22030):
This original definition would lead to sequence 4, 16, 63, 248, 976, 3841, ...
which agrees to over 2000 terms with the conjectured generating function
$G(x) = (4 - x^2)/(1 - 4x + x^3)$.

This generating function corresponds to the linear recurrence relation:
$b_0 = 4, b_1 = 16, b_2 = 63$.
For $n \ge 3$, $b_n = 4 b_{n-1} - b_{n-3}$.
-/

set_option maxHeartbeats 800000

namespace A022030Proof

noncomputable def B : ℕ → ℕ
  | 0 => 4
  | 1 => 16
  | 2 => 63
  | n + 3 => 4 * B (n + 2) - B n

noncomputable def D : ℕ → ℕ
  | 0 => 4
  | 1 => 1
  | 2 => 16
  | n + 3 => 4 * D (n + 1) + D n

@[simp] lemma B0 : B 0 = 4 := rfl
@[simp] lemma B1 : B 1 = 16 := rfl
@[simp] lemma B2 : B 2 = 63 := rfl
@[simp] lemma B_rec (n : ℕ) : B (n + 3) = 4 * B (n + 2) - B n := rfl

@[simp] lemma D0 : D 0 = 4 := rfl
@[simp] lemma D1 : D 1 = 1 := rfl
@[simp] lemma D2 : D 2 = 16 := rfl
@[simp] lemma D_rec (n : ℕ) : D (n + 3) = 4 * D (n + 1) + D n := rfl

lemma div_aux (q d r : ℕ) (hd : 0 < d) (hr0 : 0 < r) (hrd : r ≤ d) :
    (q * d + r + d - 1) / d - 1 = q := by
  have hdiv : (r + d - 1) / d = 1 := by
    rw [show r + d - 1 = (r - 1) + d * 1 by omega]
    rw [Nat.add_mul_div_left _ _ hd]
    rw [Nat.div_eq_of_lt]
    omega
  rw [Nat.mul_comm q d]
  rw [show d * q + r + d - 1 = (r + d - 1) + d * q by omega]
  rw [Nat.add_mul_div_left _ _ hd, hdiv]
  omega

lemma D_pos (n : ℕ) : 0 < D n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | _ | k
    · simp
    · simp
    · simp
    · have hk := ih k (by omega)
      simp [D_rec]
      omega

lemma B_pos_and_growth (n : ℕ) : 0 < B n ∧ 3 * B n ≤ B (n + 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | _ | k
    · norm_num [B]
    · norm_num [B]
    · norm_num [B]
    · have h0 := ih k (by omega)
      have h1 := ih (k+1) (by omega)
      have h2 := ih (k+2) (by omega)
      have hg0 : 3 * B k ≤ B (k+1) := h0.2
      have hg1 : 3 * B (k+1) ≤ B (k+2) := by
        simpa [show k+1+1 = k+2 by omega] using h1.2
      have hg2 : 3 * B (k+2) ≤ B (k+3) := by
        simpa [show k+2+1 = k+3 by omega] using h2.2
      have hle : B k ≤ 4 * B (k+2) := by omega
      have e3 : B (k+3) + B k = 4 * B (k+2) := by
        rw [B_rec]
        omega
      have hle4 : B (k+1) ≤ 4 * B (k+3) := by omega
      have e4 : B (k+4) + B (k+1) = 4 * B (k+3) := by
        rw [show k+4 = (k+1)+3 by omega]
        rw [B_rec]
        change (4 * B (k + 3) - B (k + 1)) + B (k + 1) = 4 * B (k + 3)
        omega
      constructor
      · have hlt : B k < 4 * B (k+2) := by omega
        have r3 : (B (k+3) : ℤ) = 4 * (B (k+2) : ℤ) - (B k : ℤ) := by
          rw [B_rec]
          omega
        have hlt' : (B k : ℤ) < 4 * (B (k+2) : ℤ) := by exact_mod_cast hlt
        have : (0 : ℤ) < (B (k+3) : ℤ) := by nlinarith
        exact_mod_cast this
      · have h13 : B (k+1) ≤ B (k+3) := by omega
        have r4 : (B (k+4) : ℤ) = 4 * (B (k+3) : ℤ) - (B (k+1) : ℤ) := by
          rw [show k+4 = (k+1)+3 by omega]
          rw [B_rec]
          rw [show k+1+2 = k+3 by omega]
          omega
        have h13' : (B (k+1) : ℤ) ≤ (B (k+3) : ℤ) := by exact_mod_cast h13
        have : (3 * B (k+3) : ℤ) ≤ (B (k+4) : ℤ) := by
          norm_num only [Nat.cast_mul, Nat.cast_ofNat]
          nlinarith
        exact_mod_cast this

lemma B_pos (n : ℕ) : 0 < B n := (B_pos_and_growth n).1
lemma B_growth (n : ℕ) : 3 * B n ≤ B (n+1) := (B_pos_and_growth n).2

lemma B_mono_step (n : ℕ) : B n < B (n+1) := by
  have hp := B_pos n
  have hg := B_growth n
  omega

lemma B_le_two (n : ℕ) : B n ≤ B (n+2) := by
  exact le_trans (le_of_lt (B_mono_step n)) (le_of_lt (B_mono_step (n+1)))

lemma B_rec_int (n : ℕ) : ((B (n + 3) : ℕ) : ℤ) = 4 * (B (n + 2) : ℤ) - (B n : ℤ) := by
  have hle : B n ≤ 4 * B (n + 2) := by
    have h := B_le_two n
    omega
  rw [B_rec]
  omega

lemma det_identity (k : ℕ) : B (k+1)^2 = B (k+2) * B k + D k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | _ | _ | n
    · norm_num [B, D]
    · norm_num [B, D]
    · norm_num [B, D]
    · have ih0 := ih n (by omega)
      have ih1 := ih (n+1) (by omega)
      have r0 := B_rec_int n
      have r1 := B_rec_int (n+1)
      have r2 := B_rec_int (n+2)
      have drec : (D (n+3) : ℤ) = 4 * (D (n+1) : ℤ) + (D n : ℤ) := by simp [D_rec]
      have h0 : ((B (n+1)^2 : ℕ) : ℤ) = ((B (n+2) * B n + D n : ℕ) : ℤ) := by exact_mod_cast ih0
      have h1 : ((B (n+2)^2 : ℕ) : ℤ) = ((B (n+3) * B (n+1) + D (n+1) : ℕ) : ℤ) := by exact_mod_cast ih1
      apply Nat.cast_injective (R := ℤ)
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
      rw [drec]
      nlinarith [h0, h1, r0, r1, r2]

lemma D_le_B (k : ℕ) : D k ≤ B k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | _ | _ | n
    · norm_num [B, D]
    · norm_num [B, D]
    · norm_num [B, D]
    · have ih0 := ih n (by omega)
      have ih1 := ih (n+1) (by omega)
      have hg0 : 3 * B n ≤ B (n+1) := B_growth n
      have hg1 : 3 * B (n+1) ≤ B (n+2) := by
        simpa [show n+1+1 = n+2 by omega] using B_growth (n+1)
      have hle : B n ≤ 4 * B (n+2) := by omega
      have rB : (B (n+3) : ℤ) = 4 * (B (n+2) : ℤ) - (B n : ℤ) := by
        rw [B_rec]
        omega
      have hInt : ((4 * D (n+1) + D n : ℕ) : ℤ) ≤ (B (n+3) : ℤ) := by
        norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
        have ih0' : (D n : ℤ) ≤ (B n : ℤ) := by exact_mod_cast ih0
        have ih1' : (D (n+1) : ℤ) ≤ (B (n+1) : ℤ) := by exact_mod_cast ih1
        have hg0' : (3 * B n : ℤ) ≤ (B (n+1) : ℤ) := by exact_mod_cast hg0
        have hg1' : (3 * B (n+1) : ℤ) ≤ (B (n+2) : ℤ) := by exact_mod_cast hg1
        nlinarith
      have hNat : 4 * D (n+1) + D n ≤ B (n+3) := by
        exact_mod_cast hInt
      simpa [D_rec] using hNat

lemma B_nonlinear (k : ℕ) :
    (B (k+1)^2 + B k - 1) / B k - 1 = B (k+2) := by
  have hdet := det_identity k
  have hd : 0 < B k := B_pos k
  have hr0 : 0 < D k := D_pos k
  have hrd : D k ≤ B k := D_le_B k
  rw [hdet]
  exact div_aux (B (k+2)) (B k) (D k) hd hr0 hrd

lemma A_eq_B (n : ℕ) : A022030_original n = B n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => simp [A022030_original, B]
    | 1 => simp [A022030_original, B]
    | k + 2 =>
        have h1 : A022030_original (k + 2 - 1) = B (k+1) := by
          simpa using ih (k+1) (by omega)
        have h2 : A022030_original (k + 2 - 2) = B k := by
          simpa using ih k (by omega)
        rw [A022030_original]
        rw [h1, h2]
        exact B_nonlinear k

end A022030Proof

open A022030Proof

theorem oeis_22030_original_conjecture (n : ℕ) :
  A022030_original n = (
    if n = 0 then 4
    else if n = 1 then 16
    else if n = 2 then 63
    else
      4 * (A022030_original (n - 1)) - (A022030_original (n - 3))
  ) :=
by
  rw [A_eq_B n]
  rcases n with _ | _ | _ | k
  · simp [B]
  · simp [B]
  · simp [B]
  · simp [A_eq_B, B_rec]
