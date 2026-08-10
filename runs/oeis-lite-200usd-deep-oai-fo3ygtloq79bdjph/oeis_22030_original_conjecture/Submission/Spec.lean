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


private def B022030 : ℕ → ℕ
  | 0 => 4
  | 1 => 16
  | 2 => 63
  | n + 3 => 4 * B022030 (n + 2) - B022030 n

private lemma B022030_pos_double (n : ℕ) : 0 < B022030 n ∧ 2 * B022030 n ≤ B022030 (n + 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | _ | k
    · norm_num [B022030]
    · norm_num [B022030]
    · norm_num [B022030]
    · have hk2 := ih (k + 2) (by omega)
      have hk1 := ih (k + 1) (by omega)
      constructor
      · nlinarith [hk2.1, hk2.2]
      · change 2 * B022030 (k + 3) ≤ 4 * B022030 (k + 3) - B022030 (k + 1)
        have : B022030 (k + 1) ≤ 2 * B022030 (k + 3) := by
          nlinarith [hk1.1, hk1.2, hk2.1, hk2.2]
        omega

private lemma B022030_pos (n : ℕ) : 0 < B022030 n := (B022030_pos_double n).1
private lemma B022030_double (n : ℕ) : 2 * B022030 n ≤ B022030 (n + 1) := (B022030_pos_double n).2

private lemma B022030_rec_add (n : ℕ) : B022030 (n + 3) + B022030 n = 4 * B022030 (n + 2) := by
  change (4 * B022030 (n + 2) - B022030 n) + B022030 n = 4 * B022030 (n + 2)
  have h : B022030 n ≤ 4 * B022030 (n + 2) := by
    have h0 := B022030_pos n
    have h1 := B022030_double n
    have h2 := B022030_double (n + 1)
    nlinarith
  omega

private def R022030 : ℕ → ℕ
  | 0 => 4
  | 1 => 1
  | 2 => 16
  | n + 3 => 4 * R022030 (n + 1) + R022030 n

private lemma R022030_pos_bound (n : ℕ) : 0 < R022030 n ∧ R022030 n ≤ B022030 n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | _ | k
    · norm_num [R022030, B022030]
    · norm_num [R022030, B022030]
    · norm_num [R022030, B022030]
    · have hk := ih k (by omega)
      have hk1 := ih (k + 1) (by omega)
      have hbrec := B022030_rec_add k
      constructor
      · change 0 < 4 * R022030 (k + 1) + R022030 k
        nlinarith [hk.1]
      · change 4 * R022030 (k + 1) + R022030 k ≤ B022030 (k + 3)
        have hb1 := B022030_double k
        have hb2 := B022030_double (k + 1)
        nlinarith

private lemma R022030_pos (n : ℕ) : 0 < R022030 n := (R022030_pos_bound n).1
private lemma R022030_bound (n : ℕ) : R022030 n ≤ B022030 n := (R022030_pos_bound n).2

private lemma R022030_rel (n : ℕ) : B022030 (n + 1) ^ 2 = B022030 n * B022030 (n + 2) + R022030 n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | _ | k
    · norm_num [B022030, R022030]
    · norm_num [B022030, R022030]
    · norm_num [B022030, R022030]
    · have ih0 := ih k (by omega)
      have ih1 := ih (k + 1) (by omega)
      have hrec0 := B022030_rec_add k
      have hrec1 := B022030_rec_add (k + 1)
      have hrec2 := B022030_rec_add (k + 2)
      change B022030 (k + 4) ^ 2 = B022030 (k + 3) * B022030 (k + 5) + (4 * R022030 (k + 1) + R022030 k)
      nlinarith

private lemma ceil_pred_div022030 {q d r : ℕ} (_hd : 0 < d) (hr0 : 0 < r) (hrle : r ≤ d) :
    ((q * d + r + d - 1) / d - 1 = q) := by
  have hle' : q * d + d ≤ q * d + r + d - 1 := by omega
  have hle : (q + 1) * d ≤ q * d + r + d - 1 := by
    simpa [Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hle'
  have hlt' : q * d + r + d - 1 < q * d + (d + d) := by omega
  have hlt : q * d + r + d - 1 < (q + 2) * d := by
    simpa [Nat.add_mul, Nat.succ_mul, Nat.one_mul, two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlt'
  have hdiv : (q * d + r + d - 1) / d = q + 1 := Nat.div_eq_of_lt_le hle hlt
  omega

private lemma A022030_original_eq_B022030 (n : ℕ) : A022030_original n = B022030 n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | k
    · simp [A022030_original.eq_def, B022030]
    · simp [A022030_original.eq_def, B022030]
    · have ih1 := ih (k + 1) (by omega)
      have ih2 := ih k (by omega)
      rw [A022030_original.eq_def]
      simp only [reduceCtorEq, dite_false]
      change (A022030_original (k + 2 - 1) ^ 2 + A022030_original (k + 2 - 2) - 1) /
            A022030_original (k + 2 - 2) - 1 = B022030 (k + 2)
      rw [show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega]
      rw [ih1, ih2]
      rw [R022030_rel k]
      rw [Nat.mul_comm (B022030 k) (B022030 (k + 2))]
      exact ceil_pred_div022030 (B022030_pos k) (R022030_pos k) (R022030_bound k)

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
  rw [A022030_original_eq_B022030 n]
  rcases n with _ | _ | _ | k
  · simp [B022030]
  · simp [B022030]
  · simp [B022030]
  · rw [A022030_original_eq_B022030 (k + 3 - 1), A022030_original_eq_B022030 (k + 3 - 3)]
    simp [B022030]
