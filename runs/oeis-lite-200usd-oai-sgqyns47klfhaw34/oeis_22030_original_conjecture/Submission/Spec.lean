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

/--
Conjecture (from OEIS comment C A022030 22030):
This original definition would lead to sequence 4, 16, 63, 248, 976, 3841, ...
which agrees to over 2000 terms with the conjectured generating function
$G(x) = (4 - x^2)/(1 - 4x + x^3)$.

This generating function corresponds to the linear recurrence relation:
$b_0 = 4, b_1 = 16, b_2 = 63$.
For $n \ge 3$, $b_n = 4 b_{n-1} - b_{n-3}$.
-/
noncomputable def C : ℕ → ℤ
  | 0 => 4
  | 1 => 16
  | 2 => 63
  | n + 3 => 4 * C (n + 2) - C n

noncomputable def R : ℕ → ℤ
  | 0 => 4
  | 1 => 1
  | 2 => 16
  | n + 3 => 4 * R (n + 1) + R n

noncomputable def L (n : ℕ) : ℕ := Int.toNat (C n)

lemma C_good : ∀ n : ℕ, 0 < C n ∧ C n < C (n + 1) ∧ C n + C (n + 1) ≤ C (n + 2)
  | 0 => by norm_num [C]
  | 1 => by norm_num [C]
  | n + 2 => by
      have g0 := C_good n
      have g1 := C_good (n + 1)
      simp [C]
      constructor
      · linarith
      constructor
      · linarith
      · linarith

lemma C_pos (n : ℕ) : 0 < C n := (C_good n).1

lemma C_mono_succ (n : ℕ) : C n < C (n + 1) := (C_good n).2.1

lemma C_pair_le (n : ℕ) : C n + C (n + 1) ≤ C (n + 2) := (C_good n).2.2

lemma R_pos : ∀ n : ℕ, 0 < R n
  | 0 => by norm_num [R]
  | 1 => by norm_num [R]
  | 2 => by norm_num [R]
  | n + 3 => by
      have h0 := R_pos n
      have h1 := R_pos (n + 1)
      simp [R]
      linarith

lemma R_le_C : ∀ n : ℕ, R n ≤ C n
  | 0 => by norm_num [R, C]
  | 1 => by norm_num [R, C]
  | 2 => by norm_num [R, C]
  | n + 3 => by
      have h0 := R_le_C n
      have h1 := R_le_C (n + 1)
      have hg := C_pair_le n
      have hp := C_pos n
      simp [R, C]
      linarith

lemma C_cassini : ∀ n : ℕ, C (n + 1) ^ 2 = C n * C (n + 2) + R n
  | 0 => by norm_num [C, R]
  | 1 => by norm_num [C, R]
  | 2 => by norm_num [C, R]
  | n + 3 => by
      have h0 := C_cassini n
      have h1 := C_cassini (n + 1)
      have hrec : C (n + 3) = 4 * C (n + 2) - C n := by simp [C]
      simp [C, R]
      linear_combination (norm := ring) h0 + 4 * h1 + 4 * C (n + 1) * hrec

lemma L_cast (n : ℕ) : (L n : ℤ) = C n := by
  rw [L, Int.toNat_of_nonneg]
  exact le_of_lt (C_pos n)

@[simp] lemma L_zero : L 0 = 4 := by
  apply Int.ofNat.inj
  change (L 0 : ℤ) = (4 : ℤ)
  rw [L_cast]
  norm_num [C]

@[simp] lemma L_one : L 1 = 16 := by
  apply Int.ofNat.inj
  change (L 1 : ℤ) = (16 : ℤ)
  rw [L_cast]
  norm_num [C]

@[simp] lemma L_two : L 2 = 63 := by
  apply Int.ofNat.inj
  change (L 2 : ℤ) = (63 : ℤ)
  rw [L_cast]
  norm_num [C]


lemma L_pos (n : ℕ) : 0 < L n := by
  apply Int.ofNat_lt.mp
  rw [Nat.cast_zero, L_cast]
  exact C_pos n

lemma L_rec (n : ℕ) : L (n + 3) = 4 * L (n + 2) - L n := by
  apply Int.ofNat.inj
  change (L (n + 3) : ℤ) = ((4 * L (n + 2) - L n : ℕ) : ℤ)
  have hleZ : C n ≤ 4 * C (n + 2) := by
    have hmono1 := C_mono_succ n
    have hmono2 := C_mono_succ (n + 1)
    have hp := C_pos (n + 2)
    linarith
  have hle : L n ≤ 4 * L (n + 2) := by
    apply Int.ofNat_le.mp
    rw [Nat.cast_mul, Nat.cast_ofNat, L_cast, L_cast]
    exact hleZ
  rw [L_cast, Nat.cast_sub hle, Nat.cast_mul, Nat.cast_ofNat, L_cast, L_cast]
  simp [C]

lemma L_cassini (n : ℕ) : L (n + 1) ^ 2 = L n * L (n + 2) + Int.toNat (R n) := by
  apply Int.ofNat.inj
  change ((L (n + 1) ^ 2 : ℕ) : ℤ) = ((L n * L (n + 2) + Int.toNat (R n) : ℕ) : ℤ)
  rw [Nat.cast_pow, Nat.cast_add, Nat.cast_mul, L_cast, L_cast, L_cast]
  rw [Int.toNat_of_nonneg (le_of_lt (R_pos n))]
  exact C_cassini n

lemma R_toNat_pos (n : ℕ) : 0 < Int.toNat (R n) := by
  apply Int.ofNat_lt.mp
  rw [Nat.cast_zero, Int.toNat_of_nonneg (le_of_lt (R_pos n))]
  exact R_pos n

lemma R_toNat_le_L (n : ℕ) : Int.toNat (R n) ≤ L n := by
  apply Int.ofNat_le.mp
  rw [Int.toNat_of_nonneg (le_of_lt (R_pos n)), L_cast]
  exact R_le_C n

lemma L_div_step (n : ℕ) :
    (L (n + 1) ^ 2 + L n - 1) / L n - 1 = L (n + 2) := by
  let d := L n
  let q := L (n + 2)
  let r := Int.toNat (R n)
  have hd : 0 < d := by simpa [d] using L_pos n
  have hrpos : 0 < r := by simpa [r] using R_toNat_pos n
  have hrle : r ≤ d := by simpa [r, d] using R_toNat_le_L n
  have hc : L (n + 1) ^ 2 = d * q + r := by
    simpa [d, q, r, Nat.mul_comm] using L_cassini n
  have hd_eq : d = L n := rfl
  have hq_eq : q = L (n + 2) := rfl
  clear_value d
  clear_value q
  clear_value r
  have hrem : r - 1 < d := by omega
  have hr_eq : r - 1 + 1 = r := Nat.sub_add_cancel (Nat.succ_le_of_lt hrpos)
  have hx0 : d * q + r + d - 1 = (q + 1) * d + (r - 1) := by
    have hmul : (q + 1) * d = d * q + d := by ring
    rw [hmul, ← hr_eq]
    omega
  have hx : L (n + 1) ^ 2 + d - 1 = (q + 1) * d + (r - 1) := by
    rw [hc]
    exact hx0
  have hdiv : (L (n + 1) ^ 2 + d - 1) / d = q + 1 := by
    rw [hx]
    apply Nat.div_eq_of_lt_le
    · nlinarith [hrem]
    · nlinarith [hrem]
  rw [← hd_eq, hdiv]
  rw [hq_eq]
  omega

lemma A_original_eq_L : ∀ n : ℕ, A022030_original n = L n
  | 0 => by
      rw [A022030_original]
      simp
  | 1 => by
      rw [A022030_original]
      simp
  | n + 2 => by
      rw [A022030_original]
      simp only [Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false,
        Nat.add_sub_cancel_right, Nat.reduceSubDiff]
      rw [A_original_eq_L (n + 1), A_original_eq_L n]
      exact L_div_step n


theorem oeis_22030_original_conjecture (n : ℕ) :
  A022030_original n = (
    if n = 0 then 4
    else if n = 1 then 16
    else if n = 2 then 63
    else
      4 * (A022030_original (n - 1)) - (A022030_original (n - 3))
  ) :=
by
  rw [A_original_eq_L n]
  cases n with
  | zero => simp
  | succ n =>
      cases n with
      | zero => simp
      | succ n =>
          cases n with
          | zero => simp
          | succ n =>
              simp [A_original_eq_L, L_rec]
