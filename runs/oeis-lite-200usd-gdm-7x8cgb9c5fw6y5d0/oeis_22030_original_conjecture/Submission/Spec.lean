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


def A022030_linear : ℕ → ℕ
  | 0 => 4
  | 1 => 16
  | 2 => 63
  | n + 3 => 4 * A022030_linear (n + 2) - A022030_linear n

theorem A022030_linear_mono (n : ℕ) : A022030_linear n < A022030_linear (n + 1) ∧ A022030_linear (n + 1) < A022030_linear (n + 2) := by
  induction n with
  | zero =>
    decide
  | succ n ih =>
    rcases ih with ⟨h1, h2⟩
    change A022030_linear (n + 1) < A022030_linear (n + 2) ∧ A022030_linear (n + 2) < A022030_linear (n + 3)
    refine ⟨h2, ?_⟩
    have h_def : A022030_linear (n + 3) = 4 * A022030_linear (n + 2) - A022030_linear n := rfl
    rw [h_def]
    have h_lt : A022030_linear n < A022030_linear (n + 2) := lt_trans h1 h2
    omega

theorem A022030_linear_lt_succ (n : ℕ) : A022030_linear n < A022030_linear (n + 1) := (A022030_linear_mono n).1
theorem A022030_linear_lt_succ_succ (n : ℕ) : A022030_linear n < A022030_linear (n + 2) := lt_trans (A022030_linear_mono n).1 (A022030_linear_mono n).2

theorem A022030_linear_pos (n : ℕ) : 0 < A022030_linear n := by
  induction n with
  | zero => decide
  | succ n ih => exact lt_trans ih (A022030_linear_lt_succ n)

theorem A022030_linear_ge_three (n : ℕ) : A022030_linear (n + 1) ≥ 3 * A022030_linear n := by
  rcases n with _ | _ | n
  · decide
  · decide
  · change A022030_linear (n + 3) ≥ 3 * A022030_linear (n + 2)
    have h_def : A022030_linear (n + 3) = 4 * A022030_linear (n + 2) - A022030_linear n := rfl
    rw [h_def]
    have := A022030_linear_lt_succ_succ n
    omega

def A022030_linear_i (n : ℕ) : ℤ := A022030_linear n

theorem A022030_linear_i_rec (n : ℕ) : A022030_linear_i (n + 3) = 4 * A022030_linear_i (n + 2) - A022030_linear_i n := by
  unfold A022030_linear_i
  have h_lt := A022030_linear_lt_succ_succ n
  have h_def : A022030_linear (n + 3) = 4 * A022030_linear (n + 2) - A022030_linear n := rfl
  omega

theorem A022030_linear_i_id (n : ℕ) :
  A022030_linear_i (n + 4) ^ 2 - A022030_linear_i (n + 5) * A022030_linear_i (n + 3) =
  4 * (A022030_linear_i (n + 2) ^ 2 - A022030_linear_i (n + 3) * A022030_linear_i (n + 1)) + (A022030_linear_i (n + 1) ^ 2 - A022030_linear_i (n + 2) * A022030_linear_i n) := by
  have h3 : A022030_linear_i (n + 3) = 4 * A022030_linear_i (n + 2) - A022030_linear_i n := A022030_linear_i_rec n
  have h4 : A022030_linear_i (n + 4) = 4 * A022030_linear_i (n + 3) - A022030_linear_i (n + 1) := A022030_linear_i_rec (n + 1)
  have h5 : A022030_linear_i (n + 5) = 4 * A022030_linear_i (n + 4) - A022030_linear_i (n + 2) := A022030_linear_i_rec (n + 2)
  linear_combination (A022030_linear_i (n + 4) - A022030_linear_i (n + 1)) * h4 - A022030_linear_i (n + 3) * h5 + A022030_linear_i (n + 2) * h3

def A022030_linear_Di (n : ℕ) : ℤ := A022030_linear_i (n + 1) ^ 2 - A022030_linear_i (n + 2) * A022030_linear_i n

theorem A022030_linear_Di_rec (n : ℕ) : A022030_linear_Di (n + 3) = 4 * A022030_linear_Di (n + 1) + A022030_linear_Di n := by
  change A022030_linear_i (n + 4) ^ 2 - A022030_linear_i (n + 5) * A022030_linear_i (n + 3) = 4 * (A022030_linear_i (n + 2) ^ 2 - A022030_linear_i (n + 3) * A022030_linear_i (n + 1)) + (A022030_linear_i (n + 1) ^ 2 - A022030_linear_i (n + 2) * A022030_linear_i n)
  exact A022030_linear_i_id n

theorem A022030_linear_Di_pos_triple (n : ℕ) : A022030_linear_Di n > 0 ∧ A022030_linear_Di (n + 1) > 0 ∧ A022030_linear_Di (n + 2) > 0 := by
  induction n with
  | zero =>
    decide
  | succ n ih =>
    change A022030_linear_Di (n + 1) > 0 ∧ A022030_linear_Di (n + 2) > 0 ∧ A022030_linear_Di (n + 3) > 0
    rcases ih with ⟨h0, h1, h2⟩
    refine ⟨h1, h2, ?_⟩
    have h_rec := A022030_linear_Di_rec n
    omega

theorem A022030_linear_Di_pos (n : ℕ) : A022030_linear_Di n > 0 := (A022030_linear_Di_pos_triple n).1

theorem A022030_linear_ineq1 (n : ℕ) : A022030_linear (n + 2) * A022030_linear n < A022030_linear (n + 1) ^ 2 := by
  have h := A022030_linear_Di_pos n
  unfold A022030_linear_Di A022030_linear_i at h
  rw [← Nat.cast_lt (α := ℤ)]
  push_cast
  omega

theorem A022030_linear_ineq2_helper (n : ℕ) : 2 * A022030_linear n + 4 * A022030_linear (n + 1) ≤ 4 * A022030_linear (n + 2) := by
  have h1 := A022030_linear_ge_three n
  have h2 := A022030_linear_ge_three (n + 1)
  change A022030_linear (n + 2) ≥ 3 * A022030_linear (n + 1) at h2
  omega

theorem A022030_linear_Di_le_ai_triple (n : ℕ) : A022030_linear_Di n ≤ A022030_linear_i n ∧ A022030_linear_Di (n + 1) ≤ A022030_linear_i (n + 1) ∧ A022030_linear_Di (n + 2) ≤ A022030_linear_i (n + 2) := by
  induction n with
  | zero =>
    decide
  | succ n ih =>
    change A022030_linear_Di (n + 1) ≤ A022030_linear_i (n + 1) ∧ A022030_linear_Di (n + 2) ≤ A022030_linear_i (n + 2) ∧ A022030_linear_Di (n + 3) ≤ A022030_linear_i (n + 3)
    rcases ih with ⟨h0, h1, h2⟩
    refine ⟨h1, h2, ?_⟩
    have h_rec_D := A022030_linear_Di_rec n
    have h_rec_ai := A022030_linear_i_rec n
    rw [h_rec_D, h_rec_ai]
    have h_helper := A022030_linear_ineq2_helper n
    unfold A022030_linear_i at *
    omega

theorem A022030_linear_Di_le_ai (n : ℕ) : A022030_linear_Di n ≤ A022030_linear_i n := (A022030_linear_Di_le_ai_triple n).1

theorem A022030_linear_ineq2 (n : ℕ) : A022030_linear (n + 1) ^ 2 ≤ (A022030_linear (n + 2) + 1) * A022030_linear n := by
  have h := A022030_linear_Di_le_ai n
  unfold A022030_linear_Di A022030_linear_i at h
  rw [← Nat.cast_le (α := ℤ)]
  push_cast
  have h_ring : (↑(A022030_linear (n + 2)) + 1) * (↑(A022030_linear n) : ℤ) = ↑(A022030_linear (n + 2)) * ↑(A022030_linear n) + ↑(A022030_linear n) := by ring
  rw [h_ring]
  omega

lemma div_ceil_minus_one_eq {A N D : ℕ} (hD : D > 0) (hN : N ≥ 1) :
  A = (N + D - 1) / D - 1 ↔ A * D < N ∧ N ≤ (A + 1) * D := by
  have h_prop : (N + D - 1) / D = A + 1 ↔ (A + 1) * D ≤ N + D - 1 ∧ N + D - 1 ≤ (A + 1) * D + D - 1 := Nat.div_eq_iff hD
  have h_ge : (N + D - 1) / D ≥ 1 := by
    have h_le : D ≤ N + D - 1 := by omega
    exact Nat.div_pos h_le hD
  have h_dist : (A + 1) * D = A * D + D := by ring
  rw [h_dist] at h_prop
  generalize hY : (N + D - 1) / D = Y at *
  constructor
  case mp =>
    intro h
    have h_eq : Y = A + 1 := by omega
    have h_cond := h_prop.mp h_eq
    omega
  case mpr =>
    intro h
    have h_cond : A * D + D ≤ N + D - 1 ∧ N + D - 1 ≤ A * D + D + D - 1 := by omega
    have h_eq := h_prop.mpr h_cond
    omega

theorem A022030_linear_recurrence (n : ℕ) (hn : n ≥ 2) :
  A022030_linear n = (A022030_linear (n - 1) ^ 2 + A022030_linear (n - 2) - 1) / A022030_linear (n - 2) - 1 := by
  have hD : A022030_linear (n - 2) > 0 := A022030_linear_pos (n - 2)
  have hN : A022030_linear (n - 1) ^ 2 ≥ 1 := by
    have h_pos := A022030_linear_pos (n - 1)
    have h_ge : 1 ≤ A022030_linear (n - 1) := by omega
    exact Nat.one_le_pow 2 (A022030_linear (n - 1)) h_ge
  rw [div_ceil_minus_one_eq hD hN]
  have h1 : A022030_linear (n - 2 + 2) * A022030_linear (n - 2) < A022030_linear (n - 2 + 1) ^ 2 := A022030_linear_ineq1 (n - 2)
  have h2 : A022030_linear (n - 2 + 1) ^ 2 ≤ (A022030_linear (n - 2 + 2) + 1) * A022030_linear (n - 2) := A022030_linear_ineq2 (n - 2)
  have h_sub1 : n - 2 + 2 = n := by omega
  have h_sub2 : n - 2 + 1 = n - 1 := by omega
  rw [h_sub1, h_sub2] at h1 h2
  exact ⟨h1, h2⟩

theorem A022030_original_eq_a (n : ℕ) : A022030_original n = A022030_linear n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [A022030_original]
    split_ifs with h0 h1
    · rw [h0]; rfl
    · rw [h1]; rfl
    · have hn : n ≥ 2 := by omega
      have h_ih1 := ih (n - 1) (by omega)
      have h_ih2 := ih (n - 2) (by omega)
      dsimp only
      rw [h_ih1, h_ih2]
      exact (A022030_linear_recurrence n hn).symm

theorem A022030_linear_def_unfolded (n : ℕ) :
  A022030_linear n = (
    if n = 0 then 4
    else if n = 1 then 16
    else if n = 2 then 63
    else
      4 * A022030_linear (n - 1) - A022030_linear (n - 3)
  ) := by
  rcases n with _ | _ | _ | n
  · rfl
  · rfl
  · rfl
  · rfl

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
  rw [A022030_original_eq_a]
  rw [A022030_linear_def_unfolded]
  split_ifs with h0 h1 h2
  · rfl
  · rfl
  · rfl
  · rw [A022030_original_eq_a, A022030_original_eq_a]
