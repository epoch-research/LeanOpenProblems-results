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

def B : ℕ → ℤ
| 0 => 4
| 1 => 16
| 2 => 63
| (n + 3) => 4 * B (n + 2) - B n

def D (n : ℕ) : ℤ := B (n + 1) ^ 2 - B n * B (n + 2)

lemma B_step (n : ℕ) : B (n + 3) = 4 * B (n + 2) - B n := rfl
lemma B_step_shift (n : ℕ) : B (n + 4) = 4 * B (n + 3) - B (n + 1) := rfl

lemma D_step (n : ℕ) : D (n + 3) = 4 * D (n + 1) + D n := by
  dsimp [D]
  repeat rw [B_step]
  ring

lemma B_pos_and_ge_3 : ∀ n, 0 < B n ∧ 3 * B n ≤ B (n + 1)
| 0 => by decide
| 1 => by decide
| 2 => by decide
| (n + 3) => by
  have ⟨p1, ih1⟩ := B_pos_and_ge_3 (n + 2)
  have ⟨p2, ih2⟩ := B_pos_and_ge_3 (n + 1)
  have ⟨p3, ih3⟩ := B_pos_and_ge_3 n
  constructor
  · rw [B_step]
    linarith
  · rw [B_step_shift]
    linarith

lemma B_pos (n : ℕ) : 0 < B n := (B_pos_and_ge_3 n).1
lemma B_ge_3 (n : ℕ) : 3 * B n ≤ B (n + 1) := (B_pos_and_ge_3 n).2

lemma D_pos : ∀ n, 0 < D n
| 0 => by decide
| 1 => by decide
| 2 => by decide
| (n + 3) => by
  have h1 : 0 < D (n + 1) := D_pos (n + 1)
  have h2 : 0 < D n := D_pos n
  rw [D_step]
  linarith

lemma D_le_B : ∀ n, D n ≤ B n
| 0 => by decide
| 1 => by decide
| 2 => by decide
| (n + 3) => by
  have h1 : D (n + 1) ≤ B (n + 1) := D_le_B (n + 1)
  have h2 : D n ≤ B n := D_le_B n
  have hb1 : 3 * B (n + 1) ≤ B (n + 2) := B_ge_3 (n + 1)
  have hb2 : 3 * B n ≤ B (n + 1) := B_ge_3 n
  have p1 := B_pos (n + 1)
  rw [D_step, B_step]
  linarith

lemma div_ceil_trick (x y z d : ℕ) (h1 : x = y * z + d) (h2 : 1 ≤ d) (h3 : d ≤ y) :
  (x + y - 1) / y - 1 = z := by
  have hy : 0 < y := by omega
  have h4 : x + y - 1 = y * z + y + d - 1 := by omega
  have h5 : y * z + y + d - 1 = y * z + y + (d - 1) := by omega
  have h7 : x + y - 1 = y * (z + 1) + (d - 1) := by
    calc x + y - 1
      _ = y * z + y + d - 1 := h4
      _ = y * z + y + (d - 1) := h5
      _ = y * (z + 1) + (d - 1) := by ring
  have h8 : (x + y - 1) / y = z + 1 := by
    rw [h7, Nat.add_comm]
    have h9 : (d - 1 + y * (z + 1)) / y = (d - 1) / y + (z + 1) := Nat.add_mul_div_left (d - 1) (z + 1) hy
    rw [h9]
    have h10 : (d - 1) / y = 0 := Nat.div_eq_of_lt (by omega)
    rw [h10]
    omega
  omega

def b (n : ℕ) : ℕ := (B n).toNat

lemma b_step_eq_clean (n : ℕ) : b (n + 1) ^ 2 = b n * b (n + 2) + (D n).toNat := by
  dsimp [b]
  have h1 : ((B (n + 1)).toNat : ℤ) = B (n + 1) := Int.toNat_of_nonneg (by linarith [B_pos (n + 1)])
  have h2 : ((B n).toNat : ℤ) = B n := Int.toNat_of_nonneg (by linarith [B_pos n])
  have h3 : ((B (n + 2)).toNat : ℤ) = B (n + 2) := Int.toNat_of_nonneg (by linarith [B_pos (n + 2)])
  have h4 : ((D n).toNat : ℤ) = D n := Int.toNat_of_nonneg (by linarith [D_pos n])
  zify
  rw [h1, h2, h3, h4]
  dsimp [D]
  ring

lemma toNat_pos_of_pos {x : ℤ} (h : 0 < x) : 1 ≤ x.toNat := by
  have : (1 : ℤ) ≤ x := h
  exact Int.toNat_le_toNat this

lemma b_rec (n : ℕ) : b (n + 2) = (b (n + 1) ^ 2 + b n - 1) / b n - 1 := by
  have h1 : b (n + 1) ^ 2 = b n * b (n + 2) + (D n).toNat := b_step_eq_clean n
  have h2 : 1 ≤ (D n).toNat := toNat_pos_of_pos (D_pos n)
  have h3 : (D n).toNat ≤ b n := by
    dsimp [b]
    have h : D n ≤ B n := D_le_B n
    exact Int.toNat_le_toNat h
  exact (div_ceil_trick (b (n + 1) ^ 2) (b n) (b (n + 2)) (D n).toNat h1 h2 h3).symm

lemma b_step_nat (k : ℕ) : b (k + 3) = 4 * b (k + 2) - b k := by
  dsimp [b]
  have h := B_step k
  have hk1 : 0 ≤ B k := by linarith [B_pos k]
  have hk2 : 0 ≤ B (k + 2) := by linarith [B_pos (k + 2)]
  have hk3 : B k ≤ 4 * B (k + 2) := by
    have h1 := B_ge_3 k
    have h2 := B_ge_3 (k + 1)
    linarith
  omega


lemma A_eq_b (n : ℕ) : A022030_original n = b n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [A022030_original]
    split_ifs with h0 h1
    · subst h0; rfl
    · subst h1; rfl
    · have h_n : 2 ≤ n := by omega
      obtain ⟨k, hk⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
      subst hk
      have ih1 : A022030_original (k + 1) = b (k + 1) := ih (k + 1) (by omega)
      have ih2 : A022030_original k = b k := ih k (by omega)
      dsimp
      have hk2 : k + 2 - 2 = k := by omega
      rw [hk2]
      rw [ih1, ih2]
      exact (b_rec k).symm

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
  rw [A_eq_b]
  split_ifs with h0 h1 h2
  · subst h0; rfl
  · subst h1; rfl
  · subst h2; rfl
  · have hn : 3 ≤ n := by omega
    obtain ⟨k, hk⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    subst hk
    have hk1 : k + 3 - 1 = k + 2 := by omega
    have hk3 : k + 3 - 3 = k := by omega
    rw [hk1, hk3]
    have H1 : A022030_original (k + 2) = b (k + 2) := A_eq_b (k + 2)
    have H2 : A022030_original k = b k := A_eq_b k
    rw [H1, H2]
    exact b_step_nat k


theorem oeis_22030_original_conjecture.disproof : ¬ (type_of% @oeis_22030_original_conjecture) := sorry
