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


private def B22030 : ℕ → ℤ
| 0 => 4
| 1 => 16
| 2 => 63
| n+3 => 4 * B22030 (n+2) - B22030 n

private lemma B22030_pos_growth : ∀ n, 0 < B22030 n ∧ 2 * B22030 n < B22030 (n+1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => norm_num [B22030]
    | 1 => norm_num [B22030]
    | 2 => norm_num [B22030]
    | k+3 =>
      have p1 : 0 < B22030 (k+1) := (ih (k+1) (by omega)).1
      have p2 : 0 < B22030 (k+2) := (ih (k+2) (by omega)).1
      have h1 : 2 * B22030 (k+2) < B22030 (k+3) := (ih (k+2) (by omega)).2
      have h2 : 2 * B22030 (k+1) < B22030 (k+2) := (ih (k+1) (by omega)).2
      constructor
      · nlinarith
      · have hsmall : B22030 (k+1) < 2 * B22030 (k+3) := by nlinarith
        change 2 * B22030 (k+3) < 4 * B22030 (k+3) - B22030 (k+1)
        omega

private lemma B22030_pos (n : ℕ) : 0 < B22030 n := (B22030_pos_growth n).1

private lemma B22030_two_growth (n : ℕ) : 2 * B22030 n < B22030 (n+1) :=
  (B22030_pos_growth n).2

private def Delta22030 (n : ℕ) : ℤ :=
  B22030 n ^ 2 - B22030 (n-1) * B22030 (n+1)

private lemma Delta22030_rec (k : ℕ) :
    Delta22030 (k+4) = 4 * Delta22030 (k+2) + Delta22030 (k+1) := by
  unfold Delta22030
  simp [B22030]
  ring

private lemma Delta22030_pos_lt : ∀ n, 2 ≤ n →
    0 < Delta22030 n ∧ Delta22030 n < B22030 (n-1) := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => omega
    | 1 => omega
    | 2 => norm_num [Delta22030, B22030]
    | 3 => norm_num [Delta22030, B22030]
    | 4 => norm_num [Delta22030, B22030]
    | k+5 =>
      have d1 := ih (k+3) (by omega) (by omega)
      have d2 := ih (k+2) (by omega) (by omega)
      have hrec : Delta22030 (k+5) = 4 * Delta22030 (k+3) + Delta22030 (k+2) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Delta22030_rec (k+1)
      have d1u : Delta22030 (k+3) < B22030 (k+2) := by simpa using d1.2
      have d2u : Delta22030 (k+2) < B22030 (k+1) := by simpa using d2.2
      have hupper : 4 * B22030 (k+2) + B22030 (k+1) < B22030 (k+4) := by
        have g1 : 2 * B22030 (k+2) < B22030 (k+3) := B22030_two_growth (k+2)
        have g2 : 2 * B22030 (k+1) < B22030 (k+2) := B22030_two_growth (k+1)
        have p : 0 < B22030 (k+1) := B22030_pos (k+1)
        change 4 * B22030 (k+2) + B22030 (k+1) < 4 * B22030 (k+3) - B22030 (k+1)
        nlinarith
      rw [hrec]
      constructor
      · nlinarith [d1.1, d2.1]
      · change 4 * Delta22030 (k+3) + Delta22030 (k+2) < B22030 (k+4)
        nlinarith [d1u, d2u, hupper]

private lemma ceil_sub_one_eq_of_bounds (x y k : ℕ) (hy : 0 < y)
    (hlo : k * y < x) (hhi : x ≤ (k+1) * y) :
    (x + y - 1) / y - 1 = k := by
  have hxy : x + y - 1 = x + (y - 1) := by omega
  have hk1 : (k+1) * y = k*y + y := by ring
  have hk2 : (k+1+1) * y = k*y + y + y := by ring
  have hdiv : (x + y - 1) / y = k+1 := by
    apply Nat.div_eq_of_lt_le
    · rw [hxy, hk1]
      omega
    · rw [hxy, hk2]
      omega
  omega

private lemma B22030_step (m : ℕ) (hm : 2 ≤ m) :
    ((B22030 m).toNat ^ 2 + (B22030 (m-1)).toNat - 1) /
        (B22030 (m-1)).toNat - 1 = (B22030 (m+1)).toNat := by
  have d := Delta22030_pos_lt m hm
  have c1 : ((B22030 (m+1)).toNat : ℤ) = B22030 (m+1) :=
    Int.toNat_of_nonneg (le_of_lt (B22030_pos (m+1)))
  have c0 : ((B22030 (m-1)).toNat : ℤ) = B22030 (m-1) :=
    Int.toNat_of_nonneg (le_of_lt (B22030_pos (m-1)))
  have cm : ((B22030 m).toNat : ℤ) = B22030 m :=
    Int.toNat_of_nonneg (le_of_lt (B22030_pos m))
  have hlo : (B22030 (m+1)).toNat * (B22030 (m-1)).toNat < (B22030 m).toNat ^ 2 := by
    have hi : B22030 (m+1) * B22030 (m-1) < B22030 m ^ 2 := by
      unfold Delta22030 at d
      nlinarith [d.1]
    apply Int.ofNat_lt.mp
    change (((B22030 (m+1)).toNat * (B22030 (m-1)).toNat : ℕ) : ℤ) <
      (((B22030 m).toNat ^ 2 : ℕ) : ℤ)
    rw [Nat.cast_mul, Nat.cast_pow, c1, c0, cm]
    exact hi
  have hhi : (B22030 m).toNat ^ 2 ≤ ((B22030 (m+1)).toNat + 1) * (B22030 (m-1)).toNat := by
    have hi : B22030 m ^ 2 ≤ (B22030 (m+1) + 1) * B22030 (m-1) := by
      unfold Delta22030 at d
      nlinarith [d.2]
    apply Int.ofNat_le.mp
    change ((((B22030 m).toNat ^ 2 : ℕ) : ℤ) ≤
      ((((B22030 (m+1)).toNat + 1) * (B22030 (m-1)).toNat : ℕ) : ℤ))
    rw [Nat.cast_pow, Nat.cast_mul, Nat.cast_add, Nat.cast_one, c1, c0, cm]
    exact hi
  exact ceil_sub_one_eq_of_bounds _ _ _ (by
    apply Int.ofNat_lt.mp
    change (0 : ℤ) < ((B22030 (m-1)).toNat : ℤ)
    rw [c0]
    exact B22030_pos (m-1)) hlo hhi

private lemma A022030_original_eq_B22030 : ∀ n, A022030_original n = (B22030 n).toNat := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 =>
      rw [A022030_original, B22030]
      rfl
    | 1 =>
      rw [A022030_original, B22030]
      rfl
    | 2 =>
      rw [A022030_original]
      simp only [OfNat.ofNat_ne_zero, ↓reduceDIte]
      rw [A022030_original]
      simp only [↓reduceDIte]
      rw [A022030_original]
      simp only [reduceCtorEq, ↓reduceDIte]
      norm_num [B22030]
      rfl
    | k+3 =>
      have ih1 : A022030_original (k+2) = (B22030 (k+2)).toNat := ih (k+2) (by omega)
      have ih2 : A022030_original (k+1) = (B22030 (k+1)).toNat := ih (k+1) (by omega)
      rw [A022030_original]
      simp [show k+3 ≠ 1 by omega]
      change (A022030_original (k+2) ^ 2 + A022030_original (k+1) - 1) /
          A022030_original (k+1) - 1 = (B22030 (k+3)).toNat
      rw [ih1, ih2]
      exact B22030_step (k+2) (by omega)

private lemma B22030_nat_rec_k (k : ℕ) :
    (B22030 (k+3)).toNat = 4 * (B22030 (k+2)).toNat - (B22030 k).toNat := by
  have ck : ((B22030 k).toNat : ℤ) = B22030 k :=
    Int.toNat_of_nonneg (le_of_lt (B22030_pos k))
  have c2 : ((B22030 (k+2)).toNat : ℤ) = B22030 (k+2) :=
    Int.toNat_of_nonneg (le_of_lt (B22030_pos (k+2)))
  have c3 : ((B22030 (k+3)).toNat : ℤ) = B22030 (k+3) :=
    Int.toNat_of_nonneg (le_of_lt (B22030_pos (k+3)))
  have hle : (B22030 k).toNat ≤ 4 * (B22030 (k+2)).toNat := by
    apply Int.ofNat_le.mp
    rw [Nat.cast_mul, Nat.cast_ofNat, ck, c2]
    change B22030 k ≤ 4 * B22030 (k+2)
    have hp := B22030_pos (k+3)
    change 0 < 4 * B22030 (k+2) - B22030 k at hp
    omega
  apply Int.ofNat.inj
  change ((B22030 (k+3)).toNat : ℤ) =
    ((4 * (B22030 (k+2)).toNat - (B22030 k).toNat : ℕ) : ℤ)
  rw [c3, Nat.cast_sub hle, Nat.cast_mul, Nat.cast_ofNat, c2, ck]
  rfl

private lemma B22030_nat_rec (n : ℕ) (hn : 3 ≤ n) :
    (B22030 n).toNat = 4 * (B22030 (n-1)).toNat - (B22030 (n-3)).toNat := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k+3 := by
    refine ⟨n-3, ?_⟩
    omega
  simpa using B22030_nat_rec_k k

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
  by_cases h0 : n = 0
  · subst h0
    change A022030_original 0 = 4
    rw [A022030_original_eq_B22030]
    rfl
  · by_cases h1 : n = 1
    · subst h1
      change A022030_original 1 = 16
      rw [A022030_original_eq_B22030]
      rfl
    · by_cases h2 : n = 2
      · subst h2
        change A022030_original 2 = 63
        rw [A022030_original_eq_B22030]
        rfl
      · have hn : 3 ≤ n := by omega
        simp [h0, h1, h2]
        rw [A022030_original_eq_B22030 n,
          A022030_original_eq_B22030 (n-1),
          A022030_original_eq_B22030 (n-3)]
        exact B22030_nat_rec n hn
