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

namespace Aux22030

def c : ℕ → ℤ
  | 0 => 4
  | 1 => 16
  | 2 => 63
  | (n+3) => 4 * c (n+2) - c n

lemma c_succ3 (n : ℕ) : c (n+3) = 4 * c (n+2) - c n := by
  rw [c]

lemma growth (n : ℕ) : 0 < c n ∧ 3 * c n ≤ c (n+1) ∧ 3 * c (n+1) ≤ c (n+2) := by
  induction n with
  | zero => simp [c]
  | succ k ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    refine ⟨by linarith, h2, ?_⟩
    rw [c_succ3]
    linarith

lemma d_rec (n : ℕ) :
    c (n+4) ^ 2 - c (n+3) * c (n+5)
      = 4 * (c (n+2) ^ 2 - c (n+1) * c (n+3)) + (c (n+1) ^ 2 - c n * c (n+2)) := by
  have h3 := c_succ3 n
  have h4 := c_succ3 (n+1)
  have h5 := c_succ3 (n+2)
  simp only [show n + 1 + 3 = n + 4 from rfl, show n + 1 + 2 = n + 3 from rfl,
    show n + 2 + 3 = n + 5 from rfl] at h4 h5
  rw [h5, h4, h3]
  ring

lemma d_bounds (n : ℕ) :
    (0 < c (n+1) ^ 2 - c n * c (n+2) ∧ c (n+1) ^ 2 - c n * c (n+2) ≤ c n) ∧
    (0 < c (n+2) ^ 2 - c (n+1) * c (n+3) ∧ c (n+2) ^ 2 - c (n+1) * c (n+3) ≤ c (n+1)) ∧
    (0 < c (n+3) ^ 2 - c (n+2) * c (n+4) ∧ c (n+3) ^ 2 - c (n+2) * c (n+4) ≤ c (n+2)) := by
  induction n with
  | zero =>
    simp [c]
  | succ k ih =>
    obtain ⟨⟨a0, a1⟩, ⟨b0, b1⟩, ⟨e0, e1⟩⟩ := ih
    refine ⟨⟨b0, b1⟩, ⟨e0, e1⟩, ?_⟩
    have hr := d_rec k
    have hg := growth k
    have hg1 := growth (k+1)
    have hc := c_succ3 k
    simp only [show k + 1 + 3 = k + 4 from rfl, show k + 1 + 2 = k + 3 from rfl,
      show k + 1 + 1 = k + 2 from rfl] at hg1 ⊢
    rw [hr]
    constructor
    · linarith
    · linarith

lemma key (n : ℕ) :
    (A022030_original n : ℤ) = c n ∧ (A022030_original (n+1) : ℤ) = c (n+1) := by
  induction n with
  | zero =>
    constructor
    · rw [A022030_original]; simp [c]
    · rw [A022030_original]; simp [c]
  | succ k ih =>
    obtain ⟨h0, h1⟩ := ih
    refine ⟨h1, ?_⟩
    rw [A022030_original]
    simp only [show k + 1 + 1 ≠ 0 by omega, show k + 1 + 1 ≠ 1 by omega, dif_neg,
      not_false_eq_true, show k + 1 + 1 - 1 = k + 1 by omega,
      show k + 1 + 1 - 2 = k by omega]
    obtain ⟨⟨d0, d1⟩, -, -⟩ := d_bounds k
    have hg := growth k
    -- work in ℕ
    set a := A022030_original k with ha
    set b := A022030_original (k+1) with hb
    have hcpos : 0 < c (k+2) := (growth (k+2)).1
    obtain ⟨m, hm⟩ : ∃ m : ℕ, c (k+2) = m := ⟨(c (k+2)).toNat, by omega⟩
    have h0' : (a : ℤ) = c k := h0
    have h1' : (b : ℤ) = c (k+1) := h1
    rw [hm]
    have lo : a * m + 1 ≤ b ^ 2 := by
      have : (a : ℤ) * m + 1 ≤ (b : ℤ) ^ 2 := by rw [h0', h1', ← hm]; linarith
      exact_mod_cast this
    have hi : b ^ 2 ≤ a * m + a := by
      have : (b : ℤ) ^ 2 ≤ (a : ℤ) * m + a := by rw [h0', h1', ← hm]; linarith
      exact_mod_cast this
    have apos : 0 < a := by
      have : (0:ℤ) < a := by rw [h0']; exact hg.1
      exact_mod_cast this
    have hdiv : (b ^ 2 + a - 1) / a = m + 1 := by
      apply Nat.div_eq_of_lt_le
      · have : (m + 1) * a = a * m + a := by ring
        omega
      · have : (m + 1 + 1) * a = a * m + a + a := by ring
        omega
    rw [hdiv]
    simp

end Aux22030

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
  rcases Nat.lt_or_ge n 3 with h | h
  · interval_cases n
    · simp only [if_true]; rw [A022030_original]; simp
    · simp only [if_true, if_false, one_ne_zero]; rw [A022030_original]; simp
    · simp only [if_true]; rw [A022030_original]; simp
      rw [A022030_original]; simp
      rw [A022030_original]; simp
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    simp only [show k + 3 ≠ 0 by omega, show k + 3 ≠ 1 by omega, show k + 3 ≠ 2 by omega,
      if_false, show k + 3 - 1 = k + 2 by omega, show k + 3 - 3 = k by omega]
    have h3 := (Aux22030.key (k+3)).1
    have h2 := (Aux22030.key (k+2)).1
    have h0 := (Aux22030.key k).1
    have hr := Aux22030.c_succ3 k
    have hpos := (Aux22030.growth (k+3)).1
    have : (A022030_original (k+3) : ℤ) = 4 * (A022030_original (k+2) : ℤ) - (A022030_original k : ℤ) := by
      rw [h3, h2, h0, hr]
    have hle : A022030_original k ≤ 4 * A022030_original (k+2) := by
      have : (A022030_original k : ℤ) ≤ 4 * (A022030_original (k+2) : ℤ) := by linarith
      exact_mod_cast this
    zify [hle]
    exact this

theorem oeis_22030_original_conjecture.disproof : ¬ (type_of% @oeis_22030_original_conjecture) := sorry
