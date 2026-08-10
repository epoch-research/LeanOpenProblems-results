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

/-!
### Auxiliary development for the proof

We introduce the linear recurrence sequence `cSeq` given by the conjectured
generating function $G(x) = (4 - x^2)/(1 - 4x + x^3)$, i.e.
`cSeq 0 = 4`, `cSeq 1 = 16`, `cSeq 2 = 63` and
`cSeq (n+3) = 4 * cSeq (n+2) - cSeq n`, working over `ℤ`.

The crucial quantity is the "discriminant"
`dSeq n = cSeq (n+1)^2 - cSeq n * cSeq (n+2)`.
Since the roots of the characteristic polynomial $x^3 - 4x^2 + 1$ are
$\alpha, \beta, \gamma$, the sequence `dSeq` is a linear combination of
$(\alpha\beta)^n, (\alpha\gamma)^n, (\beta\gamma)^n$, whose elementary
symmetric functions give the characteristic polynomial $x^3 - 4x - 1$;
hence `dSeq` satisfies `dSeq (n+3) = 4 * dSeq (n+1) + dSeq n`, with
`dSeq 0 = 4`, `dSeq 1 = 1`, `dSeq 2 = 16`.

From the positive recurrence, `0 < dSeq n`, and by comparison with the
growth of `cSeq`, `dSeq n ≤ cSeq n`.  These two bounds say exactly that
`cSeq n * cSeq (n+2) < cSeq (n+1)^2 ≤ cSeq n * (cSeq (n+2) + 1)`, i.e.
`⌈cSeq (n+1)^2 / cSeq n⌉ - 1 = cSeq (n+2)`, which shows that
`A022030_original` coincides with `cSeq`, proving the conjecture.
-/

private def cSeq : ℕ → ℤ
  | 0 => 4
  | 1 => 16
  | 2 => 63
  | (n+3) => 4 * cSeq (n+2) - cSeq n

private def dSeq : ℕ → ℤ
  | 0 => 4
  | 1 => 1
  | 2 => 16
  | (n+3) => 4 * dSeq (n+1) + dSeq n

private lemma cSeq_succ3 (n : ℕ) : cSeq (n+3) = 4 * cSeq (n+2) - cSeq n := rfl

private lemma dSeq_succ3 (n : ℕ) : dSeq (n+3) = 4 * dSeq (n+1) + dSeq n := rfl

/-- Positivity and growth of the linear recurrence sequence. -/
private lemma cSeq_pos_growth : ∀ n, 0 < cSeq n ∧ 3 * cSeq n ≤ cSeq (n+1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 3 with h | h
    · interval_cases n <;> norm_num [cSeq]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
      have h0 : 0 < cSeq k := (ih k (by omega)).1
      have h0' : 3 * cSeq k ≤ cSeq (k+1) := (ih k (by omega)).2
      have h1' : 3 * cSeq (k+1) ≤ cSeq (k+2) := (ih (k+1) (by omega)).2
      have h2' : 3 * cSeq (k+2) ≤ cSeq (k+3) := (ih (k+2) (by omega)).2
      have r1 : cSeq (k+3) = 4 * cSeq (k+2) - cSeq k := cSeq_succ3 k
      have r2 : cSeq (k+4) = 4 * cSeq (k+3) - cSeq (k+1) := cSeq_succ3 (k+1)
      refine ⟨by linarith, ?_⟩
      show 3 * cSeq (k+3) ≤ cSeq (k+4)
      linarith

private lemma cSeq_pos (n : ℕ) : 0 < cSeq n := (cSeq_pos_growth n).1

private lemma cSeq_growth (n : ℕ) : 3 * cSeq n ≤ cSeq (n+1) := (cSeq_pos_growth n).2

/-- Positivity and the bound `dSeq n ≤ cSeq n`. -/
private lemma dSeq_pos_le : ∀ n, 0 < dSeq n ∧ dSeq n ≤ cSeq n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 3 with h | h
    · interval_cases n <;> norm_num [cSeq, dSeq]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
      have hd0 : 0 < dSeq k := (ih k (by omega)).1
      have hd0' : dSeq k ≤ cSeq k := (ih k (by omega)).2
      have hd1 : 0 < dSeq (k+1) := (ih (k+1) (by omega)).1
      have hd1' : dSeq (k+1) ≤ cSeq (k+1) := (ih (k+1) (by omega)).2
      have h0 := cSeq_pos k
      have h0' : 3 * cSeq k ≤ cSeq (k+1) := cSeq_growth k
      have h1' : 3 * cSeq (k+1) ≤ cSeq (k+2) := cSeq_growth (k+1)
      have r1 : cSeq (k+3) = 4 * cSeq (k+2) - cSeq k := cSeq_succ3 k
      have rd : dSeq (k+3) = 4 * dSeq (k+1) + dSeq k := dSeq_succ3 k
      exact ⟨by linarith, by linarith⟩

/-- The key identity: `cSeq (n+1)^2 = cSeq n * cSeq (n+2) + dSeq n`. -/
private lemma key : ∀ n, cSeq (n+1)^2 = cSeq n * cSeq (n+2) + dSeq n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 3 with h | h
    · interval_cases n <;> norm_num [cSeq, dSeq]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
      have e0 : cSeq (k+1)^2 = cSeq k * cSeq (k+2) + dSeq k := ih k (by omega)
      have e1 : cSeq (k+2)^2 = cSeq (k+1) * cSeq (k+3) + dSeq (k+1) := ih (k+1) (by omega)
      have r1 : cSeq (k+3) = 4 * cSeq (k+2) - cSeq k := cSeq_succ3 k
      have r2 : cSeq (k+4) = 4 * cSeq (k+3) - cSeq (k+1) := cSeq_succ3 (k+1)
      have r3 : cSeq (k+5) = 4 * cSeq (k+4) - cSeq (k+2) := cSeq_succ3 (k+2)
      have rd : dSeq (k+3) = 4 * dSeq (k+1) + dSeq k := dSeq_succ3 k
      rw [r1] at e1
      show cSeq (k+4)^2 = cSeq (k+3) * cSeq (k+5) + dSeq (k+3)
      rw [rd, r3, r2, r1]
      linear_combination e0 + 4 * e1

/-- The main lemma: `A022030_original` agrees with the linear recurrence sequence. -/
private lemma A022030_original_eq_cSeq : ∀ n, (A022030_original n : ℤ) = cSeq n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> (rw [A022030_original]; norm_num [cSeq])
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
      have ha : (A022030_original k : ℤ) = cSeq k := ih k (by omega)
      have hb : (A022030_original (k+1) : ℤ) = cSeq (k+1) := ih (k+1) (by omega)
      have hkey : cSeq (k+1)^2 = cSeq k * cSeq (k+2) + dSeq k := key k
      obtain ⟨hdpos, hdle⟩ := dSeq_pos_le k
      have hc0 : 0 < cSeq k := cSeq_pos k
      have hc2 : 0 < cSeq (k+2) := cSeq_pos (k+2)
      rw [A022030_original, dif_neg (by omega : ¬(k+2 = 0)), dif_neg (by omega : ¬(k+2 = 1))]
      show (((A022030_original (k+1) ^ 2 + A022030_original k - 1) / A022030_original k - 1 : ℕ) : ℤ)
        = cSeq (k+2)
      set a := A022030_original k with ha_def
      set b := A022030_original (k+1) with hb_def
      set m := (cSeq (k+2)).toNat with hm_def
      set d := (dSeq k).toNat with hd_def
      have hm : (m : ℤ) = cSeq (k+2) := Int.toNat_of_nonneg hc2.le
      have hd : (d : ℤ) = dSeq k := Int.toNat_of_nonneg hdpos.le
      have hbsq : b ^ 2 = a * m + d := by
        have : ((b ^ 2 : ℕ) : ℤ) = ((a * m + d : ℕ) : ℤ) := by
          push_cast
          rw [hb, ha, hm, hd]
          linarith [hkey]
        exact_mod_cast this
      have hd1 : 1 ≤ d := by
        have : (0:ℤ) < (d:ℤ) := by rw [hd]; exact hdpos
        exact_mod_cast this
      have hda : d ≤ a := by
        have : (d:ℤ) ≤ (a:ℤ) := by rw [hd, ha]; exact hdle
        exact_mod_cast this
      have ha1 : 1 ≤ a := by
        have : (0:ℤ) < (a:ℤ) := by rw [ha]; exact hc0
        exact_mod_cast this
      have hcalc : (b ^ 2 + a - 1) / a - 1 = m := by
        rw [hbsq, show a * m + d + a - 1 = a * m + (d + a - 1) by omega,
          Nat.mul_add_div (by omega : 0 < a),
          Nat.div_eq_of_lt_le (by omega : 1 * a ≤ d + a - 1) (by omega : d + a - 1 < (1+1) * a)]
        omega
      rw [hcalc]
      exact hm

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
    · simpa using congrArg Int.toNat (A022030_original_eq_cSeq 0)
    · simpa using congrArg Int.toNat (A022030_original_eq_cSeq 1)
    · have h2 := A022030_original_eq_cSeq 2
      norm_num [cSeq] at h2 ⊢
      exact_mod_cast h2
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    show A022030_original (k+3) = 4 * A022030_original (k+2) - A022030_original k
    have h1 := A022030_original_eq_cSeq (k+3)
    have h2 := A022030_original_eq_cSeq (k+2)
    have h3 := A022030_original_eq_cSeq k
    have r1 : cSeq (k+3) = 4 * cSeq (k+2) - cSeq k := cSeq_succ3 k
    have hle : cSeq k ≤ cSeq (k+2) := by
      have g0 : 3 * cSeq k ≤ cSeq (k+1) := cSeq_growth k
      have g1 : 3 * cSeq (k+1) ≤ cSeq (k+2) := cSeq_growth (k+1)
      have p0 := cSeq_pos k
      linarith
    omega
