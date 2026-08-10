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

namespace A022030ConjProof

/-- The linear-recurrence sequence `cseq` with `cseq 0 = 4`, `cseq 1 = 16`, `cseq 2 = 63`
and `cseq (n+3) = 4 * cseq (n+2) - cseq n`, i.e. the sequence with generating function
`(4 - x^2)/(1 - 4x + x^3)`. -/
def cseq : ℕ → ℕ
  | 0 => 4
  | 1 => 16
  | 2 => 63
  | (n+3) => 4 * cseq (n+2) - cseq n

/-- The auxiliary "defect" sequence `Eseq k = cseq (k+1)^2 - cseq (k+2) * cseq k`,
which satisfies the linear recurrence `Eseq (n+3) = 4 * Eseq (n+1) + Eseq n`. -/
def Eseq : ℕ → ℕ
  | 0 => 4
  | 1 => 1
  | 2 => 16
  | (n+3) => 4 * Eseq (n+1) + Eseq n

theorem cseq_mono : ∀ n, cseq n ≤ cseq (n+1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => decide
    | 1 => decide
    | (m+2) =>
      have h1 : cseq m ≤ cseq (m+1) := ih m (by omega)
      have h2 : cseq (m+1) ≤ cseq (m+2) := ih (m+1) (by omega)
      have hdef : cseq (m+2+1) = 4 * cseq (m+2) - cseq m := rfl
      omega

theorem cseq_le_of_le {a b : ℕ} (h : a ≤ b) : cseq a ≤ cseq b := by
  induction b with
  | zero => have : a = 0 := by omega
            subst this; exact le_refl _
  | succ k ih =>
    rcases Nat.lt_or_ge a (k+1) with h' | h'
    · exact le_trans (ih (by omega)) (cseq_mono k)
    · have : a = k+1 := by omega
      simp [this]

theorem cseq_pos : ∀ n, 1 ≤ cseq n := by
  intro n
  have : cseq 0 ≤ cseq n := cseq_le_of_le (Nat.zero_le n)
  simp only [cseq] at this
  omega

theorem cseq_add_form : ∀ n, cseq (n+3) + cseq n = 4 * cseq (n+2) := by
  intro n
  have hdef : cseq (n+3) = 4 * cseq (n+2) - cseq n := rfl
  have hle : cseq n ≤ cseq (n+2) := cseq_le_of_le (by omega)
  omega

/-- The key algebraic identity `cseq (k+1)^2 = cseq (k+2) * cseq k + Eseq k`. -/
theorem cseq_id : ∀ k, cseq (k+1) ^ 2 = cseq (k+2) * cseq k + Eseq k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | (m+3) =>
      have qA : (cseq (m+1) : ℤ)^2 = cseq (m+2) * cseq m + Eseq m := by
        exact_mod_cast ih m (by omega)
      have qB : (cseq (m+2) : ℤ)^2 = cseq (m+3) * cseq (m+1) + Eseq (m+1) := by
        exact_mod_cast ih (m+1) (by omega)
      have e3 : (Eseq (m+3) : ℤ) = 4 * Eseq (m+1) + Eseq m := by
        exact_mod_cast (rfl : Eseq (m+3) = 4 * Eseq (m+1) + Eseq m)
      have R3 : (cseq (m+3) : ℤ) + cseq m = 4 * cseq (m+2) := by exact_mod_cast cseq_add_form m
      have R4 : (cseq (m+4) : ℤ) + cseq (m+1) = 4 * cseq (m+3) := by
        exact_mod_cast cseq_add_form (m+1)
      have R5 : (cseq (m+5) : ℤ) + cseq (m+2) = 4 * cseq (m+4) := by
        exact_mod_cast cseq_add_form (m+2)
      have key : (cseq (m+4) : ℤ)^2 = cseq (m+5) * cseq (m+3) + Eseq (m+3) := by
        linear_combination (-1 : ℤ) * e3 + qA + (4:ℤ) * qB
          + (-(cseq (m+3):ℤ)) * R5 + ((cseq (m+4):ℤ) - cseq (m+1)) * R4 + (cseq (m+2):ℤ) * R3
      exact_mod_cast key

theorem Eseq_pos : ∀ k, 1 ≤ Eseq k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | (m+3) =>
      have h1 : 1 ≤ Eseq (m+1) := ih (m+1) (by omega)
      have h2 : 1 ≤ Eseq m := ih m (by omega)
      have hdef : Eseq (m+3) = 4 * Eseq (m+1) + Eseq m := rfl
      omega

theorem Eseq_le_cseq : ∀ k, Eseq k ≤ cseq k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | 3 => decide
    | 4 => decide
    | (m+5) =>
      have iE1 : Eseq (m+3) ≤ cseq (m+3) := ih (m+3) (by omega)
      have iE2 : Eseq (m+2) ≤ cseq (m+2) := ih (m+2) (by omega)
      have hdef : Eseq (m+5) = 4 * Eseq (m+3) + Eseq (m+2) := rfl
      have A5 : cseq (m+5) + cseq (m+2) = 4 * cseq (m+4) := cseq_add_form (m+2)
      have A4 : cseq (m+4) + cseq (m+1) = 4 * cseq (m+3) := cseq_add_form (m+1)
      have A3 : cseq (m+3) + cseq m = 4 * cseq (m+2) := cseq_add_form m
      have m21 : cseq (m+1) ≤ cseq (m+2) := cseq_le_of_le (by omega)
      have m12 : cseq m ≤ cseq (m+1) := cseq_le_of_le (by omega)
      have m23 : cseq (m+2) ≤ cseq (m+3) := cseq_le_of_le (by omega)
      omega

theorem div_step (m : ℕ) :
    (cseq (m+1) ^ 2 + cseq m - 1) / cseq m - 1 = cseq (m+2) := by
  have hid : cseq (m+1) ^ 2 = cseq (m+2) * cseq m + Eseq m := cseq_id m
  have hr1 : 1 ≤ Eseq m := Eseq_pos m
  have hrd : Eseq m ≤ cseq m := Eseq_le_cseq m
  have hd : 1 ≤ cseq m := cseq_pos m
  have heq : cseq (m+1) ^ 2 + cseq m - 1 = cseq m * (cseq (m+2) + 1) + (Eseq m - 1) := by
    rw [hid]; rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm (cseq m) (cseq (m+2))]; omega
  have key : (cseq (m+1) ^ 2 + cseq m - 1) / cseq m = cseq (m+2) + 1 := by
    rw [heq, Nat.mul_add_div (by omega : 0 < cseq m),
        Nat.div_eq_of_lt (by omega : Eseq m - 1 < cseq m)]
  rw [key]; omega

/-- The original ceiling-based sequence coincides with the linear-recurrence sequence. -/
theorem main : ∀ n, A022030_original n = cseq n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rw [A022030_original]; rfl
    | 1 => rw [A022030_original]; rfl
    | (m+2) =>
      have e1 : A022030_original (m+1) = cseq (m+1) := ih (m+1) (by omega)
      have e0 : A022030_original m = cseq m := ih m (by omega)
      conv_lhs => rw [A022030_original]
      have h0 : ¬ (m+2 = 0) := by omega
      have h1 : ¬ (m+2 = 1) := by omega
      simp only [h0, h1]
      norm_num
      rw [e1, e0]
      exact div_step m

end A022030ConjProof

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
  simp only [A022030ConjProof.main]
  match n with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | (m+3) =>
    have h0 : ¬ (m+3 = 0) := by omega
    have h1 : ¬ (m+3 = 1) := by omega
    have h2 : ¬ (m+3 = 2) := by omega
    simp only [h0, h1, h2, if_false]
    have e1 : m + 3 - 1 = m + 2 := by omega
    have e3 : m + 3 - 3 = m := by omega
    rw [e1, e3]
    rfl
