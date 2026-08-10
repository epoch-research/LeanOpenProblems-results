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

-- The integer linear recurrence sequence from the conjectured generating function.
private def L : ℕ → ℤ
  | 0 => 4
  | 1 => 16
  | 2 => 63
  | (n+3) => 4 * L (n+2) - L n

private theorem L_rec (n : ℕ) : L (n+3) = 4 * L (n+2) - L n := by rfl

-- Monotonicity and positivity, bundled.
private theorem L_mono_pos (n : ℕ) : 1 ≤ L n ∧ L n < L (n+1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => exact ⟨by norm_num [L], by norm_num [L]⟩
    | 1 => exact ⟨by norm_num [L], by norm_num [L]⟩
    | 2 => refine ⟨by norm_num [L], ?_⟩; rw [show (2+1) = 3 from rfl, L_rec 0]; norm_num [L]
    | (m+3) =>
      have h1 := ih (m+1) (by omega)
      have h2 := ih (m+2) (by omega)
      obtain ⟨hp1, hlt1⟩ := h1
      obtain ⟨hp2, hlt2⟩ := h2
      have hlt1 : L (m+1) < L (m+2) := hlt1
      have hlt2 : L (m+2) < L (m+3) := hlt2
      have e1 : L (m+3) = 4 * L (m+2) - L m := L_rec m
      have e2 : L (m+3+1) = 4 * L (m+3) - L (m+1) := L_rec (m+1)
      constructor
      · omega
      · rw [e2]
        have : L (m+1) < L (m+3) := lt_trans hlt1 hlt2
        omega

private theorem L_pos (n : ℕ) : 1 ≤ L n := (L_mono_pos n).1
private theorem L_lt (n : ℕ) : L n < L (n+1) := (L_mono_pos n).2
private theorem L_le (n : ℕ) : L n ≤ L (n+1) := le_of_lt (L_lt n)

-- Growth lemma: 4 L(m+1) + 2 L(m) ≤ 4 L(m+2).
private theorem L_growth (m : ℕ) : 4 * L (m+1) + 2 * L m ≤ 4 * L (m+2) := by
  match m with
  | 0 =>
    have : L 2 = 63 := by rfl
    norm_num [L]
  | (m'+1) =>
    have e : L (m'+3) = 4 * L (m'+2) - L m' := L_rec m'
    have hp := L_pos m'
    have hlt1 : L m' < L (m'+1) := L_lt m'
    have hlt2 : L (m'+1) < L (m'+2) := L_lt (m'+1)
    show 4 * L (m'+1+1) + 2 * L (m'+1) ≤ 4 * L (m'+1+2)
    have h1 : L (m'+1+1) = L (m'+2) := rfl
    have h2 : L (m'+1+2) = L (m'+3) := rfl
    rw [h1, h2, e]
    omega

-- The "defect" quantity f k = L(k+1)^2 - L(k+2) * L k.
private def f (k : ℕ) : ℤ := L (k+1) ^ 2 - L (k+2) * L k

-- f satisfies f(m+3) = 4 f(m+1) + f m.
private theorem f_rec (m : ℕ) : f (m+3) = 4 * f (m+1) + f m := by
  unfold f
  have e3 : L (m+3) = 4 * L (m+2) - L m := L_rec m
  have e4 : L (m+4) = 4 * L (m+3) - L (m+1) := L_rec (m+1)
  have e5 : L (m+5) = 4 * L (m+4) - L (m+2) := L_rec (m+2)
  have i1 : L (m+3+1) = L (m+4) := rfl
  have i2 : L (m+3+2) = L (m+5) := rfl
  have i3 : L (m+1+1) = L (m+2) := rfl
  have i4 : L (m+1+2) = L (m+3) := rfl
  rw [i1, i2, i3, i4, e5, e4, e3]
  ring

-- The main invariant: 0 < f k ≤ L k.
private theorem f_inv (k : ℕ) : 0 < f k ∧ f k ≤ L k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 =>
      constructor
      · show (0:ℤ) < L 1 ^ 2 - L 2 * L 0; norm_num [L]
      · show L 1 ^ 2 - L 2 * L 0 ≤ L 0; norm_num [L]
    | 1 =>
      constructor
      · show (0:ℤ) < L 2 ^ 2 - L 3 * L 1
        rw [show (3:ℕ) = 0+3 from rfl, L_rec 0]; norm_num [L]
      · show L 2 ^ 2 - L 3 * L 1 ≤ L 1
        rw [show (3:ℕ) = 0+3 from rfl, L_rec 0]; norm_num [L]
    | 2 =>
      have e3 : L 3 = 4 * L 2 - L 0 := L_rec 0
      have e4 : L 4 = 4 * L 3 - L 1 := L_rec 1
      constructor
      · show (0:ℤ) < L 3 ^ 2 - L 4 * L 2
        rw [e4, e3]; norm_num [L]
      · show L 3 ^ 2 - L 4 * L 2 ≤ L 2
        rw [e4, e3]; norm_num [L]
    | (m+3) =>
      have hf := f_rec m
      have hm := ih m (by omega)
      have hm1 := ih (m+1) (by omega)
      obtain ⟨hm_pos, hm_le⟩ := hm
      obtain ⟨hm1_pos, hm1_le⟩ := hm1
      have hgr := L_growth m
      have e3 : L (m+3) = 4 * L (m+2) - L m := L_rec m
      constructor
      · rw [hf]; omega
      · rw [hf, e3]
        have hm1_le' : f (m+1) ≤ L (m+1) := hm1_le
        omega

private theorem A_unfold (m : ℕ) :
    A022030_original (m+2) =
      (A022030_original (m+1) ^ 2 + A022030_original m - 1) / A022030_original m - 1 := by
  rw [A022030_original, dif_neg (show m+2 ≠ 0 by omega), dif_neg (show m+2 ≠ 1 by omega)]
  norm_num

-- Nat division helper.
private theorem A_div_helper (q den r : ℕ) (hden : 0 < den) (hr1 : 1 ≤ r) (hr2 : r ≤ den) :
    (q * den + r + den - 1) / den - 1 = q := by
  have key : (q * den + r + den - 1) / den = q + 1 := by
    apply Nat.div_eq_of_lt_le
    · have : (q + 1) * den = q * den + den := by ring
      omega
    · have : (q + 1 + 1) * den = q * den + 2 * den := by ring
      omega
  omega

-- Key lemma: A022030_original agrees with the integer linear recurrence L.
private theorem A_eq_L (n : ℕ) : (A022030_original n : ℤ) = L n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rw [A022030_original]; norm_num [L]
    | 1 => rw [A022030_original]; norm_num [L]
    | (m+2) =>
      set a1 := A022030_original (m+1) with ha1def
      set a0 := A022030_original m with ha0def
      have ha1 : (a1 : ℤ) = L (m+1) := ih (m+1) (by omega)
      have ha0 : (a0 : ℤ) = L m := ih m (by omega)
      have hLm_pos : (1:ℤ) ≤ L m := L_pos m
      have hden : 0 < a0 := by
        have : (0:ℤ) < (a0:ℤ) := by rw [ha0]; linarith
        exact_mod_cast this
      set q := (L (m+2)).toNat with hqdef
      set r := (f m).toNat with hrdef
      have hq : (q : ℤ) = L (m+2) := Int.toNat_of_nonneg (by linarith [L_pos (m+2)])
      have hfpos := (f_inv m).1
      have hfle := (f_inv m).2
      have hr : (r : ℤ) = f m := Int.toNat_of_nonneg (le_of_lt hfpos)
      have num_eq : a1 ^ 2 = q * a0 + r := by
        have : ((a1 ^ 2 : ℕ) : ℤ) = ((q * a0 + r : ℕ) : ℤ) := by
          push_cast
          rw [ha1, ha0, hq, hr]
          unfold f
          ring
        exact_mod_cast this
      have hr1 : 1 ≤ r := by
        have : (1:ℤ) ≤ (r:ℤ) := by rw [hr]; linarith
        exact_mod_cast this
      have hr2 : r ≤ a0 := by
        have : (r:ℤ) ≤ (a0:ℤ) := by rw [hr, ha0]; linarith
        exact_mod_cast this
      have hnat : A022030_original (m+2) = q := by
        rw [A_unfold m, ← ha1def, ← ha0def, num_eq]
        exact A_div_helper q a0 r hden hr1 hr2
      rw [hnat, hq]

-- Nat linear recurrence for A022030_original.
private theorem A_rec (m : ℕ) :
    A022030_original (m+3) = 4 * A022030_original (m+2) - A022030_original m := by
  have h3 : (A022030_original (m+3) : ℤ) = L (m+3) := A_eq_L (m+3)
  have h2 : (A022030_original (m+2) : ℤ) = L (m+2) := A_eq_L (m+2)
  have h0 : (A022030_original m : ℤ) = L m := A_eq_L m
  have hL : L (m+3) = 4 * L (m+2) - L m := L_rec m
  have hle : A022030_original m ≤ 4 * A022030_original (m+2) := by
    have : (A022030_original m : ℤ) ≤ (4 * A022030_original (m+2) : ℕ) := by
      push_cast
      rw [h0, h2]
      have hmono : L m ≤ L (m+2) := le_trans (L_le m) (L_le (m+1))
      have := L_pos (m+2)
      linarith
    exact_mod_cast this
  have : (A022030_original (m+3) : ℤ) = ((4 * A022030_original (m+2) - A022030_original m : ℕ) : ℤ) := by
    rw [Nat.cast_sub hle]
    push_cast
    rw [h3, h2, h0, hL]
  exact_mod_cast this


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
  match n with
  | 0 => rw [A022030_original]; norm_num
  | 1 => rw [A022030_original]; norm_num
  | 2 =>
    have : (A022030_original 2 : ℤ) = L 2 := A_eq_L 2
    have h2 : A022030_original 2 = 63 := by
      have hL : L 2 = 63 := by rfl
      rw [hL] at this; exact_mod_cast this
    simp [h2]
  | (m+3) =>
    have hrec := A_rec m
    have e1 : m + 3 - 1 = m + 2 := by omega
    have e2 : m + 3 - 3 = m := by omega
    simp only [show (m+3) ≠ 0 by omega, show (m+3) ≠ 1 by omega, show (m+3) ≠ 2 by omega,
      if_false, e1, e2]
    rw [hrec]
