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

namespace SpecAux

/-- State function computing consecutive triples `(L n, L (n+1), L (n+2))` of the
linear sequence with `L 0 = 4`, `L 1 = 16`, `L 2 = 63`, `L (n+3) = 4 L (n+2) - L n`. -/
def Lst : ℕ → ℕ × ℕ × ℕ
  | 0 => (4, 16, 63)
  | (n+1) => let p := Lst n; (p.2.1, p.2.2, 4 * p.2.2 - p.1)

/-- The linear recurrence sequence underlying `A022030_original`. -/
def L (n : ℕ) : ℕ := (Lst n).1

@[simp] lemma L0 : L 0 = 4 := rfl
@[simp] lemma L1 : L 1 = 16 := rfl
@[simp] lemma L2 : L 2 = 63 := rfl

lemma snd1 (n : ℕ) : (Lst n).2.1 = L (n+1) := rfl
lemma snd2 (n : ℕ) : (Lst n).2.2 = L (n+2) := rfl

lemma Lrec (n : ℕ) : L (n+3) = 4 * L (n+2) - L n := by
  show (Lst (n+3)).1 = 4 * L (n+2) - L n
  rfl

lemma mono_aux (n : ℕ) : 0 < L n ∧ L n < L (n+1) ∧ L (n+1) < L (n+2) := by
  induction n with
  | zero => refine ⟨by simp, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    refine ⟨by omega, h2, ?_⟩
    have hr : L (k+3) = 4 * L (k+2) - L k := Lrec k
    have e1 : L (k+1+1) = L (k+2) := rfl
    have e2 : L (k+1+2) = L (k+3) := rfl
    omega

lemma Lpos (n : ℕ) : 0 < L n := (mono_aux n).1
lemma Lmono (n : ℕ) : L n < L (n+1) := (mono_aux n).2.1

lemma Ladd (n : ℕ) : L (n+3) + L n = 4 * L (n+2) := by
  have hr : L (n+3) = 4 * L (n+2) - L n := Lrec n
  have h1 : L n < L (n+1) := Lmono n
  have h2 : L (n+1) < L (n+2) := Lmono (n+1)
  omega

lemma Lz (n : ℕ) : ((L (n+3) : ℤ)) = 4 * (L (n+2) : ℤ) - (L n : ℤ) := by
  have := Ladd n
  have : (L (n+3) : ℤ) + (L n : ℤ) = 4 * (L (n+2) : ℤ) := by exact_mod_cast this
  linarith

lemma Lmonoz (n : ℕ) : (L n : ℤ) ≤ (L (n+1) : ℤ) := by
  have := Lmono n; exact_mod_cast (le_of_lt this)

/-- The discrete "Hankel" quantity `L(n+1)^2 - L(n+2) L n`. -/
noncomputable def F (n : ℕ) : ℤ := (L (n+1) : ℤ)^2 - (L (n+2) : ℤ) * (L n : ℤ)

lemma Frec (n : ℕ) : F (n+3) = 4 * F (n+1) + F n := by
  have h3 : (L (n+3) : ℤ) = 4 * (L (n+2) : ℤ) - (L n : ℤ) := Lz n
  have h4 : (L (n+4) : ℤ) = 4 * (L (n+3) : ℤ) - (L (n+1) : ℤ) := Lz (n+1)
  have h5 : (L (n+5) : ℤ) = 4 * (L (n+4) : ℤ) - (L (n+2) : ℤ) := Lz (n+2)
  simp only [F]
  rw [show n+3+1 = n+4 from rfl, show n+3+2 = n+5 from rfl,
      show n+1+1 = n+2 from rfl, show n+1+2 = n+3 from rfl]
  rw [h5, h4, h3]
  ring

@[simp] lemma L3 : L 3 = 248 := rfl
@[simp] lemma L4 : L 4 = 976 := rfl

lemma F0 : F 0 = 4 := by simp [F]
lemma F1 : F 1 = 1 := by simp [F]
lemma F2 : F 2 = 16 := by simp [F]

lemma Fpos_aux (n : ℕ) : 0 < F n ∧ 0 < F (n+1) ∧ 0 < F (n+2) := by
  induction n with
  | zero =>
    refine ⟨by rw [F0]; norm_num, by rw [F1]; norm_num, by rw [F2]; norm_num⟩
  | succ k ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    have hr : F (k+3) = 4 * F (k+1) + F k := Frec k
    refine ⟨h1, h2, ?_⟩
    have e : F (k+1+2) = F (k+3) := rfl
    rw [e, hr]; linarith

lemma Fpos (n : ℕ) : 0 < F n := (Fpos_aux n).1

lemma auxL2 (n : ℕ) : 2 * (L (n+1) : ℤ) + (L n : ℤ) ≤ 2 * (L (n+2) : ℤ) := by
  cases n with
  | zero => simp
  | succ k =>
    have hr : (L (k+3) : ℤ) = 4 * (L (k+2) : ℤ) - (L k : ℤ) := Lz k
    have m1 : (L k : ℤ) ≤ (L (k+1) : ℤ) := Lmonoz k
    have m2 : (L (k+1) : ℤ) ≤ (L (k+2) : ℤ) := Lmonoz (k+1)
    have e1 : k + 1 + 1 = k + 2 := rfl
    have e2 : k + 1 + 2 = k + 3 := rfl
    rw [e1, e2, hr]; linarith

lemma auxL (n : ℕ) : 4 * (L (n+1) : ℤ) + (L n : ℤ) ≤ (L (n+3) : ℤ) := by
  have h := auxL2 n
  have hr : (L (n+3) : ℤ) = 4 * (L (n+2) : ℤ) - (L n : ℤ) := Lz n
  linarith

lemma Fbound_aux (n : ℕ) :
    F n ≤ (L n : ℤ) ∧ F (n+1) ≤ (L (n+1) : ℤ) ∧ F (n+2) ≤ (L (n+2) : ℤ) := by
  induction n with
  | zero =>
    refine ⟨by rw [F0]; simp, by rw [F1]; simp, by rw [F2]; simp⟩
  | succ k ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    have hr : F (k+3) = 4 * F (k+1) + F k := Frec k
    refine ⟨h1, h2, ?_⟩
    have e : F (k+1+2) = F (k+3) := rfl
    have e2 : L (k+1+2) = L (k+3) := rfl
    rw [e, hr, e2]
    have hax : 4 * (L (k+1) : ℤ) + (L k : ℤ) ≤ (L (k+3) : ℤ) := auxL k
    linarith

lemma Fbound (n : ℕ) : F n ≤ (L n : ℤ) := (Fbound_aux n).1

lemma posF (m : ℕ) : L (m+2) * L m < L (m+1) ^ 2 := by
  have h := Fpos m
  simp only [F] at h
  have : (L (m+2) : ℤ) * (L m : ℤ) < (L (m+1) : ℤ) ^ 2 := by linarith
  exact_mod_cast this

lemma bndF (m : ℕ) : L (m+1) ^ 2 ≤ L (m+2) * L m + L m := by
  have h := Fbound m
  simp only [F] at h
  have : (L (m+1) : ℤ) ^ 2 ≤ (L (m+2) : ℤ) * (L m : ℤ) + (L m : ℤ) := by linarith
  exact_mod_cast this

/-- The single nonlinear recurrence step matches the linear sequence. -/
lemma divstep (m : ℕ) :
    (L (m+1) ^ 2 + L m - 1) / L m - 1 = L (m+2) := by
  set N := L (m+1) ^ 2 with hN
  set D := L m with hD
  set k := L (m+2) with hk
  have hDpos : 0 < D := Lpos m
  have hp : k * D < N := posF m
  have hb : N ≤ k * D + D := bndF m
  have ek1 : (k + 1) * D = k * D + D := by ring
  have ek2 : (k + 1 + 1) * D = k * D + D + D := by ring
  have hq : (N + D - 1) / D = k + 1 := by
    apply Nat.div_eq_of_lt_le
    · rw [ek1]; omega
    · rw [ek2]; omega
  rw [hq]
  omega

lemma orig0 : A022030_original 0 = 4 := by rw [A022030_original]; simp
lemma orig1 : A022030_original 1 = 16 := by rw [A022030_original]; simp

lemma orig_rec (m : ℕ) :
    A022030_original (m+2) =
      (A022030_original (m+1) ^ 2 + A022030_original m - 1) / A022030_original m - 1 := by
  rw [A022030_original]
  have h0 : ¬ (m + 2 = 0) := by omega
  have h1 : ¬ (m + 2 = 1) := by omega
  rw [dif_neg h0, dif_neg h1]
  simp only [show m + 2 - 1 = m + 1 from rfl, show m + 2 - 2 = m from rfl]

/-- `A022030_original` agrees with the linear recurrence sequence `L`. -/
lemma orig_eq_L (n : ℕ) : A022030_original n = L n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [orig0]
    | 1 => simp [orig1]
    | (m+2) =>
      rw [orig_rec m]
      rw [ih (m+1) (by omega), ih m (by omega)]
      exact divstep m

end SpecAux

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
  simp only [SpecAux.orig_eq_L]
  match n with
  | 0 => simp
  | 1 => simp
  | 2 => simp
  | (k+3) =>
    have h0 : ¬ (k + 3 = 0) := by omega
    have h1 : ¬ (k + 3 = 1) := by omega
    have h2 : ¬ (k + 3 = 2) := by omega
    rw [if_neg h0, if_neg h1, if_neg h2]
    simp only [show k + 3 - 1 = k + 2 from rfl, show k + 3 - 3 = k from rfl]
    exact SpecAux.Lrec k
