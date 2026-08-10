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

/-- Linear-recurrence sequence with the conjectured generating function
`(4 - x^2)/(1 - 4x + x^3)`: `b 0 = 4`, `b 1 = 16`, `b 2 = 63`,
and `b (n+3) = 4 * b (n+2) - b n`. -/
def bSeq : ℕ → ℤ
  | 0 => 4
  | 1 => 16
  | 2 => 63
  | (n+3) => 4 * bSeq (n+2) - bSeq n

theorem bSeq_rec (n : ℕ) : bSeq (n+3) = 4 * bSeq (n+2) - bSeq n := by simp [bSeq]

theorem bSeq_props : ∀ n, 1 ≤ bSeq n ∧ 3 * bSeq n ≤ bSeq (n+1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => refine ⟨by simp [bSeq], by simp [bSeq]⟩
    | 1 => refine ⟨by simp [bSeq], by simp [bSeq]⟩
    | 2 => refine ⟨by simp [bSeq], by simp [bSeq]⟩
    | (m+3) =>
      have h0 := ih m (by omega)
      have h1 := ih (m+1) (by omega)
      have h2 := ih (m+2) (by omega)
      have eq3 : bSeq (m+3) = 4 * bSeq (m+2) - bSeq m := bSeq_rec m
      have eq4 : bSeq (m+3+1) = 4 * bSeq (m+3) - bSeq (m+1) := bSeq_rec (m+1)
      refine ⟨by linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2], ?_⟩
      rw [eq4]
      linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2]

/-- The key quadratic invariant `D n = bSeq (n+1)^2 - bSeq n * bSeq (n+2)`. -/
def DSeq (n : ℕ) : ℤ := bSeq (n+1)^2 - bSeq n * bSeq (n+2)

theorem DSeq_rec (n : ℕ) : DSeq (n+3) = 4 * DSeq (n+1) + DSeq n := by
  have e3 : bSeq (n+3) = 4 * bSeq (n+2) - bSeq n := bSeq_rec n
  have e4 : bSeq (n+4) = 4 * bSeq (n+3) - bSeq (n+1) := bSeq_rec (n+1)
  have e5 : bSeq (n+5) = 4 * bSeq (n+4) - bSeq (n+2) := bSeq_rec (n+2)
  simp only [DSeq]
  ring_nf
  ring_nf at e3 e4 e5
  rw [e5, e4, e3]
  ring

theorem DSeq_pos : ∀ n, 1 ≤ DSeq n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | (m+3) =>
      have hm := ih m (by omega)
      have hm1 := ih (m+1) (by omega)
      rw [DSeq_rec m]
      linarith

theorem DSeq_bound : ∀ n, DSeq n ≤ bSeq n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | (m+3) =>
      have hm := ih m (by omega)
      have hm1 := ih (m+1) (by omega)
      have g0 := bSeq_props m
      have g1 := bSeq_props (m+1)
      have eb : bSeq (m+3) = 4 * bSeq (m+2) - bSeq m := bSeq_rec m
      rw [eb, DSeq_rec m]
      linarith [g0.1, g0.2, g1.1, g1.2, hm, hm1]

theorem A022030_original_zero : A022030_original 0 = 4 := by rw [A022030_original]; simp
theorem A022030_original_one : A022030_original 1 = 16 := by rw [A022030_original]; simp

theorem A022030_original_unfold (k : ℕ) :
    A022030_original (k+2) =
      ((A022030_original (k+1))^2 + A022030_original k - 1) / A022030_original k - 1 := by
  rw [A022030_original, dif_neg (by omega : k+2 ≠ 0), dif_neg (by omega : k+2 ≠ 1)]
  simp only [show k+2-1 = k+1 from by omega, show k+2-2 = k from by omega]

theorem A022030_original_eq_bSeq : ∀ n, A022030_original n = (bSeq n).toNat := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rw [A022030_original_zero]; decide
    | 1 => rw [A022030_original_one]; decide
    | (k+2) =>
      have ih1 := ih (k+1) (by omega)
      have ih0 := ih k (by omega)
      rw [A022030_original_unfold k, ih1, ih0]
      have nb0 : (0:ℤ) ≤ bSeq k := by linarith [(bSeq_props k).1]
      have nb1 : (0:ℤ) ≤ bSeq (k+1) := by linarith [(bSeq_props (k+1)).1]
      have nb2 : (0:ℤ) ≤ bSeq (k+2) := by linarith [(bSeq_props (k+2)).1]
      have hP : ((bSeq (k+1)).toNat : ℤ) = bSeq (k+1) := Int.toNat_of_nonneg nb1
      have hQ : ((bSeq k).toNat : ℤ) = bSeq k := Int.toNat_of_nonneg nb0
      have hR : ((bSeq (k+2)).toNat : ℤ) = bSeq (k+2) := Int.toNat_of_nonneg nb2
      have hDk : ((DSeq k).toNat : ℤ) = DSeq k := Int.toNat_of_nonneg (by linarith [DSeq_pos k])
      set P := (bSeq (k+1)).toNat with hPdef
      set Q := (bSeq k).toNat with hQdef
      set R := (bSeq (k+2)).toNat with hRdef
      set Dk := (DSeq k).toNat with hDkdef
      have keyint : (bSeq (k+1))^2 = bSeq k * bSeq (k+2) + DSeq k := by unfold DSeq; ring
      have hP2 : P ^ 2 = Q * R + Dk := by
        have : (P : ℤ) ^ 2 = (Q : ℤ) * (R : ℤ) + (Dk : ℤ) := by
          rw [hP, hQ, hR, hDk]; exact keyint
        exact_mod_cast this
      have hQpos : 0 < Q := by
        have : (1:ℤ) ≤ (Q : ℤ) := by rw [hQ]; exact (bSeq_props k).1
        exact_mod_cast this
      have hDk1 : 1 ≤ Dk := by
        have : (1:ℤ) ≤ (Dk : ℤ) := by rw [hDk]; exact DSeq_pos k
        exact_mod_cast this
      have hDkQ : Dk ≤ Q := by
        have : (Dk : ℤ) ≤ (Q : ℤ) := by rw [hDk, hQ]; exact DSeq_bound k
        exact_mod_cast this
      rw [hP2]
      have key : Q * R + Dk + Q - 1 = (Dk - 1) + Q * (R + 1) := by
        have : Q * (R + 1) = Q * R + Q := by ring
        omega
      rw [key, Nat.add_mul_div_left _ _ hQpos, Nat.div_eq_of_lt (show Dk - 1 < Q by omega)]
      omega

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
  match n with
  | 0 => rw [A022030_original_zero, if_pos (rfl : (0:ℕ) = 0)]
  | 1 => rw [A022030_original_one, if_neg (by omega : (1:ℕ) ≠ 0), if_pos (rfl : (1:ℕ) = 1)]
  | 2 =>
    rw [A022030_original_eq_bSeq 2, if_neg (by omega : (2:ℕ) ≠ 0), if_neg (by omega : (2:ℕ) ≠ 1),
        if_pos (rfl : (2:ℕ) = 2)]
    decide
  | (m+3) =>
    rw [if_neg (by omega : m+3 ≠ 0), if_neg (by omega : m+3 ≠ 1), if_neg (by omega : m+3 ≠ 2)]
    simp only [show m+3-1 = m+2 from by omega, show m+3-3 = m from by omega]
    rw [A022030_original_eq_bSeq (m+3), A022030_original_eq_bSeq (m+2), A022030_original_eq_bSeq m]
    have eb : bSeq (m+3) = 4 * bSeq (m+2) - bSeq m := bSeq_rec m
    have nb_m : (0:ℤ) ≤ bSeq m := by linarith [(bSeq_props m).1]
    have nb_m2 : (0:ℤ) ≤ bSeq (m+2) := by linarith [(bSeq_props (m+2)).1]
    have nb_m3 : (0:ℤ) ≤ bSeq (m+3) := by linarith [(bSeq_props (m+3)).1]
    have hm : ((bSeq m).toNat : ℤ) = bSeq m := Int.toNat_of_nonneg nb_m
    have hm2 : ((bSeq (m+2)).toNat : ℤ) = bSeq (m+2) := Int.toNat_of_nonneg nb_m2
    have hm3 : ((bSeq (m+3)).toNat : ℤ) = bSeq (m+3) := Int.toNat_of_nonneg nb_m3
    have hCint : ((bSeq (m+3)).toNat : ℤ)
        = 4 * ((bSeq (m+2)).toNat : ℤ) - ((bSeq m).toNat : ℤ) := by
      rw [hm3, hm2, hm]; exact eb
    omega
