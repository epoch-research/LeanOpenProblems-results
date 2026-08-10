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
def L : ℕ → ℤ
  | 0 => 4
  | 1 => 16
  | 2 => 63
  | n + 3 => 4 * L (n + 2) - L n

def D : ℕ → ℤ
  | 0 => 4
  | 1 => 1
  | 2 => 16
  | n + 3 => 4 * D (n + 1) + D n

theorem L_rel (n : ℕ) : L (n + 1) ^ 2 - L (n + 2) * L n = D n := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | _ | _ | n
  · rfl
  · rfl
  · rfl
  · -- n + 3 case
    have ih1 := ih (n + 1) (by omega)
    have ih2 := ih n (by omega)
    change L (n + 4) ^ 2 - L (n + 5) * L (n + 3) = 4 * D (n + 1) + D n
    rw [← ih1, ← ih2]
    have h3 : L (n + 3) = 4 * L (n + 2) - L n := rfl
    have h4 : L (n + 4) = 4 * L (n + 3) - L (n + 1) := rfl
    have h5 : L (n + 5) = 4 * L (n + 4) - L (n + 2) := rfl
    rw [h5, h4, h3]
    ring

theorem L_pos_and_increasing (n : ℕ) : L n > 0 ∧ L (n + 1) ≥ 3 * L n := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | _ | n
  · decide
  · decide
  · -- n + 2 case, which is (n + 2)
    have ih1 := ih (n + 1) (by omega)
    have ih0 := ih n (by omega)
    have h_pos1 : L (n + 1) > 0 := ih1.1
    have h_inc1 : L (n + 2) ≥ 3 * L (n + 1) := ih1.2
    have h_pos0 : L n > 0 := ih0.1
    have h_inc0 : L (n + 1) ≥ 3 * L n := ih0.2
    have h_pos2 : L (n + 2) > 0 := by linarith
    refine ⟨h_pos2, ?_⟩
    have h3 : L (n + 3) = 4 * L (n + 2) - L n := rfl
    rw [h3]
    linarith

theorem D_pos (n : ℕ) : D n > 0 := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | _ | _ | n
  · decide
  · decide
  · decide
  · change 4 * D (n + 1) + D n > 0
    have ih1 : D (n + 1) > 0 := ih (n + 1) (by omega)
    have ih0 : D n > 0 := ih n (by omega)
    omega

def l (n : ℕ) : ℕ := (L n).toNat
def d (n : ℕ) : ℕ := (D n).toNat

theorem L_toNat (n : ℕ) : (l n : ℤ) = L n := by
  have := (L_pos_and_increasing n).1
  exact Int.toNat_of_nonneg (by omega)

theorem D_toNat (n : ℕ) : (d n : ℤ) = D n := by
  have := D_pos n
  exact Int.toNat_of_nonneg (by omega)

theorem l_rel (n : ℕ) : l (n + 1) ^ 2 = l (n + 2) * l n + d n := by
  apply Int.ofNat.inj
  change ((l (n + 1) ^ 2 : ℤ) = (l (n + 2) * l n + d n : ℤ))
  rw [L_toNat, L_toNat, L_toNat, D_toNat]
  have h := L_rel n
  omega

theorem D_le_L (n : ℕ) : D n ≤ L n := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | _ | _ | n
  · decide
  · decide
  · decide
  · -- n + 3 case
    change 4 * D (n + 1) + D n ≤ L (n + 3)
    have ih1 := ih (n + 1) (by omega)
    have ih0 := ih n (by omega)
    have h3 : L (n + 3) = 4 * L (n + 2) - L n := rfl
    rw [h3]
    have h_inc2 := (L_pos_and_increasing (n + 1)).2
    have h_inc1 := (L_pos_and_increasing n).2
    have h_pos := (L_pos_and_increasing n).1
    linarith

theorem d_le_l (n : ℕ) : d n ≤ l n := by
  have h := D_le_L n
  exact Int.ofNat_le.mp (by rw [D_toNat, L_toNat]; exact h)

theorem my_div_eq_one (B C : ℕ) (hB : 0 < B) (h1 : B ≤ C) (h2 : C < 2 * B) : C / B = 1 := by
  have h_ge : 1 ≤ C / B := (Nat.le_div_iff_mul_le hB).mpr (by omega)
  have h_lt : C / B < 2 := Nat.div_lt_of_lt_mul (by omega)
  omega

theorem b_recurrence (n : ℕ) : l (n + 2) = (l (n + 1) ^ 2 + l n - 1) / l n - 1 := by
  have hl_pos : 0 < l n := by
    have h := (L_pos_and_increasing n).1
    have h_cast := L_toNat n
    omega
  have h_rel := l_rel n
  have h_num : l (n + 1) ^ 2 + l n - 1 = (d n + l n - 1) + l (n + 2) * l n := by
    omega
  rw [h_num]
  rw [Nat.add_mul_div_right _ _ hl_pos]
  have hd_pos : d n > 0 := by
    have h := D_pos n
    have h_cast := D_toNat n
    omega
  have hd_le := d_le_l n
  have h_div : (d n + l n - 1) / l n = 1 := by
    apply my_div_eq_one (l n) (d n + l n - 1) hl_pos
    · omega
    · omega
  rw [h_div]
  omega

theorem A022030_original_eq_l (n : ℕ) : A022030_original n = l n := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | _ | n
  · rw [A022030_original]
    rw [dif_pos (by rfl)]
    rfl
  · rw [A022030_original]
    have h_not0 : ¬ (1 = 0) := by decide
    rw [dif_neg h_not0, dif_pos (by rfl)]
    rfl
  · -- n + 2 case
    rw [A022030_original]
    have h0 : ¬ (n + 2 = 0) := by omega
    have h1 : ¬ (n + 2 = 1) := by omega
    rw [dif_neg h0, dif_neg h1]
    dsimp only
    have h_sub1 : n + 2 - 1 = n + 1 := by omega
    have h_sub2 : n + 2 - 2 = n := by omega
    rw [h_sub1, h_sub2]
    rw [ih (n + 1) (by omega), ih n (by omega)]
    exact (b_recurrence n).symm

theorem l_recurrence (n : ℕ) :
  l n = (
    if n = 0 then 4
    else if n = 1 then 16
    else if n = 2 then 63
    else
      4 * (l (n - 1)) - (l (n - 3))
  ) := by
  rcases n with _ | _ | _ | n
  · rfl
  · rfl
  · rfl
  · -- n + 3 case
    have h0 : ¬ (n + 3 = 0) := by omega
    have h1 : ¬ (n + 3 = 1) := by omega
    have h2 : ¬ (n + 3 = 2) := by omega
    rw [if_neg h0, if_neg h1, if_neg h2]
    change (L (n + 3)).toNat = 4 * (L (n + 2)).toNat - (L n).toNat
    have h3 : L (n + 3) = 4 * L (n + 2) - L n := rfl
    rw [h3]
    have h_pos : L n ≥ 0 := by
      have := (L_pos_and_increasing n).1
      omega
    have h_pos2 : L (n + 2) ≥ 0 := by
      have := (L_pos_and_increasing (n + 2)).1
      omega
    have h_le : L n ≤ 4 * L (n + 2) := by
      have h1 := (L_pos_and_increasing n).2
      have h2 := (L_pos_and_increasing (n + 1)).2
      change L (n + 2) ≥ 3 * L (n + 1) at h2
      omega
    omega

theorem oeis_22030_original_conjecture (n : ℕ) :
  A022030_original n = (
    if n = 0 then 4
    else if n = 1 then 16
    else if n = 2 then 63
    else
      4 * (A022030_original (n - 1)) - (A022030_original (n - 3))
  ) := by
  rw [A022030_original_eq_l n]
  rw [A022030_original_eq_l (n - 1)]
  rw [A022030_original_eq_l (n - 3)]
  exact l_recurrence n
