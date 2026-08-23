import FormalConjectures.Util.ProblemImports

namespace A078590

/--
Helper definition for A078590, indexed from 0.
a_val 0 corresponds to A078590(1).
a_val 1 corresponds to A078590(2).
a_val (n+2) corresponds to A078590(n+3).
The definition uses standard natural number division, relying on the conjecture that the division is exact.
-/
private noncomputable def a_val : ℕ → ℕ
| 0 => 1
| 1 => 1
| n + 2 =>
  let a_n_minus_2 : ℕ := a_val n
  let a_n_minus_1 : ℕ := a_val (n + 1)

  -- The division is Nat.div, which is integer division.
  -- The terms are positive, so we do not fear division by zero.
  (2 ^ a_n_minus_1 + 1) / a_n_minus_2

end A078590

open A078590

/--
A078590: $a(1)=1$, $a(2)=1$, $a(n)=(2^{a(n-1)} + 1)/a(n-2)$.
Are all terms integers?
-/
noncomputable def A078590 (n : ℕ) : ℕ :=
  if n ≥ 1 then
    a_val (n - 1)
  else
    0

lemma A078590_eq_a_val {n : ℕ} (hn : 1 ≤ n) : A078590 n = a_val (n - 1) :=
  if_pos hn

lemma a_val_zero : a_val 0 = 1 := rfl
lemma a_val_one : a_val 1 = 1 := rfl
lemma a_val_add_two (k : ℕ) : a_val (k + 2) = (2 ^ a_val (k + 1) + 1) / a_val k := rfl

-- Prevent the kernel from evaluating `A078590 6` to a ~50-digit numeral
-- (which would make `2 ^ A078590 6` infeasible to reduce).
attribute [irreducible] a_val A078590

/-- The defining recurrence, for `n ≥ 1`. -/
lemma A078590_add_two (n : ℕ) (hn : 1 ≤ n) :
    A078590 (n + 2) = (2 ^ A078590 (n + 1) + 1) / A078590 n := by
  rw [A078590_eq_a_val (by omega : 1 ≤ n + 2)]
  rw [A078590_eq_a_val (by omega : 1 ≤ n + 1)]
  rw [A078590_eq_a_val hn]
  rw [show n + 2 - 1 = n - 1 + 2 from (by omega)]
  rw [a_val_add_two]
  rw [show n - 1 + 1 = n from (by omega)]
  rw [Nat.add_sub_cancel]

lemma A078590_one : A078590 1 = 1 := by
  rw [A078590_eq_a_val (by decide), a_val_zero]

lemma A078590_two : A078590 2 = 1 := by
  rw [A078590_eq_a_val (by decide), a_val_one]

lemma A078590_three : A078590 3 = 3 := by
  rw [show 3 = 1 + 2 from rfl, A078590_add_two 1 (by decide), A078590_one, A078590_two]
  decide

lemma A078590_four : A078590 4 = 9 := by
  rw [show 4 = 2 + 2 from rfl, A078590_add_two 2 (by decide), A078590_two, A078590_three]
  decide

lemma A078590_five : A078590 5 = 171 := by
  rw [show 5 = 3 + 2 from rfl, A078590_add_two 3 (by decide), A078590_three, A078590_four]
  decide

lemma A078590_six : A078590 6 = (2 ^ 171 + 1) / 9 := by
  rw [show 6 = 4 + 2 from rfl, A078590_add_two 4 (by decide), A078590_four, A078590_five]

lemma two_pow_171_add_one_mod_162 : (2 ^ 171 + 1) % 162 = 27 := by
  norm_num

/-- `A078590 6 = 18 * q + 3` for `q = (2^171 + 1) / 162`. -/
lemma A078590_six_eq_mul_add :
    A078590 6 = 18 * ((2 ^ 171 + 1) / 162) + 3 := by
  rw [A078590_six]
  let q := (2 ^ 171 + 1) / 162
  have hdecomp : 2 ^ 171 + 1 = 162 * q + 27 := by
    calc
      2 ^ 171 + 1 = 162 * ((2 ^ 171 + 1) / 162) + (2 ^ 171 + 1) % 162 :=
        (Nat.div_add_mod _ _).symm
      _ = 162 * q + 27 := by rw [two_pow_171_add_one_mod_162]
  calc
    (2 ^ 171 + 1) / 9 = (162 * q + 27) / 9 := by rw [hdecomp]
    _ = (9 * (18 * q + 3)) / 9 := by ring
    _ = 18 * q + 3 := Nat.mul_div_cancel_left _ (by decide)

lemma two_pow_18_mod_19 : 2 ^ 18 ≡ 1 [MOD 19] := by
  change 2 ^ 18 % 19 = 1 % 19
  decide

/-- `2^{A078590 6} ≡ 8 [MOD 19]`. -/
lemma two_pow_A078590_six_mod_19 : 2 ^ A078590 6 ≡ 8 [MOD 19] := by
  rw [A078590_six_eq_mul_add, pow_add, pow_mul]
  set q := (2 ^ 171 + 1) / 162
  have hpow : (2 ^ 18) ^ q ≡ 1 [MOD 19] := by
    simpa [one_pow] using two_pow_18_mod_19.pow q
  have h8 : 2 ^ 3 ≡ 8 [MOD 19] := by decide
  simpa using hpow.mul h8

lemma nineteen_not_dvd_two_pow_A078590_six_add_one : ¬19 ∣ 2 ^ A078590 6 + 1 := by
  intro h
  have h0 : 2 ^ A078590 6 + 1 ≡ 0 [MOD 19] := h.modEq_zero_nat
  have h9 : 2 ^ A078590 6 + 1 ≡ 9 [MOD 19] :=
    two_pow_A078590_six_mod_19.add_right 1
  have : 9 ≡ 0 [MOD 19] := h9.symm.trans h0
  change 9 % 19 = 0 % 19 at this
  exact (by decide : 9 % 19 ≠ 0) this

lemma one_seven_one_not_dvd_two_pow_A078590_six_add_one : ¬171 ∣ 2 ^ A078590 6 + 1 := by
  intro h
  exact nineteen_not_dvd_two_pow_A078590_six_add_one
    (dvd_trans (by decide : 19 ∣ 171) h)

/--
oeis_78590_conjecture_0: Are all terms integers?
This is framed as a divisibility conjecture, ensuring that the division in the definition is exact at every step.
Specifically, for $n \ge 3$, $a(n-2)$ divides $2^{a(n-1)} + 1$.
-/
theorem oeis_A078590_conjecture.disproof :
    ¬∀ (n : ℕ), 3 ≤ n → A078590 (n-2) ∣ (2 ^ A078590 (n-1) + 1) := by
  intro h
  have h7 := h 7 (by decide)
  rw [show (7 - 2 : ℕ) = 5 from rfl, show (7 - 1 : ℕ) = 6 from rfl] at h7
  rw [A078590_five] at h7
  exact one_seven_one_not_dvd_two_pow_A078590_six_add_one h7



