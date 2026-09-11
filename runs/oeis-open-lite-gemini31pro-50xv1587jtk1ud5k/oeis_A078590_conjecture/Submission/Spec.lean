import FormalConjectures.Util.ProblemImports

namespace A078590

/--
Helper definition for A078590, indexed from 0.
a_val 0 corresponds to A078590(1).
a_val 1 corresponds to A078590(2).
a_val (n+2) corresponds to A078590(n+3).
The definition uses standard natural number division, relying on the conjecture that the division is exact.
-/
noncomputable def a_val : ℕ → ℕ
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

/--
oeis_78590_conjecture_0: Are all terms integers?
This is framed as a divisibility conjecture, ensuring that the division in the definition is exact at every step.
Specifically, for $n \ge 3$, $a(n-2)$ divides $2^{a(n-1)} + 1$.
-/
theorem oeis_A078590_conjecture : ∀ (n : ℕ), 3 ≤ n → A078590 (n-2) ∣ (2 ^ A078590 (n-1) + 1) := by sorry

lemma a_val_0 : a_val 0 = 1 := rfl
lemma a_val_1 : a_val 1 = 1 := rfl
lemma a_val_2 : a_val 2 = 3 := rfl
lemma a_val_3 : a_val 3 = 9 := rfl
lemma a_val_4 : a_val 4 = 171 := rfl
lemma a_val_5_eq : a_val 5 = (2 ^ 171 + 1) / 9 := by
  change (2 ^ a_val 4 + 1) / a_val 3 = (2 ^ 171 + 1) / 9
  rw [a_val_4, a_val_3]
lemma a_val_5_mod : a_val 5 % 18 = 3 := by rw [a_val_5_eq]; decide

lemma a_val_5_div : ∃ k, a_val 5 = 18 * k + 3 := by
  use a_val 5 / 18
  have h := a_val_5_mod
  omega

lemma two_pow_a_val_5_zmod : (2 : ZMod 19) ^ a_val 5 = 8 := by
  rcases a_val_5_div with ⟨k, hk⟩
  rw [hk, pow_add, pow_mul]
  have h1 : (2 : ZMod 19) ^ 18 = 1 := by decide
  rw [h1, one_pow, one_mul]
  decide

lemma not_19_dvd : ¬ 19 ∣ (2 ^ a_val 5 + 1) := by
  intro h
  have h2 : ((2 ^ a_val 5 + 1 : ℕ) : ZMod 19) = 0 := by
    rw [← CharP.cast_eq_zero_iff (ZMod 19) 19 (2 ^ a_val 5 + 1)] at h
    exact h
  have h3 : ((2 ^ a_val 5 + 1 : ℕ) : ZMod 19) = (2 : ZMod 19) ^ a_val 5 + 1 := by
    push_cast
    rfl
  rw [h3, two_pow_a_val_5_zmod] at h2
  revert h2
  decide

lemma not_171_dvd : ¬ 171 ∣ (2 ^ a_val 5 + 1) := by
  intro h
  have h19 : 19 ∣ 171 := by decide
  have h_dvd : 19 ∣ (2 ^ a_val 5 + 1) := dvd_trans h19 h
  exact not_19_dvd h_dvd

lemma A078590_5 : A078590 5 = 171 := by
  change (if 5 ≥ 1 then a_val 4 else 0) = 171
  have h : 5 ≥ 1 := by decide
  rw [if_pos h, a_val_4]

lemma A078590_6 : A078590 6 = a_val 5 := by
  change (if 6 ≥ 1 then a_val 5 else 0) = a_val 5
  have h : 6 ≥ 1 := by decide
  rw [if_pos h]

theorem oeis_A078590_conjecture.disproof : ¬ (type_of% @oeis_A078590_conjecture) := by
  intro h
  have h7 := h 7 (by decide)
  have h7_5 : 7 - 2 = 5 := rfl
  have h7_6 : 7 - 1 = 6 := rfl
  rw [h7_5, h7_6] at h7
  rw [A078590_5, A078590_6] at h7
  exact not_171_dvd h7
