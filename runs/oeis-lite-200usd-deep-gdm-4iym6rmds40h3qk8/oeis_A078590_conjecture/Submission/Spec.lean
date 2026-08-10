import FormalConjectures.Util.ProblemImports

namespace A078590

/--
Helper definition for A078590, indexed from 0.
a_val 0 corresponds to A078590(1).
a_val 1 corresponds to A078590(2).
a_val (n+2) corresponds to A078590(n+3).
The definition uses standard natural number division, relying on the conjecture that the division is exact.
-/
private def a_val : ℕ → ℕ
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
def A078590 (n : ℕ) : ℕ :=
  if n ≥ 1 then
    a_val (n - 1)
  else
    0

/--
oeis_78590_conjecture_0: Are all terms integers?
This is framed as a divisibility conjecture, ensuring that the division in the definition is exact at every step.
Specifically, for $n \ge 3$, $a(n-2)$ divides $2^{a(n-1)} + 1$.
-/
theorem a5_eq : A078590 5 = 171 := rfl
theorem a6_eq : A078590 6 = 332572817028187686275682948600327513806149983112761 := rfl
theorem a6_mod_18 : A078590 6 % 18 = 3 := rfl
lemma pow_mod_18 (n : ℕ) : (2 : ZMod 19) ^ n = (2 : ZMod 19) ^ (n % 18) := by
  have h := Nat.div_add_mod n 18
  nth_rw 1 [← h]
  rw [pow_add, pow_mul]
  have h18 : (2 : ZMod 19) ^ 18 = 1 := rfl
  rw [h18, one_pow, one_mul]

theorem a6_pow_zmod_19 : (2 : ZMod 19) ^ A078590 6 + 1 = 9 := by
  rw [pow_mod_18]
  rw [a6_mod_18]
  rfl

theorem a5_zmod_19 : (A078590 5 : ZMod 19) = 0 := rfl

theorem nine_ne_zero : (9 : ZMod 19) ≠ 0 := by decide

attribute [irreducible] A078590

theorem oeis_A078590_conjecture.disproof : ¬ (∀ (n : ℕ), 3 ≤ n → A078590 (n-2) ∣ (2 ^ A078590 (n-1) + 1)) := by
  intro h
  have h7 : 3 ≤ 7 := by decide
  have h_div := h 7 h7
  rcases h_div with ⟨k, hk⟩
  have h_six : 7 - 1 = 6 := rfl
  have h_five : 7 - 2 = 5 := rfl
  rw [h_six, h_five] at hk
  have h_zmod := congrArg (fun x : ℕ => (x : ZMod 19)) hk
  push_cast at h_zmod
  rw [a6_pow_zmod_19] at h_zmod
  rw [a5_zmod_19, zero_mul] at h_zmod
  exact nine_ne_zero h_zmod









