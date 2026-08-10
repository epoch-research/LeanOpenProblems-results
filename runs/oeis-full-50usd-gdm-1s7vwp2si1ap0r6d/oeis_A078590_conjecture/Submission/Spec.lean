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

/--
oeis_78590_conjecture_0: Are all terms integers?
This is framed as a divisibility conjecture, ensuring that the division in the definition is exact at every step.
Specifically, for $n \ge 3$, $a(n-2)$ divides $2^{a(n-1)} + 1$.
-/
def E : ℕ := (2^171 + 1) / 9

theorem A078590_5 : A078590 5 = 171 := rfl
theorem A078590_6_eq_E : A078590 6 = E := rfl

attribute [irreducible] A078590


theorem E_decomp : E = 18 * (E / 18) + 3 := by
  have h := Nat.div_add_mod E 18
  -- h : 18 * (E / 18) + E % 18 = E
  have h_mod : E % 18 = 3 := rfl
  rw [h_mod] at h
  exact h.symm


theorem zmod_18 : (2 : ZMod 19) ^ 18 = 1 := by decide

theorem zmod_E : (2 : ZMod 19) ^ E = 8 := by
  have h_decomp := E_decomp
  rw [h_decomp]
  rw [pow_add]
  rw [pow_mul]
  rw [zmod_18]
  rw [one_pow]
  rw [one_mul]
  decide

theorem dvd_zmod_zero (X : ℕ) (h : 19 ∣ X) : (X : ZMod 19) = 0 := by
  rcases h with ⟨c, rfl⟩
  push_cast
  have h19 : (19 : ZMod 19) = 0 := rfl
  rw [h19, zero_mul]

theorem zmod_E_ne_zero : ((2 ^ E + 1 : ℕ) : ZMod 19) ≠ 0 := by
  push_cast
  rw [zmod_E]
  decide

theorem not_dvd_19 : ¬ (19 ∣ 2 ^ E + 1) := by
  intro h
  have hz := dvd_zmod_zero _ h
  exact zmod_E_ne_zero hz

theorem not_dvd_171_of_not_dvd_19 (X : ℕ) (h : ¬ (19 ∣ X)) : ¬ (171 ∣ X) := by
  intro h171
  have h19_171 : 19 ∣ 171 := by decide
  have h19_X : 19 ∣ X := dvd_trans h19_171 h171
  exact h h19_X

theorem not_dvd_171 : ¬ (171 ∣ 2 ^ E + 1) :=
  not_dvd_171_of_not_dvd_19 (2 ^ E + 1) not_dvd_19

theorem counterexample_not_dvd : ¬ (A078590 5 ∣ 2 ^ A078590 6 + 1) := by
  rw [A078590_5, A078590_6_eq_E]
  exact not_dvd_171


theorem counterexample (n : ℕ) (hn : n = 7) : ¬ (A078590 (n-2) ∣ 2 ^ A078590 (n-1) + 1) := by
  have hn2 : n - 2 = 5 := by rw [hn]
  have hn1 : n - 1 = 6 := by rw [hn]
  rw [hn2, hn1]
  rw [A078590_5, A078590_6_eq_E]
  exact not_dvd_171

theorem oeis_A078590_conjecture.disproof : ¬ (∀ (n : ℕ), 3 ≤ n → A078590 (n-2) ∣ (2 ^ A078590 (n-1) + 1)) := by
  intro h
  let n := 7
  have hn : n = 7 := rfl
  have h3 : 3 ≤ n := by decide
  have h_div := h n h3
  have h_not := counterexample n hn
  exact h_not h_div
