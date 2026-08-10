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
private theorem A078590_five_dvd19 : 19 ∣ A078590 (7 - 2) := by
  norm_num [A078590, a_val]

private theorem A078590_six_mod18 : A078590 6 % 18 = 3 := by
  norm_num [A078590, a_val]

private theorem A078590_counterexample_at_seven : ¬ A078590 (7 - 2) ∣ (2 ^ A078590 (7 - 1) + 1 : ℕ) := by
  rintro ⟨k, hk⟩
  have hA0 : ((A078590 (7 - 2) : ℕ) : ZMod 19) = 0 := by
    exact (ZMod.natCast_eq_zero_iff _ _).mpr A078590_five_dvd19
  have hz : ((2 ^ A078590 (7 - 1) + 1 : ℕ) : ZMod 19) = 0 := by
    rw [hk, Nat.cast_mul, hA0, zero_mul]
  rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow] at hz
  change ((2 : ZMod 19) ^ A078590 (7 - 1)) + 1 = 0 at hz
  rw [pow_eq_pow_mod _ (by decide : (2 : ZMod 19) ^ 18 = 1)] at hz
  have hA6mod' : A078590 (7 - 1) % 18 = 3 := by
    simpa only [Nat.reduceSub] using A078590_six_mod18
  rw [hA6mod'] at hz
  norm_num at hz
  exact (by decide : (9 : ZMod 19) ≠ 0) hz

theorem oeis_A078590_conjecture.disproof : ¬ (∀ (n : ℕ), 3 ≤ n → A078590 (n-2) ∣ (2 ^ A078590 (n-1) + 1)) := by
  intro h
  exact A078590_counterexample_at_seven (h 7 (by norm_num))

