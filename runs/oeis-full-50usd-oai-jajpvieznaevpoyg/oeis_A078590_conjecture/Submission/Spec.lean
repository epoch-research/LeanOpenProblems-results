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
theorem oeis_A078590_conjecture.disproof : ¬ (∀ (n : ℕ), 3 ≤ n → A078590 (n-2) ∣ (2 ^ A078590 (n-1) + 1)) := by
  intro h
  let X : ℕ := 332572817028187686275682948600327513806149983112761
  have h7 : A078590 (7 - 2) ∣ (2 ^ A078590 (7 - 1) + 1) := h 7 (by norm_num)
  have hA5 : A078590 (7 - 2) = 171 := by
    norm_num [A078590, A078590.a_val]
  have hA6 : A078590 (7 - 1) = X := by
    norm_num [A078590, A078590.a_val]
  rw [hA5, hA6] at h7
  have hX : X = 18 * (X / 18) + 3 := by
    norm_num
  have hbase : (2 ^ 18) ≡ 1 [MOD 171] := by
    norm_num [Nat.ModEq]
  have hp : (2 ^ 18) ^ (X / 18) ≡ 1 [MOD 171] := by
    simpa using Nat.ModEq.pow (X / 18) hbase
  have hcong : (2 ^ X + 1) ≡ 9 [MOD 171] := by
    rw [hX, pow_add, pow_mul]
    have hmul : (2 ^ 18) ^ (X / 18) * 2 ^ 3 ≡ 1 * 8 [MOD 171] := by
      simpa using hp.mul (Nat.ModEq.refl (2 ^ 3))
    have hadd : (2 ^ 18) ^ (X / 18) * 2 ^ 3 + 1 ≡ 1 * 8 + 1 [MOD 171] :=
      hmul.add (Nat.ModEq.refl 1)
    simpa using hadd
  have hz : (2 ^ X + 1) ≡ 0 [MOD 171] := Nat.modEq_zero_iff_dvd.mpr h7
  have bad : 9 ≡ 0 [MOD 171] := hcong.symm.trans hz
  norm_num [Nat.ModEq] at bad
