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
private lemma two_pow_mod19_of_mod18_eq_3 (n : ℕ) (h : n % 18 = 3) :
    (2 ^ n) % 19 = 8 := by
  have hn : n = 18 * (n / 18) + 3 := by
    rw [← h]
    exact (Nat.div_add_mod n 18).symm
  rw [hn, pow_add, pow_mul]
  have hbase : (2 ^ 18) ≡ 1 [MOD 19] := by norm_num [Nat.ModEq]
  have hpow : (2 ^ 18) ^ (n / 18) ≡ 1 ^ (n / 18) [MOD 19] := hbase.pow _
  have hmul : (2 ^ 18) ^ (n / 18) * 2 ^ 3 ≡ 1 ^ (n / 18) * 8 [MOD 19] := by
    exact hpow.mul (by norm_num [Nat.ModEq])
  simpa [Nat.ModEq] using hmul

theorem oeis_A078590_conjecture.disproof :
    ¬ (∀ (n : ℕ), 3 ≤ n → A078590 (n-2) ∣ (2 ^ A078590 (n-1) + 1)) := by
  intro h
  have h7 : A078590 (7 - 2) ∣ (2 ^ A078590 (7 - 1) + 1) := h 7 (by norm_num)
  have hA5 : A078590 (7 - 2) = 171 := by norm_num [A078590, A078590.a_val]
  rw [hA5] at h7
  have h19 : 19 ∣ 2 ^ A078590 (7 - 1) + 1 :=
    dvd_trans (by norm_num : 19 ∣ 171) h7
  have hzero : 2 ^ A078590 (7 - 1) + 1 ≡ 0 [MOD 19] :=
    Nat.modEq_zero_iff_dvd.mpr h19
  have hpoweq : (2 ^ A078590 (7 - 1)) % 19 = 8 := by
    apply two_pow_mod19_of_mod18_eq_3
    norm_num [A078590, A078590.a_val]
  have hpowmod : 2 ^ A078590 (7 - 1) ≡ 8 [MOD 19] := hpoweq
  have hsum : 2 ^ A078590 (7 - 1) + 1 ≡ 9 [MOD 19] := by
    simpa using hpowmod.add (Nat.ModEq.refl 1 : 1 ≡ 1 [MOD 19])
  have hbad : 9 ≡ 0 [MOD 19] := hsum.symm.trans hzero
  norm_num [Nat.ModEq] at hbad
