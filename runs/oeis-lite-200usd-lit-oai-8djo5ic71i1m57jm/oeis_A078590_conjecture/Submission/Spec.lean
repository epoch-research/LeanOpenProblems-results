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
private theorem A078590_five : A078590 5 = 171 := by
  norm_num [A078590, a_val]

private theorem A078590_six_mod : A078590 6 % 18 = 3 := by
  norm_num [A078590, a_val]

private theorem zmod19_pow_A078590_six : (2 : ZMod 19) ^ A078590 6 + 1 = 9 := by
  obtain ⟨k, hk⟩ : ∃ k, A078590 6 = 18 * k + 3 := by
    rcases (Nat.mod_eq_iff.mp A078590_six_mod) with hbad | hgood
    · rcases hbad with ⟨h18, _⟩
      norm_num at h18
    · rcases hgood with ⟨_, k, hk⟩
      exact ⟨k, hk⟩
  rw [hk, pow_add, pow_mul]
  change (262144 : ZMod 19) ^ k * 8 + 1 = 9
  have hbase : (262144 : ZMod 19) = 1 := by decide
  rw [hbase]
  norm_num

theorem oeis_A078590_conjecture.disproof : ¬ ∀ (n : ℕ), 3 ≤ n → A078590 (n-2) ∣ (2 ^ A078590 (n-1) + 1) := by
  intro h
  have h7 := h 7 (by norm_num)
  have hleft : 19 ∣ A078590 (7 - 2) := by
    rw [show 7 - 2 = 5 by norm_num, A078590_five]
    norm_num
  have h19 : 19 ∣ 2 ^ A078590 (7 - 1) + 1 := dvd_trans hleft h7
  have hzero : ((2 ^ A078590 (7 - 1) + 1 : ℕ) : ZMod 19) = 0 := by
    exact (CharP.cast_eq_zero_iff (ZMod 19) 19 _).2 h19
  have hresZ : (2 : ZMod 19) ^ A078590 (7 - 1) + 1 = 9 := by
    simpa only [Nat.reduceSub] using zmod19_pow_A078590_six
  have hres : ((2 ^ A078590 (7 - 1) + 1 : ℕ) : ZMod 19) = 9 := by
    norm_num only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]
    exact hresZ
  rw [hres] at hzero
  have hne : (9 : ZMod 19) ≠ 0 := by decide
  exact hne hzero
