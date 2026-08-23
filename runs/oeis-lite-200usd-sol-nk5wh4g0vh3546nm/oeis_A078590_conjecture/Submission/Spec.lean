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
  have h7 := h 7 (by norm_num)
  have h19 : 19 ∣ A078590 (7 - 2) := by
    norm_num [A078590, a_val]
  have he : A078590 (7 - 1) ≡ 3 [MOD 18] := by
    change ((2 ^ 171 + 1) / 9) ≡ 3 [MOD 18]
    rw [Nat.ModEq]
    rw [← Nat.mod_mul_right_div_self]
    norm_num
  let u : (ZMod 19)ˣ := ZMod.unitOfCoprime 2 (by norm_num)
  have hu : (u : ZMod 19) = 2 := by rfl
  have hm : 2 ^ 18 ≡ 1 [MOD 19] := by
    simpa using Nat.ModEq.pow_card_sub_one_eq_one (by norm_num : Nat.Prime 19)
      (by norm_num : Nat.Coprime 2 19)
  have hzm : ((2 ^ 18 : ℕ) : ZMod 19) = 1 :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr hm
  have ho : orderOf u ∣ 18 := by
    apply orderOf_dvd_iff_pow_eq_one.mpr
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, hu, Units.val_one] using hzm
  have aux (n : ℕ) (hn : n ≡ 3 [MOD 18]) : ¬ 19 ∣ 2 ^ n + 1 := by
    intro hd
    have hpU : u ^ n = u ^ 3 :=
      (pow_eq_pow_iff_modEq (x := u) (n := n) (m := 3)).mpr
        (Nat.ModEq.of_dvd ho hn)
    have hp : (2 : ZMod 19) ^ n = (2 : ZMod 19) ^ 3 := by
      simpa only [← hu, Units.val_pow_eq_pow_val] using congrArg Units.val hpU
    have hz : ((2 ^ n + 1 : ℕ) : ZMod 19) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hd
    push_cast at hz
    rw [hp] at hz
    have hnine : (9 : ZMod 19) ≠ 0 := by
      intro hh
      have hm9 := (ZMod.natCast_eq_natCast_iff 9 0 19).mp hh
      norm_num [Nat.ModEq] at hm9
    exact hnine hz
  exact aux (A078590 (7 - 1)) he (h19.trans h7)
