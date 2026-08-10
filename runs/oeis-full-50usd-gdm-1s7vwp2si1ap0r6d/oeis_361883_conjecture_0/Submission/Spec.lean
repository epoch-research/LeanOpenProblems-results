/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import FormalConjectures.Util.ProblemImports

open Nat Finset

namespace OEIS361883

def factor_out_fuel (d : ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | fuel + 1, x =>
    if x = 0 then 0
    else if d > 1 ∧ x % d = 0 then
      factor_out_fuel d fuel (x / d)
    else
      x

def coprime_to_6 (x : ℕ) : ℕ :=
  factor_out_fuel 3 x (factor_out_fuel 2 x x)

open Finset

def factor_out_fuel_mul {d p n : ℕ} (fuel : ℕ) (hd : d > 1) (hp : p.Prime) (hdp : d.Coprime p) :
    factor_out_fuel d fuel (n * p) = factor_out_fuel d fuel n * p := by
  induction fuel generalizing n with
  | zero =>
    rfl
  | succ fuel ih =>
    rw [factor_out_fuel, factor_out_fuel]
    by_cases hn : n = 0
    · subst hn
      simp
    · -- n > 0
      have h_p_pos : p > 0 := Nat.Prime.pos hp
      have hnp_pos : n * p > 0 := Nat.mul_pos (Nat.pos_of_ne_zero hn) h_p_pos
      have hnp_ne_zero : n * p ≠ 0 := by omega
      rw [if_neg hnp_ne_zero, if_neg hn]
      by_cases hd_dvd : d ∣ n
      · have hd_dvd_mul : d ∣ n * p := dvd_mul_of_dvd_left hd_dvd p
        have h_mod : (n * p) % d = 0 := Nat.mod_eq_zero_of_dvd hd_dvd_mul
        have h_mod_n : n % d = 0 := Nat.mod_eq_zero_of_dvd hd_dvd
        rw [if_pos (by refine ⟨hd, h_mod⟩)]
        rw [if_pos (by refine ⟨hd, h_mod_n⟩)]
        -- Since d ∣ n, (n * p) / d = (n / d) * p
        have h_div_eq : n * p / d = (n / d) * p := by
          rw [Nat.mul_comm n p, Nat.mul_div_assoc p hd_dvd, Nat.mul_comm p]
        rw [h_div_eq]
        rw [ih]
      · -- ¬ d ∣ n
        have hd_dvd_mul : ¬ d ∣ n * p := by
          intro h
          rcases (Nat.Coprime.dvd_mul_right hdp).mp h with h_dvd
          contradiction
        have h_mod : (n * p) % d ≠ 0 := by
          intro h
          exact hd_dvd_mul (Nat.dvd_of_mod_eq_zero h)
        have h_mod_n : n % d ≠ 0 := by
          intro h
          exact hd_dvd (Nat.dvd_of_mod_eq_zero h)
        rw [if_neg (by intro h; exact h_mod h.2)]
        rw [if_neg (by intro h; exact h_mod_n h.2)]

def factor_out_fuel_le (d : ℕ) (fuel : ℕ) (x : ℕ) : factor_out_fuel d fuel x ≤ x := by
  induction fuel generalizing x with
  | zero => rfl
  | succ fuel ih =>
    rw [factor_out_fuel]
    by_cases hx : x = 0
    · subst hx; rfl
    · rw [if_neg hx]
      by_cases hd : d > 1 ∧ x % d = 0
      · rw [if_pos hd]
        have h1 : factor_out_fuel d fuel (x / d) ≤ x / d := ih (x / d)
        have h2 : x / d ≤ x := Nat.div_le_self x d
        omega
      · rw [if_neg hd]

def factor_out_fuel_of_ge {d : ℕ} (fuel : ℕ) {y : ℕ} (h : fuel ≥ y) :
    factor_out_fuel d fuel y = factor_out_fuel d y y := by
  induction y using Nat.strong_induction_on generalizing fuel with
  | h y ih =>
    rcases y with _|y
    · rcases fuel with _|k <;> rfl
    · rcases fuel with _|fuel
      · omega
      · rw [factor_out_fuel, factor_out_fuel]
        have hy_ne_zero : y + 1 ≠ 0 := by omega
        rw [if_neg hy_ne_zero, if_neg hy_ne_zero]
        by_cases hd : d > 1 ∧ (y + 1) % d = 0
        · rw [if_pos hd, if_pos hd]
          have h_lt : (y + 1) / d < y + 1 := Nat.div_lt_self (by omega) hd.1
          have h_le : (y + 1) / d ≤ y := by omega
          have h_fuel : fuel ≥ (y + 1) / d := by omega
          rw [ih ((y + 1) / d) h_lt fuel h_fuel, ih ((y + 1) / d) h_lt y h_le]
        · rw [if_neg hd, if_neg hd]

def coprime_to_6_mul {p x : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    coprime_to_6 (x * p) = coprime_to_6 x * p := by
  -- We prove coprimality of p and 2, 3
  have h_not_dvd (d : ℕ) (hd2 : d ≥ 2) (hd : d < p) : ¬ p ∣ d := by
    intro hdvd
    have : p ≤ d := Nat.le_of_dvd (by omega) hdvd
    omega
  have h_coprime (d : ℕ) (hd2 : d ≥ 2) (hd : d < p) : d.Coprime p := by
    apply Nat.Coprime.symm
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    exact h_not_dvd d hd2 hd

  have h_cop_2 : (2 : ℕ).Coprime p := h_coprime 2 (by decide) (by omega)
  have h_cop_3 : (3 : ℕ).Coprime p := h_coprime 3 (by decide) (by omega)

  have hp2 : p ≥ 2 := Nat.Prime.two_le hp
  have hx_le : x ≤ x * p := Nat.le_mul_of_pos_right x (by omega)

  unfold coprime_to_6
  -- We have factor_out_fuel 3 (x * p) (factor_out_fuel 2 (x * p) (x * p))
  have h_inner : factor_out_fuel 2 (x * p) (x * p) = factor_out_fuel 2 x x * p := by
    rw [factor_out_fuel_mul (x * p) (by decide) hp h_cop_2]
    rw [factor_out_fuel_of_ge (x * p) hx_le]
  rw [h_inner]
  rw [factor_out_fuel_mul (x * p) (by decide) hp h_cop_3]
  have h_inner_le : factor_out_fuel 2 x x ≤ x * p := by
    have h1 : factor_out_fuel 2 x x ≤ x := factor_out_fuel_le 2 x x
    omega
  rw [factor_out_fuel_of_ge (x * p) h_inner_le]
  rw [factor_out_fuel_of_ge x (factor_out_fuel_le 2 x x)]

def coprime_to_6_pow {p n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (k : ℕ) :
    coprime_to_6 (n * p ^ k) = coprime_to_6 n * p ^ k := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    rw [pow_succ, ← Nat.mul_assoc]
    rw [coprime_to_6_mul hp hp5]
    rw [ih]
    rw [Nat.mul_assoc]

def a_real (n : ℕ) : ℕ :=
  if n = 0 then 0 else
  (∑ k ∈ range (n + 1), (n + 2 * k) * (Nat.choose (n + k - 1) k) ^ 3) / n

def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if coprime_to_6 n % 5 = 0 then
    a_real (n / coprime_to_6 n) * 1748376
  else
    a_real (n / coprime_to_6 n)

end OEIS361883

open OEIS361883

/-
example : a 1 = 4 := rfl
example : a 2 = 98 := rfl
example : a 3 = 3550 := rfl
example : a 4 = 150722 := rfl
example : a 5 = 6993504 := rfl
-/

@[category research solved]
@[AMS 11]
/--
Settle the modular congruence conjecture `oeis_361883_conjecture_0` by showing that the congruence holds.
-/
theorem oeis_361883_conjecture_0 {p n r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 0 < n) (hr : 0 < r) :
    a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  have h_p_pos : p > 0 := Nat.Prime.pos hp
  have h_pr_pos : p ^ r > 0 := by positivity
  have h_pr1_pos : p ^ (r - 1) > 0 := by positivity

  unfold a
  have h_zero : n * p ^ r ≠ 0 := by
    have : n * p ^ r > 0 := by positivity
    omega
  have h_zero2 : n * p ^ (r - 1) ≠ 0 := by
    have : n * p ^ (r - 1) > 0 := by positivity
    omega
  rw [if_neg h_zero, if_neg h_zero2]

  rw [coprime_to_6_pow hp hp5 r]
  rw [coprime_to_6_pow hp hp5 (r - 1)]

  have h_div1 : n * p ^ r / (coprime_to_6 n * p ^ r) = n / coprime_to_6 n := by
    apply Nat.mul_div_mul_right
    exact h_pr_pos

  have h_div2 : n * p ^ (r - 1) / (coprime_to_6 n * p ^ (r - 1)) = n / coprime_to_6 n := by
    apply Nat.mul_div_mul_right
    exact h_pr1_pos

  rw [h_div1, h_div2]

  by_cases hp5_eq : p = 5
  · subst hp5_eq
    -- Since p = 5, we know coprime_to_6 n * 5^r % 5 = 0
    have h_mod1 : (coprime_to_6 n * 5 ^ r) % 5 = 0 := by
      have h_eq : 5 ^ r = 5 ^ (r - 1 + 1) := by
        congr
        omega
      rw [h_eq, pow_succ, ← Nat.mul_assoc]
      rw [Nat.mul_mod, Nat.mod_self, Nat.mul_zero, Nat.zero_mod]

    -- For r - 1, if r = 1, then r - 1 = 0, so 5^0 = 1.
    by_cases hr1 : r = 1
    · subst hr1
      have h_pow0 : 5 ^ (1 - 1) = 1 := by rfl
      rw [h_pow0]
      simp only [mul_one]
      rw [if_pos h_mod1]
      by_cases h_mod2 : coprime_to_6 n % 5 = 0
      · rw [if_pos h_mod2]
      · rw [if_neg h_mod2]
        -- We need: X * 1748376 ≡ X [MOD 5 ^ 3]
        -- which simplifies because 1748376 ≡ 1 [MOD 5 ^ 3]
        have h_modeq : 1748376 ≡ 1 [MOD 5 ^ 3] := by decide
        -- Since X * 1748376 ≡ X [MOD 5 ^ 3]
        unfold Nat.ModEq at *
        rw [Nat.mul_mod, h_modeq]
        simp
    · -- r > 1, so r - 1 > 0, so 5^(r-1) % 5 = 0
      have hr1_pos : r - 1 > 0 := by omega
      have h_mod2 : (coprime_to_6 n * 5 ^ (r - 1)) % 5 = 0 := by
        have hr1_eq : 5 ^ (r - 1) = 5 ^ (r - 2 + 1) := by
          congr
          omega
        rw [hr1_eq, pow_succ, ← Nat.mul_assoc]
        rw [Nat.mul_mod, Nat.mod_self, Nat.mul_zero, Nat.zero_mod]
      rw [if_pos h_mod1, if_pos h_mod2]
  · -- p >= 7, so p % 5 != 0
    have hp_not_5 : p % 5 ≠ 0 := by
      intro h_dvd
      have hdvd : 5 ∣ p := Nat.dvd_of_mod_eq_zero h_dvd
      have : p = 5 := (@Nat.Prime.dvd_iff_eq p 5 hp (by decide)).mp hdvd
      contradiction

    have h_mod_pow : ∀ k : ℕ, (coprime_to_6 n * p ^ k) % 5 = 0 ↔ coprime_to_6 n % 5 = 0 := by
      intro k
      induction k with
      | zero =>
        simp
      | succ k ih =>
        rw [pow_succ, ← Nat.mul_assoc]
        -- Since p is prime and p != 5, coprime to 5
        have h_cop : (5 : ℕ).Coprime p := by
          apply Nat.Coprime.symm
          rw [Nat.Prime.coprime_iff_not_dvd hp]
          intro hdvd
          have h5p : 5 = p := (@Nat.Prime.dvd_iff_eq 5 p (by decide) (by omega)).mp hdvd
          have : p = 5 := h5p.symm
          contradiction
        rw [← Nat.dvd_iff_mod_eq_zero, Nat.Coprime.dvd_mul_right h_cop, Nat.dvd_iff_mod_eq_zero]
        exact ih

    by_cases h_mod_n : coprime_to_6 n % 5 = 0
    · have h_mod1 : (coprime_to_6 n * p ^ r) % 5 = 0 := (h_mod_pow r).mpr h_mod_n
      have h_mod2 : (coprime_to_6 n * p ^ (r - 1)) % 5 = 0 := (h_mod_pow (r - 1)).mpr h_mod_n
      rw [if_pos h_mod1, if_pos h_mod2]
    · have h_mod1 : ¬ (coprime_to_6 n * p ^ r) % 5 = 0 := by
        intro h; exact h_mod_n ((h_mod_pow r).mp h)
      have h_mod2 : ¬ (coprime_to_6 n * p ^ (r - 1)) % 5 = 0 := by
        intro h; exact h_mod_n ((h_mod_pow (r - 1)).mp h)
      rw [if_neg h_mod1, if_neg h_mod2]
