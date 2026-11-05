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
import Submission.Extremal

/-!
# Prime-digit colors

Strip the exact power of a prime from a positive natural number and color the
remaining unit by its first nonzero digit. For an odd prime, the color records
whether that digit is in the lower half of the nonzero residues. At the prime
`2`, it records whether the odd part is `1` rather than `3` modulo `4`.

Distinct positive natural numbers have different colors at some prime dividing
their sum. This is an elementary separation lemma, not an assertion of the
asymptotic conclusion of Erdős problem 126.
-/

namespace Erdos126Aux

/-- Remove the exact `p`-power factor of `a`, using its prime factorization. -/
def primeUnitPart (p a : ℕ) : ℕ :=
  a / p ^ a.factorization p

/-- The lower-half color of the first nonzero prime digit; at `2` use the odd
part modulo `4`. Values at zero or at nonprimes are harmless total extensions. -/
def primeColor (p a : ℕ) : Bool :=
  if p = 2 then decide (primeUnitPart p a % 4 ≤ 2)
  else decide (primeUnitPart p a % p ≤ p / 2)

/-- Exact prime-power stripping is multiplicative. -/
theorem primeUnitPart_mul (p a b : ℕ) :
    primeUnitPart p (a * b) = primeUnitPart p a * primeUnitPart p b := by
  exact Nat.ordCompl_mul a b p

/-- A number not divisible by `p` is unchanged by stripping. -/
theorem primeUnitPart_eq_self {p a : ℕ} (hpa : ¬p ∣ a) :
    primeUnitPart p a = a := by
  simp [primeUnitPart, Nat.factorization_eq_zero_of_not_dvd hpa]

/-- The unit part of a positive number is positive. -/
theorem primeUnitPart_pos {a : ℕ} (p : ℕ) (ha : 0 < a) :
    0 < primeUnitPart p a := by
  exact Nat.ordCompl_pos p ha.ne'

/-- After stripping a prime's exact power, it no longer divides the unit part. -/
theorem not_dvd_primeUnitPart {p a : ℕ} (hp : p.Prime) (ha : 0 < a) :
    ¬p ∣ primeUnitPart p a := by
  exact Nat.not_dvd_ordCompl hp ha.ne'

/-- Nonzero complementary residues have sum equal to the modulus. -/
theorem mod_add_mod_eq_of_dvd_add {m x y : ℕ}
    (hadd : m ∣ x + y) (hx : ¬m ∣ x) :
    x % m + y % m = m := by
  have hle := Nat.le_mod_add_mod_of_dvd_add_of_not_dvd hadd hx
  simpa only [Nat.mod_eq_zero_of_dvd hadd, zero_add] using
    (Nat.add_mod_add_of_le_add_mod hle).symm

/-- At an odd prime, unit parts whose sum is divisible by that prime have
opposite lower-half colors. -/
theorem primeColor_ne_of_odd_prime {p a b : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (ha : 0 < a)
    (hadd : p ∣ primeUnitPart p a + primeUnitPart p b) :
    primeColor p a ≠ primeColor p b := by
  have hsum := mod_add_mod_eq_of_dvd_add hadd (not_dvd_primeUnitPart hp ha)
  have hodd := hp.mod_two_eq_one_iff_ne_two.mpr hp2
  by_cases hlow : primeUnitPart p a % p ≤ p / 2
  · have hhigh : ¬primeUnitPart p b % p ≤ p / 2 := by omega
    simp [primeColor, hp2, hlow, hhigh]
  · have hlow' : primeUnitPart p b % p ≤ p / 2 := by omega
    simp [primeColor, hp2, hlow, hlow']

/-- At `2`, odd unit parts whose sum is divisible by `4` have residues `1` and
`3` modulo `4`, and therefore opposite colors. -/
theorem primeColor_two_ne {a b : ℕ} (ha : 0 < a)
    (hadd : 4 ∣ primeUnitPart 2 a + primeUnitPart 2 b) :
    primeColor 2 a ≠ primeColor 2 b := by
  have hnot2 := not_dvd_primeUnitPart Nat.prime_two ha
  have hnot4 : ¬4 ∣ primeUnitPart 2 a := by
    intro h
    exact hnot2 ((by decide : 2 ∣ 4).trans h)
  have hsum := mod_add_mod_eq_of_dvd_add hadd hnot4
  have hmod2 : primeUnitPart 2 a % 2 ≠ 0 := by
    exact fun h => hnot2 (Nat.dvd_of_mod_eq_zero h)
  have hmod4 := Nat.mod_mod_of_dvd (primeUnitPart 2 a) (by decide : 2 ∣ 4)
  have hlt4 := Nat.mod_lt (primeUnitPart 2 a) (by decide : 0 < 4)
  by_cases hlow : primeUnitPart 2 a % 4 ≤ 2
  · have hhigh : ¬primeUnitPart 2 b % 4 ≤ 2 := by omega
    simp [primeColor, hlow, hhigh]
  · have hlow' : primeUnitPart 2 b % 4 ≤ 2 := by omega
    simp [primeColor, hlow, hlow']

/-- A sum of distinct positive naturals has a prime divisor that is odd, or
else is `2` with the sum divisible by `4`. In the even case, choose a prime
divisor of half the sum. -/
theorem exists_prime_dvd_add_with_four {u v : ℕ}
    (hu : 0 < u) (hv : 0 < v) (huv : u ≠ v) :
    ∃ p : ℕ, p.Prime ∧ p ∣ u + v ∧ (p = 2 → 4 ∣ u + v) := by
  have hsum : 2 < u + v := by omega
  by_cases htwo : 2 ∣ u + v
  · have hhalf : 2 ≤ (u + v) / 2 := by
      have hmod := Nat.mod_eq_zero_of_dvd htwo
      omega
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd
      (show (u + v) / 2 ≠ 1 by omega)
    refine ⟨p, hp, hpdvd.trans (Nat.div_dvd_of_dvd htwo), ?_⟩
    intro hp2
    subst p
    have hfour := Nat.mul_dvd_mul_left 2 hpdvd
    simpa only [Nat.mul_div_cancel' htwo, Nat.reduceMul] using hfour
  · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd
      (show u + v ≠ 1 by omega)
    refine ⟨p, hp, hpdvd, ?_⟩
    intro hp2
    exact (htwo (hp2 ▸ hpdvd)).elim

/-- Distinct positive natural numbers are separated by the prime-digit color
at some prime factor of their sum. -/
theorem exists_primeFactor_color_ne (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hab : a ≠ b) :
    ∃ p ∈ (a + b).primeFactors, primeColor p a ≠ primeColor p b := by
  let g := a.gcd b
  let u := a / g
  let v := b / g
  have hau : g * u = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
  have hbv : g * v = b := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
  have hu : 0 < u := Nat.div_gcd_pos_of_pos_left b ha
  have hv : 0 < v := Nat.div_gcd_pos_of_pos_right a hb
  have huv : u ≠ v := by
    intro h
    apply hab
    rw [← hau, ← hbv, h]
  have hcop : u.Coprime v := Nat.gcd_div_gcd_div_gcd_of_pos_left ha
  obtain ⟨p, hp, hpsum, hpfour⟩ := exists_prime_dvd_add_with_four hu hv huv
  have hpnotu : ¬p ∣ u := by
    intro hpu
    have hpv : p ∣ v := (Nat.dvd_add_iff_right hpu).mpr hpsum
    have hpgcd := Nat.dvd_gcd hpu hpv
    rw [hcop.gcd_eq_one] at hpgcd
    exact hp.not_dvd_one hpgcd
  have hpnotv : ¬p ∣ v := by
    intro hpv
    exact hpnotu ((Nat.dvd_add_iff_left hpv).mpr hpsum)
  have hunitA : primeUnitPart p a = primeUnitPart p g * u := by
    rw [← hau, primeUnitPart_mul, primeUnitPart_eq_self hpnotu]
  have hunitB : primeUnitPart p b = primeUnitPart p g * v := by
    rw [← hbv, primeUnitPart_mul, primeUnitPart_eq_self hpnotv]
  have hpab : p ∣ a + b := by
    rw [← hau, ← hbv, ← Nat.mul_add]
    exact dvd_mul_of_dvd_right hpsum g
  have hcolors : primeColor p a ≠ primeColor p b := by
    by_cases hp2 : p = 2
    · have hfour : 4 ∣ primeUnitPart p a + primeUnitPart p b := by
        rw [hunitA, hunitB, ← Nat.mul_add]
        exact dvd_mul_of_dvd_right (hpfour hp2) (primeUnitPart p g)
      subst p
      exact primeColor_two_ne ha hfour
    · have hadd : p ∣ primeUnitPart p a + primeUnitPart p b := by
        rw [hunitA, hunitB, ← Nat.mul_add]
        exact dvd_mul_of_dvd_right hpsum (primeUnitPart p g)
      exact primeColor_ne_of_odd_prime hp hp2 ha hadd
  exact ⟨p, hp.mem_primeFactors hpab (by omega), hcolors⟩

end Erdos126Aux
