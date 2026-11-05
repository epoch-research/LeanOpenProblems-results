import Submission.AdjacentFactor

/-!
# A second prohibited Type-II modular residue

For `m ≥ 2`, a divisor `d ∣ m²` cannot satisfy `4m-1 ∣ 2+4d`.
Consequently a modulus dividing `p-2` cannot be the modulus of a full
`d ∣ m²` Type-II witness for a hard prime. This does not rule out a Type-I
witness, a Type-II witness at another modulus, or an Erdős–Straus solution.
In particular, this file does not import or modify `Submission/Spec.lean`.
-/

namespace Erdos242

/-- Apart from the trivial pair `(m,d)=(1,1)`, the residue `2` cannot occur
as `-4d` modulo `4m-1` with `d ∣ m²`. This is stronger than the Jacobi
sign obstruction: for odd `m`, the residue `2` has the necessary *negative*
Jacobi sign, but the allowed divisor exponents still cannot hit it. -/
theorem no_two_modular_divisor (m d : ℕ) (hm : 2 ≤ m) (hd : 0 < d)
    (hdsq : d ∣ m ^ 2) : ¬ (4 * m - 1 ∣ 2 + 4 * d) := by
  intro hdiv
  let h := 4 * m - 1
  let e := m ^ 2 / d
  let t := (2 + 4 * d) / h
  have hh : h + 1 = 4 * m := by dsimp [h]; omega
  have hde : d * e = m ^ 2 := Nat.mul_div_cancel' hdsq
  have hdt : h * t = 2 + 4 * d := Nat.mul_div_cancel' hdiv
  have ht4 : t % 4 = 2 := by
    have heq : 4 * (m * t) = t + 2 + 4 * d := by
      nlinarith only [hdt, hh]
    have heqmod : (t + 2 + 4 * d) % 4 = 0 := by rw [← heq]; simp
    omega
  have ht : t = 2 ∨ 6 ≤ t := by
    have hmodle : t % 4 ≤ t := Nat.mod_le _ _
    omega
  have hediv : h ∣ 8 * e + 1 := by
    have hh' := (typeII_modular_dual 2 m d (by omega) hdsq).mp hdiv
    simpa only [h, e, Nat.reduceMul, mul_assoc] using hh'
  have hege : 2 * m - 1 ≤ 4 * e := by
    have hle : h ≤ 8 * e + 1 := Nat.le_of_dvd (by omega) hediv
    dsimp [h] at hle
    omega
  rcases ht with ht | ht
  · have hdeq : d = 2 * m - 1 := by
      rw [ht] at hdt
      dsimp [h] at hdt
      omega
    have hfour : 4 * m ^ 2 = d * (2 * m + 1) + 1 := by
      rw [hdeq]
      have htwom : (2 * m - 1) + 1 = 2 * m := by omega
      nlinarith only [htwom]
    have hfourdiv : d ∣ d * (2 * m + 1) + 1 := by
      rw [← hfour]
      exact hdsq.mul_left 4
    have hdone : d ∣ 1 :=
      (Nat.dvd_add_iff_left (dvd_mul_right d (2 * m + 1))).mpr (by
        simpa only [add_comm] using hfourdiv)
    have hdone' : d ≤ 1 := Nat.le_of_dvd (by omega) hdone
    omega
  · have hdge : 6 * m - 2 ≤ d := by
      have hbound : h * 6 ≤ 2 + 4 * d := by
        calc
          h * 6 ≤ h * t := Nat.mul_le_mul_left h ht
          _ = 2 + 4 * d := hdt
      dsimp [h] at hbound
      omega
    have hmul : (6 * m - 2) * (2 * m - 1) ≤ 4 * m ^ 2 := by
      calc
        (6 * m - 2) * (2 * m - 1) ≤ d * (2 * m - 1) :=
          Nat.mul_le_mul_right _ hdge
        _ ≤ d * (4 * e) := Nat.mul_le_mul_left d hege
        _ = 4 * m ^ 2 := by rw [← hde]; ring
    have hstrict : 4 * m ^ 2 < (6 * m - 2) * (2 * m - 1) := by
      let n := m - 2
      have hn : m = n + 2 := by dsimp [n]; omega
      have h6 : 6 * m - 2 = 6 * n + 10 := by omega
      have h2 : 2 * m - 1 = 2 * n + 3 := by omega
      rw [h6, h2, hn]
      nlinarith
    exact (not_le_of_gt hstrict) hmul

/-- When `p ≡ 2 (mod 4m-1)` and `m≥2`, no complete `d ∣ m²` witness can
use this modular parameter. An admissible negative Jacobi sign is not enough. -/
theorem no_modular_divisor_if_two_remainder (p m d : ℕ) (hm : 2 ≤ m)
    (hd : 0 < d) (hdsq : d ∣ m ^ 2)
    (hrem : p % (4 * m - 1) = 2) : ¬ (4 * m - 1 ∣ p + 4 * d) := by
  intro hdiv
  have hh : 2 < 4 * m - 1 := by omega
  have hmod : (p + 4 * d) % (4 * m - 1) = 0 := Nat.mod_eq_zero_of_dvd hdiv
  have hmod2 : (2 + 4 * d) % (4 * m - 1) = 0 := by
    rw [Nat.add_mod, hrem] at hmod
    rw [Nat.add_mod, Nat.mod_eq_of_lt hh]
    exact hmod
  exact no_two_modular_divisor m d hm hd hdsq (Nat.dvd_of_mod_eq_zero hmod2)

/-- In particular, a divisor of `p-2` cannot serve as the Type-II modulus
`4m-1` for `p=24k+1`, `k>0`; this includes divisors forced into the class
`3 (mod 4)` by `p-2 ≡ 3 (mod 4)`. It does **not** rule out other moduli. -/
theorem hard_modular_modulus_not_dvd_p_minus_two (k m d : ℕ)
    (hk : 0 < k) (hm : 0 < m) (hd : 0 < d) (hdsq : d ∣ m ^ 2)
    (hminus : 4 * m - 1 ∣ (24 * k + 1) - 2) :
    ¬ (4 * m - 1 ∣ (24 * k + 1) + 4 * d) := by
  have hm2 : 2 ≤ m := by
    by_contra h
    have hm1 : m = 1 := by omega
    rw [hm1] at hminus
    have hmod : ((24 * k + 1) - 2) % 3 = 0 := by
      simpa using Nat.mod_eq_zero_of_dvd hminus
    omega
  have hh : 2 < 4 * m - 1 := by omega
  have hrem : (24 * k + 1) % (4 * m - 1) = 2 := by
    have hmod : ((24 * k + 1) - 2) % (4 * m - 1) = 0 :=
      Nat.mod_eq_zero_of_dvd hminus
    have heq : 24 * k + 1 = ((24 * k + 1) - 2) + 2 := by omega
    rw [heq, Nat.add_mod, hmod]
    simp [Nat.mod_eq_of_lt hh]
  exact no_modular_divisor_if_two_remainder (24 * k + 1) m d hm2 hd hdsq hrem

end Erdos242
