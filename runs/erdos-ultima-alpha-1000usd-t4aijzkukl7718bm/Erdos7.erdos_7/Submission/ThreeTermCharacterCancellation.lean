import Submission.FourTermCharacterCancellation

/-!
Three-term cancellation in odd-order character sums. This is a conditional
noncoverage criterion; it does not assert the existence of suitable frequencies
for every odd distinct modulus family.
-/
namespace Erdos7ThreeTermCancellation
open scoped BigOperators
open Erdos7SubsetFourier Erdos7FourTermCancellation
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Three unit complex numbers summing to zero are vertices of an equilateral
triangle about zero. Here we retain the algebraic equal-cube consequence. -/
theorem three_unit_zero_cubes (a b c : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hz : a + b + c = 0) : a^3 = b^3 ∧ b^3 = c^3 := by
  have hau : a * star a = 1 := by simpa [ha] using Complex.mul_conj' a
  have hbu : b * star b = 1 := by simpa [hb] using Complex.mul_conj' b
  have hcu : c * star c = 1 := by simpa [hc] using Complex.mul_conj' c
  have hs : a*b*c*star (a+b+c) = 0 := by rw [hz, star_zero, mul_zero]
  have he : a*b*c*star (a+b+c) = a*b + a*c + b*c := by
    simp only [star_add]
    calc
      _ = (a*star a)*b*c + a*(b*star b)*c + a*b*(c*star c) := by ring
      _ = _ := by rw [hau, hbu, hcu]; ring
  rw [he] at hs
  constructor
  · linear_combination (a-b)*(a+b)*hz - (a-b)*hs
  · linear_combination (b-c)*(b+c)*hz - (b-c)*hs


lemma three_unit_zero_ne (a b c : ℂ)
    (_ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hz : a+b+c = 0) : a ≠ b := by
  intro he
  rw [he] at hz
  have hec : c = -((2 : ℂ)*b) := by linear_combination hz
  rw [hec] at hc
  norm_num [norm_mul, hb] at hc

lemma sign_cube (t : ℕ) : ((-1 : ℂ)^t)^3 = (-1 : ℂ)^t := by
  rw [← pow_mul, mul_comm t 3, pow_mul]
  norm_num

/-- Three signed odd-order character values can vanish only when all signs
agree. The hypothesis is stronger than an unrestricted three-term vanishing
sum because the character group has odd order. -/
theorem three_signed_char_same_sign {N : ℕ} [NeZero N] (hN : Odd N)
    (u : Fin 3 → ZMod N) (t : Fin 3 → ℕ)
    (hz : (∑ j : Fin 3, (-1 : ℂ)^t j * ZMod.stdAddChar (u j)) = 0) :
    (-1 : ℂ)^t 0 = (-1 : ℂ)^t 1 ∧
      (-1 : ℂ)^t 1 = (-1 : ℂ)^t 2 := by
  have h := three_unit_zero_cubes
    ((-1 : ℂ)^t 0 * ZMod.stdAddChar (u 0))
    ((-1 : ℂ)^t 1 * ZMod.stdAddChar (u 1))
    ((-1 : ℂ)^t 2 * ZMod.stdAddChar (u 2))
    (signed_char_norm _ _) (signed_char_norm _ _) (signed_char_norm _ _)
    (by simpa [Fin.sum_univ_succ, add_assoc] using hz)
  have commute (z : ℂ) : (z^3)^N = (z^N)^3 := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm 3 N]
  constructor
  · have hh := congrArg (fun z : ℂ => z^N) h.1
    simpa only [commute, signed_char_odd_pow hN, sign_cube] using hh
  · have hh := congrArg (fun z : ℂ => z^N) h.2
    simpa only [commute, signed_char_odd_pow hN, sign_cube] using hh

/-- Retain the phase information as well as the signs. -/
theorem three_signed_char_phase_cubes {N : ℕ} [NeZero N] (hN : Odd N)
    (u : Fin 3 → ZMod N) (t : Fin 3 → ℕ)
    (hz : (∑ j : Fin 3, (-1 : ℂ)^t j * ZMod.stdAddChar (u j)) = 0) :
    (3 : ZMod N) * u 0 = 3 * u 1 ∧ (3 : ZMod N) * u 1 = 3 * u 2 := by
  have hs := three_signed_char_same_sign hN u t hz
  have h := three_unit_zero_cubes
    ((-1 : ℂ)^t 0 * ZMod.stdAddChar (u 0))
    ((-1 : ℂ)^t 1 * ZMod.stdAddChar (u 1))
    ((-1 : ℂ)^t 2 * ZMod.stdAddChar (u 2))
    (signed_char_norm _ _) (signed_char_norm _ _) (signed_char_norm _ _)
    (by simpa [Fin.sum_univ_succ, add_assoc] using hz)
  simp only [mul_pow, sign_cube] at h
  rw [hs.1] at h
  have h01 := mul_left_cancel₀ (pow_ne_zero (t 1) (by norm_num : (-1 : ℂ) ≠ 0)) h.1
  rw [hs.2] at h
  have h12 := mul_left_cancel₀ (pow_ne_zero (t 2) (by norm_num : (-1 : ℂ) ≠ 0)) h.2
  have charpow (v : ZMod N) : ZMod.stdAddChar v ^ 3 = ZMod.stdAddChar (3*v) := by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
    norm_num
  simp only [charpow] at h01 h12
  exact ⟨ZMod.injective_stdAddChar h01, ZMod.injective_stdAddChar h12⟩

/-- The three-term cancellation also forces genuine order-three torsion in
its character group. -/
theorem three_signed_char_forces_three_dvd {N : ℕ} [NeZero N] (hN : Odd N)
    (u : Fin 3 → ZMod N) (t : Fin 3 → ℕ)
    (hz : (∑ j : Fin 3, (-1 : ℂ)^t j * ZMod.stdAddChar (u j)) = 0) : 3 ∣ N := by
  by_contra hn
  have hunit : IsUnit (3 : ZMod N) :=
    ZMod.isUnit_prime_of_not_dvd (by decide : Nat.Prime 3) hn
  have he := (three_signed_char_phase_cubes hN u t hz).1
  have huv : u 0 = u 1 := hunit.mul_left_cancel he
  have hs := (three_signed_char_same_sign hN u t hz).1
  have hne := three_unit_zero_ne
    ((-1 : ℂ)^t 0 * ZMod.stdAddChar (u 0))
    ((-1 : ℂ)^t 1 * ZMod.stdAddChar (u 1))
    ((-1 : ℂ)^t 2 * ZMod.stdAddChar (u 2))
    (signed_char_norm _ _) (signed_char_norm _ _) (signed_char_norm _ _)
    (by simpa [Fin.sum_univ_succ, add_assoc] using hz)
  exact hne (by rw [hs, huv])

/-- Any coefficient with exactly three subset representations in an odd-order
character-kernel cover must have three equal cardinality signs. -/
theorem cover_three_representations_same_sign {ι : Type*} [Fintype ι]
    {N : ℕ} [NeZero N] (hN : Odd N) (k a : ι → ZMod N)
    (hc : ∀ x : ZMod N, ∃ i, k i * (x-a i) = 0)
    (r : Fin 3 → Finset ι) (hr : Function.Injective r) (b : ZMod N)
    (hfreq : ∀ s : Finset ι, (∑ i ∈ s, k i = b) ↔ ∃ j, s = r j) :
    (-1 : ℂ)^(r 0).card = (-1 : ℂ)^(r 1).card ∧
      (-1 : ℂ)^(r 1).card = (-1 : ℂ)^(r 2).card := by
  classical
  have hz := cover_coefficient_vanishes k a hc b
  rw [← Finset.sum_filter] at hz
  have hset : (Finset.univ : Finset ι).powerset.filter (fun s => ∑ i ∈ s, k i = b) =
      Finset.univ.image r := by
    ext s
    simp [hfreq, eq_comm]
  rw [hset, Finset.sum_image (by intro i _ j _ h; exact hr h)] at hz
  exact three_signed_char_same_sign hN (fun j => -(∑ i ∈ r j, k i * a i))
    (fun j => (r j).card) hz

/-- A mixed-parity three-representation coefficient is a noncoverage
certificate independent of the actual class residues. -/
theorem not_cover_three_mixed {ι : Type*} [Fintype ι]
    {N : ℕ} [NeZero N] (hN : Odd N) (k a : ι → ZMod N)
    (r : Fin 3 → Finset ι) (hr : Function.Injective r) (b : ZMod N)
    (hfreq : ∀ s : Finset ι, (∑ i ∈ s, k i = b) ↔ ∃ j, s = r j)
    (hsign : ¬ ((-1 : ℂ)^(r 0).card = (-1 : ℂ)^(r 1).card ∧
      (-1 : ℂ)^(r 1).card = (-1 : ℂ)^(r 2).card)) :
    ¬ (∀ x : ZMod N, ∃ i, k i * (x-a i) = 0) := by
  intro hc
  exact hsign (cover_three_representations_same_sign hN k a hc r hr b hfreq)

/-- Arithmetic transfer. Frequencies only need to be annihilated by their
moduli; no exact-order requirement is imposed. -/
theorem not_arithmetic_cover_three_mixed {ι : Type*} [Fintype ι]
    {N : ℕ} [NeZero N] (hN : Odd N) (m : ι → ℕ) (a : ι → ℤ)
    (k : ι → ZMod N) (horder : ∀ i, (m i : ZMod N) * k i = 0)
    (r : Fin 3 → Finset ι) (hr : Function.Injective r) (b : ZMod N)
    (hfreq : ∀ s : Finset ι, (∑ i ∈ s, k i = b) ↔ ∃ j, s = r j)
    (hsign : ¬ ((-1 : ℂ)^(r 0).card = (-1 : ℂ)^(r 1).card ∧
      (-1 : ℂ)^(r 1).card = (-1 : ℂ)^(r 2).card)) :
    ¬ (∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x-a i) := by
  intro hc
  apply not_cover_three_mixed hN k (fun i => (a i : ZMod N)) r hr b hfreq hsign
  intro x
  obtain ⟨i,z,hz⟩ := hc (x.val : ℤ)
  refine ⟨i, ?_⟩
  have he : x-(a i : ZMod N) = (m i : ZMod N) * (z : ZMod N) := by
    have hh := congrArg (fun t : ℤ => (t : ZMod N)) hz
    simpa using hh
  rw [he, ← mul_assoc, mul_comm (k i) (m i : ZMod N), horder i, zero_mul]

/-- A same-sign triple really can vanish in an odd-order group. -/
theorem three_positive_vanishing :
    (∑ u : ZMod 3, ZMod.stdAddChar u) = 0 := by
  have h := AddChar.sum_eq_zero_of_ne_one
    (ZMod.isPrimitive_stdAddChar 3 (show (1 : ZMod 3) ≠ 0 by decide))
  simpa using h

/-- This is a character-kernel cover with repeated order3, not a strict
arithmetic covering system. Thus the mixed-sign hypothesis is essential. -/
theorem repeated_three_kernel_cover :
    ∀ x : ZMod 3, ∃ i : ZMod 3, (1 : ZMod 3) * (x-i) = 0 := by
  intro x
  exact ⟨x, by simp⟩

#print axioms three_unit_zero_cubes
#print axioms three_signed_char_forces_three_dvd
#print axioms three_positive_vanishing
#print axioms three_signed_char_same_sign
#print axioms three_signed_char_phase_cubes
#print axioms not_arithmetic_cover_three_mixed
end Erdos7ThreeTermCancellation
