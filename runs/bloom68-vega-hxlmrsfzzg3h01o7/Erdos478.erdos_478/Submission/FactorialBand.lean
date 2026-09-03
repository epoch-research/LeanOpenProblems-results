import Mathlib
import Submission.FactorialPairing

/-!
# Avoidance of seven on five factorial-product bands

For a prime `p > 29` with `p % 6699 = 2`, the product `i! * j!` in `ZMod p`
is not seven when `i,j < p` and `i+j` is one of `p-3,p-2,p-1,p,p+1`.
Dirichlet's theorem supplies infinitely many such primes.

This is only a statement about these five bands of pairs of indices. It does
not assert that seven is missing from the full factorial-residue product set,
and makes no assertion about the factorial-residue asymptotic conjecture.

The proof uses Wilson reflection from `Submission.FactorialPairing`, parity
for the two adjacent bands, and quadratic reciprocity (in its Jacobi-symbol
form) for the two outer bands. No problem-specification file is imported.
-/

set_option autoImplicit false
set_option warningAsError true

namespace FactorialBand

private lemma cast_ne_zero {p n : ℕ} (hn : 0 < n) (hnp : n < p) :
    (n : ZMod p) ≠ 0 := by
  intro h
  have hv := congrArg ZMod.val h
  rw [ZMod.val_cast_of_lt hnp, ZMod.val_zero] at hv
  omega

private lemma odd_mod_two {p : ℕ} [Fact p.Prime] (hp : 29 < p) :
    p % 2 = 1 := by
  exact (Fact.out : p.Prime).eq_two_or_odd.resolve_left (by omega)

private lemma progression_mod {p m : ℕ} (hm : p % 6699 = 2)
    (hd : m ∣ 6699) (h2 : 2 < m) : p % m = 2 := by
  have h := Nat.mod_mod_of_dvd p hd
  rw [hm, Nat.mod_eq_of_lt h2] at h
  exact h.symm

private lemma jacobi_residue_two {a p : ℕ} (ha : a % 4 = 1)
    (hp : Odd p) (hm : p % a = 2) :
    jacobiSym (a : ℤ) p = jacobiSym 2 a := by
  rw [jacobiSym.quadratic_reciprocity_one_mod_four ha hp,
    jacobiSym.mod_left, ← Int.natCast_mod, hm]
  norm_num

/-- The four nonsquares needed for the outer two bands. -/
private lemma four_nonsquares {p : ℕ} [Fact p.Prime]
    (hp : 29 < p) (hm : p % 6699 = 2) :
    ¬IsSquare (29 : ZMod p) ∧ ¬IsSquare (-3 : ZMod p) ∧
      ¬IsSquare (77 : ZMod p) ∧ ¬IsSquare (21 : ZMod p) := by
  have ho : Odd p := Nat.odd_iff.mpr (odd_mod_two hp)
  have hm3 := progression_mod hm (show 3 ∣ 6699 by decide) (by decide)
  have hm29 := progression_mod hm (show 29 ∣ 6699 by decide) (by decide)
  have hm77 := progression_mod hm (show 77 ∣ 6699 by decide) (by decide)
  have hm21 := progression_mod hm (show 21 ∣ 6699 by decide) (by decide)
  clear hm
  have h29 : jacobiSym 29 p = -1 := by
    have h := jacobi_residue_two (a := 29) (by decide) ho hm29
    norm_num at h
    exact h
  have h3 : jacobiSym (-3) p = -1 := by
    rw [jacobiSym.mod_right (-3) ho]
    change jacobiSym (-3) (p % 12) = -1
    have hp2 := odd_mod_two hp
    have hr : p % 12 = 5 ∨ p % 12 = 11 := by
      clear hm29 hm77 hm21 h29
      omega
    rcases hr with hr | hr <;> rw [hr] <;> norm_num
  have h77 : jacobiSym 77 p = -1 := by
    have h := jacobi_residue_two (a := 77) (by decide) ho hm77
    norm_num at h
    exact h
  have h21 : jacobiSym 21 p = -1 := by
    have h := jacobi_residue_two (a := 21) (by decide) ho hm21
    norm_num at h
    exact h
  exact ⟨by simpa using ZMod.nonsquare_of_jacobiSym_eq_neg_one h29,
    by simpa using ZMod.nonsquare_of_jacobiSym_eq_neg_one h3,
    by simpa using ZMod.nonsquare_of_jacobiSym_eq_neg_one h77,
    by simpa using ZMod.nonsquare_of_jacobiSym_eq_neg_one h21⟩

/-- Scaling by seven in the last two conclusions avoids division by seven. -/
private lemma quadratic_obstructions {p : ℕ} [Fact p.Prime]
    (hp : 29 < p) (hm : p % 6699 = 2) (x : ZMod p) :
    (x + 1) * (x + 2) ≠ 7 ∧ (x + 1) * (x + 2) ≠ -7 ∧
      7 * ((x + 1) * (x + 2)) ≠ 1 ∧
      7 * ((x + 1) * (x + 2)) ≠ -1 := by
  obtain ⟨h29, h3, h77, h21⟩ := four_nonsquares hp hm
  have hthree : (3 : ZMod p) ≠ 0 := cast_ne_zero (n := 3) (by decide) (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    apply h29
    refine ⟨2 * x + 3, ?_⟩
    linear_combination -4 * h
  · intro h
    apply h3
    refine ⟨(2 * x + 3) / 3, ?_⟩
    field_simp
    linear_combination -4 * h
  · intro h
    apply h77
    refine ⟨7 * (2 * x + 3), ?_⟩
    linear_combination -28 * h
  · intro h
    apply h21
    refine ⟨7 * (2 * x + 3), ?_⟩
    linear_combination -28 * h

private lemma val_neg_cast {p n : ℕ} (hn : 0 < n) (hnp : n < p) :
    (-(n : ZMod p)).val = p - n := by
  have he : ((p - n : ℕ) : ZMod p) = -(n : ZMod p) := by
    rw [Nat.cast_sub hnp.le, ZMod.natCast_self, zero_sub]
  rw [← he, ZMod.val_cast_of_lt (by omega)]

/-- Upper adjacent-band products have even canonical representative. -/
private lemma signed_index_even {p n : ℕ} (hp : p % 2 = 1) (hn : n < p) :
    (((-1 : ZMod p) ^ n * (n : ZMod p)).val) % 2 = 0 := by
  rcases Nat.even_or_odd n with he | ho
  · rw [he.neg_one_pow, one_mul, ZMod.val_cast_of_lt hn]
    exact Nat.even_iff.mp he
  · rw [ho.neg_one_pow, neg_one_mul, val_neg_cast (by
      have := Nat.odd_iff.mp ho
      omega) hn]
    have := Nat.odd_iff.mp ho
    omega

/-- Inverses of lower adjacent-band products have odd canonical representative. -/
private lemma signed_index_odd {p n : ℕ} (hp : p % 2 = 1)
    (hn0 : 0 < n) (hn : n < p) :
    (((-1 : ZMod p) ^ (n + 1) * (n : ZMod p)).val) % 2 = 1 := by
  rcases Nat.even_or_odd n with he | ho
  · rw [pow_succ, he.neg_one_pow, one_mul, neg_one_mul, val_neg_cast hn0 hn]
    have := Nat.even_iff.mp he
    omega
  · rw [pow_succ, ho.neg_one_pow, neg_one_mul, neg_neg, one_mul,
      ZMod.val_cast_of_lt hn]
    exact Nat.odd_iff.mp ho

/-- For the chosen progression, `7⁻¹ = (3*p+1)/7` has even representative. -/
private lemma inverse_seven_even {p : ℕ} [Fact p.Prime]
    (hp : 29 < p) (hm : p % 6699 = 2) :
    ((7 : ZMod p)⁻¹).val % 2 = 0 := by
  have hp2 := odd_mod_two hp
  have hm7 := progression_mod hm (show 7 ∣ 6699 by decide) (by decide)
  clear hm
  have hdiv : 7 * ((3 * p + 1) / 7) = 3 * p + 1 := by omega
  have hlt : (3 * p + 1) / 7 < p := by omega
  have hseven : (7 : ZMod p) ≠ 0 := cast_ne_zero (n := 7) (by decide) (by omega)
  have he : (((3 * p + 1) / 7 : ℕ) : ZMod p) = (7 : ZMod p)⁻¹ := by
    apply mul_left_cancel₀ hseven
    rw [mul_inv_cancel₀ hseven]
    calc
      (7 : ZMod p) * (((3 * p + 1) / 7 : ℕ) : ZMod p) =
          ((7 * ((3 * p + 1) / 7) : ℕ) : ZMod p) := by push_cast; rfl
      _ = ((3 * p + 1 : ℕ) : ZMod p) := by rw [hdiv]
      _ = 1 := by push_cast; simp
  rw [← he, ZMod.val_cast_of_lt hlt]
  omega

private lemma upper_one_identity {p x : ℕ} [Fact p.Prime] (hx : x < p) :
    ((x + 1).factorial : ZMod p) * ((p - 1 - x).factorial : ZMod p) =
      (-1) ^ (x + 1) * ((x + 1 : ℕ) : ZMod p) := by
  rw [Nat.factorial_succ, Nat.cast_mul]
  calc
    _ = ((x + 1 : ℕ) : ZMod p) *
        ((x.factorial : ZMod p) * ((p - 1 - x).factorial : ZMod p)) := by ring
    _ = _ := by rw [FactorialPairing.factorial_mul_reflection hx]; ring

private lemma upper_two_identity {p x : ℕ} [Fact p.Prime] (hx : x < p) :
    ((x + 2).factorial : ZMod p) * ((p - 1 - x).factorial : ZMod p) =
      (-1) ^ (x + 1) * (((x : ZMod p) + 1) * ((x : ZMod p) + 2)) := by
  rw [show x + 2 = (x + 1) + 1 by omega, Nat.factorial_succ, Nat.cast_mul]
  calc
    _ = ((x + 1 + 1 : ℕ) : ZMod p) *
        (((x + 1).factorial : ZMod p) * ((p - 1 - x).factorial : ZMod p)) := by ring
    _ = _ := by rw [upper_one_identity hx]; push_cast; ring

private lemma lower_one_identity {p x : ℕ} [Fact p.Prime] (hx : x + 1 < p) :
    ((x + 1 : ℕ) : ZMod p) *
        ((x.factorial : ZMod p) * ((p - 1 - (x + 1)).factorial : ZMod p)) =
      (-1) ^ (x + 2) := by
  have h := FactorialPairing.factorial_mul_reflection hx
  rw [Nat.factorial_succ, Nat.cast_mul] at h
  convert h using 1
  ring

private lemma lower_two_identity {p x : ℕ} [Fact p.Prime] (hx : x + 2 < p) :
    (((x : ZMod p) + 1) * ((x : ZMod p) + 2)) *
        ((x.factorial : ZMod p) * ((p - 1 - (x + 2)).factorial : ZMod p)) =
      (-1) ^ (x + 3) := by
  have h := FactorialPairing.factorial_mul_reflection hx
  rw [show x + 2 = (x + 1) + 1 by omega, Nat.factorial_succ,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_mul] at h
  push_cast at h
  convert h using 1
  ring

private lemma middle_ne_seven {p x : ℕ} [Fact p.Prime]
    (hp : 29 < p) (hx : x < p) :
    (x.factorial : ZMod p) * ((p - 1 - x).factorial : ZMod p) ≠ 7 := by
  rw [FactorialPairing.factorial_mul_reflection hx]
  intro h
  rcases neg_one_pow_eq_or (ZMod p) (x + 1) with hs | hs
  · have he : (1 : ZMod p) = 7 := hs.symm.trans h
    apply cast_ne_zero (p := p) (n := 6) (by decide) (by omega)
    linear_combination -he
  · have he : (-1 : ZMod p) = 7 := hs.symm.trans h
    apply cast_ne_zero (p := p) (n := 8) (by decide) (by omega)
    linear_combination -he

private lemma upper_one_ne_seven {p x : ℕ} [Fact p.Prime]
    (hp : 29 < p) (hx : x + 1 < p) :
    ((x + 1).factorial : ZMod p) * ((p - 1 - x).factorial : ZMod p) ≠ 7 := by
  rw [upper_one_identity (show x < p by omega)]
  intro h
  have he := signed_index_even (odd_mod_two hp) hx
  have hval : (7 : ZMod p).val = 7 := ZMod.val_cast_of_lt (show 7 < p by omega)
  rw [h, hval] at he
  norm_num at he

private lemma lower_one_ne_seven {p x : ℕ} [Fact p.Prime]
    (hp : 29 < p) (hm : p % 6699 = 2) (hx : x + 1 < p) :
    (x.factorial : ZMod p) * ((p - 1 - (x + 1)).factorial : ZMod p) ≠ 7 := by
  intro h
  have hid := lower_one_identity hx
  rw [h] at hid
  have hseven : (7 : ZMod p) ≠ 0 := cast_ne_zero (n := 7) (by decide) (by omega)
  have he : (-1 : ZMod p) ^ (x + 1 + 1) * ((x + 1 : ℕ) : ZMod p) =
      (7 : ZMod p)⁻¹ := by
    apply mul_right_cancel₀ hseven
    rw [inv_mul_cancel₀ hseven]
    calc
      _ = (-1 : ZMod p) ^ (x + 2) * (((x + 1 : ℕ) : ZMod p) * 7) := by ring
      _ = (-1 : ZMod p) ^ (x + 2) * (-1) ^ (x + 2) := by rw [hid]
      _ = 1 := by rw [← mul_pow]; norm_num
  have ho := signed_index_odd (odd_mod_two hp) (show 0 < x + 1 by omega) hx
  rw [he] at ho
  have hev := inverse_seven_even hp hm
  omega

private lemma upper_two_ne_seven {p x : ℕ} [Fact p.Prime]
    (hp : 29 < p) (hm : p % 6699 = 2) (hx : x + 2 < p) :
    ((x + 2).factorial : ZMod p) * ((p - 1 - x).factorial : ZMod p) ≠ 7 := by
  rw [upper_two_identity (show x < p by omega)]
  intro h
  obtain ⟨hpos, hneg, _, _⟩ := quadratic_obstructions hp hm (x : ZMod p)
  rcases neg_one_pow_eq_or (ZMod p) (x + 1) with hs | hs
  · exact hpos (by simpa only [hs, one_mul] using h)
  · exact hneg (by simpa only [hs, neg_one_mul, neg_eq_iff_eq_neg] using h)

private lemma lower_two_ne_seven {p x : ℕ} [Fact p.Prime]
    (hp : 29 < p) (hm : p % 6699 = 2) (hx : x + 2 < p) :
    (x.factorial : ZMod p) * ((p - 1 - (x + 2)).factorial : ZMod p) ≠ 7 := by
  intro h
  have hid := lower_two_identity hx
  rw [h] at hid
  obtain ⟨_, _, hpos, hneg⟩ := quadratic_obstructions hp hm (x : ZMod p)
  rcases neg_one_pow_eq_or (ZMod p) (x + 3) with hs | hs
  · apply hpos
    rw [mul_comm, hid, hs]
  · apply hneg
    rw [mul_comm, hid, hs]

/-- **Five-band avoidance only.** For these primes, no factorial pair with
sum in `{p-3,p-2,p-1,p,p+1}` represents seven. The indices are natural numbers,
so their lower bounds by zero are automatic. No other sums are covered. -/
theorem factorial_mul_ne_seven_in_five_bands {p i j : ℕ}
    (hprime : p.Prime) (hp : 29 < p) (hm : p % 6699 = 2)
    (hi : i < p) (hj : j < p)
    (hband : i + j ∈ ({p - 3, p - 2, p - 1, p, p + 1} : Finset ℕ)) :
    (i.factorial : ZMod p) * (j.factorial : ZMod p) ≠ 7 := by
  letI : Fact p.Prime := ⟨hprime⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hband
  rcases hband with h | h | h | h | h
  · rw [show j = p - 1 - (i + 2) by omega]
    exact lower_two_ne_seven hp hm (by omega)
  · rw [show j = p - 1 - (i + 1) by omega]
    exact lower_one_ne_seven hp hm (by omega)
  · rw [show j = p - 1 - i by omega]
    exact middle_ne_seven hp hi
  · have hi' : i - 1 + 1 = i := by omega
    have hj' : j = p - 1 - (i - 1) := by omega
    have ha := upper_one_ne_seven (x := i - 1) hp (by omega)
    simpa only [hi', ← hj'] using ha
  · have hi' : i - 2 + 2 = i := by omega
    have hj' : j = p - 1 - (i - 2) := by omega
    have ha := upper_two_ne_seven (x := i - 2) hp hm (by omega)
    simpa only [hi', ← hj'] using ha

/-- Dirichlet gives arbitrarily large primes for which the five-band
avoidance theorem applies. This still asserts nothing about other bands. -/
theorem arbitrarily_large_primes_with_five_band_avoidance (N : ℕ) :
    ∃ p > N, p.Prime ∧ 29 < p ∧ p % 6699 = 2 ∧
      ∀ i j : ℕ, i < p → j < p →
        i + j ∈ ({p - 3, p - 2, p - 1, p, p + 1} : Finset ℕ) →
        (i.factorial : ZMod p) * (j.factorial : ZMod p) ≠ 7 := by
  obtain ⟨p, hlarge, hprime, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max N 29)
      (q := 6699) (a := 2) (by decide) (by decide)
  have hp : 29 < p := lt_of_le_of_lt (le_max_right N 29) hlarge
  have hm : p % 6699 = 2 := by simpa [Nat.ModEq] using hmod
  refine ⟨p, lt_of_le_of_lt (le_max_left N 29) hlarge, hprime, hp, hm, ?_⟩
  intro i j hi hj hband
  exact factorial_mul_ne_seven_in_five_bands hprime hp hm hi hj hband

/-- Infinitely many primes in `2 mod 6699`, above 29, avoid seven on the
five indicated factorial-product bands (not necessarily on other bands). -/
theorem infinitely_many_primes_with_five_band_avoidance :
    Set.Infinite {p : ℕ | p.Prime ∧ 29 < p ∧ p % 6699 = 2 ∧
      ∀ i j : ℕ, i < p → j < p →
        i + j ∈ ({p - 3, p - 2, p - 1, p, p + 1} : Finset ℕ) →
        (i.factorial : ZMod p) * (j.factorial : ZMod p) ≠ 7} := by
  apply Set.infinite_iff_exists_gt.mpr
  intro N
  obtain ⟨p, hN, hprime, hp, hm, hband⟩ :=
    arbitrarily_large_primes_with_five_band_avoidance N
  exact ⟨p, ⟨hprime, hp, hm, hband⟩, hN⟩

end FactorialBand

#print axioms FactorialBand.factorial_mul_ne_seven_in_five_bands
#print axioms FactorialBand.arbitrarily_large_primes_with_five_band_avoidance
#print axioms FactorialBand.infinitely_many_primes_with_five_band_avoidance
