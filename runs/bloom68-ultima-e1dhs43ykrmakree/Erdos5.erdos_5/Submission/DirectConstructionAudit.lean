import FormalConjecturesUtil

/-!
# Elementary audit of a direct construction

This independent scratch file does not import `Submission.Spec`. These lemmas
are construction obstructions only: they neither prove nor disprove Erdős #5,
and do not assert the existence of any proposed family of factor pairs.

All variables are natural numbers. Ordered factors suffice for the algebraic
results; positivity is not needed. The certified-range constant is `16 * M`.
No additional axioms or unfinished proofs are used.
-/

namespace DirectConstructionAudit

/-- Covering every prime up to `y` forces a coprime factor difference in
`(1, y²]` to be prime. -/
theorem prime_difference_of_small_prime_cover {y A B : ℕ}
    (hAB : A ≤ B) (hcop : Nat.Coprime A B)
    (hlarge : 1 < B - A) (hsmall : B - A ≤ y ^ 2)
    (hcover : ∀ p : ℕ, Nat.Prime p → p ≤ y → p ∣ A * B) :
    Nat.Prime (B - A) := by
  by_contra hnot
  let p := (B - A).minFac
  have hp : Nat.Prime p := Nat.minFac_prime (by omega)
  have hpd : p ∣ B - A := Nat.minFac_dvd _
  have hpsq : p ^ 2 ≤ y ^ 2 :=
    (Nat.minFac_sq_le_self (by omega) hnot).trans hsmall
  have hpy : p ≤ y := (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp hpsq
  have hcommon : p ∣ A ∧ p ∣ B := by
    rcases hp.dvd_mul.mp (hcover p hp hpy) with hpA | hpB
    · refine ⟨hpA, ?_⟩
      simpa only [Nat.sub_add_cancel hAB] using dvd_add hpd hpA
    · have hsum : p ∣ (B - A) + A := by rwa [Nat.sub_add_cancel hAB]
      exact ⟨(Nat.dvd_add_iff_right hpd).mpr hsum, hpB⟩
  apply hp.not_dvd_one
  simpa only [hcop.gcd_eq_one] using Nat.dvd_gcd hcommon.1 hcommon.2

/-- The sum/difference identity, with truncated subtraction justified by order. -/
theorem factor_square_identity {A B : ℕ} (hAB : A ≤ B) :
    (A + B) ^ 2 = 4 * (A * B) + (B - A) ^ 2 := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hAB
  simp only [Nat.add_sub_cancel_left]
  ring

/-- Distinct increasing differences force the natural-number sum to rise by
at least one, so their squares are separated by at least `2 * s1 + 1`. -/
theorem square_spacing {M e1 e2 s1 s2 : ℕ}
    (h1 : s1 ^ 2 = 4 * M + e1 ^ 2)
    (h2 : s2 ^ 2 = 4 * M + e2 ^ 2) (he : e1 < e2) :
    e1 ^ 2 + 2 * s1 + 1 ≤ e2 ^ 2 := by
  have hesq : e1 ^ 2 < e2 ^ 2 := Nat.pow_lt_pow_left he (by decide)
  have hssq : s1 ^ 2 < s2 ^ 2 := by omega
  have hs : s1 + 1 ≤ s2 :=
    Nat.succ_le_of_lt ((Nat.pow_lt_pow_iff_left (by decide : 2 ≠ 0)).mp hssq)
  have hstep := Nat.pow_le_pow_left hs 2
  nlinarith only [h1, h2, hstep]

/-- Factor-pair form of the spacing bound for a fixed product `M`. -/
theorem factor_difference_spacing {A1 B1 A2 B2 M : ℕ}
    (hAB1 : A1 ≤ B1) (hAB2 : A2 ≤ B2)
    (hprod1 : A1 * B1 = M) (hprod2 : A2 * B2 = M)
    (he : B1 - A1 < B2 - A2) :
    (B1 - A1) ^ 2 + 2 * (A1 + B1) + 1 ≤ (B2 - A2) ^ 2 := by
  exact square_spacing (M := M) (s2 := A2 + B2)
    (by simpa only [hprod1] using factor_square_identity hAB1)
    (by simpa only [hprod2] using factor_square_identity hAB2) he

/-- A local certified range: the smaller difference's sum satisfies the bound.
The lower difference need not separately be assumed to lie below `y²`. -/
theorem no_two_small_differences {y M e1 e2 s1 s2 : ℕ}
    (h1 : s1 ^ 2 = 4 * M + e1 ^ 2)
    (h2 : s2 ^ 2 = 4 * M + e2 ^ 2)
    (he : e1 < e2) (he2 : e2 ≤ y ^ 2) (hrange : y ^ 4 ≤ 2 * s1) :
    False := by
  have hgap := square_spacing h1 h2 he
  have hupper : e2 ^ 2 ≤ y ^ 4 := by
    calc
      e2 ^ 2 ≤ (y ^ 2) ^ 2 := Nat.pow_le_pow_left he2 2
      _ = y ^ 4 := by ring
  omega

/-- The global range `y⁸ ≤ 16M` supplies the local sum bound for either pair,
so any two differences at most `y²` must coincide. -/
theorem certified_range_unique {y M e1 e2 s1 s2 : ℕ}
    (h1 : s1 ^ 2 = 4 * M + e1 ^ 2)
    (h2 : s2 ^ 2 = 4 * M + e2 ^ 2)
    (he1 : e1 ≤ y ^ 2) (he2 : e2 ≤ y ^ 2) (hrange : y ^ 8 ≤ 16 * M) :
    e1 = e2 := by
  have hbound : ∀ s e : ℕ, s ^ 2 = 4 * M + e ^ 2 → y ^ 4 ≤ 2 * s := by
    intro s e hs
    apply (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp
    calc
      (y ^ 4) ^ 2 = y ^ 8 := by ring
      _ ≤ 16 * M := hrange
      _ ≤ 4 * s ^ 2 := by omega
      _ = (2 * s) ^ 2 := by ring
  rcases lt_trichotomy e1 e2 with hlt | heq | hgt
  · exact (no_two_small_differences h1 h2 hlt he2 (hbound s1 e1 h1)).elim
  · exact heq
  · exact (no_two_small_differences h2 h1 hgt he1 (hbound s2 e2 h2)).elim

/-- In the certified range, a fixed product cannot have two distinct ordered
factor differences at most `y²`. This is not an existence theorem. -/
theorem factor_difference_unique {y A1 B1 A2 B2 M : ℕ}
    (hAB1 : A1 ≤ B1) (hAB2 : A2 ≤ B2)
    (hprod1 : A1 * B1 = M) (hprod2 : A2 * B2 = M)
    (he1 : B1 - A1 ≤ y ^ 2) (he2 : B2 - A2 ≤ y ^ 2)
    (hrange : y ^ 8 ≤ 16 * M) : B1 - A1 = B2 - A2 := by
  exact certified_range_unique (M := M) (s1 := A1 + B1) (s2 := A2 + B2)
    (by simpa only [hprod1] using factor_square_identity hAB1)
    (by simpa only [hprod2] using factor_square_identity hAB2) he1 he2 hrange

#print axioms prime_difference_of_small_prime_cover
#print axioms factor_square_identity
#print axioms square_spacing
#print axioms factor_difference_spacing
#print axioms no_two_small_differences
#print axioms certified_range_unique
#print axioms factor_difference_unique

end DirectConstructionAudit
