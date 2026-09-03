import Submission.BinomialFilteredLambert

/-!
A large-prime valuation bound for recursive gcds of the actual filtered
Lambert coefficients. This is auxiliary arithmetic, not an irrationality
proof and not a bound on an integer lift.
-/

namespace FilteredCoefficientGcd

open BinomialFilteredLambert

/-- The gcd recurrence for factorial-scaled coefficient prefixes, with the
factorial denominator itself included in the initial ideal. -/
def coeffGcd (a : ℕ → ℤ) : ℕ → ℕ
  | 0 => 1
  | n+1 => Nat.gcd (a (n+1)).natAbs ((n+1)*coeffGcd a n)

lemma coeffGcd_pos (a : ℕ → ℤ) (n : ℕ) : 0 < coeffGcd a n := by
  induction n with
  | zero => simp [coeffGcd]
  | succ n ih =>
    exact Nat.gcd_pos_of_pos_right _ (by positivity)


/-- The integer sequence whose gcd is taken at a fixed factorial scale. -/
def scaledCoeff (a : ℕ → ℤ) (n k : ℕ) : ℕ :=
  (a k).natAbs * (n.factorial / k.factorial)

lemma scaledCoeff_last (a : ℕ → ℤ) (n : ℕ) :
    scaledCoeff a n n = (a n).natAbs := by
  simp [scaledCoeff, Nat.div_self (Nat.factorial_pos n)]

lemma scaledCoeff_succ (a : ℕ → ℤ) (n k : ℕ) (hk : k ≤ n) :
    scaledCoeff a (n+1) k = (n+1)*scaledCoeff a n k := by
  unfold scaledCoeff
  rw [Nat.factorial_succ,
    Nat.mul_div_assoc _ (Nat.factorial_dvd_factorial hk)]
  ring

lemma finite_gcd_succ (a : ℕ → ℤ) (n : ℕ) :
    (Finset.range (n+2)).gcd (scaledCoeff a (n+1)) =
      Nat.gcd (a (n+1)).natAbs
        ((n+1)*(Finset.range (n+1)).gcd (scaledCoeff a n)) := by
  rw [show n+2=(n+1)+1 by omega, Finset.range_add_one, Finset.gcd_insert,
    scaledCoeff_last]
  have he : (Finset.range (n+1)).gcd (scaledCoeff a (n+1)) =
      (Finset.range (n+1)).gcd (fun k => (n+1)*scaledCoeff a n k) := by
    apply Finset.gcd_congr rfl
    intro k hk
    exact scaledCoeff_succ a n k (by have := Finset.mem_range.mp hk; omega)
  rw [he, Finset.gcd_mul_left]
  simp [gcd_eq_nat_gcd]

/-- The recurrence is precisely a gcd of the individually scaled prefix
coefficients together with n!, not a gcd of their sum. -/
theorem coeffGcd_eq_finite (a : ℕ → ℤ) (n : ℕ) :
    coeffGcd a n = Nat.gcd n.factorial
      ((Finset.range (n+1)).gcd (scaledCoeff a n)) := by
  induction n with
  | zero => simp [coeffGcd]
  | succ n ih =>
    rw [coeffGcd, ih, show n+1+1=n+2 by omega, finite_gcd_succ,
      Nat.factorial_succ, ← Nat.gcd_mul_left]
    ac_rfl

lemma coeffGcd_dvd_factorial (a : ℕ → ℤ) (n : ℕ) :
    coeffGcd a n ∣ n.factorial := by
  induction n with
  | zero => simp [coeffGcd]
  | succ n ih =>
    rw [coeffGcd, Nat.factorial_succ]
    exact (Nat.gcd_dvd_right _ _).trans (Nat.mul_dvd_mul_left (n+1) ih)

lemma coeffGcd_dvd_last (a : ℕ → ℤ) (n : ℕ) :
    coeffGcd a (n+1) ∣ (a (n+1)).natAbs :=
  Nat.gcd_dvd_left _ _

lemma modEq_one_not_dvd {p : ℕ} (hp : p.Prime) {z : ℤ}
    (hz : Int.ModEq p z 1) : ¬p ∣ z.natAbs := by
  intro hdiv
  have hzero : Int.ModEq p z 0 :=
    Int.modEq_zero_iff_dvd.mpr (Int.natCast_dvd.mpr hdiv)
  have hone : (p : ℤ) ∣ (1 : ℤ) :=
    Int.modEq_zero_iff_dvd.mp (hz.symm.trans hzero)
  exact hp.not_dvd_one (by exact_mod_cast hone)

/-- A predecessor-unit congruence prevents the old p-part of the gcd from
surviving the next step. Only the current index can contribute a p-part. -/
theorem prime_valuation_bound (a : ℕ → ℤ) (p : ℕ) (hp : p.Prime)
    (ha : ∀ n, 2 ≤ n → p ∣ n-1 → Int.ModEq p (a n) 1)
    (n : ℕ) (hn : 0 < n) :
    (coeffGcd a n).factorization p ≤ n.factorization p := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n
      simp [coeffGcd]
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hi := ih hnpos
    have hgpos := coeffGcd_pos a n
    by_cases hpn : p ∣ n
    · have hz := ha (n+1) (by omega) (by simpa using hpn)
      have hunit := modEq_one_not_dvd hp hz
      have hgunit : ¬p ∣ coeffGcd a (n+1) :=
        fun h => hunit (h.trans (coeffGcd_dvd_last a n))
      rw [Nat.factorization_eq_zero_of_not_dvd hgunit]
      omega
    · have hnf : n.factorization p = 0 :=
        Nat.factorization_eq_zero_of_not_dvd hpn
      have hgf : (coeffGcd a n).factorization p = 0 := by omega
      have hdiv : coeffGcd a (n+1) ∣ (n+1)*coeffGcd a n :=
        Nat.gcd_dvd_right _ _
      have hle := (Nat.factorization_le_iff_dvd
        (coeffGcd_pos a (n+1)).ne'
        (mul_pos (by omega : 0 < n+1) hgpos).ne').mpr hdiv
      have hpoint := hle p
      rw [Nat.factorization_mul (by omega) hgpos.ne', Finsupp.add_apply, hgf,
        add_zero] at hpoint
      exact hpoint

/-- Applies to the exact binomial filters, without carrying or changing the
original Lambert coefficients before applying the specified operator. -/
theorem filtered_prime_valuation_bound (ks : List ℕ) (p : ℕ) (hp : p.Prime)
    (hks : ∀ k ∈ ks, 2 ≤ k ∧ k < p) (n : ℕ) (hn : 0 < n) :
    (coeffGcd (filtered ks) n).factorization p ≤ n.factorization p := by
  apply prime_valuation_bound (filtered ks) p hp
    (fun m hm hpm => filtered_at_pred ks p m hp hm hpm hks) n hn

/-- In particular, a prime above every filter degree that is absent from the
current index is also absent from this recursive gcd. -/
theorem filtered_gcd_not_dvd (ks : List ℕ) (p : ℕ) (hp : p.Prime)
    (hks : ∀ k ∈ ks, 2 ≤ k ∧ k < p) (n : ℕ) (hn : 0 < n)
    (hpn : ¬p ∣ n) : ¬p ∣ coeffGcd (filtered ks) n := by
  intro hdiv
  have hpos := hp.factorization_pos_of_dvd (coeffGcd_pos (filtered ks) n).ne' hdiv
  have hle := filtered_prime_valuation_bound ks p hp hks n hn
  have hzero := Nat.factorization_eq_zero_of_not_dvd hpn
  omega

end FilteredCoefficientGcd

#print axioms FilteredCoefficientGcd.prime_valuation_bound
#print axioms FilteredCoefficientGcd.filtered_prime_valuation_bound
#print axioms FilteredCoefficientGcd.filtered_gcd_not_dvd

#print axioms FilteredCoefficientGcd.coeffGcd_eq_finite
