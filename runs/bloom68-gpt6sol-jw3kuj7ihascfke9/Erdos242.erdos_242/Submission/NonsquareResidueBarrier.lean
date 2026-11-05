import Submission.PointwiseJacobi

/-!
# An infinite nonsquare family with an unsaturated divisor-residue box

This is a **local obstruction**, not a counterexample to Erdős–Straus and
not a failure of Type I at every possible first denominator.  For
`x = 59 * 229^t`, `n = 4*x - 19`, the chosen eligible denominator has
`a = 19`.  Although `59` is a primitive root modulo `19`, has negative
Jacobi symbol modulo `n`, and the number of divisors of `x²` grows without
bound, all their residues modulo `19` belong to `{1, 2, 4}`.  Neither
required residue (`14` for Type I, `17` for Type II) occurs.  This file
does not import or modify `Submission.Spec`.
-/

namespace Erdos242

/-- The candidate first denominator of the local obstruction. -/
def residueMissX (t : ℕ) : ℕ := 59 * 229 ^ t

/-- A nonsquare numerator in the hard congruence class. -/
def residueMissN (t : ℕ) : ℕ := 4 * residueMissX t - 19

private theorem pow229_mod_nineteen (t : ℕ) : 229 ^ t % 19 = 1 := by
  rw [Nat.pow_mod]
  norm_num

private theorem pow229_mod_six (t : ℕ) : 229 ^ t % 6 = 1 := by
  rw [Nat.pow_mod]
  norm_num

/-- All first denominators in the family are `2` modulo 19 and `5`
modulo 6; the second congruence ensures the hard numerator class. -/
theorem residueMissX_moduli (t : ℕ) :
    residueMissX t % 19 = 2 ∧ residueMissX t % 6 = 5 := by
  constructor
  · change (59 * 229 ^ t) % 19 = 2
    rw [Nat.mul_mod, pow229_mod_nineteen]
  · change (59 * 229 ^ t) % 6 = 5
    rw [Nat.mul_mod, pow229_mod_six]

/-- The candidate is in the *strict* first-denominator interval, with
first-denominator modulus exactly 19. -/
theorem residueMiss_eligible (t : ℕ) :
    residueMissN t < 4 * residueMissX t ∧
      2 * residueMissX t < residueMissN t ∧
        4 * residueMissX t - residueMissN t = 19 := by
  have hpow : 0 < 229 ^ t := pow_pos (by norm_num) t
  have hx : 59 ≤ residueMissX t := by
    dsimp [residueMissX]
    omega
  dsimp [residueMissN]
  omega

/-- The numerators are hard integers and nonresidues modulo 19. -/
theorem residueMissN_moduli (t : ℕ) :
    residueMissN t % 24 = 1 ∧ residueMissN t % 19 = 8 ∧
      residueMissN t % 8 = 1 := by
  obtain ⟨h19, h6⟩ := residueMissX_moduli t
  have hx2 : residueMissX t % 2 = 1 := by omega
  have hx : 19 < 4 * residueMissX t := by
    have hpow : 0 < 229 ^ t := pow_pos (by norm_num) t
    dsimp [residueMissX]
    omega
  dsimp [residueMissN]
  omega

/-- `8` is not a square modulo 19.  The finite residue calculation is
performed by Lean's kernel, not by a numerical search over numerators. -/
private theorem eight_not_square_mod_nineteen (s : ℕ) : s ^ 2 % 19 ≠ 8 := by
  have htable : ∀ r : Fin 19, r.val ^ 2 % 19 ≠ 8 := by decide
  intro h
  rw [Nat.pow_mod] at h
  exact htable ⟨s % 19, Nat.mod_lt s (by norm_num)⟩ h

/-- All numerators in this family are genuinely nonsquare, not merely
integers which have not been detected as squares in a finite audit. -/
theorem residueMissN_nonsquare (t : ℕ) :
    ¬ ∃ s : ℕ, s ^ 2 = residueMissN t := by
  rintro ⟨s, hs⟩
  have hmod : s ^ 2 % 19 = 8 := by
    rw [hs]
    exact (residueMissN_moduli t).2.1
  exact eight_not_square_mod_nineteen s hmod

/-- The two coprime prime-power factors of the squared denominator. -/
theorem residueMiss_square_factorization (t : ℕ) :
    (residueMissX t) ^ 2 = 59 ^ 2 * 229 ^ (2 * t) := by
  dsimp [residueMissX]
  calc
    (59 * 229 ^ t) ^ 2 = 59 ^ 2 * (229 ^ t) ^ 2 := by ring
    _ = 59 ^ 2 * 229 ^ (2 * t) := by rw [← pow_mul, mul_comm t 2]

/-- The number of divisors of `x²` is unbounded in this *obstructed*
family, not just the size of `x` or `n`. -/
theorem residueMiss_divisor_count (t : ℕ) :
    ((residueMissX t) ^ 2).divisors.card = 3 * (2 * t + 1) := by
  rw [residueMiss_square_factorization]
  have hcop : (59 ^ 2).Coprime (229 ^ (2 * t)) :=
    (by norm_num : Nat.Coprime 59 229).pow 2 (2 * t)
  have h59 : (59 ^ 2).divisors.card = 3 := by
    rw [Nat.divisors_prime_pow (by norm_num : Nat.Prime 59)]
    simp
  have h229 : (229 ^ (2 * t)).divisors.card = 2 * t + 1 := by
    rw [Nat.divisors_prime_pow (by norm_num : Nat.Prime 229)]
    simp
  rw [hcop.card_divisors_mul, h59, h229]

/-- For any prescribed threshold the number of divisors of `x²`
exceeds it.  The later lemma `residueMiss_no_types` simultaneously proves
that none of these divisors meets either target at this `x`. -/
theorem residueMiss_divisor_count_unbounded (B : ℕ) :
    ∃ t : ℕ, B < ((residueMissX t) ^ 2).divisors.card := by
  refine ⟨B, ?_⟩
  rw [residueMiss_divisor_count]
  omega


/-- Full characterization of the residues of *all* possible Type-I
cofactors (and Type-II divisors), with their complete exponent bounds.
No restriction `c ∣ x` is made: the input is `c ∣ x²`. -/
theorem residueMiss_divisor_residues (t c : ℕ)
    (hc : c ∣ (residueMissX t) ^ 2) :
    c % 19 = 1 ∨ c % 19 = 2 ∨ c % 19 = 4 := by
  rw [residueMiss_square_factorization] at hc
  obtain ⟨u, v, hu, hv, huv⟩ := exists_dvd_and_dvd_of_dvd_mul hc
  obtain ⟨i, hi, hui⟩ :=
    (Nat.dvd_prime_pow (by norm_num : Nat.Prime 59)).mp hu
  obtain ⟨j, hj, hvj⟩ :=
    (Nat.dvd_prime_pow (by norm_num : Nat.Prime 229)).mp hv
  have hmod : c % 19 = 59 ^ i % 19 := by
    calc
      c % 19 = (59 ^ i * 229 ^ j) % 19 := by rw [huv, hui, hvj]
      _ = 59 ^ i % 19 := by
        rw [Nat.mul_mod, pow229_mod_nineteen]
        simp
  rw [hmod]
  interval_cases i <;> norm_num

/-- **Neither** full divisor condition works at this particular eligible
first denominator, even though the numerator is nonsquare. -/
theorem residueMiss_no_types (t : ℕ) :
    ¬ TypeI (residueMissN t) (residueMissX t) ∧
      ¬ TypeII (residueMissN t) (residueMissX t) := by
  have ha := (residueMiss_eligible t).2.2
  have hx19 := (residueMissX_moduli t).1
  constructor
  · rintro ⟨c, _, hc, hac⟩
    rw [ha] at hac
    have hzero : (4 * c + 1) % 19 = 0 := Nat.mod_eq_zero_of_dvd hac
    rcases residueMiss_divisor_residues t c hc with h | h | h <;> omega
  · rintro ⟨d, _, _, hd, had⟩
    rw [ha] at had
    have hzero : (residueMissX t + d) % 19 = 0 := Nat.mod_eq_zero_of_dvd had
    rcases residueMiss_divisor_residues t d hd with h | h | h <;> omega

/-- The failing candidate nevertheless contains a quadratic nonresidue
prime factor: its Jacobi symbol transfers from `19` to `n`.  The sign is
necessary for Type I, but cannot supply the exact residue `14`. -/
theorem residueMiss_nonresidue_factor (t : ℕ) :
    jacobiSym (59 : ℤ) (residueMissN t) = -1 := by
  have hsum : 19 + residueMissN t = 4 * residueMissX t := by
    have hd := residueMiss_eligible t
    omega
  have hdiv : 59 ∣ (residueMissX t) ^ 2 := by
    refine ⟨59 * (229 ^ t) ^ 2, ?_⟩
    dsimp [residueMissX]
    ring
  have htrans := jacobi_divisor_transfer (residueMissN t) 19
    (residueMissX t) 59 (residueMissN_moduli t).2.2 (by norm_num)
    hsum hdiv
  calc
    jacobiSym (59 : ℤ) (residueMissN t) = jacobiSym (59 : ℤ) 19 := htrans.symm
    _ = -1 := by norm_num

/-- The first numerator `n=217` has a Type-I certificate at a *different*
eligible first denominator, `x=55`, `c=5`.  This explicitly illustrates
why a local obstruction does not make an Erdős–Straus counterexample. -/
theorem residueMiss_zero_good : Good (residueMissN 0) := by
  change Good 217
  apply good_of_typeI 217 55 (by norm_num) (by norm_num) (by norm_num)
  exact ⟨5, by norm_num, by norm_num, by norm_num⟩

/-- Even the sole nontrivial prime factor generating the entire unit group
modulo 19 does not help: its available exponents in `c ∣ x²` are only
`0`, `1`, and `2`. -/
theorem residueMiss_primitive_root : orderOf (59 : ZMod 19) = 18 := by
  apply (orderOf_eq_iff (x := (59 : ZMod 19)) (by norm_num : 0 < 18)).mpr
  constructor
  · decide
  · intro m hm hpos
    interval_cases m <;> decide

/-- The exact obstruction in one statement: arbitrarily many divisors,
a nonsquare numerator in the hard congruence class, a genuine negative
Jacobi symbol, and *no* full divisor certificate of either type at the
specified (eligible) first denominator.  This is **not** a claim about
all first denominators of these numerators. -/
theorem residueMiss_unbounded_local_obstruction (B : ℕ) :
    ∃ t : ℕ, B < ((residueMissX t) ^ 2).divisors.card ∧
      residueMissN t % 24 = 1 ∧
      (¬ ∃ s : ℕ, s ^ 2 = residueMissN t) ∧
      jacobiSym (59 : ℤ) (residueMissN t) = -1 ∧
      ¬ TypeI (residueMissN t) (residueMissX t) ∧
      ¬ TypeII (residueMissN t) (residueMissX t) := by
  refine ⟨B, ?_, (residueMissN_moduli B).1, residueMissN_nonsquare B,
    residueMiss_nonresidue_factor B, (residueMiss_no_types B).1,
    (residueMiss_no_types B).2⟩
  rw [residueMiss_divisor_count]
  omega

/-- Such local failures exist above *any* threshold; this statement
still makes NO claim that any numerator fails at every other candidate. -/
theorem arbitrarily_large_nonsquare_residue_misses (N : ℕ) :
    ∃ t : ℕ, N < residueMissN t ∧
      residueMissN t % 24 = 1 ∧
      (¬ ∃ s : ℕ, s ^ 2 = residueMissN t) ∧
      residueMissN t < 4 * residueMissX t ∧
      2 * residueMissX t < residueMissN t ∧
      ¬ TypeI (residueMissN t) (residueMissX t) := by
  obtain ⟨t, hpow⟩ := pow_unbounded_of_one_lt (N + 19)
    (by norm_num : 1 < (229 : ℕ))
  have hsum : residueMissN t + 19 = 4 * residueMissX t := by
    have hd := residueMiss_eligible t
    omega
  have hN : N < residueMissN t := by
    have hx : 229 ^ t ≤ residueMissX t := by
      dsimp [residueMissX]
      omega
    omega
  exact ⟨t, hN, (residueMissN_moduli t).1, residueMissN_nonsquare t,
    (residueMiss_eligible t).1, (residueMiss_eligible t).2.1,
    (residueMiss_no_types t).1⟩

end Erdos242

#print axioms Erdos242.residueMissN_nonsquare
#print axioms Erdos242.residueMiss_divisor_count
#print axioms Erdos242.residueMiss_divisor_residues
#print axioms Erdos242.residueMiss_no_types
#print axioms Erdos242.residueMiss_nonresidue_factor
#print axioms Erdos242.residueMiss_primitive_root
#print axioms Erdos242.residueMiss_unbounded_local_obstruction
#print axioms Erdos242.arbitrarily_large_nonsquare_residue_misses
