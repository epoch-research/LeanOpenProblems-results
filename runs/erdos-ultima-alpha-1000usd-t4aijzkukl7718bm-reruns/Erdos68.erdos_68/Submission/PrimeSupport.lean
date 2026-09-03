import Submission.Development

/-! Prime support of the original denominators; not an irrationality proof. -/

namespace Erdos68Development

/-- No prime at most the factorial index divides its predecessor. -/
lemma prime_dvd_denom_gt {n p : ℕ} (hp : p.Prime) (hd : p ∣ denom n) :
    n + 2 < p := by
  by_contra h
  have hf : p ∣ (n + 2).factorial :=
    Nat.dvd_factorial hp.pos (by omega)
  have he : (n + 2).factorial = denom n + 1 := by
    unfold denom
    have := Nat.factorial_pos (n + 2)
    omega
  rw [he] at hf
  have h1 : p ∣ 1 := (Nat.dvd_add_iff_right hd).mpr hf
  exact hp.not_dvd_one h1

/-- A fixed prime divides none of the sufficiently late denominators. -/
lemma prime_not_dvd_denom_of_le {n p : ℕ} (hp : p.Prime) (hn : p ≤ n + 2) :
    ¬ p ∣ denom n := by
  intro hd
  have := prime_dvd_denom_gt hp hd
  omega

/-- Wilson's theorem locates a denominator divisible by each prime at least five. -/
lemma prime_dvd_denom_sub_four {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    p ∣ denom (p - 4) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hw := ZMod.wilsons_lemma p
  have hf : (p - 1).factorial = (p - 1) * (p - 2).factorial := by
    rw [show p - 1 = (p - 2) + 1 by omega, Nat.factorial_succ]
  have hcast : ((p - 1 : ℕ) : ZMod p) = -1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p)]
    simp
  rw [hf, Nat.cast_mul, hcast] at hw
  have hw' : ((p - 2).factorial : ZMod p) = 1 := by
    simpa only [neg_one_mul, neg_inj] using hw
  unfold denom
  rw [show p - 4 + 2 = p - 2 by omega]
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.factorial_pos _),
    Nat.cast_one, hw', sub_self]

/-- The prime support of all the denominators is exactly the primes at least five. -/
lemma prime_dvd_some_denom_iff {p : ℕ} (hp : p.Prime) :
    (∃ n : ℕ, p ∣ denom n) ↔ 5 ≤ p := by
  constructor
  · rintro ⟨n, hn⟩
    have hlt := prime_dvd_denom_gt hp hn
    by_contra h
    have hp2 := hp.two_le
    have hp4 : p ≤ 4 := by omega
    interval_cases p
    · omega
    · have : n = 0 := by omega
      subst n
      norm_num [denom, Nat.factorial] at hn
    · norm_num at hp
  · intro hp5
    exact ⟨p - 4, prime_dvd_denom_sub_four hp hp5⟩

end Erdos68Development

#print axioms Erdos68Development.prime_dvd_denom_gt

#print axioms Erdos68Development.prime_dvd_denom_sub_four
#print axioms Erdos68Development.prime_dvd_some_denom_iff
