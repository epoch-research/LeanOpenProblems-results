import Submission.ExceptionSieveDecision

/-! Arithmetic meaning of the exception-retaining Gaussian sieve.
The least-factor argument below identifies its composite vertices exactly.
It does not prove that the component at 3 is finite at some cutoff for every
jump bound. -/
namespace Erdos952Investigation.RoughCandidateArithmetic
open FiniteSieveReduction ExceptionSieveReduction GaussianPrimeDecision
set_option maxHeartbeats 0

/-- Every nonzero nonunit composite has a rational prime divisor of its norm
whose square is at most that norm. -/
theorem composite_small_norm_divisor {z : GaussianInt}
    (hz : 1 < z.norm) (hnp : ¬ Prime z) :
    ∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ z.norm ∧ (p : ℤ)^2 ≤ z.norm := by
  have hzu : ¬ IsUnit z := by
    intro hu
    have hnorm := (Zsqrtd.norm_eq_one_iff' (by decide : (-1 : ℤ) ≤ 0) z).mpr hu
    omega
  have hni : ¬ Irreducible z := fun h => hnp (irreducible_iff_prime.mp h)
  have hfac : ∃ a b : GaussianInt, z = a*b ∧ ¬ IsUnit a ∧ ¬ IsUnit b := by
    simpa [irreducible_iff,hzu,not_forall,not_or] using hni
  obtain ⟨a,b,hab,hau,hbu⟩ := hfac
  have ha0 : a ≠ 0 := by
    intro he
    rw [hab,he,zero_mul] at hz
    norm_num at hz
  have hb0 : b ≠ 0 := by
    intro he
    rw [hab,he,mul_zero] at hz
    norm_num at hz
  have ha := norm_gt_one_of_nonunit ha0 hau
  have hb := norm_gt_one_of_nonunit hb0 hbu
  have hnorm : z.norm = a.norm*b.norm := by rw [hab,Zsqrtd.norm_mul]
  have hsmall (u v : GaussianInt) (hu : 1 < u.norm)
      (huv : u.norm ≤ v.norm) (hn : z.norm = u.norm*v.norm) :
      ∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ z.norm ∧ (p : ℤ)^2 ≤ z.norm := by
    have hcast : (u.norm.natAbs : ℤ) = u.norm := GaussianInt.abs_natCast_norm u
    have hne : u.norm.natAbs ≠ 1 := by
      intro h
      rw [h] at hcast
      norm_num at hcast
      omega
    obtain ⟨p,hp,hpd⟩ := Nat.exists_prime_and_dvd hne
    have hpos : 0 < u.norm.natAbs := Int.natAbs_pos.mpr (by omega)
    have hpule : (p : ℤ) ≤ u.norm := by
      have hh : (p : ℤ) ≤ u.norm.natAbs := by
        exact_mod_cast Nat.le_of_dvd hpos hpd
      rwa [hcast] at hh
    have hpd' : (p : ℤ) ∣ u.norm := Int.natCast_dvd.mpr hpd
    have hp0 : (0 : ℤ) ≤ p := Int.natCast_nonneg p
    refine ⟨p,hp,?_,?_⟩
    · rw [hn]
      exact dvd_mul_of_dvd_left hpd' _
    · rw [hn]
      nlinarith
  rcases le_total a.norm b.norm with h | h
  · exact hsmall a b ha h hnorm
  · exact hsmall b a hb h (by rw [hnorm,mul_comm])

/-- A rough nonunit in the norm ball N² is already Gaussian prime. -/
theorem prime_of_allowed_of_norm_le {N : ℕ} {z : GaussianInt}
    (ha : Allowed N z) (hz : 1 < z.norm) (hsmall : z.norm ≤ (N : ℤ)^2) :
    Prime z := by
  by_contra hn
  obtain ⟨p,hp,hpd,hpsq⟩ := composite_small_norm_divisor hz hn
  have hN : (0 : ℤ) ≤ N := Int.natCast_nonneg N
  have hp0 : (0 : ℤ) ≤ p := Int.natCast_nonneg p
  have hpN : p ≤ N := by
    have hh : (p : ℤ) ≤ N := by nlinarith
    exact_mod_cast hh
  exact ha p hpN hp hpd

/-- A nonprime rough nonunit can only occur outside the exact-primality ball. -/
theorem composite_allowed_norm_gt {N : ℕ} {z : GaussianInt}
    (ha : Allowed N z) (hz : 1 < z.norm) (hnp : ¬ Prime z) :
    (N : ℤ)^2 < z.norm := by
  by_contra! h
  exact hnp (prime_of_allowed_of_norm_le ha hz h)

lemma candidate_of_allowed_nonunit {N : ℕ} {z : GaussianInt}
    (ha : Allowed N z) (hz : 1 < z.norm) : Candidate N z := by
  by_cases hsmall : z.norm ≤ (N : ℤ)^2
  · exact prime_candidate (prime_of_allowed_of_norm_le ha hz hsmall)
  · exact Or.inr ⟨lt_of_not_ge hsmall,ha⟩

/-- At every positive cutoff the radius condition can equivalently be
replaced by exclusion of norm-zero and norm-one vertices. -/
theorem candidate_iff_prime_or_rough_nonunit {N : ℕ} (hN : 1 ≤ N)
    (z : GaussianInt) :
    Candidate N z ↔ Prime z ∨ (1 < z.norm ∧ Allowed N z) := by
  constructor
  · rintro (hp | ⟨hlarge,ha⟩)
    · exact Or.inl hp
    · have hN' : (1 : ℤ) ≤ N := by exact_mod_cast hN
      exact Or.inr ⟨by nlinarith,ha⟩
  · rintro (hp | ⟨hlarge,ha⟩)
    · exact prime_candidate hp
    · exact candidate_of_allowed_nonunit ha hlarge

/-- For a composite nonunit, candidate status is exactly ordinary sieve
survival; retaining genuine primes is the only arithmetic exception. -/
theorem composite_candidate_iff_allowed {N : ℕ} {z : GaussianInt}
    (hz : 1 < z.norm) (hnp : ¬ Prime z) :
    Candidate N z ↔ Allowed N z := by
  constructor
  · rintro (hp | ⟨_,ha⟩)
    · exact (hnp hp).elim
    · exact ha
  · exact fun ha => candidate_of_allowed_nonunit ha hz

#print axioms composite_small_norm_divisor
#print axioms prime_of_allowed_of_norm_le
#print axioms candidate_iff_prime_or_rough_nonunit
#print axioms composite_candidate_iff_allowed
end Erdos952Investigation.RoughCandidateArithmetic
