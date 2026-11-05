import Submission.Classification
import Submission.Partial

/-!
# Pointwise divisor covering for the ordered Erdős–Straus conjecture

These are equivalences, finite stress-test witnesses, and an infinite obstruction
to *bounded* type-II parameters. Nothing here supplies the missing universal
divisor-covering assertion, proves `Good` for all hard primes, or edits `Spec.lean`.
-/

namespace Erdos242

/-- Exact counterexample obligation, excluding *both* types at *every* eligible first denominator. -/
theorem bad_prime_iff_no_divisors (p : ℕ) (hp : p.Prime) (hgt : 2 < p) :
    ¬ Good p ↔ ∀ x : ℕ, p < 4 * x → 2 * x < p →
      ¬ TypeI p x ∧ ¬ TypeII p x := by
  rw [good_iff_ordered_divisors p hp hgt]
  constructor
  · intro h x hlo hhi
    constructor
    · intro hI
      exact h ⟨x, hlo, hhi, Or.inl hI⟩
    · intro hII
      exact h ⟨x, hlo, hhi, Or.inr hII⟩
  · intro h ⟨x, hlo, hhi, hcase⟩
    rcases hcase with hI | hII
    · exact (h x hlo hhi).1 hI
    · exact (h x hlo hhi).2 hII

/-- A counterexample at any `n>2` has a counterexample prime divisor
congruent to `1 (mod 24)`. Thus the least counterexample, if one exists,
is itself such a prime; no assumption that it exists is used here. -/
theorem bad_has_hard_prime_divisor (n : ℕ) (hn : 2 < n) (hbad : ¬ Good n) :
    ∃ p : ℕ, p.Prime ∧ p % 24 = 1 ∧ p ∣ n ∧ ¬ Good p := by
  have hn24 : n % 24 = 1 := by
    by_contra h
    exact hbad (good_outside_24 n hn h)
  obtain ⟨p, hp, ⟨k, heq⟩⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
  have hpgt : 2 < p := by
    have hp2 := hp.two_le
    by_contra h
    have hp2' : p = 2 := by omega
    rw [hp2'] at heq
    have heven : n % 2 = 0 := Nat.mod_eq_zero_of_dvd ⟨k, heq⟩
    omega
  have hk : 0 < k := by
    by_contra h
    have hk0 : k = 0 := by omega
    rw [hk0] at heq
    simp at heq
    omega
  have hbadp : ¬ Good p := by
    intro hgood
    have hgoodn : Good n := by rw [heq]; exact good_mul hgood hk
    exact hbad hgoodn
  have hp24 : p % 24 = 1 := by
    by_contra h
    exact hbadp (good_outside_24 p hpgt h)
  exact ⟨p, hp, hp24, ⟨k, heq⟩, hbadp⟩

/-- In the hard residue class, the complete candidate list is `x=6k+1+j`
with `j<6k`, and its congruence modulus is exactly `4j+3`. -/
theorem good_iff_hard_indices (k : ℕ) (hp : (24 * k + 1).Prime) :
    Good (24 * k + 1) ↔ ∃ j : ℕ, j < 6 * k ∧
      (TypeI (24 * k + 1) (6 * k + 1 + j) ∨
       TypeII (24 * k + 1) (6 * k + 1 + j)) := by
  have hgt : 2 < 24 * k + 1 := by
    have := hp.two_le
    omega
  rw [good_iff_ordered_divisors (24 * k + 1) hp hgt]
  constructor
  · rintro ⟨x, hlo, hhi, htypes⟩
    have hx : x = 6 * k + 1 + (x - (6 * k + 1)) := by omega
    refine ⟨x - (6 * k + 1), by omega, ?_⟩
    simpa only [← hx] using htypes
  · rintro ⟨j, hj, htypes⟩
    exact ⟨6 * k + 1 + j, by omega, by omega, htypes⟩

/-- The *pointwise*, unproved hard-prime covering statement is logically
necessary and sufficient for the entire ordered Erdős–Straus assertion. -/
theorem all_good_iff_hard_divisor_cover :
    (∀ n : ℕ, 2 < n → Good n) ↔
      ∀ k : ℕ, (24 * k + 1).Prime →
        ∃ j : ℕ, j < 6 * k ∧
          (TypeI (24 * k + 1) (6 * k + 1 + j) ∨
           TypeII (24 * k + 1) (6 * k + 1 + j)) := by
  constructor
  · intro all k hp
    exact (good_iff_hard_indices k hp).mp (all _ (by
      have := hp.two_le
      omega))
  · intro cover
    apply good_of_hard_primes
    intro p hp hmod
    have heq : p = 24 * (p / 24) + 1 := by omega
    have hp' : (24 * (p / 24) + 1).Prime := by rwa [← heq]
    have hg := (good_iff_hard_indices (p / 24) hp').mpr
      (cover (p / 24) hp')
    rwa [← heq] at hg

/-- The arithmetic progression index has its promised (independent-of-`k`) modulus. -/
theorem hard_shift_eq (k j : ℕ) :
    4 * (6 * k + 1 + j) - (24 * k + 1) = 4 * j + 3 := by omega

/-- A finite (but unbounded in `k`) exact divisor-residue covering criterion
for each hard prime. No existence claim is asserted here. -/
theorem good_iff_hard_explicit (k : ℕ) (hp : (24 * k + 1).Prime) :
    Good (24 * k + 1) ↔ ∃ j : ℕ, j < 6 * k ∧
      ((∃ c : ℕ, 0 < c ∧ c ∣ (6 * k + 1 + j) ^ 2 ∧ (4 * j + 3) ∣ 4 * c + 1) ∨
       (∃ d : ℕ, 0 < d ∧ d < 6 * k + 1 + j ∧
         d ∣ (6 * k + 1 + j) ^ 2 ∧ (4 * j + 3) ∣ 6 * k + 1 + j + d)) := by
  simpa only [TypeI, TypeII, hard_shift_eq] using good_iff_hard_indices k hp

/-- Fully expanded equivalence for the universal assertion. The forward
implication is formal; proving the displayed right-hand side remains open. -/
theorem all_good_iff_explicit_hard_cover :
    (∀ n : ℕ, 2 < n → Good n) ↔
      ∀ k : ℕ, (24 * k + 1).Prime →
        ∃ j : ℕ, j < 6 * k ∧
          ((∃ c : ℕ, 0 < c ∧ c ∣ (6 * k + 1 + j) ^ 2 ∧ (4 * j + 3) ∣ 4 * c + 1) ∨
           (∃ d : ℕ, 0 < d ∧ d < 6 * k + 1 + j ∧
             d ∣ (6 * k + 1 + j) ^ 2 ∧ (4 * j + 3) ∣ 6 * k + 1 + j + d)) := by
  simpa only [TypeI, TypeII, hard_shift_eq] using all_good_iff_hard_divisor_cover

/-- A type-II divisor at `x` also gives a precise modular parameter `m`;
this is the *necessary* half of `good_of_modular_witness`. -/
theorem typeII_modular_parameter (p x d : ℕ) (hp : p.Prime)
    (hlo : p < 4 * x) (hhi : 2 * x < p)
    (hd : 0 < d) (hdx : d < x) (hdsq : d ∣ x ^ 2)
    (hadiv : 4 * x - p ∣ x + d) :
    let m := (x + d) / (4 * x - p)
    0 < m ∧ d ∣ m ^ 2 ∧ 0 < 4 * m - 1 ∧
      4 * m - 1 ∣ p + 4 * d ∧
      x = (p * m + d) / (4 * m - 1) := by
  let a := 4 * x - p
  let m := (x + d) / a
  have ha : 0 < a := by dsimp [a]; omega
  have haeq : a + p = 4 * x := by dsimp [a]; omega
  have hm : a * m = x + d := Nat.mul_div_cancel' hadiv
  have hmp : 0 < m := by
    by_contra h
    have : m = 0 := Nat.eq_zero_of_not_pos h
    rw [this] at hm
    simp at hm
    omega
  have hh : (4 * m - 1) + 1 = 4 * m := by omega
  have hhpos : 0 < 4 * m - 1 := by omega
  have hrel : (4 * m - 1) * a = p + 4 * d := by
    nlinarith only [hm, haeq, congrArg (fun t : ℕ => t * a) hh]
  have hxrel : (4 * m - 1) * x = p * m + d := by
    nlinarith only [hm, congrArg (fun t : ℕ => t * m) haeq,
      congrArg (fun t : ℕ => t * x) hh]
  have hx : 0 < x := lt_trans hd hdx
  have hxltp : x < p := by omega
  have hax : a.Coprime x := by
    apply Nat.coprime_of_dvd
    intro q hq hqa hqx
    have hqp : q ∣ p := by
      have hq4x : q ∣ 4 * x := hqx.mul_left 4
      have hqap : q ∣ a + p := by rw [haeq]; exact hq4x
      exact (Nat.dvd_add_iff_left hqa).mpr (by simpa only [add_comm] using hqap)
    have heq : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
    exact (Nat.not_dvd_of_pos_of_lt hx hxltp) (heq ▸ hqx)
  have had : a.Coprime d := by
    apply Nat.coprime_of_dvd
    intro q hq hqa hqd
    have hqxd : q ∣ x + d := dvd_trans hqa hadiv
    have hqx : q ∣ x := (Nat.dvd_add_iff_left hqd).mpr hqxd
    have hqc : q.Coprime x := hax.of_dvd_left hqa
    exact (ne_of_gt hq.one_lt) (hqc.eq_one_of_dvd hqx)
  have hdadd : d ∣ (x + d) ^ 2 := by
    rw [show (x + d) ^ 2 = x ^ 2 + d * (2 * x + d) by ring]
    exact dvd_add hdsq (dvd_mul_right d _)
  have hdam : d ∣ a ^ 2 * m ^ 2 := by
    have hd' : d ∣ (a * m) ^ 2 := by rw [hm]; exact hdadd
    simpa only [mul_pow] using hd'
  have hdmsq : d ∣ m ^ 2 := (had.symm.pow_right 2).dvd_of_dvd_mul_left hdam
  refine ⟨hmp, hdmsq, hhpos, ?_, ?_⟩
  · rw [← hrel]
    exact dvd_mul_right _ _
  · rw [← hxrel]
    exact (Nat.mul_div_cancel_left x hhpos).symm

/-- An infinite, *pointwise* obstruction to any fixed cutoff on the genuine
type-II parameter `m=(x+d)/(4x-p)`. This says nothing about type I or large `m`. -/
theorem hard_primes_escape_bounded_typeII (B N : ℕ) :
    ∃ p : ℕ, N < p ∧ p.Prime ∧ p % 840 = 1 ∧
      ∀ x d : ℕ, p < 4 * x → 2 * x < p →
        0 < d → d < x → d ∣ x ^ 2 → (4 * x - p) ∣ x + d →
        B < (x + d) / (4 * x - p) := by
  obtain ⟨p, hN, hp, h840, hno⟩ :=
    hard_primes_escape_bounded_modular_parameters B N
  refine ⟨p, hN, hp, h840, ?_⟩
  intro x d hlo hhi hd hdx hdsq hadiv
  obtain ⟨hm, hdm, hhpos, hdiv, hx⟩ :=
    typeII_modular_parameter p x d hp hlo hhi hd hdx hdsq hadiv
  by_contra h
  have hle : (x + d) / (4 * x - p) ≤ B := by omega
  exact hno ((x + d) / (4 * x - p)) d hm hle hd hdm hdiv

/-- Each of the three stress-test primes has a witness in the full type-II
criterion even though a restricted `d∣m` subfamily need not work. -/
theorem test_193_typeII : TypeII 193 52 := by
  refine ⟨8, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem test_2521_typeII : TypeII 2521 638 := by
  refine ⟨44, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem test_66529_typeII : TypeII 66529 17060 := by
  refine ⟨50, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem test_193_good : Good 193 :=
  good_of_typeII 193 52 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    test_193_typeII

theorem test_2521_good : Good 2521 :=
  good_of_typeII 2521 638 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    test_2521_typeII

theorem test_66529_good : Good 66529 :=
  good_of_typeII 66529 17060 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    test_66529_typeII

end Erdos242
