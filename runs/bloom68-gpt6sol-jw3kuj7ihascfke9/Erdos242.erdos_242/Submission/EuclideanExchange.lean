import Submission.Classification

/-!
# A conditional Euclidean-slack exchange for ordered Erdős–Straus solutions

If `a = 4*x-p` divides `p²-1`, complementary divisors of `x²` yield
Type-I witnesses simultaneously. This is a conditional construction only:
there is no assertion that some such `a` and divisor exist for every hard prime.
This file does not import `Spec.lean`.
-/

namespace Erdos242

/-- Euclidean-slack form of a Type-I certificate. If `r = x²/c` and
`a=4*x-p` divides `4*c+1`, then `a` also divides `p²+4*r`.
This does not, by itself, produce a divisor for a given prime. -/
theorem typeI_slack_divides_square_shift (p x c r : ℕ)
    (hlo : p < 4 * x) (hcr : c * r = x ^ 2)
    (hc : 4 * x - p ∣ 4 * c + 1) :
    4 * x - p ∣ p ^ 2 + 4 * r := by
  let a := 4 * x - p
  have haeq : a + p = 4 * x := by dsimp [a]; omega
  have hid : 4 * r * (4 * c + 1) = a * (a + 2 * p) + (p ^ 2 + 4 * r) := by
    calc
      4 * r * (4 * c + 1) = 16 * (c * r) + 4 * r := by ring
      _ = 16 * x ^ 2 + 4 * r := by rw [hcr]
      _ = (a + p) ^ 2 + 4 * r := by rw [haeq]; ring
      _ = a * (a + 2 * p) + (p ^ 2 + 4 * r) := by ring
  have hmul : a ∣ 4 * r * (4 * c + 1) := hc.mul_left (4 * r)
  rw [hid] at hmul
  exact (Nat.dvd_add_iff_right (dvd_mul_right a (a + 2 * p))).mpr hmul

/-- For an odd prime `p≡1 (mod 4)` in the ordered first-denominator
window, the slack-shift condition is **equivalent** to the full Type-I
target: writing `c*r=x²`, one has
`(4*x-p)∣4*c+1 ↔ (4*x-p)∣p²+4*r`. Primality is used to
cancel the cofactor `4*r`, which is coprime to `4*x-p`.
Neither divisibility is asserted to hold for a prescribed prime. -/
theorem typeI_slack_iff_square_shift (p x c r : ℕ)
    (hp : p.Prime) (hp4 : p % 4 = 1)
    (hlo : p < 4 * x) (hhi : 2 * x < p)
    (hcr : c * r = x ^ 2) :
    (4 * x - p ∣ 4 * c + 1) ↔ (4 * x - p ∣ p ^ 2 + 4 * r) := by
  constructor
  · exact typeI_slack_divides_square_shift p x c r hlo hcr
  · intro hshift
    let a := 4 * x - p
    have haeq : a + p = 4 * x := by dsimp [a]; omega
    have hx : 0 < x := by omega
    have hxlt : x < p := by omega
    have hnotpx : ¬p ∣ x := Nat.not_dvd_of_pos_of_lt hx hxlt
    have hax : a.Coprime x := by
      apply Nat.coprime_of_dvd
      intro q hq hqa hqx
      have hq4x : q ∣ 4 * x := hqx.mul_left 4
      have hqp : q ∣ p := by
        have hadd : q ∣ a + p := by rw [haeq]; exact hq4x
        exact (Nat.dvd_add_iff_right hqa).mpr hadd
      have hqeq : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
      exact hnotpx (hqeq ▸ hqx)
    have hrdiv : r ∣ x ^ 2 := by rw [← hcr]; exact dvd_mul_left r c
    have har : a.Coprime r :=
      (hax.pow_right 2).of_dvd_right hrdiv
    have haodd : Odd a := Nat.odd_iff.mpr (by dsimp [a]; omega)
    have ha4 : a.Coprime 4 := by
      have ha2 : a.Coprime 2 := Nat.coprime_two_right.mpr haodd
      simpa only [show (4 : ℕ) = 2 ^ 2 by norm_num] using ha2.pow_right 2
    have hcop : a.Coprime (4 * r) := ha4.mul_right har
    have hid : 4 * r * (4 * c + 1) = a * (a + 2 * p) + (p ^ 2 + 4 * r) := by
      calc
        4 * r * (4 * c + 1) = 16 * (c * r) + 4 * r := by ring
        _ = 16 * x ^ 2 + 4 * r := by rw [hcr]
        _ = (a + p) ^ 2 + 4 * r := by rw [haeq]; ring
        _ = a * (a + 2 * p) + (p ^ 2 + 4 * r) := by ring
    have hdiv : a ∣ 4 * r * (4 * c + 1) := by
      rw [hid]
      exact dvd_add (dvd_mul_right a _) hshift
    exact hcop.dvd_of_dvd_mul_left hdiv

/-- Construct a strictly ordered decomposition from a divisor of `x²`
in the shifted-square residue class `p²+4*r ≡ 0 (mod 4*x-p)`.
This is an exact alternative presentation of Type I, not a pointwise
existence theorem for arbitrary primes. -/
theorem good_of_typeI_square_shift (p x r : ℕ)
    (hp : p.Prime) (hp4 : p % 4 = 1)
    (hlo : p < 4 * x) (hhi : 2 * x < p)
    (hrdiv : r ∣ x ^ 2) (hshift : 4 * x - p ∣ p ^ 2 + 4 * r) : Good p := by
  let c := x ^ 2 / r
  have hrc : r * c = x ^ 2 := Nat.mul_div_cancel' hrdiv
  have hcr : c * r = x ^ 2 := by simpa only [mul_comm] using hrc
  have hcpos : 0 < c := by
    by_contra hn
    have hc0 : c = 0 := Nat.eq_zero_of_not_pos hn
    have hx : 0 < x := by omega
    have hsq : 0 < x ^ 2 := pow_pos hx 2
    rw [hc0] at hcr
    simp at hcr
    omega
  have hcdvd : c ∣ x ^ 2 := by rw [← hcr]; exact dvd_mul_right c r
  have htarget : 4 * x - p ∣ 4 * c + 1 :=
    (typeI_slack_iff_square_shift p x c r hp hp4 hlo hhi hcr).mpr hshift
  have hI : TypeI p x := ⟨c, hcpos, hcdvd, htarget⟩
  exact good_of_typeI p x (by have := hp.two_le; omega) hlo hhi hI




/-- For a Type-I square-divisor certificate `c*r=x²`, the complementary
factor `r` also hits the Type-I target precisely when `a=4*x-p` divides
`p²-1`. No primality assumption is needed for this arithmetic equivalence. -/
theorem typeI_complement_iff_square_one (p x c r : ℕ)
    (hp : 0 < p) (hlo : p < 4 * x) (hcr : c * r = x ^ 2)
    (hc : 4 * x - p ∣ 4 * c + 1) :
    (4 * x - p ∣ 4 * r + 1) ↔ (4 * x - p ∣ p ^ 2 - 1) := by
  let a := 4 * x - p
  have hpsqpos : 1 ≤ p ^ 2 := by nlinarith
  have hnum : (p ^ 2 - 1) + (4 * r + 1) = p ^ 2 + 4 * r := by omega
  have hsum : a ∣ (p ^ 2 - 1) + (4 * r + 1) := by
    rw [hnum]
    exact typeI_slack_divides_square_shift p x c r hlo hcr hc
  change (a ∣ 4 * r + 1) ↔ (a ∣ p ^ 2 - 1)
  constructor
  · intro hr
    have heq : (a ∣ p ^ 2 - 1) ↔ (a ∣ (p ^ 2 - 1) + (4 * r + 1)) :=
      Nat.dvd_add_iff_left hr
    exact heq.mpr hsum
  · intro hs
    have heq : (a ∣ 4 * r + 1) ↔ (a ∣ (p ^ 2 - 1) + (4 * r + 1)) :=
      Nat.dvd_add_iff_right hs
    exact heq.mpr hsum

/-- A Type-I witness at a root-of-one modulus gives a second Type-I
certificate, from the complementary divisor of the *whole square* `x²`.
The new certificate need not satisfy the restricted condition `r∣x`. -/
theorem typeI_square_one_exchange (p x c : ℕ)
    (hp : 0 < p) (hlo : p < 4 * x)
    (hcdvd : c ∣ x ^ 2) (htarget : 4 * x - p ∣ 4 * c + 1)
    (hroot : 4 * x - p ∣ p ^ 2 - 1) :
    ∃ r : ℕ, 0 < r ∧ c * r = x ^ 2 ∧ TypeI p x := by
  let r := x ^ 2 / c
  have hcr : c * r = x ^ 2 := Nat.mul_div_cancel' hcdvd
  have hx : 0 < x := by omega
  have hrpos : 0 < r := by
    by_contra hnot
    have hzero : r = 0 := Nat.eq_zero_of_not_pos hnot
    have hsq : 0 < x ^ 2 := pow_pos hx 2
    rw [hzero] at hcr
    simp at hcr
    omega
  have hrdiv : r ∣ x ^ 2 := by
    rw [← hcr]
    exact dvd_mul_left r c
  have hrtarget : 4 * x - p ∣ 4 * r + 1 :=
    (typeI_complement_iff_square_one p x c r hp hlo hcr htarget).mpr hroot
  exact ⟨r, hrpos, hcr, ⟨r, hrpos, hrdiv, hrtarget⟩⟩

/-- A concrete infinite *integer* progression with both complementary
Type-I certificates. Dirichlet supplies infinitely many **prime** members,
but the lemma does not assert that every hard prime belongs to this class.
The exceptional root `34 mod 55` is neither `+1` nor `-1 mod 55`. -/
theorem root55_progression_two_certificates (t : ℕ) :
    let p := 54120 * t + 12409
    let x := 13530 * t + 3116
    ∃ c r : ℕ, c = 41 ∧ r = 41 * (330 * t + 76) ^ 2 ∧ c < r ∧
      c * r = x ^ 2 ∧ (4 * x - p ∣ 4 * c + 1) ∧
      (4 * x - p ∣ 4 * r + 1) ∧ Good p := by
  let p := 54120 * t + 12409
  let x := 13530 * t + 3116
  let q := 330 * t + 76
  change ∃ c r : ℕ, c = 41 ∧ r = 41 * q ^ 2 ∧ c < r ∧
    c * r = x ^ 2 ∧ (4 * x - p ∣ 4 * c + 1) ∧
    (4 * x - p ∣ 4 * r + 1) ∧ Good p
  have hp : 0 < p := by dsimp [p]; omega
  have hlo : p < 4 * x := by dsimp [p, x]; omega
  have hhi : 2 * x < p := by dsimp [p, x]; omega
  have ha : 4 * x - p = 55 := by dsimp [p, x]; omega
  have hcr : 41 * (41 * q ^ 2) = x ^ 2 := by dsimp [x, q]; ring
  have hcert : 4 * x - p ∣ 4 * 41 + 1 := by rw [ha]; norm_num
  have hroot : 4 * x - p ∣ p ^ 2 - 1 := by
    rw [ha]
    let u := 984 * t + 225
    refine ⟨55 * u ^ 2 + 68 * u + 21, ?_⟩
    have heq : p ^ 2 = 55 * (55 * u ^ 2 + 68 * u + 21) + 1 := by
      dsimp [p, u]
      ring
    omega
  have hdual : 4 * x - p ∣ 4 * (41 * q ^ 2) + 1 :=
    (typeI_complement_iff_square_one p x 41 (41 * q ^ 2)
      hp hlo hcr hcert).mpr hroot
  have hc : TypeI p x := by
    refine ⟨41, by norm_num, ?_, hcert⟩
    rw [← hcr]
    exact dvd_mul_right 41 (41 * q ^ 2)
  have hq : 1 < q := by dsimp [q]; omega
  refine ⟨41, 41 * q ^ 2, rfl, rfl, ?_, hcr, hcert, hdual,
    good_of_typeI p x hp hlo hhi hc⟩
  nlinarith

/-- The complementary-factor construction occurs for arbitrarily large
hard **primes** in one explicit progression. This is a selected progression,
not a covering argument for an arbitrary hard prime. -/
theorem infinitely_many_root55_exchange_primes (N : ℕ) :
    ∃ p k x c r : ℕ, N < p ∧ p.Prime ∧ p = 24 * k + 1 ∧
      p % 55 = 34 ∧ c = 41 ∧ c < r ∧ c * r = x ^ 2 ∧
      4 * x - p = 55 ∧ (4 * x - p ∣ 4 * c + 1) ∧
      (4 * x - p ∣ 4 * r + 1) ∧ Good p := by
  obtain ⟨p, hpN, hpprime, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq N (q := 54120) (a := 12409)
      (by decide) (by decide)
  have hrem : p % 54120 = 12409 := by simpa [Nat.ModEq] using hmod
  let t := p / 54120
  have hpform : p = 54120 * t + 12409 := by dsimp [t]; omega
  obtain ⟨c, r, hceq, _, hlt, hcr, hdc, hdr, hgood⟩ :=
    root55_progression_two_certificates t
  have hhard : p = 24 * (2255 * t + 517) + 1 := by
    rw [hpform]
    ring
  have hp55 : p % 55 = 34 := by
    rw [hpform]
    have heq : 54120 * t + 12409 = 55 * (984 * t + 225) + 34 := by ring
    rw [heq]
    simp
  have ha : 4 * (13530 * t + 3116) - p = 55 := by rw [hpform]; omega
  refine ⟨p, 2255 * t + 517, 13530 * t + 3116, c, r,
    hpN, hpprime, hhard, hp55, hceq, hlt, hcr, ha, ?_, ?_, ?_⟩
  · rw [hpform]
    exact hdc
  · rw [hpform]
    exact hdr
  · rw [hpform]
    exact hgood


/-- An explicit hard-prime example where `p≡34 (mod 55)`, rather than
`±1 (mod 55)`. Both complementary cofactors give distinct ordered
Egyptian-fraction expansions of the *same* `4/p`. -/
theorem test_66529_nontrivial_root :
    (66529).Prime ∧ 66529 % 55 = 34 ∧
      41 * 6758276 = 16646 ^ 2 ∧
      (55 ∣ 4 * 41 + 1) ∧ (55 ∣ 4 * 6758276 + 1) ∧
      (¬55 ∣ 66529 - 1) ∧ (¬55 ∣ 66529 + 1) ∧
      (4 / 66529 : ℚ) = 1 / 16646 + 1 / 20258182 + 1 / 3319597513 ∧
      (4 / 66529 : ℚ) = 1 / 16646 + 1 / 20135305 + 1 / 543870172776070 := by
  norm_num

/-- The extra **root-of-one Type-I strategy** really is stronger than the
original problem: the *soluble* hard prime `193` has no full Type-I witness
whose associated modulus divides `193²-1`. This rules out this strategy
at `193`, not an Erdős–Straus solution at a different modulus/type. -/
theorem no_root_one_typeI_193 :
    ¬ ∃ x : ℕ, 193 < 4 * x ∧ 2 * x < 193 ∧
      TypeI 193 x ∧ (4 * x - 193 ∣ 193 ^ 2 - 1) := by
  rintro ⟨x, hlo, hhi, hI, hroot⟩
  let a := 4 * x - 193
  have haodd : Odd a := Nat.odd_iff.mpr (by dsimp [a]; omega)
  have ha4 : a % 4 = 3 := by dsimp [a]; omega
  have halp : a < 193 := by dsimp [a]; omega
  have ha2 : a.Coprime 2 := Nat.coprime_two_right.mpr haodd
  have ha128 : a.Coprime 128 := by
    have heq : (128 : ℕ) = 2 ^ 7 := by norm_num
    rw [heq]
    exact ha2.pow_right 7
  have h37248 : a ∣ 37248 := by simpa [a] using hroot
  have h291 : a ∣ 291 := by
    have heq : 37248 = 128 * 291 := by norm_num
    rw [heq] at h37248
    exact ha128.dvd_of_dvd_mul_left h37248
  have hadiv : a = 1 ∨ a = 3 ∨ a = 97 ∨ a = 291 := by
    have hale : a ≤ 291 := Nat.le_of_dvd (by norm_num) h291
    have hfactors : ∀ v : Fin 292,
        v.val ∣ 291 → v.val = 1 ∨ v.val = 3 ∨ v.val = 97 ∨ v.val = 291 := by
      set_option maxRecDepth 2048 in
        decide
    exact hfactors ⟨a, by omega⟩ h291
  have ha3 : a = 3 := by rcases hadiv with h | h | h | h <;> omega
  have hx49 : x = 49 := by dsimp [a] at ha3; omega
  subst x
  obtain ⟨c, _, hcdvd, htarget⟩ := hI
  have hpow : 49 ^ 2 = 7 ^ 4 := by norm_num
  rw [hpow] at hcdvd
  obtain ⟨e, he, hceq⟩ := (Nat.dvd_prime_pow (by norm_num : (7 : ℕ).Prime)).mp hcdvd
  have hemod : 7 ^ e % 3 = 1 := by interval_cases e <;> norm_num at he ⊢
  have h3 : 3 ∣ 4 * 7 ^ e + 1 := by simpa [hceq] using htarget
  have hrem := Nat.mod_eq_zero_of_dvd h3
  omega


/-- Exact slack-congruence and strictly ordered rational checks for the
three requested hard primes. These are *individual* prime witnesses, not
a proof that a matching slack exists for every prime. -/
theorem test_193_square_shift :
    (193).Prime ∧ 10 ∣ 50 ^ 2 ∧
      (4 * 50 - 193 ∣ 193 ^ 2 + 4 * 10) ∧
      50 < 1380 ∧ 1380 < 1331700 ∧
      (4 / 193 : ℚ) = 1 / 50 + 1 / 1380 + 1 / 1331700 := by
  norm_num

theorem test_2521_square_shift :
    (2521).Prime ∧ 3509 ∣ 638 ^ 2 ∧
      (4 * 638 - 2521 ∣ 2521 ^ 2 + 4 * 3509) ∧
      638 < 51997 ∧ 51997 < 23833534 ∧
      (4 / 2521 : ℚ) = 1 / 638 + 1 / 51997 + 1 / 23833534 := by
  norm_num

theorem test_6553_square_shift :
    (6553).Prime ∧ 5 ∣ 1640 ^ 2 ∧
      (4 * 1640 - 6553 ∣ 6553 ^ 2 + 4 * 5) ∧
      1640 < 1535275 ∧ 1535275 < 3299895520600 ∧
      (4 / 6553 : ℚ) = 1 / 1640 + 1 / 1535275 + 1 / 3299895520600 := by
  norm_num



/-- Direct, strictly ordered validations of all three specified hard primes.
The `2521` identity uses Type II, so it is *not* an instance of the
root-of-one Type-I exchange above. -/
theorem test_193_good : Good 193 := by
  refine ⟨50, 1450, 27985, by norm_num, by norm_num, by norm_num, ?_⟩
  norm_num

theorem test_2521_good : Good 2521 := by
  refine ⟨638, 55462, 804199, by norm_num, by norm_num, by norm_num, ?_⟩
  norm_num

theorem test_6553_good : Good 6553 := by
  refine ⟨1640, 1612120, 32207995, by norm_num, by norm_num, by norm_num, ?_⟩
  norm_num

/-- The complement at `p=6553, a=7` yields a distinct ordered solution
with the same first denominator but a smaller middle denominator. -/
theorem test_6553_exchanged_good :
    ∃ y z : ℕ, 1640 < y ∧ y < z ∧
      (4 / 6553 : ℚ) = 1 / 1640 + 1 / y + 1 / z := by
  refine ⟨1535275, 3299895520600, by norm_num, by norm_num, ?_⟩
  norm_num

end Erdos242
