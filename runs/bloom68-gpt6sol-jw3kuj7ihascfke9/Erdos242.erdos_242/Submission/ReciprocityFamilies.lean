import Submission.Classification

/-!
# Two further conditional prime families

All results here are unconditional implications, not a proof of the universal
Erdős–Straus conjecture. In particular this file does not import or change
`Submission/Spec.lean`.
-/

namespace Erdos242

/-- A balanced (not necessarily consecutive) pair of small denominators gives
an ordered Type I witness.  The equation `4srt=(r+t)p+1` supplies the exact
congruence rather than an approximation. -/
theorem balanced_typeI (p s r t : ℕ) (hp : 1 < p) (hs : 0 < s)
    (hr : 0 < r) (hrt : r < t)
    (hidentity : 4 * s * r * t = (r + t) * p + 1) :
    TypeI p (s * r) ∧ Good p := by
  let x := s * r
  let c := s * r ^ 2
  have ht : 0 < t := by omega
  have hlo : p < 4 * x := by
    apply (Nat.mul_lt_mul_right ht).mp
    calc
      p * t < (r + t) * p + 1 := by
        have hpr : 0 < p * r := Nat.mul_pos (by omega) hr
        nlinarith only [hpr]
      _ = 4 * s * r * t := hidentity.symm
      _ = (4 * x) * t := by dsimp [x]; ring
  have hhi : 2 * x < p := by
    have hrt : r + t + 1 ≤ 2 * t := by omega
    have hmul : (r + t + 1) * p ≤ (2 * t) * p :=
      Nat.mul_le_mul_right p hrt
    have hstrict : (r + t) * p + 1 < (2 * t) * p := by
      nlinarith only [hmul, hp]
    apply (Nat.mul_lt_mul_right (by omega : 0 < 2 * t)).mp
    calc
      (2 * x) * (2 * t) = 4 * s * r * t := by dsimp [x]; ring
      _ = (r + t) * p + 1 := hidentity
      _ < (2 * t) * p := hstrict
      _ = p * (2 * t) := by ring
  have hc : 0 < c := by dsimp [c]; positivity
  have hcdvd : c ∣ x ^ 2 := by
    refine ⟨s, ?_⟩
    dsimp [c, x]
    ring
  have haeq : (4 * x - p) + p = 4 * x := Nat.sub_add_cancel (by omega)
  have hmul : (r + t) * (4 * x) = (r + t) * p + (4 * c + 1) := by
    calc
      (r + t) * (4 * x) = 4 * c + 4 * s * r * t := by
        dsimp [c, x]; ring
      _ = 4 * c + ((r + t) * p + 1) := by rw [hidentity]
      _ = (r + t) * p + (4 * c + 1) := by omega
  have hcoef : (r + t) * (4 * x - p) = 4 * c + 1 := by
    have hsum : (r + t) * (4 * x - p) + (r + t) * p =
        (r + t) * p + (4 * c + 1) := by
      rw [← mul_add, haeq]
      exact hmul
    omega
  have hI : TypeI p x := by
    refine ⟨c, hc, hcdvd, ⟨r + t, ?_⟩⟩
    simpa only [mul_comm] using hcoef.symm
  exact ⟨hI, good_of_typeI p x (by omega) hlo hhi hI⟩

/-- An arithmetic progression in the difficult residue class `1 mod 840`,
using the genuinely nonconsecutive pair `(r,t)=(2,13)`. -/
def balancedP (u : ℕ) : ℕ := 10920 * u + 10081

def balancedS (u : ℕ) : ℕ := 1575 * u + 1454

theorem balanced_progression (u : ℕ) :
    TypeI (balancedP u) (balancedS u * 2) ∧ Good (balancedP u) := by
  have hid : 4 * balancedS u * 2 * 13 =
      (2 + 13) * balancedP u + 1 := by
    dsimp [balancedP, balancedS]
    ring
  exact balanced_typeI (balancedP u) (balancedS u) 2 13
    (by dsimp [balancedP]; omega) (by dsimp [balancedS]; omega)
    (by norm_num) (by norm_num) hid

theorem balanced_progression_hard (u : ℕ) : balancedP u % 840 = 1 := by
  have heq : balancedP u = 840 * (13 * u + 12) + 1 := by
    dsimp [balancedP]
    ring
  rw [heq]
  simp

/-- Dirichlet's theorem gives arbitrarily large hard primes in the explicit
balanced Type I progression.  This is not a covering of all hard primes. -/
theorem infinitely_many_balanced_residual_typeI (N : ℕ) :
    ∃ p x : ℕ, N < p ∧ p.Prime ∧ p % 840 = 1 ∧ TypeI p x ∧ Good p := by
  obtain ⟨p, hpN, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq N (q := 10920) (a := 10081)
      (by decide) (by decide)
  have hrem : p % 10920 = 10081 := by simpa [Nat.ModEq] using hmod
  let u := p / 10920
  have heq : p = balancedP u := by dsimp [balancedP, u]; omega
  obtain ⟨hI, hg⟩ := balanced_progression u
  refine ⟨p, balancedS u * 2, hpN, hp, ?_, ?_, ?_⟩
  · rw [heq]; exact balanced_progression_hard u
  · rw [heq]; exact hI
  · rw [heq]; exact hg

/-- For an arbitrary fixed offset `4d`, an eligible divisor of `p+4d` gives
an ordered Type II solution as soon as `p>4d`.  This removes the quotient
inequality in the general modular witness theorem. -/
theorem good_of_shifted_offset (p m d : ℕ)
    (hp : 4 * d < p) (hm : 0 < m) (hd : 0 < d)
    (hdsq : d ∣ m ^ 2) (hdiv : 4 * m - 1 ∣ p + 4 * d) : Good p := by
  let h := 4 * m - 1
  have hh : 0 < h := by dsimp [h]; omega
  have hfour : h + 1 = 4 * m := by dsimp [h]; omega
  have hdiv' : h ∣ p + 4 * d := hdiv
  have hsum : p * m + d + h * d = (p + 4 * d) * m := by
    calc
      p * m + d + h * d = p * m + (h + 1) * d := by ring
      _ = p * m + (4 * m) * d := by rw [hfour]
      _ = (p + 4 * d) * m := by ring
  have hnum : h ∣ p * m + d := by
    have hadd : h ∣ p * m + d + h * d := by
      rw [hsum]
      exact dvd_mul_of_dvd_left hdiv' m
    exact (Nat.dvd_add_iff_left (dvd_mul_right h d)).mpr hadd
  have hx : h * ((p * m + d) / h) = p * m + d := Nat.mul_div_cancel' hnum
  have hlt : h * d < p * m + d := by
    have hpm : (4 * d) * m < p * m := Nat.mul_lt_mul_of_pos_right hp hm
    have heq : h * d + d = (4 * d) * m := by
      calc
        h * d + d = (h + 1) * d := by ring
        _ = (4 * m) * d := by rw [hfour]
        _ = (4 * d) * m := by ring
    omega
  have hxd : d < (p * m + d) / h := by
    by_contra hnot
    have hle : (p * m + d) / h ≤ d := by omega
    have hmul : h * ((p * m + d) / h) ≤ h * d :=
      Nat.mul_le_mul_left h hle
    omega
  exact good_of_modular_witness p m d (by omega) hm hd hdsq
    (by simpa [h] using hh) hdiv (by simpa [h] using hxd)

/-- A concrete shifted-product/offset subfamily.  If `q ≡ -1 (mod 16)`
divides `p+32`, then `m=(q+1)/4` is a multiple of four, so `8|m²`.
Unlike the more restricted `d|m` axis, `d=8` need not divide `m`. -/
theorem good_of_shifted_32 (p q : ℕ)
    (hp : 32 < p) (hq : q % 16 = 15) (hdiv : q ∣ p + 32) : Good p := by
  let m := (q + 1) / 4
  have hm : 0 < m := by dsimp [m]; omega
  have hqeq : 4 * m - 1 = q := by dsimp [m]; omega
  have hm4 : m = 4 * (q / 16 + 1) := by dsimp [m]; omega
  have hdsq : 8 ∣ m ^ 2 := by
    refine ⟨2 * (q / 16 + 1) ^ 2, ?_⟩
    rw [hm4]
    ring
  exact good_of_shifted_offset p m 8 (by simpa using hp) hm
    (by norm_num) hdsq (by simpa [hqeq] using hdiv)

/-- A hard prime not settled by the `p+4` test, the minimal first denominator,
or the `m=2,3,4` modular residue tests.  Its *particular* modular witness
is `(m,d)=(12,8)` with `d∤m`. -/
theorem prime_261241 : Nat.Prime 261241 := by norm_num

theorem good_261241_shift32 : Good 261241 :=
  good_of_shifted_32 261241 47 (by norm_num) (by norm_num) (by norm_num)


/-- Elementary prime factorizations certifying that the old minimal-`x` and
`p+4` tests both miss this particular hard prime. -/
theorem residual_261241_factor_data :
    Nat.Prime 241 ∧ Nat.Prime 271 ∧ Nat.Prime 52249 ∧
    (261241 + 3) / 4 = 241 * 271 ∧ 261241 + 4 = 5 * 52249 := by
  norm_num

theorem typeII_261241_shift32 : TypeII 261241 66700 := by
  exact ⟨8, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem good_261241_explicit :
    (4 / 261241 : ℚ) = 1 / 66700 + 1 / 3134892 + 1 / 26137162050 := by
  norm_num

/-- The entire residue class `p ≡ 15 (mod 47)` is covered (above 32) by the
full Type II parameter `(m,d)=(12,8)`. -/
theorem good_of_mod47_fifteen (p : ℕ) (hp : 32 < p)
    (hrem : p % 47 = 15) : Good p := by
  apply good_of_shifted_offset p 12 8 (by omega) (by norm_num)
    (by norm_num) (by norm_num)
  change 47 ∣ p + 32
  exact Nat.dvd_iff_mod_eq_zero.mpr (by omega)

/-- Infinitely many hard primes in `1 (mod 840)` meet the preceding Type II
class.  Dirichlet supplies selected primes, not an all-prime covering. -/
theorem infinitely_many_mod47_residual_typeII (N : ℕ) :
    ∃ p : ℕ, N < p ∧ p.Prime ∧ p % 840 = 1 ∧ Good p := by
  obtain ⟨p, hpN, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq N (q := 39480) (a := 24361)
      (by decide) (by decide)
  have hrem : p % 39480 = 24361 := by simpa [Nat.ModEq] using hmod
  let u := p / 39480
  have heq : p = 39480 * u + 24361 := by dsimp [u]; omega
  have hp840 : p % 840 = 1 := by
    have hform : p = 840 * (47 * u + 29) + 1 := by omega
    rw [hform]
    simp
  have hp32 : 32 < p := by omega
  have hp47 : p % 47 = 15 := by
    have hform : p = 47 * (840 * u + 518) + 15 := by omega
    rw [hform]
    simp
  exact ⟨p, hpN, hp, hp840, good_of_mod47_fifteen p hp32 hp47⟩


/-- An example in the new balanced family, with a Type I witness at a
nonminimal first denominator. -/
theorem prime_130201 : Nat.Prime 130201 := by norm_num

theorem good_130201_balanced : Good 130201 := by
  simpa only [balancedP] using (balanced_progression 11).2

theorem good_130201_explicit :
    (4 / 130201 : ℚ) = 1 / 37558 + 1 / 244127 + 1 / 63571159054 := by
  norm_num

/-- Checked factorizations behind the local Type I / Type II comparison and
the failure of two earlier shifted tests at this prime. -/
theorem residual_130201_factor_data :
    Nat.Prime 43 ∧ Nat.Prime 757 ∧ Nat.Prime 26041 ∧
    Nat.Prime 89 ∧ Nat.Prime 211 ∧
    (130201 + 3) / 4 = 43 * 757 ∧ 130201 + 4 = 5 * 26041 ∧
    37558 = 2 * 89 * 211 := by
  norm_num

theorem typeI_130201_balanced : TypeI 130201 37558 := by
  exact ⟨75116, by norm_num, by norm_num, by norm_num⟩

/-- Both unused nonresidue classes modulo eleven really do exclude *every*
`m=3` modular divisor, not just the three smallest proposed divisors.  Other
parameters and Type I remain possible. -/
theorem no_m3_if_two_or_six_mod11 (p d : ℕ)
    (hp : p % 11 = 2 ∨ p % 11 = 6) (hd : 0 < d) (hdsq : d ∣ 9) :
    ¬ 11 ∣ p + 4 * d := by
  have hdle : d ≤ 9 := Nat.le_of_dvd (by decide) hdsq
  have hvals : d = 1 ∨ d = 3 ∨ d = 9 := by
    interval_cases d <;> norm_num at hdsq <;> omega
  intro hdiv
  have hrem : (p + 4 * d) % 11 = 0 := Nat.mod_eq_zero_of_dvd hdiv
  rcases hvals with rfl | rfl | rfl <;> omega

/-- An infinite CRT/Dirichlet obstruction to the claim that a nonresidue
modulo eleven alone forces the corresponding `m=3` Type II witness.  These
primes may still have many other Erdős–Straus solutions. -/
theorem infinitely_many_hard_two_mod11_without_m3 (N : ℕ) :
    ∃ p : ℕ, N < p ∧ p.Prime ∧ p % 840 = 1 ∧ p % 11 = 2 ∧
      ∀ d : ℕ, 0 < d → d ∣ 9 → ¬ 11 ∣ p + 4 * d := by
  obtain ⟨p, hpN, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq N (q := 9240) (a := 2521)
      (by decide) (by decide)
  have hrem : p % 9240 = 2521 := by simpa [Nat.ModEq] using hmod
  let u := p / 9240
  have heq : p = 9240 * u + 2521 := by dsimp [u]; omega
  have h840 : p % 840 = 1 := by
    have hform : p = 840 * (11 * u + 3) + 1 := by omega
    rw [hform]
    simp
  have h11 : p % 11 = 2 := by
    have hform : p = 11 * (840 * u + 229) + 2 := by omega
    rw [hform]
    simp
  exact ⟨p, hpN, hp, h840, h11, fun d hd hdsq =>
    no_m3_if_two_or_six_mod11 p d (Or.inl h11) hd hdsq⟩



end Erdos242
