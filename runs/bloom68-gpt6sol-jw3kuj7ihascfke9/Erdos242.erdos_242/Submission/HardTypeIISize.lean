import Submission.CoveringGap

/-!
# A strict first-denominator bound for hard-prime type-II solutions

This is an exact, conditional sharpening of `good_iff_hard_indices`. It does not
prove that any hard prime has a solution. A *pointwise* bound `x < p/3`
for Type I is false: `p = 97`, `x = 34` is a Type I witness. This example
does not rule out a different witness closer to `p/4` for the same prime.
-/

namespace Erdos242

/-- At a hard prime, a type-II solution has `x < p/3`, not merely `x < p/2`.
The modular parameter `m=(x+d)/(4x-p)` cannot be 1: this would force
`3 ∣ p+4`, contrary to `p≡1 (mod 3)`. Then the identity
`(4m-1)x=pm+d` and `d<x` give `(4m-2)x<pm`, while `m≥2` gives
`3m≤4m-2`. -/
theorem hard_typeII_below_third (k x : ℕ)
    (hp : (24 * k + 1).Prime)
    (hlo : 24 * k + 1 < 4 * x)
    (hhi : 2 * x < 24 * k + 1)
    (hII : TypeII (24 * k + 1) x) :
    3 * x < 24 * k + 1 := by
  obtain ⟨d, hd, hdx, hdsq, hadiv⟩ := hII
  let p := 24 * k + 1
  let a := 4 * x - p
  let m := (x + d) / a
  have hpart := typeII_modular_parameter p x d hp hlo hhi hd hdx hdsq hadiv
  change 0 < m ∧ d ∣ m ^ 2 ∧ 0 < 4 * m - 1 ∧
    4 * m - 1 ∣ p + 4 * d ∧ x = (p * m + d) / (4 * m - 1) at hpart
  obtain ⟨hmpos, hdm, _, hmod, _⟩ := hpart
  have hmge : 2 ≤ m := by
    by_contra hn
    have hmone : m = 1 := by omega
    have hdvdone : d ∣ 1 := by simpa [hmone] using hdm
    have hdone : d = 1 := Nat.dvd_one.mp hdvdone
    have hthree : 3 ∣ p + 4 := by simpa [hmone, hdone] using hmod
    have hbad := Nat.mod_eq_zero_of_dvd hthree
    dsimp [p] at hbad
    omega
  have ham : a * m = x + d := Nat.mul_div_cancel' hadiv
  have haeq : a + p = 4 * x := by dsimp [a]; omega
  have hh : (4 * m - 1) + 1 = 4 * m := by omega
  have hxm : (4 * m - 1) * x = p * m + d := by
    nlinarith only [ham, congrArg (fun t : ℕ => t * m) haeq,
      congrArg (fun t : ℕ => t * x) hh]
  have hcoef : (4 * m - 1) = (4 * m - 2) + 1 := by omega
  have hmx : (4 * m - 2) * x < p * m := by
    nlinarith only [hxm, hdx, congrArg (fun t : ℕ => t * x) hcoef]
  have hle : 3 * m * x ≤ (4 * m - 2) * x :=
    Nat.mul_le_mul_right x (by omega : 3 * m ≤ 4 * m - 2)
  apply (Nat.mul_lt_mul_right hmpos).mp
  calc
    (3 * x) * m = 3 * m * x := by ring
    _ ≤ (4 * m - 2) * x := hle
    _ < p * m := hmx

/-- A stronger, sharp size bound: every hard-prime Type II witness has
`7*x ≤ 2*p+4`. For `m=2` this follows from `d ∣ 4`, for `m=3` from
`d ∣ 9` and `p≥19`, and for `m≥4` it follows from `d<x`.
Equality can actually occur; see `typeII_313_sharp` below. -/
theorem hard_typeII_sharp_bound (k x : ℕ)
    (hp : (24 * k + 1).Prime)
    (hlo : 24 * k + 1 < 4 * x)
    (hhi : 2 * x < 24 * k + 1)
    (hII : TypeII (24 * k + 1) x) :
    7 * x ≤ 2 * (24 * k + 1) + 4 := by
  obtain ⟨d, hd, hdx, hdsq, hadiv⟩ := hII
  let p := 24 * k + 1
  let a := 4 * x - p
  let m := (x + d) / a
  change 7 * x ≤ 2 * p + 4
  have hpart := typeII_modular_parameter p x d hp hlo hhi hd hdx hdsq hadiv
  change 0 < m ∧ d ∣ m ^ 2 ∧ 0 < 4 * m - 1 ∧
    4 * m - 1 ∣ p + 4 * d ∧ x = (p * m + d) / (4 * m - 1) at hpart
  obtain ⟨hmpos, hdm, _, _, _⟩ := hpart
  have ham : a * m = x + d := Nat.mul_div_cancel' hadiv
  have haeq : a + p = 4 * x := by dsimp [a]; omega
  have hh : (4 * m - 1) + 1 = 4 * m := by omega
  have hxm : (4 * m - 1) * x = p * m + d := by
    nlinarith only [ham, congrArg (fun t : ℕ => t * m) haeq,
      congrArg (fun t : ℕ => t * x) hh]
  have hthird := hard_typeII_below_third k x hp hlo hhi
    ⟨d, hd, hdx, hdsq, hadiv⟩
  have hmge : 2 ≤ m := by
    by_contra hn
    have hmone : m = 1 := by omega
    have hbad : 3 * x = p + d := by simpa [hmone] using hxm
    dsimp [p] at hbad hthird
    omega
  by_cases hm2 : m = 2
  · have hdvd : d ∣ 4 := by simpa [hm2] using hdm
    have hdle : d ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    have heq : 7 * x = 2 * p + d := by simpa [hm2, mul_comm] using hxm
    omega
  by_cases hm3 : m = 3
  · have hdvd : d ∣ 9 := by simpa [hm3] using hdm
    have hdle : d ≤ 9 := Nat.le_of_dvd (by norm_num) hdvd
    have heq : 11 * x = 3 * p + d := by simpa [hm3, mul_comm] using hxm
    have hp19 : 19 ≤ p := by
      have hp2 := hp.two_le
      dsimp [p]
      omega
    omega
  have hm4 : 4 ≤ m := by omega
  have hcoef : (4 * m - 1) = (4 * m - 2) + 1 := by omega
  have hmx : (4 * m - 2) * x < p * m := by
    nlinarith only [hxm, hdx, congrArg (fun t : ℕ => t * x) hcoef]
  have hbound : 7 * m ≤ 2 * (4 * m - 2) := by omega
  have hmul : (7 * x) * m < (2 * p) * m := by
    calc
      (7 * x) * m = (7 * m) * x := by ring
      _ ≤ (2 * (4 * m - 2)) * x := Nat.mul_le_mul_right x hbound
      _ = 2 * ((4 * m - 2) * x) := by ring
      _ < 2 * (p * m) := Nat.mul_lt_mul_of_pos_left hmx (by norm_num)
      _ = (2 * p) * m := by ring
  have hstrict : 7 * x < 2 * p := (Nat.mul_lt_mul_right hmpos).mp hmul
  omega

/-- In the hard-prime candidate list, Type II can only occur for `7*j < 6*k`.
The former bound `j<2*k` is valid but much weaker. -/
theorem hard_typeII_index_sharp (k j : ℕ) (hp : (24 * k + 1).Prime)
    (hj : j < 6 * k)
    (hII : TypeII (24 * k + 1) (6 * k + 1 + j)) :
    7 * j < 6 * k := by
  have hbound := hard_typeII_sharp_bound k (6 * k + 1 + j) hp
    (by omega) (by omega) hII
  omega

/-- Sharpened exact cover: the Type II search needs at most
`⌈6k/7⌉` indices, while Type I retains all `6k` possible indices.
Neither existential alternative is supplied for an arbitrary prime here. -/
theorem good_iff_hard_sharp_typeII (k : ℕ) (hp : (24 * k + 1).Prime) :
    Good (24 * k + 1) ↔
      (∃ j : ℕ, j < 6 * k ∧ TypeI (24 * k + 1) (6 * k + 1 + j)) ∨
      (∃ j : ℕ, 7 * j < 6 * k ∧ TypeII (24 * k + 1) (6 * k + 1 + j)) := by
  rw [good_iff_hard_indices k hp]
  constructor
  · rintro ⟨j, hj, hI | hII⟩
    · exact Or.inl ⟨j, hj, hI⟩
    · exact Or.inr ⟨j, hard_typeII_index_sharp k j hp hj hII, hII⟩
  · rintro (⟨j, hj, hI⟩ | ⟨j, hj, hII⟩)
    · exact ⟨j, hj, Or.inl hI⟩
    · exact ⟨j, by omega, Or.inr hII⟩

/-- A whole arithmetic progression of exact equality cases, without claiming
that every integer in the progression is prime. For prime members this is an
ordered Type II solution. -/
theorem typeII_sharp_family (t : ℕ) :
    TypeII (168 * t + 145) (48 * t + 42) := by
  refine ⟨4, by norm_num, by omega, ?_, ?_⟩
  · refine ⟨(24 * t + 21) ^ 2, ?_⟩
    ring
  · have ha : 4 * (48 * t + 42) - (168 * t + 145) = 24 * t + 23 := by omega
    rw [ha]
    refine ⟨2, ?_⟩
    omega

/-- Dirichlet supplies arbitrarily large hard primes `p ≡ 145 (mod 168)`.
For each, `x=(2p+4)/7` is a Type II witness, proving that the constant
`2/7` and additive term `4` in the preceding bound are both optimal. -/
theorem infinitely_many_sharp_typeII (N : ℕ) :
    ∃ p x : ℕ, N < p ∧ p.Prime ∧ p % 24 = 1 ∧
      TypeII p x ∧ 7 * x = 2 * p + 4 ∧ Good p := by
  obtain ⟨p, hpN, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq N (q := 168) (a := 145)
      (by decide) (by decide)
  have hrem : p % 168 = 145 := by simpa [Nat.ModEq] using hmod
  let t := p / 168
  have heq : p = 168 * t + 145 := by dsimp [t]; omega
  let x := 48 * t + 42
  have hprime : (168 * t + 145).Prime := by rw [← heq]; exact hp
  have hgood : Good (168 * t + 145) :=
    good_of_typeII (168 * t + 145) x hprime (by omega) (by omega)
      (by omega) (typeII_sharp_family t)
  refine ⟨168 * t + 145, x, ?_, hprime, ?_, typeII_sharp_family t, ?_, hgood⟩
  · omega
  · dsimp [x]; omega
  · dsimp [x]; omega

/-- Fully quantified necessary-and-sufficient shortened covering obligation
for all `n>2`. The existential right side remains unproved for arbitrary hard
primes. -/
theorem all_good_iff_hard_sharp_typeII_cover :
    (∀ n : ℕ, 2 < n → Good n) ↔
      ∀ k : ℕ, (24 * k + 1).Prime →
        (∃ j : ℕ, j < 6 * k ∧ TypeI (24 * k + 1) (6 * k + 1 + j)) ∨
        (∃ j : ℕ, 7 * j < 6 * k ∧ TypeII (24 * k + 1) (6 * k + 1 + j)) := by
  constructor
  · intro hall k hp
    have hgt : 2 < 24 * k + 1 := by
      have htwo := hp.two_le
      omega
    exact (good_iff_hard_sharp_typeII k hp).mp (hall _ hgt)
  · intro hcover
    apply good_of_hard_primes
    intro p hp hmod
    have heq : p = 24 * (p / 24) + 1 := by omega
    have hp' : (24 * (p / 24) + 1).Prime := by rwa [← heq]
    have hgood := (good_iff_hard_sharp_typeII (p / 24) hp').mpr
      (hcover (p / 24) hp')
    rwa [← heq] at hgood

/-- The exact unresolved pointwise problem with both divisor conditions fully
expanded. The Type II disjunction only ranges over `7*j < 6*k`.
This is an equivalence, **not** a proof of its right-hand side. -/
theorem all_good_iff_explicit_sharp_cover :
    (∀ n : ℕ, 2 < n → Good n) ↔
      ∀ k : ℕ, (24 * k + 1).Prime →
        (∃ j : ℕ, j < 6 * k ∧
          ∃ c : ℕ, 0 < c ∧ c ∣ (6 * k + 1 + j) ^ 2 ∧
            (4 * j + 3) ∣ 4 * c + 1) ∨
        (∃ j : ℕ, 7 * j < 6 * k ∧
          ∃ d : ℕ, 0 < d ∧ d < 6 * k + 1 + j ∧
            d ∣ (6 * k + 1 + j) ^ 2 ∧
            (4 * j + 3) ∣ 6 * k + 1 + j + d) := by
  simpa only [TypeI, TypeII, hard_shift_eq] using
    all_good_iff_hard_sharp_typeII_cover


/-- A small hard prime where the bound is an equality. -/
theorem typeII_313_sharp : TypeII 313 90 := by
  simpa using typeII_sharp_family 1

theorem good_313_sharp_explicit :
    ∃ x y z : ℕ, x = 90 ∧ y = 626 ∧ z = 14085 ∧
      1 ≤ x ∧ x < y ∧ y < z ∧
      (4 / 313 : ℚ) = 1 / x + 1 / y + 1 / z := by
  exact ⟨90, 626, 14085, rfl, rfl, rfl,
    by norm_num, by norm_num, by norm_num, by norm_num⟩





/-- The type-II alternative only needs the first `2k` possible values of `j`.
The type-I alternative is left in its full original `6k`-element range. -/
theorem good_iff_hard_short_typeII (k : ℕ) (hp : (24 * k + 1).Prime) :
    Good (24 * k + 1) ↔
      (∃ j : ℕ, j < 6 * k ∧ TypeI (24 * k + 1) (6 * k + 1 + j)) ∨
      (∃ j : ℕ, j < 2 * k ∧ TypeII (24 * k + 1) (6 * k + 1 + j)) := by
  rw [good_iff_hard_indices k hp]
  constructor
  · rintro ⟨j, hj, hI | hII⟩
    · exact Or.inl ⟨j, hj, hI⟩
    · have hthird := hard_typeII_below_third k (6 * k + 1 + j)
        hp (by omega) (by omega) hII
      exact Or.inr ⟨j, by omega, hII⟩
  · rintro (⟨j, hj, hI⟩ | ⟨j, hj, hII⟩)
    · exact ⟨j, hj, Or.inl hI⟩
    · exact ⟨j, by omega, Or.inr hII⟩

/-- The sharpened exact covering obligation for *all* `n > 2`. The right-hand
side is not established here: this theorem is a reduction, not a solution. -/
theorem all_good_iff_hard_short_typeII_cover :
    (∀ n : ℕ, 2 < n → Good n) ↔
      ∀ k : ℕ, (24 * k + 1).Prime →
        (∃ j : ℕ, j < 6 * k ∧ TypeI (24 * k + 1) (6 * k + 1 + j)) ∨
        (∃ j : ℕ, j < 2 * k ∧ TypeII (24 * k + 1) (6 * k + 1 + j)) := by
  constructor
  · intro hall k hp
    have hgt : 2 < 24 * k + 1 := by
      have htwo := hp.two_le
      omega
    exact (good_iff_hard_short_typeII k hp).mp (hall _ hgt)
  · intro hcover
    apply good_of_hard_primes
    intro p hp hmod
    have heq : p = 24 * (p / 24) + 1 := by omega
    have hp' : (24 * (p / 24) + 1).Prime := by rwa [← heq]
    have hgood := (good_iff_hard_short_typeII (p / 24) hp').mpr
      (hcover (p / 24) hp')
    rwa [← heq] at hgood


/-- Concrete Type I witness with `p/3 < x < p/2`: the pointwise Type II
bound fails if one replaces `TypeII` with `TypeI`. -/
theorem typeI_97_far : TypeI 97 34 := by
  exact ⟨68, by norm_num, by norm_num, by norm_num⟩

theorem good_97_far_typeI : Good 97 :=
  good_of_typeI 97 34 (by norm_num) (by norm_num) (by norm_num) typeI_97_far

/-- The corresponding distinct ordered denominators, checked as rational numbers. -/
theorem good_97_far_explicit :
    ∃ x y z : ℕ, x = 34 ∧ y = 85 ∧ z = 16490 ∧
      1 ≤ x ∧ x < y ∧ y < z ∧
      (4 / 97 : ℚ) = 1 / x + 1 / y + 1 / z := by
  exact ⟨34, 85, 16490, rfl, rfl, rfl,
    by norm_num, by norm_num, by norm_num, by norm_num⟩


theorem typeI_far_cannot_be_typeII : ¬ TypeII 97 34 := by
  intro h
  have hlt := hard_typeII_below_third 4 34 (by norm_num)
    (by norm_num) (by norm_num) h
  norm_num at hlt

end Erdos242
