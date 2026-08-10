import FormalConjectures.Util.ProblemImports

open Nat

/--
Numbers whose prime divisors all end in the same digit.
-/
def A381159_condition (n : ℕ) : Prop :=
  Finset.card (n.primeFactors.image (fun p => p % 10)) ≤ 1

/--
A381159: Numbers whose prime divisors all end in the same digit.
-/
noncomputable def A381159 (n : ℕ) : ℕ := n.nth A381159_condition

/--
Key lemma. Suppose `a, a + d, …, a + 149·d` are all "lopsided" (each has all prime
divisors ending in the same digit). If `p` and `q` are primes ending in *different*
digits with `p * q ≤ 150`, then `p ∣ d` or `q ∣ d`.

Reason: if neither divides `d`, then `d` is invertible modulo `p * q`, so there is an
index `i₀ < p * q ≤ 150` with `p * q ∣ a + i₀ · d`. That term then has the two prime
divisors `p` and `q`, which end in different digits — contradicting lopsidedness.
-/
private theorem key_conflict (a d : ℕ) (ha : 2 ≤ a)
    (hd : ∀ (i : Fin 150), A381159_condition (a + i.val * d))
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpq10 : p % 10 ≠ q % 10) (hbound : p * q ≤ 150) :
    p ∣ d ∨ q ∣ d := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hpd, hqd⟩ := hcon
  set n := p * q with hn
  haveI : NeZero n := ⟨by rw [hn]; have := hp.pos; have := hq.pos; positivity⟩
  have hcpd : Nat.Coprime p d := (hp.coprime_iff_not_dvd).2 hpd
  have hcqd : Nat.Coprime q d := (hq.coprime_iff_not_dvd).2 hqd
  have hdc : Nat.Coprime d n := by
    rw [hn]; exact (hcpd.symm).mul_right (hcqd.symm)
  have hunit : IsUnit (d : ZMod n) := (ZMod.isUnit_iff_coprime d n).2 hdc
  obtain ⟨u, hu⟩ := hunit
  set x : ZMod n := (-(a : ZMod n)) * (↑u⁻¹ : ZMod n) with hx
  have hxd : x * (d : ZMod n) = -(a : ZMod n) := by
    rw [hx, ← hu, mul_assoc, Units.inv_mul, mul_one]
  have hzero : ((a + x.val * d : ℕ) : ZMod n) = 0 := by
    push_cast
    rw [ZMod.natCast_zmod_val, hxd]
    ring
  have hdvd : n ∣ (a + x.val * d) := (ZMod.natCast_eq_zero_iff _ n).1 hzero
  have hlt : x.val < 150 := lt_of_lt_of_le (ZMod.val_lt x) hbound
  have hterm_ne : a + x.val * d ≠ 0 := by omega
  have hpdvd : p ∣ (a + x.val * d) := dvd_trans ⟨q, hn⟩ hdvd
  have hqdvd : q ∣ (a + x.val * d) := dvd_trans ⟨p, by rw [hn]; ring⟩ hdvd
  have hpmem : p ∈ (a + x.val * d).primeFactors := Nat.mem_primeFactors.2 ⟨hp, hpdvd, hterm_ne⟩
  have hqmem : q ∈ (a + x.val * d).primeFactors := Nat.mem_primeFactors.2 ⟨hq, hqdvd, hterm_ne⟩
  have hcond : Finset.card ((a + x.val * d).primeFactors.image (fun r => r % 10)) ≤ 1 :=
    hd ⟨x.val, hlt⟩
  have hp10 : p % 10 ∈ (a + x.val * d).primeFactors.image (fun r => r % 10) :=
    Finset.mem_image.2 ⟨p, hpmem, rfl⟩
  have hq10 : q % 10 ∈ (a + x.val * d).primeFactors.image (fun r => r % 10) :=
    Finset.mem_image.2 ⟨q, hqmem, rfl⟩
  have hgt : 1 < Finset.card ((a + x.val * d).primeFactors.image (fun r => r % 10)) :=
    Finset.one_lt_card.2 ⟨p % 10, hp10, q % 10, hq10, hpq10⟩
  omega

/--
A381159 51st All-Russian Mathematical Olympiad for Schoolchildren. Problem.
Let us call a natural number "lopsided" if it is greater than 1 and all its prime divisors end with the same digit.
Is there an increasing arithmetic progression with a difference not exceeding 2025,
consisting of 150 natural numbers, each of which is "lopsided"? (A. Chironov)

It turns out the answer is **no**, so we *disprove* the (positive) conjecture.

Sketch. By the key lemma, for every pair of primes `p, q` with different last digits and
`p * q ≤ 150`, the common difference `d` is divisible by `p` or by `q`. The primes
`2, 3, 5, 7, 11` are pairwise of different last digits with pairwise products `≤ 150`, so
they form a clique of the "conflict graph"; hence at most one of them can fail to divide
`d`. A short case analysis (using extra edges such as `11 · 13 = 143 ≤ 150`,
`3 · 17 = 51 ≤ 150`, …) shows that `d` is in every case divisible by a product of distinct
primes exceeding `2025`, contradicting `d ≤ 2025`.
-/
theorem oeis_381159_conjecture_0.disproof :
    ¬ ∃ (a d : ℕ),
      2 ≤ a ∧
      1 ≤ d ∧
      d ≤ 2025 ∧
      ∀ (i : Fin 150), A381159_condition (a + i.val * d) := by
  rintro ⟨a, d, ha, hd1, hd2025, hd⟩
  have hdpos : 0 < d := by omega
  by_cases h2 : 2 ∣ d
  · by_cases h3 : 3 ∣ d
    · by_cases h5 : 5 ∣ d
      · by_cases h7 : 7 ∣ d
        · by_cases h11 : 11 ∣ d
          · -- {2,3,5,7,11} -> 2310
            have h6 : (6 : ℕ) ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
            have h30 : (30 : ℕ) ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h6 h5
            have h210 : (210 : ℕ) ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h30 h7
            have h2310 : (2310 : ℕ) ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h210 h11
            exact absurd (le_trans (Nat.le_of_dvd hdpos h2310) hd2025) (by norm_num)
          · -- {2,3,5,7,13} -> 2730
            have h13 : 13 ∣ d :=
              (key_conflict a d ha hd 11 13 (by norm_num) (by norm_num) (by decide) (by norm_num)).resolve_left h11
            have h6 : (6 : ℕ) ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
            have h30 : (30 : ℕ) ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h6 h5
            have h210 : (210 : ℕ) ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h30 h7
            have h2730 : (2730 : ℕ) ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h210 h13
            exact absurd (le_trans (Nat.le_of_dvd hdpos h2730) hd2025) (by norm_num)
        · -- 7 ∤ d : {2,3,5,11,13} -> 4290
          have h11 : 11 ∣ d :=
            (key_conflict a d ha hd 7 11 (by norm_num) (by norm_num) (by decide) (by norm_num)).resolve_left h7
          have h13 : 13 ∣ d :=
            (key_conflict a d ha hd 7 13 (by norm_num) (by norm_num) (by decide) (by norm_num)).resolve_left h7
          have h6 : (6 : ℕ) ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
          have h30 : (30 : ℕ) ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h6 h5
          have h330 : (330 : ℕ) ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h30 h11
          have h4290 : (4290 : ℕ) ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h330 h13
          exact absurd (le_trans (Nat.le_of_dvd hdpos h4290) hd2025) (by norm_num)
      · -- 5 ∤ d : {2,3,7,11,13} -> 6006
        have h7 : 7 ∣ d :=
          (key_conflict a d ha hd 5 7 (by norm_num) (by norm_num) (by decide) (by norm_num)).resolve_left h5
        have h11 : 11 ∣ d :=
          (key_conflict a d ha hd 5 11 (by norm_num) (by norm_num) (by decide) (by norm_num)).resolve_left h5
        have h13 : 13 ∣ d :=
          (key_conflict a d ha hd 5 13 (by norm_num) (by norm_num) (by decide) (by norm_num)).resolve_left h5
        have h6 : (6 : ℕ) ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
        have h42 : (42 : ℕ) ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h6 h7
        have h462 : (462 : ℕ) ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h42 h11
        have h6006 : (6006 : ℕ) ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h462 h13
        exact absurd (le_trans (Nat.le_of_dvd hdpos h6006) hd2025) (by norm_num)
    · -- 3 ∤ d : {2,5,7,11,17} -> 13090
      have h5 : 5 ∣ d :=
        (key_conflict a d ha hd 3 5 (by norm_num) (by norm_num) (by decide) (by norm_num)).resolve_left h3
      have h7 : 7 ∣ d :=
        (key_conflict a d ha hd 3 7 (by norm_num) (by norm_num) (by decide) (by norm_num)).resolve_left h3
      have h11 : 11 ∣ d :=
        (key_conflict a d ha hd 3 11 (by norm_num) (by norm_num) (by decide) (by norm_num)).resolve_left h3
      have h17 : 17 ∣ d :=
        (key_conflict a d ha hd 3 17 (by norm_num) (by norm_num) (by decide) (by norm_num)).resolve_left h3
      have h10 : (10 : ℕ) ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h5
      have h70 : (70 : ℕ) ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h10 h7
      have h770 : (770 : ℕ) ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h70 h11
      have h13090 : (13090 : ℕ) ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h770 h17
      exact absurd (le_trans (Nat.le_of_dvd hdpos h13090) hd2025) (by norm_num)
  · -- 2 ∤ d : {3,5,7,11,13} -> 15015
    have h3 : 3 ∣ d :=
      (key_conflict a d ha hd 2 3 (by norm_num) (by norm_num) (by decide) (by norm_num)).resolve_left h2
    have h5 : 5 ∣ d :=
      (key_conflict a d ha hd 2 5 (by norm_num) (by norm_num) (by decide) (by norm_num)).resolve_left h2
    have h7 : 7 ∣ d :=
      (key_conflict a d ha hd 2 7 (by norm_num) (by norm_num) (by decide) (by norm_num)).resolve_left h2
    have h11 : 11 ∣ d :=
      (key_conflict a d ha hd 2 11 (by norm_num) (by norm_num) (by decide) (by norm_num)).resolve_left h2
    have h13 : 13 ∣ d :=
      (key_conflict a d ha hd 2 13 (by norm_num) (by norm_num) (by decide) (by norm_num)).resolve_left h2
    have h15 : (15 : ℕ) ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h3 h5
    have h105 : (105 : ℕ) ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h15 h7
    have h1155 : (1155 : ℕ) ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h105 h11
    have h15015 : (15015 : ℕ) ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1155 h13
    exact absurd (le_trans (Nat.le_of_dvd hdpos h15015) hd2025) (by norm_num)
