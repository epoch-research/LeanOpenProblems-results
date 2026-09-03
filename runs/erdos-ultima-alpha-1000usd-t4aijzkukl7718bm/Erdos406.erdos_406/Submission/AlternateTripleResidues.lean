import Submission.AlternateOrbitTriple

/-! Residue saturation for the simultaneous ternary-good pattern 0,1,9.
This rules out finite prime-divisor covers of that pattern, not Erdős 406.
The constructed witnesses are explicitly not powers of two. -/

namespace Erdos406AlternateTripleResidues
open Erdos406SparseTriple Erdos406AlternateOrbitTriple

abbrev Hits (n : ℕ) : Prop := Good n ∧ Good (4 * n) ∧ Good (4 ^ 9 * n)

lemma hits_zero : Hits 0 := by simp [Hits, Good]
lemma hits_seed : Hits seed := ⟨seed_good, four_seed_good, ninth_seed_good⟩
lemma hits_otherSeed : Hits otherSeed :=
  ⟨other_seed_good, four_other_seed_good, ninth_other_seed_good⟩

lemma hits_concat {n m L : ℕ} (hn : Hits n) (hm : Hits m)
    (hsmall : 4 ^ 9 * m < 3 ^ L) : Hits (3 ^ L * n + m) := by
  have hm4 : 4 * m < 3 ^ L := by norm_num at hsmall ⊢; omega
  have hm1 : m < 3 ^ L := by norm_num at hsmall; omega
  refine ⟨good_prefix hn.1 hm.1 hm1, ?_, ?_⟩
  · have hh := good_prefix hn.2.1 hm.2.1 hm4
    convert hh using 1 <;> ring
  · have hh := good_prefix hn.2.2 hm.2.2 hsmall
    convert hh using 1 <;> ring

/-- Separated concatenation realizes addition modulo any modulus coprime to
three. The output retains the low ternary digit of the second summand. -/
lemma hits_add_mod {q n m : ℕ} (hq : Nat.Coprime 3 q) (hn : Hits n) (hm : Hits m) :
    ∃ z : ℕ, Hits z ∧ Nat.ModEq q z (n + m) ∧ n + m ≤ z ∧ z % 3 = m % 3 := by
  have hqpos : 0 < q := by
    by_contra hh
    have hz : q = 0 := by omega
    simp [hz] at hq
  have ht : 0 < q.totient := Nat.totient_pos.mpr hqpos
  let L := q.totient * (4 ^ 9 * m + 1)
  have hL : 4 ^ 9 * m + 1 ≤ L := Nat.le_mul_of_pos_left _ ht
  have hLp : 0 < L := by omega
  have hb : 4 ^ 9 * m < 3 ^ L := by
    have hp : L < 3 ^ L := Nat.lt_pow_self (by decide)
    omega
  have hpow : Nat.ModEq q (3 ^ L) 1 := by
    have hh := (Nat.ModEq.pow_totient hq).pow (4 ^ 9 * m + 1)
    simpa only [← pow_mul, one_pow] using hh
  have hd : 3 ∣ 3 ^ L := dvd_pow_self 3 (ne_of_gt hLp)
  refine ⟨3 ^ L * n + m, hits_concat hn hm hb, ?_, ?_, ?_⟩
  · simpa only [one_mul] using (hpow.mul_right n).add_right m
  · have hp : 1 ≤ 3 ^ L := Nat.one_le_pow _ _ (by decide)
    nlinarith
  · simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_zero_of_dvd hd, zero_mul,
      Nat.zero_mod, zero_add, Nat.mod_mod]

lemma hits_multiple_mod {q n : ℕ} (hq : Nat.Coprime 3 q) (hn : Hits n) (k : ℕ) :
    ∃ z : ℕ, Hits z ∧ Nat.ModEq q z (k * n) ∧ k * n ≤ z := by
  induction k with
  | zero => exact ⟨0, hits_zero, by simp [Nat.ModEq], by simp⟩
  | succ k ih =>
    obtain ⟨z, hz, hmod, hle⟩ := ih
    obtain ⟨w, hw, hwm, hwl, _⟩ := hits_add_mod hq hz hn
    refine ⟨w, hw, ?_, ?_⟩
    · have hh := hwm.trans (hmod.add_right n)
      simpa only [Nat.succ_mul] using hh
    · rw [Nat.succ_mul]
      omega

/-- An exact positive-coefficient Bézout identity for the checked seed pair. -/
lemma seed_bezout : 6170 * otherSeed = 7171144275559 * seed + 1 := by
  norm_num [seed, otherSeed]

lemma seed_combination_mod {q : ℕ} (hq : 0 < q) :
    Nat.ModEq q (((q - 1) * 7171144275559) * seed + 6170 * otherSeed) 1 := by
  have he : ((q - 1) * 7171144275559) * seed + 6170 * otherSeed =
      q * (7171144275559 * seed) + 1 := by
    rw [seed_bezout]
    calc
      _ = ((q - 1) + 1) * (7171144275559 * seed) + 1 := by ring
      _ = _ := by rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
  rw [he]
  simp [Nat.ModEq]

/-- The simultaneous 0,1,9 hit language represents every residue class,
arbitrarily far out. This does not require a finite carry-graph computation. -/
theorem hits_every_residue {q : ℕ} (hq : Nat.Coprime 3 q) (r M : ℕ) :
    ∃ n : ℕ, M < n ∧ Hits n ∧ Nat.ModEq q n r := by
  have hqpos : 0 < q := by
    by_contra hh
    have hz : q = 0 := by omega
    simp [hz] at hq
  let R := r + q * (M + 1)
  let a := (q - 1) * 7171144275559
  have hR : M < R := by dsimp [R]; nlinarith
  have hRmod : Nat.ModEq q R r := by dsimp [R]; simp [Nat.ModEq]
  have hunit := seed_combination_mod hqpos
  change Nat.ModEq q (a * seed + 6170 * otherSeed) 1 at hunit
  obtain ⟨x, hx, hxm, hxl⟩ := hits_multiple_mod hq hits_seed (R * a)
  obtain ⟨y, hy, hym, hyl⟩ := hits_multiple_mod hq hits_otherSeed (R * 6170)
  obtain ⟨n, hn, hnm, hnl, _⟩ := hits_add_mod hq hx hy
  have he : (R * a) * seed + (R * 6170) * otherSeed =
      R * (a * seed + 6170 * otherSeed) := by ring
  have hmod : Nat.ModEq q n r := by
    have hh := hnm.trans (hxm.add hym)
    rw [he] at hh
    have hu := hunit.mul_left R
    simp only [mul_one] at hu
    exact (hh.trans hu).trans hRmod
  have hc : 1 ≤ a * seed + 6170 * otherSeed := by
    have hb : 1 ≤ 6170 * otherSeed := by decide
    omega
  have hle : R ≤ n := by
    have hh : R ≤ R * (a * seed + 6170 * otherSeed) := by nlinarith
    omega
  exact ⟨n, hR.trans_le hle, hn, hmod⟩

/-- The witnesses can additionally be units at three. -/
theorem unit_hits_every_residue {q : ℕ} (hq : Nat.Coprime 3 q) (r M : ℕ) :
    ∃ n : ℕ, M < n ∧ Hits n ∧ Nat.ModEq q n r ∧ n % 3 = 1 := by
  have hqpos : 0 < q := by
    by_contra hh
    have hz : q = 0 := by omega
    simp [hz] at hq
  let r' := r + q - seed % q
  have hsmall : seed % q < q := Nat.mod_lt _ hqpos
  have he : r' + seed % q = r + q := by dsimp [r']; omega
  have hrem : Nat.ModEq q (r' + seed) r := by
    have hh : Nat.ModEq q (r' + seed) (r' + seed % q) :=
      (Nat.ModEq.refl r').add (by simp [Nat.ModEq])
    rw [he] at hh
    exact hh.trans (by simp [Nat.ModEq])
  obtain ⟨x, hxM, hx, hxm⟩ := hits_every_residue hq r' M
  obtain ⟨n, hn, hnm, hnl, hn3⟩ := hits_add_mod hq hx hits_seed
  refine ⟨n, by omega, hn, (hnm.trans (hxm.add_right seed)).trans hrem, ?_⟩
  simpa only [seed, Nat.reduceMod] using hn3

/-- Arbitrarily large representatives can retain an odd prime divisor chosen
outside the modulus. Thus the residue-saturation result is not an assertion
that any power of two has the 0,1,9 pattern. -/
theorem unit_nonpower_hits_every_residue {q : ℕ} (hq : Nat.Coprime 3 q) (r M : ℕ) :
    ∃ n : ℕ, M < n ∧ Hits n ∧ Nat.ModEq q n r ∧ n % 3 = 1 ∧ ¬ n.isPowerOfTwo := by
  have hqpos : 0 < q := by
    by_contra hh
    have hz : q = 0 := by omega
    simp [hz] at hq
  obtain ⟨p, hpq, hp⟩ := Nat.exists_infinite_primes (q + 4)
  have hp3 : 3 < p := by omega
  have hcpq : Nat.Coprime p q := Nat.coprime_of_lt_prime (ne_of_gt hqpos) (by omega) hp
  have hc3p : Nat.Coprime 3 p :=
    (Nat.coprime_of_lt_prime (by decide : 3 ≠ 0) hp3 hp).symm
  let R := r * p ^ q.totient
  have hR : Nat.ModEq q R r := by
    have hh := (Nat.ModEq.pow_totient hcpq).mul_left r
    simpa only [mul_one] using hh
  have hpR : p ∣ R := by
    apply dvd_mul_of_dvd_right
    exact dvd_pow_self p (ne_of_gt (Nat.totient_pos.mpr hqpos))
  obtain ⟨n, hnM, hn, hnm, hn3⟩ := unit_hits_every_residue (hq.mul_right hc3p) R M
  have hnq : Nat.ModEq q n r :=
    (hnm.of_dvd (dvd_mul_right q p)).trans hR
  have hpn : p ∣ n := (hnm.dvd_iff (dvd_mul_left p q)).mpr hpR
  refine ⟨n, hnM, hn, hnq, hn3, ?_⟩
  rintro ⟨k, hk⟩
  rw [hk] at hpn
  have h2 := hp.dvd_of_dvd_pow hpn
  have hle := Nat.le_of_dvd (by decide : 0 < 2) h2
  omega

/-- No finite collection of primes accounts for all the non-power-of-two
integers having the three simultaneous good values n,4n,4^9*n. -/
theorem unit_nonpower_hits_avoiding_primes (F : Finset ℕ)
    (hF : ∀ p ∈ F, Nat.Prime p) (M : ℕ) :
    ∃ n : ℕ, M < n ∧ Hits n ∧ n % 3 = 1 ∧ ¬ n.isPowerOfTwo ∧
      ∀ p ∈ F, ¬ p ∣ n := by
  let q := ∏ p ∈ F.erase 3, p
  have hq : Nat.Coprime 3 q := by
    apply Nat.coprime_prod_right_iff.mpr
    intro p hp
    obtain ⟨hp3, hpF⟩ := Finset.mem_erase.mp hp
    exact (Nat.coprime_primes Nat.prime_three (hF p hpF)).mpr (Ne.symm hp3)
  obtain ⟨n, hnM, hn, hnm, hn3, hnp⟩ := unit_nonpower_hits_every_residue hq 1 M
  have hcn : Nat.Coprime n q :=
    Nat.coprime_of_mul_modEq_one 1 (by simpa only [mul_one] using hnm)
  refine ⟨n, hnM, hn, hn3, hnp, ?_⟩
  intro p hpF hpn
  by_cases hp3 : p = 3
  · subst p
    have hh := Nat.mod_eq_zero_of_dvd hpn
    omega
  · have hpq : p ∣ q := Finset.dvd_prod_of_mem (fun x : ℕ => x)
        (Finset.mem_erase.mpr ⟨hp3, hpF⟩)
    have hh := Nat.dvd_gcd hpn hpq
    rw [hcn] at hh
    have hle := Nat.le_of_dvd (by decide : 0 < 1) hh
    have hlo := (hF p hpF).two_le
    omega

/-- Even after deleting the multiples of finitely many primes, infinitely
many non-powers retain the 0,1,9 hit pattern. This is not an infinite family
of qualifying powers in the original conjecture. -/
theorem infinite_unit_nonpower_hits_avoiding_primes (F : Finset ℕ)
    (hF : ∀ p ∈ F, Nat.Prime p) :
    {n : ℕ | Hits n ∧ n % 3 = 1 ∧ ¬ n.isPowerOfTwo ∧ ∀ p ∈ F, ¬ p ∣ n}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro M
  obtain ⟨n, hnM, hn, hn3, hnp, hnF⟩ := unit_nonpower_hits_avoiding_primes F hF M
  exact ⟨n, ⟨hn, hn3, hnp, hnF⟩, hnM⟩

theorem no_finite_prime_cover :
    ¬ ∃ F : Finset ℕ, (∀ p ∈ F, Nat.Prime p) ∧
      ∀ n : ℕ, 0 < n → Hits n → ¬ n.isPowerOfTwo → ∃ p ∈ F, p ∣ n := by
  rintro ⟨F, hF, hcover⟩
  obtain ⟨n, hn0, hn, _, hnp, hnF⟩ := unit_nonpower_hits_avoiding_primes F hF 0
  obtain ⟨p, hpF, hpn⟩ := hcover n hn0 hn hnp
  exact hnF p hpF hpn

#print axioms hits_every_residue
#print axioms unit_hits_every_residue
#print axioms unit_nonpower_hits_every_residue
#print axioms unit_nonpower_hits_avoiding_primes
#print axioms infinite_unit_nonpower_hits_avoiding_primes
#print axioms no_finite_prime_cover
end Erdos406AlternateTripleResidues
