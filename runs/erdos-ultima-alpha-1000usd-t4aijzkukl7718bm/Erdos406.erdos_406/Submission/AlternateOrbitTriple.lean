import Submission.SparseTriple

/-! An alternate three-hit orbit pattern, with an infinite separated-block
family. Every member has a fixed nontrivial odd divisor, so these results
neither prove nor disprove Erdős406. In particular, no bound on the total
number of good terms in an arbitrary multiplication-by-four orbit is proved. -/
namespace Erdos406AlternateOrbitTriple
open Erdos406SparseTriple

abbrev seed : ℕ := 532261

lemma seed_good : Good seed := by decide +kernel
lemma four_seed_good : Good (4 * seed) := by decide +kernel
lemma ninth_seed_good : Good (4 ^ 9 * seed) := by decide +kernel
lemma seed_positive : 0 < seed := by decide

lemma seed_not_power_of_two : ¬ seed.isPowerOfTwo := by
  rintro ⟨k, hk⟩
  cases k with
  | zero => norm_num [seed] at hk
  | succ k =>
    have hh := congrArg (fun n : ℕ => n % 2) hk
    norm_num [seed, pow_succ, Nat.mul_mod] at hh

lemma not_power_of_two_of_seed_dvd {n : ℕ} (hn : seed ∣ n) : ¬ n.isPowerOfTwo := by
  rintro ⟨k, hk⟩
  rw [hk] at hn
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hn
  exact seed_not_power_of_two ⟨j, hj⟩

/-- The exponent pattern0,1,4 is not the only possible three-hit pattern. -/
theorem universal_triple_pattern_false :
    ¬ (∀ n k : ℕ, 0 < n → 1 < k →
      Good n → Good (4 * n) → Good (4 ^ k * n) → k = 4) := by
  intro h
  have hh := h seed 9 seed_positive (by decide) seed_good four_seed_good ninth_seed_good
  omega

lemma good_separated_copy (a L : ℕ) (ha : Good a) (hb : a < 3 ^ L) :
    Good (a * (3 ^ L + 1)) := by
  have hh := good_prefix (k := L) ha ha hb
  convert hh using 1
  ring

def family (j : ℕ) : ℕ := seed * (3 ^ (30 + j) + 1)

lemma small_block_bound {a : ℕ} (ha : a ≤ 4 ^ 9 * seed) (j : ℕ) : a < 3 ^ (30 + j) := by
  have hb : 4 ^ 9 * seed < 3 ^ 30 := by decide +kernel
  have hp : (3 : ℕ) ^ 30 ≤ 3 ^ (30 + j) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  exact (ha.trans_lt hb).trans_le hp

lemma family_good (j : ℕ) : Good (family j) := by
  exact good_separated_copy seed (30 + j) seed_good
    (small_block_bound (by decide : seed ≤ 4 ^ 9 * seed) j)

lemma four_family_good (j : ℕ) : Good (4 * family j) := by
  have hh := good_separated_copy (4 * seed) (30 + j) four_seed_good
    (small_block_bound (by decide : 4 * seed ≤ 4 ^ 9 * seed) j)
  simpa only [family, mul_assoc] using hh

lemma ninth_family_good (j : ℕ) : Good (4 ^ 9 * family j) := by
  have hh := good_separated_copy (4 ^ 9 * seed) (30 + j) ninth_seed_good
    (small_block_bound (le_refl _) j)
  simpa only [family, mul_assoc] using hh

lemma family_not_power_of_two (j : ℕ) : ¬ (family j).isPowerOfTwo :=
  not_power_of_two_of_seed_dvd (dvd_mul_right seed _)

lemma family_strictMono : StrictMono family := by
  intro i j hij
  have hh : (3 : ℕ) ^ (30 + i) < 3 ^ (30 + j) :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  dsimp [family, seed]
  omega

/-- These infinitely many alternate triples explicitly exclude powers of two. -/
theorem infinite_alternate_triples :
    {n : ℕ | Good n ∧ Good (4 * n) ∧ Good (4 ^ 9 * n) ∧ ¬ n.isPowerOfTwo}.Infinite := by
  apply (Set.infinite_range_of_injective family_strictMono.injective).mono
  rintro n ⟨j, rfl⟩
  exact ⟨family_good j, four_family_good j, ninth_family_good j, family_not_power_of_two j⟩

abbrev otherSeed : ℕ := 618625676378170

lemma other_seed_good : Good otherSeed := by decide +kernel
lemma four_other_seed_good : Good (4 * otherSeed) := by decide +kernel
lemma ninth_other_seed_good : Good (4 ^ 9 * otherSeed) := by decide +kernel
lemma seeds_coprime : Nat.Coprime seed otherSeed := by decide +kernel

lemma other_seed_not_power_of_two : ¬ otherSeed.isPowerOfTwo := by
  rintro ⟨k, hk⟩
  have hk2 : 2 ≤ k := by
    by_contra hh
    interval_cases k <;> norm_num [otherSeed] at hk
  have hd : 4 ∣ (2 : ℕ) ^ k := by
    simpa using Nat.pow_dvd_pow 2 hk2
  rw [← hk] at hd
  norm_num [otherSeed] at hd

/-- Even a common-divisor explanation of all triples with this pattern fails.
This excludes a SINGLE common divisor; it does not assert avoidance of any
arbitrary finite collection of primes. -/
theorem no_nontrivial_common_divisor :
    ¬ ∃ q : ℕ, 1 < q ∧ ∀ n : ℕ, 0 < n →
      Good n → Good (4 * n) → Good (4 ^ 9 * n) → q ∣ n := by
  rintro ⟨q, hq, hdiv⟩
  have h1 := hdiv seed seed_positive seed_good four_seed_good ninth_seed_good
  have h2 := hdiv otherSeed (by decide) other_seed_good four_other_seed_good
    ninth_other_seed_good
  have hh := Nat.dvd_gcd h1 h2
  have hc : Nat.gcd seed otherSeed = 1 := seeds_coprime
  rw [hc] at hh
  have hle := Nat.le_of_dvd (by decide : 0 < 1) hh
  omega

#print axioms seeds_coprime
#print axioms other_seed_not_power_of_two
#print axioms no_nontrivial_common_divisor

#print axioms universal_triple_pattern_false
#print axioms family_not_power_of_two
#print axioms infinite_alternate_triples
end Erdos406AlternateOrbitTriple
