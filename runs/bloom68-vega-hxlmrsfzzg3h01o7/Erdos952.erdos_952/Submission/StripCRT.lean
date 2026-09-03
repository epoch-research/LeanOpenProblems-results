import FormalConjecturesUtil

/-!
# Periodic prime exclusion for finite Gaussian-integer patterns

Given a finite pattern, the elementary Chinese remainder theorem supplies a
horizontal arithmetic progression of translations on which each point has a
fixed, bounded-norm nonunit divisor. The moduli are distinct Fermat numbers;
no primality of a Fermat number, or theorem on primes in progressions, is used.

For a pattern of size `m`, the period is the product of Fermat numbers numbered
`1, ..., m`, and the norm bound is Fermat number `m`. The divisors are
`2^(2^j) + i`, for `j < m`. In particular, any prime among these translated
points has norm at most this bound.

This is finite-pattern infrastructure, not a Gaussian moat theorem. This file
neither imports nor modifies `Submission.Spec`.
-/

namespace Erdos952.StripCRT

open scoped BigOperators

/-- The real coordinate of the `j`-th explicit Gaussian divisor. -/
def fermatRoot (j : ℕ) : ℕ := 2 ^ (2 ^ j)

/-- Pairwise coprime moduli, starting with the Fermat number `5`. -/
def fermatModulus (j : ℕ) : ℕ := Nat.fermatNumber (j + 1)

/-- The explicit nonunit Gaussian divisor `2^(2^j) + i`. -/
def fermatDivisor (j : ℕ) : GaussianInt := ⟨fermatRoot j, 1⟩

/-- An explicit positive horizontal period for a pattern of size `m`. -/
def period (m : ℕ) : ℤ := ∏ j : Fin m, (fermatModulus j.val : ℤ)

/-- A uniform norm bound; for a nonempty pattern it is the largest modulus. -/
def normBound (m : ℕ) : ℤ := Nat.fermatNumber m

lemma fermatModulus_eq (j : ℕ) : fermatModulus j = fermatRoot j ^ 2 + 1 := by
  rw [fermatModulus, Nat.fermatNumber_succ]
  simp [Nat.fermatNumber, fermatRoot]

lemma fermatModulus_pos (j : ℕ) : 0 < fermatModulus j := by
  have := Nat.three_le_fermatNumber (j + 1)
  unfold fermatModulus
  omega

lemma fermatModulus_coprime {i j : ℕ} (h : i ≠ j) :
    (fermatModulus i).Coprime (fermatModulus j) := by
  apply Nat.coprime_fermatNumber_fermatNumber
  omega

@[simp] lemma norm_fermatDivisor (j : ℕ) :
    (fermatDivisor j).norm = (fermatModulus j : ℤ) := by
  simp [fermatDivisor, Zsqrtd.norm, fermatModulus_eq, pow_two]

lemma fermatDivisor_not_isUnit (j : ℕ) : ¬ IsUnit (fermatDivisor j) := by
  intro h
  have hn := (Zsqrtd.norm_eq_one_iff' (by norm_num : (-1 : ℤ) ≤ 0)
    (fermatDivisor j)).mpr h
  rw [norm_fermatDivisor] at hn
  have := Nat.three_le_fermatNumber (j + 1)
  unfold fermatModulus at hn
  omega

lemma period_pos (m : ℕ) : 0 < period m := by
  apply Finset.prod_pos
  intro j _
  exact_mod_cast fermatModulus_pos j.val

lemma fermatModulus_dvd_period {m : ℕ} (j : Fin m) :
    (fermatModulus j.val : ℤ) ∣ period m := by
  exact Finset.dvd_prod_of_mem _ (Finset.mem_univ j)

lemma norm_fermatDivisor_le {m : ℕ} (j : Fin m) :
    (fermatDivisor j.val).norm ≤ normBound m := by
  rw [norm_fermatDivisor]
  unfold fermatModulus normBound
  exact_mod_cast Nat.fermatNumber_mono (show j.val + 1 ≤ m by omega)

/-- The elementary congruence criterion for divisibility by `a + i`.
The reverse implication uses the explicit quotient `(a*k + y) - k*i`. -/
lemma gaussian_dvd_iff (a : ℤ) (z : GaussianInt) :
    (⟨a, 1⟩ : GaussianInt) ∣ z ↔ a ^ 2 + 1 ∣ z.re - a * z.im := by
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨-w.im, ?_⟩
    simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]
    ring
  · rintro ⟨k, hk⟩
    refine ⟨⟨a * k + z.im, -k⟩, ?_⟩
    apply Zsqrtd.ext <;> simp
    nlinarith [hk]

lemma fermatDivisor_dvd_iff (j : ℕ) (z : GaussianInt) :
    fermatDivisor j ∣ z ↔
      (fermatModulus j : ℤ) ∣ z.re - (fermatRoot j : ℤ) * z.im := by
  simpa [fermatDivisor, fermatModulus_eq] using
    gaussian_dvd_iff (fermatRoot j : ℤ) z

/-- Integer CRT for these moduli, obtained from natural CRT by reducing every
possibly negative residue before converting it to a natural number. -/
lemma exists_crt {m : ℕ} (r : Fin m → ℤ) :
    ∃ t : ℤ, ∀ j : Fin m, (fermatModulus j.val : ℤ) ∣ t - r j := by
  let a : Fin m → ℕ := fun j => (r j % (fermatModulus j.val : ℤ)).toNat
  have hs : ∀ j ∈ (Finset.univ : Finset (Fin m)), fermatModulus j.val ≠ 0 := by
    intro j _
    exact (fermatModulus_pos j.val).ne'
  have hco : Set.Pairwise ((Finset.univ : Finset (Fin m)) : Set (Fin m))
      (fun i j : Fin m => (fermatModulus i.val).Coprime (fermatModulus j.val)) := by
    intro i _ j _ hij
    exact fermatModulus_coprime (fun h => hij (Fin.ext h))
  let s := Nat.chineseRemainderOfFinset a (fun j : Fin m => fermatModulus j.val)
    Finset.univ hs hco
  refine ⟨(s.val : ℤ), ?_⟩
  intro j
  have hc : Int.ModEq (fermatModulus j.val : ℤ) (s.val : ℤ) (a j : ℤ) :=
    Int.natCast_modEq_iff.mpr (s.property j (Finset.mem_univ j))
  have ha : (a j : ℤ) = r j % (fermatModulus j.val : ℤ) := by
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hs j (Finset.mem_univ j)))
  rw [ha] at hc
  exact (hc.trans (Int.mod_modEq _ _)).symm.dvd

/-- The assigned explicit Fermat divisor divides every point in every
horizontal translate in the progression. Repeated points in `f` are allowed. -/
theorem exists_periodic_fermat_divisors {m : ℕ} (f : Fin m → GaussianInt) :
    ∃ t : ℤ, ∀ n : ℤ, ∀ j : Fin m,
      fermatDivisor j.val ∣ (((t + period m * n : ℤ) : GaussianInt) + f j) := by
  obtain ⟨t, ht⟩ := exists_crt
    (fun j : Fin m => (fermatRoot j.val : ℤ) * (f j).im - (f j).re)
  refine ⟨t, ?_⟩
  intro n j
  apply (fermatDivisor_dvd_iff _ _).mpr
  have hp : (fermatModulus j.val : ℤ) ∣ period m * n :=
    dvd_mul_of_dvd_left (fermatModulus_dvd_period j) n
  convert dvd_add (ht j) hp using 1
  simp
  ring

/-- Finite patterns have uniformly bounded nonunit divisors along an explicit
positive-period horizontal arithmetic progression. -/
theorem exists_periodic_nonunit_divisors_explicit (F : Finset GaussianInt) :
    ∃ t : ℤ, ∀ n : ℤ, ∀ z ∈ F, ∃ d : GaussianInt,
      ¬ IsUnit d ∧ d ∣ (((t + period F.card * n : ℤ) : GaussianInt) + z) ∧
        d.norm ≤ normBound F.card := by
  classical
  let f : Fin F.card → GaussianInt := fun j => (F.equivFin.symm j).val
  obtain ⟨t, ht⟩ := exists_periodic_fermat_divisors f
  refine ⟨t, ?_⟩
  intro n z hz
  let j : Fin F.card := F.equivFin ⟨z, hz⟩
  refine ⟨fermatDivisor j.val, fermatDivisor_not_isUnit j.val, ?_,
    norm_fermatDivisor_le j⟩
  simpa [f, j] using ht n j

/-- A nonunit divisor of a Gaussian prime has the same norm as that prime. -/
lemma norm_eq_of_prime_dvd {p d : GaussianInt} (hp : Prime p)
    (hd : ¬ IsUnit d) (h : d ∣ p) : p.norm = d.norm := by
  exact Zsqrtd.norm_eq_of_associated (by norm_num : (-1 : ℤ) ≤ 0)
    ((hp.irreducible.dvd_iff.mp h).resolve_left hd)

/-- The explicit-period prime-exclusion interface. No Gaussian point of norm
larger than `normBound F.card` in these translates can be prime. -/
theorem exists_periodic_prime_exclusion_explicit (F : Finset GaussianInt) :
    ∃ t : ℤ, ∀ n : ℤ, ∀ z ∈ F,
      Prime (((t + period F.card * n : ℤ) : GaussianInt) + z) →
        ((((t + period F.card * n : ℤ) : GaussianInt) + z).norm ≤ normBound F.card) := by
  obtain ⟨t, ht⟩ := exists_periodic_nonunit_divisors_explicit F
  refine ⟨t, ?_⟩
  intro n z hz hp
  obtain ⟨d, hd, hdvd, hnorm⟩ := ht n z hz
  exact (norm_eq_of_prime_dvd hp hd hdvd).trans_le hnorm

/-- A positive period and a uniform nonunit-divisor bound for any finite
Gaussian-integer pattern under horizontal integer translation. -/
theorem exists_periodic_nonunit_divisors (F : Finset GaussianInt) :
    ∃ t P K : ℤ, 0 < P ∧ ∀ n : ℤ, ∀ z ∈ F, ∃ d : GaussianInt,
      ¬ IsUnit d ∧ d ∣ (((t + P * n : ℤ) : GaussianInt) + z) ∧ d.norm ≤ K := by
  obtain ⟨t, ht⟩ := exists_periodic_nonunit_divisors_explicit F
  exact ⟨t, period F.card, normBound F.card, period_pos F.card, ht⟩

/-- Every finite pattern admits periodic horizontal translations in which
all prime points have uniformly bounded norm. -/
theorem exists_periodic_prime_exclusion (F : Finset GaussianInt) :
    ∃ t P K : ℤ, 0 < P ∧ ∀ n : ℤ, ∀ z ∈ F,
      Prime (((t + P * n : ℤ) : GaussianInt) + z) →
        ((((t + P * n : ℤ) : GaussianInt) + z).norm ≤ K) := by
  obtain ⟨t, ht⟩ := exists_periodic_prime_exclusion_explicit F
  exact ⟨t, period F.card, normBound F.card, period_pos F.card, ht⟩

end Erdos952.StripCRT
