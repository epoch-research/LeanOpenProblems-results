import Submission.PrimeSieve

/-!
# Private large prime squares in a squarefree-free interval

Remove from `(x, x + H]` the numbers divisible by the square of a prime at most
`A * H`. Under the sieve bound, at least `3 * H / 16` numbers remain. If the
interval contains no squarefree number, each remaining number has a
representation `m * p^2` with `p` prime, `A * H < p`, and `m > 0`.

When `H > 0` and `A ≥ 1`, each chosen prime divides no other number of the
interval. Both the chosen primes and the complementary factors are injective
on the remaining set. These are finite necessary conditions for an interval
to contain no squarefree number, not a proof of a squarefree-gap conjecture.
All cutoffs and spacing estimates use natural numbers, without roots or ceilings.
-/

open Finset

namespace PrivateSquares

/-- The interval after removing the squares of primes at most `A * H`. -/
noncomputable def clean (x H A : ℕ) : Finset ℕ :=
  Ioc x (x + H) \ PrimeSieve.primeSquareBad x H (A * H)

@[simp]
theorem mem_clean (x H A n : ℕ) :
    n ∈ clean x H A ↔
      x < n ∧ n ≤ x + H ∧
        ¬ ∃ p : ℕ, p.Prime ∧ p ≤ A * H ∧ p ^ 2 ∣ n := by
  classical
  simp only [clean, mem_sdiff, mem_Ioc, PrimeSieve.mem_primeSquareBad]
  constructor
  · rintro ⟨⟨hnlo, hnhi⟩, hbad⟩
    exact ⟨hnlo, hnhi, fun h => hbad ⟨hnlo, hnhi, h⟩⟩
  · rintro ⟨hnlo, hnhi, hbad⟩
    exact ⟨⟨hnlo, hnhi⟩, fun h => hbad h.2.2⟩

/-- Every clean number belongs to the original interval. -/
theorem clean_subset (x H A : ℕ) : clean x H A ⊆ Ioc x (x + H) :=
  sdiff_subset

/-- The clean and removed sets partition an interval of cardinality `H`. -/
theorem card_clean_add_card_primeSquareBad (x H A : ℕ) :
    (clean x H A).card + (PrimeSieve.primeSquareBad x H (A * H)).card = H := by
  have hsub : PrimeSieve.primeSquareBad x H (A * H) ⊆ Ioc x (x + H) := by
    intro n hn
    obtain ⟨hnlo, hnhi, _⟩ := (PrimeSieve.mem_primeSquareBad x H (A * H) n).mp hn
    exact mem_Ioc.mpr ⟨hnlo, hnhi⟩
  simpa only [clean, Nat.card_Ioc, Nat.add_sub_cancel_left] using
    card_sdiff_add_card_eq_card hsub

/-- The sieve bound leaves at least three sixteenths of the interval clean. -/
theorem three_mul_le_sixteen_mul_card_clean (x H A : ℕ)
    (hsieve : 16 * (PrimeSieve.primeSquareBad x H (A * H)).card ≤ 13 * H) :
    3 * H ≤ 16 * (clean x H A).card := by
  have hcard := card_clean_add_card_primeSquareBad x H A
  omega

/-- In a positive-length interval satisfying the sieve bound, the clean set is nonempty. -/
theorem clean_nonempty (x H A : ℕ) (hH : 0 < H)
    (hsieve : 16 * (PrimeSieve.primeSquareBad x H (A * H)).card ≤ 13 * H) :
    (clean x H A).Nonempty := by
  have hcard := three_mul_le_sixteen_mul_card_clean x H A hsieve
  exact card_pos.mp (by omega)

/-- A nonsquarefree clean number has a prime-square factor above the cutoff. -/
theorem exists_large_prime_square_factor (x H A n : ℕ)
    (hn : n ∈ clean x H A) (hns : ¬ Squarefree n) :
    ∃ p m : ℕ, p.Prime ∧ A * H < p ∧ 0 < m ∧ m * p ^ 2 = n := by
  classical
  rw [Nat.squarefree_iff_prime_squarefree] at hns
  push_neg at hns
  obtain ⟨p, hp, hpdvd⟩ := hns
  have hpsq : p ^ 2 ∣ n := by simpa only [pow_two] using hpdvd
  obtain ⟨hnlo, _, hsmall⟩ := (mem_clean x H A n).mp hn
  have hlarge : A * H < p := by
    by_contra hnot
    exact hsmall ⟨p, hp, by omega, hpsq⟩
  obtain ⟨m, hnm⟩ := hpsq
  have hmn : m * p ^ 2 = n := by simpa only [mul_comm] using hnm.symm
  have hm : 0 < m := by
    apply Nat.pos_of_ne_zero
    intro hmzero
    rw [hmzero, zero_mul] at hmn
    omega
  exact ⟨p, m, hp, hlarge, hm, hmn⟩

/-- A divisor larger than the interval length divides at most one interval member.
Primality is not needed for this spacing fact. -/
theorem large_divisor_private (x H n n' p : ℕ)
    (hn : n ∈ Ioc x (x + H)) (hn' : n' ∈ Ioc x (x + H))
    (hne : n ≠ n') (hp : H < p) (hpn : p ∣ n) : ¬ p ∣ n' := by
  intro hpn'
  obtain ⟨hnlo, hnhi⟩ := mem_Ioc.mp hn
  obtain ⟨hn'lo, hn'hi⟩ := mem_Ioc.mp hn'
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hle := Nat.le_of_dvd (Nat.sub_pos_of_lt hlt) (Nat.dvd_sub hpn' hpn)
    omega
  · have hle := Nat.le_of_dvd (Nat.sub_pos_of_lt hgt) (Nat.dvd_sub hpn hpn')
    omega

/-- Squares with distinct bases above `H`, multiplied by the same positive factor,
are separated by more than `H`. -/
theorem large_square_gap (H m p q : ℕ) (hm : 0 < m) (hp : H < p) (hpq : p < q) :
    m * p ^ 2 + H < m * q ^ 2 := by
  have hsq := Nat.pow_le_pow_left (show p + 1 ≤ q by omega) 2
  have hsep : p ^ 2 + (H + 1) ≤ q ^ 2 := by nlinarith
  have hmul := Nat.mul_le_mul_left m hsep
  have hlen := Nat.le_mul_of_pos_left (H + 1) hm
  nlinarith

/-- Any such large-square representations have private bases and injective bases
and cofactors. This lemma does not require the bases to be prime. -/
theorem representations_private (x H : ℕ) (R : Finset ℕ) (p m : ℕ → ℕ)
    (hR : R ⊆ Ioc x (x + H))
    (hrep : ∀ n ∈ R, H < p n ∧ 0 < m n ∧ m n * p n ^ 2 = n) :
    Set.InjOn p (R : Set ℕ) ∧ Set.InjOn m (R : Set ℕ) ∧
      ∀ n ∈ R, ∀ n' ∈ R, n ≠ n' → ¬ p n ∣ n' := by
  have hdiv (n : ℕ) (hn : n ∈ R) : p n ∣ n := by
    calc
      p n ∣ m n * p n ^ 2 :=
        dvd_mul_of_dvd_right (dvd_pow_self (p n) (n := 2) (by decide)) (m n)
      _ = n := (hrep n hn).2.2
  have hprivate : ∀ n ∈ R, ∀ n' ∈ R, n ≠ n' → ¬ p n ∣ n' := by
    intro n hn n' hn' hne
    exact large_divisor_private x H n n' (p n) (hR hn) (hR hn') hne
      (hrep n hn).1 (hdiv n hn)
  have hpinj : Set.InjOn p (R : Set ℕ) := by
    intro n hn n' hn' he
    by_contra hne
    apply hprivate n hn n' hn' hne
    rw [he]
    exact hdiv n' hn'
  have hminj : Set.InjOn m (R : Set ℕ) := by
    intro n hn n' hn' he
    by_contra hne
    have hpne : p n ≠ p n' := fun heq => hne (hpinj hn hn' heq)
    have hnint := mem_Ioc.mp (hR hn)
    have hn'int := mem_Ioc.mp (hR hn')
    obtain ⟨hpn, hmn, hfacn⟩ := hrep n hn
    obtain ⟨hpn', hmn', hfacn'⟩ := hrep n' hn'
    rcases lt_or_gt_of_ne hpne with hlt | hgt
    · have hgap := large_square_gap H (m n) (p n) (p n') hmn hpn hlt
      rw [hfacn, he, hfacn'] at hgap
      omega
    · have hgap := large_square_gap H (m n') (p n') (p n) hmn' hpn' hgt
      rw [hfacn', ← he, hfacn] at hgap
      omega
  exact ⟨hpinj, hminj, hprivate⟩

/-- Choose total functions giving the prime-square representations on the clean set.
Their values outside the clean set are immaterial. -/
theorem exists_clean_private_squares (x H A : ℕ) (hH : 0 < H) (hA : 1 ≤ A)
    (hall : ∀ n : ℕ, x < n → n ≤ x + H → ¬ Squarefree n) :
    ∃ p m : ℕ → ℕ,
      (∀ n ∈ clean x H A,
        (p n).Prime ∧ A * H < p n ∧ 0 < m n ∧ m n * p n ^ 2 = n) ∧
      Set.InjOn p (clean x H A : Set ℕ) ∧
      Set.InjOn m (clean x H A : Set ℕ) ∧
      (∀ n ∈ clean x H A, ∀ n' ∈ clean x H A, n ≠ n' → ¬ p n ∣ n') := by
  classical
  have hex : ∀ n : ℕ, ∃ p m : ℕ,
      n ∈ clean x H A → p.Prime ∧ A * H < p ∧ 0 < m ∧ m * p ^ 2 = n := by
    intro n
    by_cases hn : n ∈ clean x H A
    · obtain ⟨p, m, hfac⟩ := exists_large_prime_square_factor x H A n hn
        (hall n ((mem_clean x H A n).mp hn).1 ((mem_clean x H A n).mp hn).2.1)
      exact ⟨p, m, fun _ => hfac⟩
    · exact ⟨0, 0, fun hn' => (hn hn').elim⟩
  choose p m hfac using hex
  have hHA : H ≤ A * H := by
    simpa only [one_mul] using (mul_le_mul_iff_left₀ hH).mpr hA
  have hrep : ∀ n ∈ clean x H A, H < p n ∧ 0 < m n ∧ m n * p n ^ 2 = n := by
    intro n hn
    exact ⟨hHA.trans_lt (hfac n hn).2.1, (hfac n hn).2.2⟩
  exact ⟨p, m, hfac,
    representations_private x H (clean x H A) p m (clean_subset x H A) hrep⟩

/-- Finite necessary condition for a positive-length interval containing no squarefree number.
The witnessing set is the clean set, so the sieve bound supplies its cardinality. -/
theorem exists_private_squares (x H A : ℕ) (hH : 0 < H) (hA : 1 ≤ A)
    (hsieve : 16 * (PrimeSieve.primeSquareBad x H (A * H)).card ≤ 13 * H)
    (hall : ∀ n : ℕ, x < n → n ≤ x + H → ¬ Squarefree n) :
    ∃ R : Finset ℕ, ∃ p m : ℕ → ℕ,
      3 * H ≤ 16 * R.card ∧ R ⊆ Ioc x (x + H) ∧
      (∀ n ∈ R, (p n).Prime ∧ A * H < p n ∧ 0 < m n ∧ m n * p n ^ 2 = n) ∧
      Set.InjOn p (R : Set ℕ) ∧ Set.InjOn m (R : Set ℕ) ∧
      (∀ n ∈ R, ∀ n' ∈ R, n ≠ n' → ¬ p n ∣ n') := by
  obtain ⟨p, m, hfac, hprivate⟩ := exists_clean_private_squares x H A hH hA hall
  exact ⟨clean x H A, p, m, three_mul_le_sixteen_mul_card_clean x H A hsieve,
    clean_subset x H A, hfac, hprivate⟩

/-- For fixed `A ≥ 1`, the finite necessary condition holds beyond a positive threshold
in `H`, uniformly in the interval's starting point `x`. -/
theorem exists_uniform_threshold (A : ℕ) (hA : 1 ≤ A) :
    ∃ H₀ : ℕ, 0 < H₀ ∧ ∀ H ≥ H₀, ∀ x : ℕ,
      (∀ n : ℕ, x < n → n ≤ x + H → ¬ Squarefree n) →
      ∃ R : Finset ℕ, ∃ p m : ℕ → ℕ,
        3 * H ≤ 16 * R.card ∧ R ⊆ Ioc x (x + H) ∧
        (∀ n ∈ R, (p n).Prime ∧ A * H < p n ∧ 0 < m n ∧ m n * p n ^ 2 = n) ∧
        Set.InjOn p (R : Set ℕ) ∧ Set.InjOn m (R : Set ℕ) ∧
        (∀ n ∈ R, ∀ n' ∈ R, n ≠ n' → ¬ p n ∣ n') := by
  obtain ⟨H₀, hthreshold⟩ := PrimeSieve.exists_uniform_threshold A
  refine ⟨max H₀ 1, by omega, ?_⟩
  intro H hH x hall
  exact exists_private_squares x H A (by omega) hA (hthreshold H (by omega) x) hall

/-- Filter formulation of the uniform eventual necessary condition. -/
theorem eventually_exists_private_squares (A : ℕ) (hA : 1 ≤ A) :
    ∀ᶠ H : ℕ in Filter.atTop, ∀ x : ℕ,
      (∀ n : ℕ, x < n → n ≤ x + H → ¬ Squarefree n) →
      ∃ R : Finset ℕ, ∃ p m : ℕ → ℕ,
        3 * H ≤ 16 * R.card ∧ R ⊆ Ioc x (x + H) ∧
        (∀ n ∈ R, (p n).Prime ∧ A * H < p n ∧ 0 < m n ∧ m n * p n ^ 2 = n) ∧
        Set.InjOn p (R : Set ℕ) ∧ Set.InjOn m (R : Set ℕ) ∧
        (∀ n ∈ R, ∀ n' ∈ R, n ≠ n' → ¬ p n ∣ n') := by
  obtain ⟨H₀, _, hthreshold⟩ := exists_uniform_threshold A hA
  exact Filter.eventually_atTop.mpr ⟨H₀, hthreshold⟩

end PrivateSquares
