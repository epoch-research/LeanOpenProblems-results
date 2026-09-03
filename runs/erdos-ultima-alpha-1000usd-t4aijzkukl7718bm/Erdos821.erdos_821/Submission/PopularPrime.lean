import Submission.CommonFactor
import Submission.SquarefreeInput

/-!
# Extracting a popular prime from a totient fiber

Every prime in an input has predecessor dividing the output, so at most the
divisor count many primes can occur. This gives a popular-prime subfamily with
subpower loss. The prime is not proved to be large. These lemmas do not settle
Erdős 821 or supply an exponent-improving iteration.
-/

open Nat Filter
open scoped Classical

namespace Erdos821

lemma mem_shiftedPrimeDivisors_of_prime_dvd {n m p : ℕ} (hn : 0 < n)
    (hφ : totient m = n) (hp : p.Prime) (hpm : p ∣ m) :
    p ∈ shiftedPrimeDivisors n := by
  have hpd := Nat.totient_dvd_of_dvd hpm
  rw [Nat.totient_prime hp, hφ] at hpd
  have hple := Nat.le_of_dvd hn hpd
  have hp2 := hp.two_le
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_range.mpr (by omega), hp, hpd⟩

/-- If every member has a prime factor above a prescribed cutoff, some such
prime divides at least a divisor-count fraction of the family. The hypothesis
about the cutoff is explicit; no lower bound for it is asserted. -/
lemma exists_popular_prime_of_totient_fiber_cover (S : Finset ℕ) (n y : ℕ)
    (hn : 0 < n) (hne : S.Nonempty) (hS : ∀ m ∈ S, totient m = n)
    (hcover : ∀ m ∈ S, ∃ p : ℕ, p.Prime ∧ y ≤ p ∧ p ∣ m) :
    ∃ p : ℕ, p.Prime ∧ y ≤ p ∧ p - 1 ∣ n ∧
      S.card ≤ n.divisors.card * (S.filter (fun m => p ∣ m)).card := by
  let P := (shiftedPrimeDivisors n).filter (fun p => y ≤ p)
  have hmaps (m : ℕ) (hm : m ∈ S) : ∃ p ∈ P, p ∣ m := by
    obtain ⟨p, hp, hyp, hpm⟩ := hcover m hm
    exact ⟨p, Finset.mem_filter.mpr
      ⟨mem_shiftedPrimeDivisors_of_prime_dvd hn (hS m hm) hp hpm, hyp⟩, hpm⟩
  have hPne : P.Nonempty := by
    obtain ⟨m, hm⟩ := hne
    obtain ⟨p, hp, _⟩ := hmaps m hm
    exact ⟨p, hp⟩
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image P
    (fun p => (S.filter (fun m => p ∣ m)).card) hPne
  have hpS := (Finset.mem_filter.mp hp).1
  have hpprime := (Finset.mem_filter.mp hpS).2.1
  have hpdiv := (Finset.mem_filter.mp hpS).2.2
  refine ⟨p, hpprime, (Finset.mem_filter.mp hp).2, hpdiv, ?_⟩
  have hsub : S ⊆ P.biUnion (fun p => S.filter (fun m => p ∣ m)) := by
    intro m hm
    obtain ⟨p, hp, hpm⟩ := hmaps m hm
    exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_filter.mpr ⟨hm, hpm⟩⟩
  calc
    S.card ≤ (P.biUnion (fun p => S.filter (fun m => p ∣ m))).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ p ∈ P, (S.filter (fun m => p ∣ m)).card := Finset.card_biUnion_le
    _ ≤ ∑ _q ∈ P, (S.filter (fun m => p ∣ m)).card := Finset.sum_le_sum hmax
    _ = P.card * (S.filter (fun m => p ∣ m)).card := by simp
    _ ≤ _ := Nat.mul_le_mul_right _
      ((Finset.card_le_card (Finset.filter_subset _ _)).trans
        (shiftedPrimeDivisors_card_le_divisors_card hn))

lemma exists_popular_prime_of_totient_fiber (S : Finset ℕ) (n : ℕ)
    (hn : 1 < n) (hne : S.Nonempty) (hS : ∀ m ∈ S, totient m = n) :
    ∃ p : ℕ, p.Prime ∧ p - 1 ∣ n ∧
      S.card ≤ n.divisors.card * (S.filter (fun m => p ∣ m)).card := by
  obtain ⟨p, hp, _, hpd, hcard⟩ := exists_popular_prime_of_totient_fiber_cover S n 0
    (by omega) hne hS (by
      intro m hm
      have hm1 : m ≠ 1 := by
        intro h
        have hφ := hS m hm
        simp only [h, Nat.totient_one] at hφ
        omega
      exact ⟨m.minFac, Nat.minFac_prime hm1, Nat.zero_le _, Nat.minFac_dvd _⟩)
  exact ⟨p, hp, hpd, hcard⟩

/-- General inputs can be divided by the popular prime with an additional
factor of two accounting for its two possible overlaps with the quotient. -/
lemma exists_popular_prime_reduction (S : Finset ℕ) (n y : ℕ)
    (hn : 0 < n) (hne : S.Nonempty) (hS : ∀ m ∈ S, totient m = n)
    (hcover : ∀ m ∈ S, ∃ p : ℕ, p.Prime ∧ y ≤ p ∧ p ∣ m) :
    ∃ p n' : ℕ, p.Prime ∧ y ≤ p ∧ p - 1 ∣ n ∧ n' ≤ n / (p - 1) ∧
      S.card ≤ 2 * n.divisors.card * g n' := by
  obtain ⟨p, hp, hyp, hpd, hcard⟩ :=
    exists_popular_prime_of_totient_fiber_cover S n y hn hne hS hcover
  obtain ⟨n', hn', hT⟩ := exists_reduced_totient_fiber_of_common_factor
    (S.filter (fun m => p ∣ m)) n p hp.pos (by
      intro m hm
      obtain ⟨hmS, hpm⟩ := Finset.mem_filter.mp hm
      exact ⟨hS m hmS, hpm⟩)
  rw [Nat.totient_prime hp] at hn'
  have hpcard : p.divisors.card = 2 := by simp [hp.divisors, hp.ne_one.symm]
  rw [hpcard] at hT
  refine ⟨p, n', hp, hyp, hpd, hn', ?_⟩
  calc
    S.card ≤ n.divisors.card * (S.filter (fun m => p ∣ m)).card := hcard
    _ ≤ n.divisors.card * (2 * g n') := Nat.mul_le_mul_left _ hT
    _ = _ := by ring

/-- For squarefree odd inputs, a popular prime is at least three and can be
removed without overlap loss. This decreases the output, but not necessarily
by a positive power of the output. -/
lemma exists_popular_prime_reduction_squarefree_odd (S : Finset ℕ) (n : ℕ)
    (hn : 1 < n) (hne : S.Nonempty)
    (hS : ∀ m ∈ S, Squarefree m ∧ Odd m ∧ totient m = n) :
    ∃ p : ℕ, p.Prime ∧ 3 ≤ p ∧ p - 1 ∣ n ∧ n / (p - 1) < n ∧
      S.card ≤ n.divisors.card * g (n / (p - 1)) := by
  obtain ⟨p, hp, hp3, hpd, hcard⟩ := exists_popular_prime_of_totient_fiber_cover S n 3
    (by omega) hne (fun m hm => (hS m hm).2.2) (by
      intro m hm
      have hm1 : m ≠ 1 := by
        intro h
        have hφ := (hS m hm).2.2
        simp only [h, Nat.totient_one] at hφ
        omega
      have hp := Nat.minFac_prime hm1
      have hp2 := hp.two_le
      have hpne : m.minFac ≠ 2 := by
        intro h
        exact (hS m hm).2.1.not_two_dvd_nat (h ▸ Nat.minFac_dvd m)
      exact ⟨m.minFac, hp, by omega, Nat.minFac_dvd _⟩)
  have hT : (S.filter (fun m => p ∣ m)).card ≤ g (n / (p - 1)) := by
    rw [← Nat.totient_prime hp]
    apply card_totient_fiber_le_g_div_of_common_coprime_factor _ n p hp.pos
    intro m hm
    obtain ⟨hmS, hpm⟩ := Finset.mem_filter.mp hm
    refine ⟨(hS m hmS).2.2, hpm, ?_⟩
    apply Nat.coprime_of_squarefree_mul
    rw [Nat.mul_div_cancel' hpm]
    exact (hS m hmS).1
  refine ⟨p, hp, hp3, hpd, Nat.div_lt_self (by omega) (by omega), ?_⟩
  exact hcard.trans (Nat.mul_le_mul_left _ hT)

/-- The loss in the squarefree odd reduction is eventually smaller than any
fixed positive power. The selected prime still has no quantitative lower
bound beyond three. -/
lemma eventually_popular_prime_reduction_squarefree_odd (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ S : Finset ℕ, S.Nonempty →
      (∀ m ∈ S, Squarefree m ∧ Odd m ∧ totient m = n) →
        ∃ p : ℕ, p.Prime ∧ 3 ≤ p ∧ p - 1 ∣ n ∧ n / (p - 1) < n ∧
          (S.card : ℝ) ≤ (n : ℝ) ^ ε * (g (n / (p - 1)) : ℝ) := by
  filter_upwards [eventually_card_divisors_le_rpow ε hε, eventually_ge_atTop 2]
    with n hτ hn S hne hS
  obtain ⟨p, hp, hp3, hpd, hn', hcard⟩ :=
    exists_popular_prime_reduction_squarefree_odd S n (by omega) hne hS
  refine ⟨p, hp, hp3, hpd, hn', ?_⟩
  calc
    (S.card : ℝ) ≤ (n.divisors.card : ℝ) * (g (n / (p - 1)) : ℝ) := by
      exact_mod_cast hcard
    _ ≤ _ := mul_le_mul_of_nonneg_right hτ (Nat.cast_nonneg _)

#print axioms exists_popular_prime_of_totient_fiber_cover
#print axioms exists_popular_prime_reduction
#print axioms exists_popular_prime_reduction_squarefree_odd
#print axioms eventually_popular_prime_reduction_squarefree_odd

end Erdos821
