import Submission.Valuation

/-!
# Coprimality obstruction to multiplying entire totient fibers

These bounds test a proposed amplification route. They do not settle Erdős 821.
A pairwise-coprime subfamily of a nontrivial totient fiber has subpower size,
even when the entire fiber is much larger.
-/

open Nat Filter
open scoped Classical

namespace Erdos821

/-- A pairwise-coprime family in a nontrivial totient fiber has at most one
member for each possible least prime predecessor, which is a divisor of the
output. -/
lemma card_coprime_totient_fiber_le_divisors (n : ℕ) (hn : 1 < n)
    (S : Finset ℕ) (hS : ∀ m ∈ S, totient m = n)
    (hcop : (S : Set ℕ).Pairwise Nat.Coprime) :
    S.card ≤ n.divisors.card := by
  have hne (m : ℕ) (hm : m ∈ S) : m ≠ 1 := by
    intro h
    have := hS m hm
    simp only [h, Nat.totient_one] at this
    omega
  apply Finset.card_le_card_of_injOn (fun m : ℕ => m.minFac - 1)
  · intro m hm
    change m ∈ S at hm
    apply Nat.mem_divisors.mpr
    have hdiv := Nat.totient_dvd_of_dvd (Nat.minFac_dvd m)
    rw [Nat.totient_prime (Nat.minFac_prime (hne m hm)), hS m hm] at hdiv
    exact ⟨hdiv, by omega⟩
  · intro a ha b hb hab
    change a ∈ S at ha
    change b ∈ S at hb
    by_contra hneab
    have hpa := Nat.minFac_prime (hne a ha)
    have hpb := Nat.minFac_prime (hne b hb)
    have hpab : a.minFac = b.minFac := by
      have := hpa.two_le
      have := hpb.two_le
      change a.minFac - 1 = b.minFac - 1 at hab
      omega
    have hdiv : a.minFac ∣ a.gcd b := Nat.dvd_gcd (Nat.minFac_dvd a)
      (hpab ▸ Nat.minFac_dvd b)
    have hc := hcop ha hb hneab
    rw [hc.gcd_eq_one] at hdiv
    exact hpa.not_dvd_one hdiv

/-- Uniformly over all pairwise-coprime subfamilies, the available number of
coprime atoms is at most an arbitrary fixed positive power of the output,
once the output is sufficiently large. -/
lemma eventually_card_coprime_totient_fiber_le_rpow (e : ℝ) (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, ∀ S : Finset ℕ,
      (∀ m ∈ S, totient m = n) → (S : Set ℕ).Pairwise Nat.Coprime →
        (S.card : ℝ) ≤ (n : ℝ) ^ e := by
  filter_upwards [eventually_card_divisors_le_rpow e he, eventually_ge_atTop 2]
    with n hn hn2 S hS hcop
  have hcard : (S.card : ℝ) ≤ n.divisors.card := by
    exact_mod_cast card_coprime_totient_fiber_le_divisors n (by omega) S hS hcop
  exact hcard.trans hn


/-- Even if the number of selected blocks grows with `n`, taking subsets of
one pairwise-coprime fiber family supplies only subpower-many choices relative
to the resulting totient `n^r`. -/
lemma eventually_choose_coprime_totient_fiber_le_rpow (e : ℝ) (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, ∀ S : Finset ℕ,
      (∀ m ∈ S, totient m = n) → (S : Set ℕ).Pairwise Nat.Coprime →
        ∀ r : ℕ, ((S.card.choose r : ℕ) : ℝ) ≤ ((n : ℝ) ^ r) ^ e := by
  filter_upwards [eventually_card_coprime_totient_fiber_le_rpow e he]
    with n hn S hS hcop r
  calc
    ((S.card.choose r : ℕ) : ℝ) ≤ (S.card : ℝ) ^ r := by
      exact_mod_cast Nat.choose_le_pow S.card r
    _ ≤ ((n : ℝ) ^ e) ^ r := pow_le_pow_left₀ (by positivity) (hn S hS hcop) r
    _ = _ := Real.rpow_pow_comm (Nat.cast_nonneg n) e r

/-- In particular, a polynomial-size family in a sufficiently large fiber
must contain two distinct members with a common prime factor. -/
lemma eventually_exists_not_coprime_of_large_totient_fiber (e : ℝ) (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, ∀ S : Finset ℕ,
      (∀ m ∈ S, totient m = n) → (n : ℝ) ^ e < S.card →
        ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ ¬a.Coprime b := by
  filter_upwards [eventually_card_coprime_totient_fiber_le_rpow e he]
    with n hn S hS hcard
  by_contra h
  push_neg at h
  have hcop : (S : Set ℕ).Pairwise Nat.Coprime := by
    intro a ha b hb hab
    exact h a ha b hb hab
  exact (not_lt_of_ge (hn S hS hcop)) hcard

#print axioms card_coprime_totient_fiber_le_divisors
#print axioms eventually_card_coprime_totient_fiber_le_rpow
#print axioms eventually_choose_coprime_totient_fiber_le_rpow
#print axioms eventually_exists_not_coprime_of_large_totient_fiber

end Erdos821
