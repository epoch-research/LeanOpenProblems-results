import Submission.PrimeReflection
import Submission.PrimeWinnerEnergy

/-! Reflection using the least prime factor of the losing integer.
The map reverses signs and preserves the winner, but is highly noninjective. -/

namespace Erdos371

/-- Reflection in a specified divisor-product period. -/
def divisorReflection (n a b : ℕ) : ℕ := a*b-1-n%(a*b)

lemma divisorReflection_eq_root (n a b : ℕ) (ha : 1 < a) (hb : 1 < b)
    (han : a ∣ n) (hbn : b ∣ n+1) :
    divisorReflection n a b = adjacentRoot b a
      (divisor_pair_coprime n a b han hbn).symm := by
  have hc := divisor_pair_coprime n a b han hbn
  have hm : Nat.ModEq (a*b) (n%(a*b)) n := Nat.mod_modEq n (a*b)
  have h₁ : a ∣ n%(a*b) :=
    (hm.dvd_iff (Nat.dvd_mul_right a b)).mpr han
  have h₂ : b ∣ n%(a*b)+1 :=
    ((hm.add_right 1).dvd_iff (Nat.dvd_mul_left b a)).mpr hbn
  have he := adjacentRoot_unique a b hc (by omega) (by omega) (n%(a*b))
    (Nat.mod_lt _ (by positivity)) h₁ h₂
  change a*b-1-n%(a*b) = _
  rw [he, adjacentRoot_swap a b hc ha hb]

lemma divisorReflection_bounds (n a b : ℕ) (ha : 1 < a) (hb : 1 < b)
    (han : a ∣ n) (hbn : b ∣ n+1) :
    1 < divisorReflection n a b ∧ divisorReflection n a b < a*b := by
  rw [divisorReflection_eq_root n a b ha hb han hbn]
  constructor
  · have hp := adjacentRoot_pos _ _ (divisor_pair_coprime n a b han hbn).symm ha
    exact hb.trans_le (Nat.le_of_dvd hp (adjacentRoot_dvd_left _ _ _))
  · simpa only [Nat.mul_comm] using adjacentRoot_lt b a
      (divisor_pair_coprime n a b han hbn).symm (by omega) (by omega)

lemma divisorReflection_structure (n a b : ℕ) (ha : a.Prime) (hb : b.Prime)
    (han : a ∣ n) (hbn : b ∣ n+1) :
    (Nat.maxPrimeFac (divisorReflection n a b) <
      Nat.maxPrimeFac (divisorReflection n a b+1) ↔ b < a) ∧
    primeWinner (divisorReflection n a b) = max a b := by
  have hm := divisorReflection_bounds n a b ha.one_lt hb.one_lt han hbn
  have h := prime_divisor_pair_bounds b a (divisorReflection n a b) hb ha
    (by omega) (by simpa only [Nat.mul_comm] using hm.2)
    (by rw [divisorReflection_eq_root n a b ha.one_lt hb.one_lt han hbn]
        exact adjacentRoot_dvd_left _ _ _)
    (by rw [divisorReflection_eq_root n a b ha.one_lt hb.one_lt han hbn]
        exact adjacentRoot_dvd_right _ _ _ ha.pos)
  exact ⟨h.1, h.2.1.trans (max_comm b a)⟩

def losingNumber (n : ℕ) : ℕ :=
  if Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1) then n else n+1

def leastLosingPrime (n : ℕ) : ℕ := (losingNumber n).minFac

def smallPrimeReflection (n : ℕ) : ℕ :=
  divisorReflection n (leastLosingPrime n) (primeWinner n)

lemma minFac_le_maxPrimeFac (n : ℕ) (hn : 1 < n) :
    n.minFac ≤ Nat.maxPrimeFac n := by
  exact Nat.le_maxPrimeFac (by omega) (Nat.minFac_prime (by omega)) (Nat.minFac_dvd n)

lemma leastLosingPrime_prime (n : ℕ) (hn : 1 < n) : (leastLosingPrime n).Prime := by
  unfold leastLosingPrime losingNumber
  split_ifs <;> exact Nat.minFac_prime (by omega)

lemma leastLosingPrime_lt_winner (n : ℕ) (hn : 1 < n) :
    leastLosingPrime n < primeWinner n := by
  unfold leastLosingPrime losingNumber primeWinner
  split_ifs with h
  · rw [max_eq_right h.le]
    exact (minFac_le_maxPrimeFac n hn).trans_lt h
  · rw [max_eq_left (not_lt.mp h)]
    exact (minFac_le_maxPrimeFac (n+1) (by omega)).trans_lt
      (lt_of_le_of_ne (not_lt.mp h) (consecutive_maxPrimeFac_ne n))

lemma smallPrimeReflection_rise (n : ℕ)
    (h : Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)) :
    smallPrimeReflection n = divisorReflection n n.minFac (Nat.maxPrimeFac (n+1)) := by
  simp [smallPrimeReflection, leastLosingPrime, losingNumber, primeWinner, h,
    max_eq_right h.le]

lemma smallPrimeReflection_fall (n : ℕ)
    (h : ¬Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)) :
    smallPrimeReflection n = divisorReflection n (Nat.maxPrimeFac n) (n+1).minFac := by
  simp [smallPrimeReflection, leastLosingPrime, losingNumber, primeWinner, h,
    max_eq_left (not_lt.mp h), divisorReflection, Nat.mul_comm]

lemma smallPrimeReflection_bounds (n : ℕ) (hn : 1 < n) :
    1 < smallPrimeReflection n ∧
      smallPrimeReflection n < leastLosingPrime n * primeWinner n := by
  by_cases h : Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)
  · rw [smallPrimeReflection_rise n h]
    simpa [leastLosingPrime, losingNumber, primeWinner, h, max_eq_right h.le] using
      divisorReflection_bounds n n.minFac (Nat.maxPrimeFac (n+1))
        (Nat.minFac_prime (by omega)).one_lt
        (Nat.prime_maxPrimeFac_of_one_lt (n+1) (by omega)).one_lt
        (Nat.minFac_dvd n) Nat.maxPrimeFac_dvd
  · rw [smallPrimeReflection_fall n h]
    simpa [leastLosingPrime, losingNumber, primeWinner, h, max_eq_left (not_lt.mp h),
      Nat.mul_comm] using
      divisorReflection_bounds n (Nat.maxPrimeFac n) (n+1).minFac
        (Nat.prime_maxPrimeFac_of_one_lt n hn).one_lt
        (Nat.minFac_prime (by omega)).one_lt
        Nat.maxPrimeFac_dvd (Nat.minFac_dvd (n+1))

theorem smallPrimeReflection_structure (n : ℕ) (hn : 1 < n) :
    (Nat.maxPrimeFac (smallPrimeReflection n) <
      Nat.maxPrimeFac (smallPrimeReflection n+1) ↔
      Nat.maxPrimeFac (n+1) < Nat.maxPrimeFac n) ∧
    primeWinner (smallPrimeReflection n) = primeWinner n := by
  by_cases h : Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)
  · have hab := (minFac_le_maxPrimeFac n hn).trans_lt h
    have hh := divisorReflection_structure n n.minFac (Nat.maxPrimeFac (n+1))
      (Nat.minFac_prime (by omega)) (Nat.prime_maxPrimeFac_of_one_lt (n+1) (by omega))
      (Nat.minFac_dvd n) Nat.maxPrimeFac_dvd
    rw [smallPrimeReflection_rise n h]
    simpa only [primeWinner, max_eq_right h.le, max_eq_right hab.le,
      hab.not_gt, h.not_gt] using hh
  · have h' : Nat.maxPrimeFac (n+1) < Nat.maxPrimeFac n :=
      lt_of_le_of_ne (not_lt.mp h) (consecutive_maxPrimeFac_ne n)
    have hab := (minFac_le_maxPrimeFac (n+1) (by omega)).trans_lt h'
    have hh := divisorReflection_structure n (Nat.maxPrimeFac n) (n+1).minFac
      (Nat.prime_maxPrimeFac_of_one_lt n hn) (Nat.minFac_prime (by omega))
      Nat.maxPrimeFac_dvd (Nat.minFac_dvd (n+1))
    rw [smallPrimeReflection_fall n h]
    simpa only [primeWinner, max_eq_left h'.le, max_eq_left hab.le, hab, h'] using hh

theorem smallPrimeReflection_sign (n : ℕ) (hn : 1 < n) :
    factorSign (smallPrimeReflection n) = -factorSign n := by
  have he := (smallPrimeReflection_structure n hn).1
  have hne := consecutive_maxPrimeFac_ne n
  unfold factorSign predicateSign
  simp only [he]
  rcases lt_or_gt_of_ne hne with h | h <;> simp [h, h.not_gt]

lemma leastLosingPrime_dvd_reflected_loser (n : ℕ) (hn : 1 < n) :
    leastLosingPrime n ∣ losingNumber (smallPrimeReflection n) := by
  have hs := (smallPrimeReflection_structure n hn).1
  by_cases h : Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)
  · have ha := (Nat.minFac_prime (by omega : n ≠ 1)).one_lt
    have hb := (Nat.prime_maxPrimeFac_of_one_lt (n+1) (by omega)).one_lt
    simp only [losingNumber, hs, h.not_gt, if_false]
    rw [smallPrimeReflection_rise n h,
      divisorReflection_eq_root n n.minFac (Nat.maxPrimeFac (n+1)) ha hb
        (Nat.minFac_dvd n) Nat.maxPrimeFac_dvd]
    simpa [leastLosingPrime, losingNumber, h] using
      adjacentRoot_dvd_right (Nat.maxPrimeFac (n+1)) n.minFac
        (divisor_pair_coprime n _ _ (Nat.minFac_dvd n) Nat.maxPrimeFac_dvd).symm
        (by omega)
  · have h' : Nat.maxPrimeFac (n+1) < Nat.maxPrimeFac n :=
      lt_of_le_of_ne (not_lt.mp h) (consecutive_maxPrimeFac_ne n)
    have ha := (Nat.prime_maxPrimeFac_of_one_lt n hn).one_lt
    have hb := (Nat.minFac_prime (by omega : n+1 ≠ 1)).one_lt
    simp only [losingNumber, hs, h', if_true]
    rw [smallPrimeReflection_fall n h,
      divisorReflection_eq_root n (Nat.maxPrimeFac n) (n+1).minFac ha hb
        Nat.maxPrimeFac_dvd (Nat.minFac_dvd (n+1))]
    simpa [leastLosingPrime, losingNumber, h] using
      adjacentRoot_dvd_left (n+1).minFac (Nat.maxPrimeFac n)
        (divisor_pair_coprime n _ _ Nat.maxPrimeFac_dvd (Nat.minFac_dvd (n+1))).symm

theorem leastLosingPrime_reflection_le (n : ℕ) (hn : 1 < n) :
    leastLosingPrime (smallPrimeReflection n) ≤ leastLosingPrime n := by
  exact Nat.minFac_le_of_dvd (leastLosingPrime_prime n hn).two_le
    (leastLosingPrime_dvd_reflected_loser n hn)

/-- Already in the smallest nontrivial group the reflection has collisions. -/
theorem smallPrimeReflection_not_injective : ¬Function.Injective smallPrimeReflection := by
  intro h
  have he : smallPrimeReflection 2 = smallPrimeReflection 8 := by decide +kernel
  have hn := h he
  omega

#print axioms smallPrimeReflection_structure
#print axioms smallPrimeReflection_sign
#print axioms leastLosingPrime_reflection_le
#print axioms smallPrimeReflection_not_injective
end Erdos371
