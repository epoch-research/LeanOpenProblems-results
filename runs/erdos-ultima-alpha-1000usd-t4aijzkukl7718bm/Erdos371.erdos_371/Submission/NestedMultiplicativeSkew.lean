import FormalConjecturesUtil

/-! An exact skew identity for two nested completely multiplicative indicators.
The allowed primes are NOT initial segments of the primes. This is not a
counterexample to Erdős 371. -/

namespace Erdos371.NestedMultiplicativeSkew
open Finset

/-- Only prime factors congruent to one modulo three are permitted. -/
def good (n : ℕ) : Prop := n ≠ 0 ∧ ∀ p ∈ n.primeFactors, p % 3 = 1
instance (n : ℕ) : Decidable (good n) := inferInstanceAs (Decidable (n ≠ 0 ∧ _))

def smallIndicator (n : ℕ) : ℕ := if good n then 1 else 0
def largeIndicator (n : ℕ) : ℕ := if 3 ∣ n then 0 else 1

lemma good_mul_iff (a b : ℕ) : good (a*b) ↔ good a ∧ good b := by
  by_cases ha : a = 0
  · subst a; simp [good]
  by_cases hb : b = 0
  · subst b; simp [good]
  constructor
  · intro h
    rw [good, Nat.primeFactors_mul ha hb] at h
    exact ⟨⟨ha, fun p hp => h.2 p (mem_union_left _ hp)⟩,
      ⟨hb, fun p hp => h.2 p (mem_union_right _ hp)⟩⟩
  · rintro ⟨h₁,h₂⟩
    refine ⟨mul_ne_zero ha hb, ?_⟩
    intro p hp
    rw [Nat.primeFactors_mul ha hb, mem_union] at hp
    exact hp.elim (h₁.2 p) (h₂.2 p)

lemma good_mod_three (n : ℕ) (hn : good n) : n % 3 = 1 := by
  have h : Nat.ModEq 3 (∏ p ∈ n.primeFactors, p^n.factorization p) 1 := by
    have hh := Nat.ModEq.prod (s := n.primeFactors)
      (f := fun p => p^n.factorization p) (g := fun p => 1^n.factorization p)
      (fun p hp => (show Nat.ModEq 3 p 1 from by simpa [Nat.ModEq] using hn.2 p hp).pow _)
    simpa using hh
  have he : (∏ p ∈ n.primeFactors, p^n.factorization p) = n :=
    Nat.factorization_prod_pow_eq_self hn.1
  rw [he] at h
  simpa [Nat.ModEq] using h

lemma smallIndicator_mul (a b : ℕ) :
    smallIndicator (a*b) = smallIndicator a*smallIndicator b := by
  simp only [smallIndicator,good_mul_iff]
  split_ifs <;> simp_all

lemma largeIndicator_mul (a b : ℕ) :
    largeIndicator (a*b) = largeIndicator a*largeIndicator b := by
  simp only [largeIndicator,Nat.prime_three.dvd_mul]
  split_ifs <;> simp_all

lemma indicators_nested (n : ℕ) : smallIndicator n ≤ largeIndicator n := by
  by_cases hn : good n
  · have hm := good_mod_three n hn
    have hnd : ¬3 ∣ n := by
      intro hd
      have hz := Nat.mod_eq_zero_of_dvd hd
      omega
    simp [smallIndicator,largeIndicator,hn,hnd]
  · simp [smallIndicator,hn]

/-- Every summand in the skew is nonnegative; no endpoint cancellation
has been omitted. The sign comes from the fixed residue restriction. -/
theorem point_skew (n : ℕ) :
    (smallIndicator n : ℤ)*largeIndicator (n+1) -
      (largeIndicator n : ℤ)*smallIndicator (n+1) = smallIndicator n := by
  have hleft : (smallIndicator n : ℤ)*largeIndicator (n+1) = smallIndicator n := by
    by_cases hn : good n
    · have hm := good_mod_three n hn
      have hnd : ¬3 ∣ n+1 := by
        intro hd
        have hz := Nat.mod_eq_zero_of_dvd hd
        omega
      simp [smallIndicator,largeIndicator,hn,hnd]
    · simp [smallIndicator,hn]
  have hright : (largeIndicator n : ℤ)*smallIndicator (n+1) = 0 := by
    by_cases hn : good (n+1)
    · have hm := good_mod_three (n+1) hn
      have hd : 3 ∣ n := Nat.dvd_of_mod_eq_zero (by omega)
      simp [largeIndicator,hd]
    · simp [smallIndicator,hn]
  rw [hleft,hright,sub_zero]

/-- The whole skew is exactly the count of the smaller multiplicative set. -/
theorem prefix_skew (N : ℕ) :
    (∑ n ∈ range N, ((smallIndicator (n+1) : ℤ)*largeIndicator (n+2) -
      (largeIndicator (n+1) : ℤ)*smallIndicator (n+2))) =
      ((range N).filter fun n => good (n+1)).card := by
  simp_rw [show ∀ n : ℕ, n+2=(n+1)+1 from fun n => by omega,point_skew]
  simp [smallIndicator]

/-- A small kernel-checked example of the exact identity. -/
lemma good_count_one_hundred :
    ((range 100).filter fun n => good (n+1)).card = 14 := by
  decide +kernel

lemma prefix_skew_one_hundred :
    (∑ n ∈ range 100, ((smallIndicator (n+1) : ℤ)*largeIndicator (n+2) -
      (largeIndicator (n+1) : ℤ)*smallIndicator (n+2))) = 14 := by
  rw [prefix_skew,good_count_one_hundred]
  norm_num

/-- The smaller indicator cannot be obtained from any largest-prime cutoff. -/
lemma small_not_initial_segment :
    ¬ ∃ B : ℕ, ∀ n : ℕ, smallIndicator n = if Nat.maxPrimeFac n ≤ B then 1 else 0 := by
  rintro ⟨B,h⟩
  have h₂ := h 2
  have h₇ := h 7
  have hs₂ : smallIndicator 2 = 0 := by decide +kernel
  have hs₇ : smallIndicator 7 = 1 := by decide +kernel
  rw [hs₂,Nat.prime_two.maxPrimeFac_eq_self] at h₂
  rw [hs₇,(show Nat.Prime 7 by norm_num).maxPrimeFac_eq_self] at h₇
  split_ifs at h₂ h₇; omega

/-- The larger indicator omits 3 but includes 5, so is not an initial segment either. -/
lemma large_not_initial_segment :
    ¬ ∃ C : ℕ, ∀ n : ℕ, largeIndicator n = if Nat.maxPrimeFac n ≤ C then 1 else 0 := by
  rintro ⟨C,h⟩
  have h₃ := h 3
  have h₅ := h 5
  have hs₃ : largeIndicator 3 = 0 := by decide +kernel
  have hs₅ : largeIndicator 5 = 1 := by decide +kernel
  rw [hs₃,Nat.prime_three.maxPrimeFac_eq_self] at h₃
  rw [hs₅,(show Nat.Prime 5 by norm_num).maxPrimeFac_eq_self] at h₅
  split_ifs at h₃ h₅; omega

#print axioms prefix_skew_one_hundred
#print axioms small_not_initial_segment
#print axioms large_not_initial_segment

#print axioms smallIndicator_mul
#print axioms largeIndicator_mul
#print axioms indicators_nested
#print axioms prefix_skew
end Erdos371.NestedMultiplicativeSkew
