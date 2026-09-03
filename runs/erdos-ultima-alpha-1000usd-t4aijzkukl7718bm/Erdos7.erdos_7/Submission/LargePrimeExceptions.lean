import Submission.SharpWeightedExceptionArithmetic

/-! Unconditional consequences of the sharper weighted exception bound.
These exclude restricted near-covers, not arbitrary odd covering systems. -/
namespace Erdos7LargePrimeExceptions
open scoped BigOperators
open Erdos7WeightedExceptionArithmetic
set_option autoImplicit false
set_option maxHeartbeats 4000000

lemma prime_weight_le (q R : ℕ) (hq : q.Prime) (hR : 0 < R) (hRq : R ≤ q) :
    weight q ≤ (5 : ℚ)/(4*R) := by
  rw [weight,hq.primeFactors,Finset.card_singleton,pow_one]
  have hR0 : (0 : ℚ) < R := by exact_mod_cast hR
  have hRq' : (R : ℚ) ≤ q := by exact_mod_cast hRq
  have hh := div_le_div_of_nonneg_left (by norm_num : (0 : ℚ) ≤ 5/4) hR0 hRq'
  simpa only [div_div] using hh

/-- Exceptional moduli may be arbitrary, provided each has a sufficiently
large prime divisor. They need not be distinct, odd, or prime to three. -/
theorem not_cover_large_prime_exceptions {I J : Type*} [Fintype I] [Fintype J]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i)
    (d : J → ℕ) (b : J → ℤ) (q : J → ℕ) (hq : ∀ j, (q j).Prime)
    (hqd : ∀ j, q j ∣ d j) (R : ℕ) (hR : 5 ≤ R) (hRq : ∀ j, R ≤ q j)
    (hsize : 625*Fintype.card J ≤ 281*R) :
    ¬ (∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-a i) ∨ ∃ j, (d j : ℤ) ∣ x-b j) := by
  classical
  have hqodd (j : J) : Odd (q j) :=
    (hq j).odd_of_ne_two (by have := hRq j; omega)
  have hq3 (j : J) : ¬ 3 ∣ q j := by
    intro hh
    have hj := hRq j
    rcases (Nat.dvd_prime (hq j)).mp hh with hh | hh <;> omega
  have hweight : (∑ j, weight (q j)) ≤ (281/500 : ℚ) := by
    calc
      (∑ j, weight (q j)) ≤ ∑ _j : J, (5 : ℚ)/(4*R) :=
        Finset.sum_le_sum (fun j _ => prime_weight_le (q j) R (hq j) (by omega) (hRq j))
      _ = (Fintype.card J : ℚ)*((5 : ℚ)/(4*R)) := by simp
      _ ≤ 281/500 := by
        have hR0 : (0 : ℚ) < R := by exact_mod_cast (show 0 < R by omega)
        have hs : (625 : ℚ)*Fintype.card J ≤ 281*R := by exact_mod_cast hsize
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (by positivity : (0 : ℚ) < 4*R)).mpr
        nlinarith
  intro hc
  apply Erdos7SharpWeightedExceptionArithmetic.not_cover_with_weighted_exceptions
    m a hinj hm h3 q b (fun j => ⟨(hq j).pos,hqodd j⟩) hq3 hweight
  intro x
  rcases hc x with ⟨i,hi⟩ | ⟨j,hj⟩
  · exact Or.inl ⟨i,hi⟩
  · exact Or.inr ⟨j,(Int.natCast_dvd_natCast.mpr (hqd j)).trans hj⟩

/-- Three exceptional classes are excluded whenever each modulus has a prime
factor at least seven. This does NOT include three extra modulus-five classes. -/
theorem not_cover_three_exceptions {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i)
    (d : Fin 3 → ℕ) (b : Fin 3 → ℤ)
    (hex : ∀ j, ∃ p, p.Prime ∧ p ∣ d j ∧ 7 ≤ p) :
    ¬ (∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-a i) ∨ ∃ j, (d j : ℤ) ∣ x-b j) := by
  classical
  choose q hq hqd hRq using hex
  exact not_cover_large_prime_exceptions m a hinj hm h3 d b q hq hqd
    7 (by decide) hRq (by norm_num)

#print axioms prime_weight_le
#print axioms not_cover_large_prime_exceptions
#print axioms not_cover_three_exceptions
end Erdos7LargePrimeExceptions
