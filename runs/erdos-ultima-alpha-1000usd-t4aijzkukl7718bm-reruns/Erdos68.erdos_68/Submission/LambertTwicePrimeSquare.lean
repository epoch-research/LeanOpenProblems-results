import Submission.LambertPrimeScaling
import Submission.CarriedSquareCongruenceBarrier

/-!
A congruence modulo the square of a prime for the original Lambert
coefficients. This auxiliary fact is not a settlement of Erdős 68.
-/

namespace LambertTwicePrimeSquare

open Erdos68Development LambertPrimeScaling

lemma central_choose_mod_square (p : ℕ) (hp : p.Prime) :
    Nat.ModEq (p^2) ((2*p).choose p) 2 := by
  have hp0 := hp.pos
  have hsum : (2*p).choose p =
      (∑ k ∈ Finset.range (p-1), p.choose (k+1) * p.choose (p-(k+1))) + 2 := by
    rw [show 2*p = p+p by omega, Nat.add_choose_eq,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => p.choose i * p.choose j) p,
      Finset.sum_range_succ]
    have hr := Finset.sum_range_succ'
      (fun k => p.choose k * p.choose (p-k)) (p-1)
    simp only [Nat.sub_add_cancel hp0, Nat.choose_zero_right, Nat.sub_zero,
      Nat.choose_self, one_mul] at hr
    rw [hr]
    simp
  rw [hsum]
  have hs : Nat.ModEq (p^2)
      (∑ k ∈ Finset.range (p-1), p.choose (k+1) * p.choose (p-(k+1))) 0 := by
    apply Nat.modEq_zero_iff_dvd.mpr
    apply Finset.dvd_sum
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have h1 := hp.dvd_choose_self (show k+1 ≠ 0 by omega) (show k+1 < p by omega)
    have h2 := hp.dvd_choose_self (show p-(k+1) ≠ 0 by omega)
      (show p-(k+1) < p by omega)
    simpa only [pow_two] using Nat.mul_dvd_mul h1 h2
  simpa using hs.add (Nat.ModEq.refl 2)

lemma divisors_twice_prime (p : ℕ) (hp : p.Prime) :
    (2*p).divisors = {1, 2, p, 2*p} := by
  ext d
  simp only [Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hd, _⟩
    obtain ⟨a,b,ha,hb,hab⟩ := Nat.dvd_mul.mp hd
    rcases (Nat.dvd_prime Nat.prime_two).mp ha with rfl | rfl <;>
      rcases (Nat.dvd_prime hp).mp hb with rfl | rfl <;> simp_all
  · intro h
    refine ⟨?_, by have := hp.pos; omega⟩
    rcases h with rfl | rfl | rfl | rfl <;> simp

lemma twice_prime_formula (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    lambertCoeff (2*p) = (2*p).factorial / 2^p + (2*p).choose p + 1 := by
  have hp2 : 2 < p := by have := hp.two_le; omega
  have h2p : p < 2*p := by omega
  rw [lambertCoeff, divisors_twice_prime p hp]
  rw [Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp; omega),
    Finset.sum_insert (by simp; omega), Finset.sum_singleton]
  simp only [show ¬2 ≤ (1 : ℕ) by omega, show 2 ≤ p by omega,
    show 2 ≤ 2*p by omega, show 2 ≤ (2 : ℕ) by omega, if_false, if_true,
    zero_add, Nat.factorial_two, Nat.mul_div_cancel_left p (by decide : 0 < 2),
    Nat.mul_div_cancel 2 hp.pos, Nat.div_self (by positivity : 0 < 2*p),
    pow_one, Nat.div_self (Nat.factorial_pos (2*p))]

  rw [show 2*p = p+p by omega, Nat.add_choose, pow_two]
  omega

lemma square_dvd_twice_factorial (p : ℕ) (hp : p.Prime) :
    p^2 ∣ (2*p).factorial := by
  have h := Nat.mul_dvd_mul (Nat.dvd_factorial hp.pos (le_refl p))
    (Nat.dvd_factorial hp.pos (le_refl p))
  have h' := h.trans (Nat.factorial_mul_factorial_dvd_factorial_add p p)
  simpa only [pow_two, two_mul] using h'

lemma square_dvd_two_row (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    p^2 ∣ (2*p).factorial / 2^p := by
  have hc : (p^2).Coprime (2^p) :=
    Nat.coprime_pow_primes 2 p hp Nat.prime_two hodd
  have hd : 2^p ∣ (2*p).factorial := by
    simpa only [Nat.factorial_two] using factorial_pow_dvd_factorial_mul 2 p
  have he := Nat.mul_div_cancel' hd
  apply hc.dvd_of_dvd_mul_left
  rw [he]
  exact square_dvd_twice_factorial p hp

/-- For odd primes, the original twice-prime coefficient is three modulo p².
This is a statement about the original coefficients, not any carried sequence. -/
theorem lambertCoeff_twice_prime_square (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    Nat.ModEq (p^2) (lambertCoeff (2*p)) 3 := by
  rw [twice_prime_formula p hp hodd]
  simpa using ((Nat.modEq_zero_iff_dvd.mpr (square_dvd_two_row p hp hodd)).add
    (central_choose_mod_square p hp)).add (Nat.ModEq.refl 1)

/-- The existing small-tail carry necessarily changes this square congruence
when the predecessor is composite. No rationality assumption is needed. -/
theorem carried_twice_prime_square_defect (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (hcomp : ¬(2*p-1).Prime) :
    ¬(p : ℤ)^2 ∣ CongruencePreservingCarry.coeff (2*p) - lambertCoeff (2*p) := by
  have h0 : (p : ℤ)^2 ∣ (lambertCoeff (2*p) : ℤ)-3 := by
    have h := Nat.modEq_iff_dvd.mp
      (lambertCoeff_twice_prime_square p hp (by omega)).symm
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using h
  intro hd
  apply CarriedSquareCongruenceBarrier.twice_square_not_congruent p hp7 hcomp
  convert dvd_add hd h0 using 1
  ring

#print axioms lambertCoeff_twice_prime_square
#print axioms carried_twice_prime_square_defect

end LambertTwicePrimeSquare
