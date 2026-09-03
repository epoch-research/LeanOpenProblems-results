import Submission.SharpCompositeGain
import Submission.HarmonicDivisorLower

/-!
# Harmonic divisor weights with exact prime support

The estimates in this file are over integers. They do not assert the
corresponding lower estimates on shifted primes.
-/

open Nat Finset Filter
open scoped Classical BigOperators
namespace Erdos821.HigherDivisors
set_option maxHeartbeats 3000000

lemma hasSum_prime_power_tau (k p : ℕ) (hp : p.Prime) :
    HasSum (fun e : ℕ => (tau (k+1) (p^e) : ℝ)/(p : ℝ)^e)
      (1/(1-(p : ℝ)⁻¹)^(k+1)) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hr : ‖(p : ℝ)⁻¹‖ < 1 := by
    rw [Real.norm_of_nonneg (inv_nonneg.mpr hp0.le)]
    exact (inv_lt_one₀ hp0).mpr hp1
  convert hasSum_choose_mul_geometric_of_norm_lt_one k hr using 1
  funext e
  rw [tau_prime_pow k e p hp]
  simp only [div_eq_mul_inv, inv_pow]

lemma positive_prime_power_tau_sum_le (k p z : ℕ) (hp : p.Prime) :
    (∑ e ∈ Icc 1 z, (tau (k+1) (p^e) : ℝ)/(p : ℝ)^e) ≤
      1/(1-(p : ℝ)⁻¹)^(k+1)-1 := by
  have hh := hasSum_prime_power_tau k p hp
  have hle := hh.summable.sum_le_tsum (insert 0 (Icc 1 z))
    (fun e _ => by positivity : ∀ e ∉ insert 0 (Icc 1 z),
      0 ≤ (tau (k+1) (p^e) : ℝ)/(p : ℝ)^e)
  rw [hh.tsum_eq, sum_insert (by simp : 0 ∉ Icc 1 z)] at hle
  have hzero : (tau (k+1) (p^0) : ℝ)/(p : ℝ)^0 = 1 := by
    simp only [pow_zero, div_one]
    exact_mod_cast (tau_multiplicative (k+1)).map_one
  rw [hzero] at hle
  linarith

lemma sum_exact_prime_support_tau_le (k z : ℕ) (S A : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime)
    (hA : ∀ n ∈ A, 0 < n ∧ n ≤ z ∧ n.primeFactors = S) :
    (∑ n ∈ A, (tau (k+1) n : ℝ)/(n : ℝ)) ≤
      ∏ p ∈ S, (1/(1-(p : ℝ)⁻¹)^(k+1)-1) := by
  let F : ℕ → (S → ℕ) := fun n p => n.factorization p
  let B := Fintype.piFinset (fun _ : S => Icc 1 z)
  let w : (S → ℕ) → ℝ := fun e => ∏ p : S,
    (tau (k+1) ((p : ℕ)^(e p)) : ℝ)/((p : ℕ) : ℝ)^(e p)
  have hrec (n : ℕ) (hn : n ∈ A) : ∏ p : S, (p : ℕ)^((F n) p) = n := by
    dsimp only [F]
    rw [Finset.prod_coe_sort S (fun p : ℕ => p^(n.factorization p))]
    change (∏ p ∈ S, p^(n.factorization p)) = n
    rw [← (hA n hn).2.2]
    simpa only [Finsupp.prod, Nat.support_factorization] using
      Nat.factorization_prod_pow_eq_self (hA n hn).1.ne'
  have hinj : Set.InjOn F (A : Set ℕ) := by
    intro n hn m hm he
    rw [← hrec n hn, ← hrec m hm, he]
  have hmap : A.image F ⊆ B := by
    intro e he
    obtain ⟨n, hn, rfl⟩ := mem_image.mp he
    apply Fintype.mem_piFinset.mpr
    intro p
    have hp := hS p p.property
    have hpN : (p : ℕ) ∈ n.primeFactors := (hA n hn).2.2.symm ▸ p.property
    apply mem_Icc.mpr
    refine ⟨hp.factorization_pos_of_dvd (hA n hn).1.ne'
      (Nat.dvd_of_mem_primeFactors hpN), ?_⟩
    apply Nat.factorization_le_of_le_pow
    exact (hA n hn).2.1.trans (Nat.lt_two_pow_self.le.trans
      (Nat.pow_le_pow_left hp.two_le z))
  have he (n : ℕ) (hn : n ∈ A) : (tau (k+1) n : ℝ)/(n : ℝ) = w (F n) := by
    dsimp only [w]
    rw [Finset.prod_div_distrib]
    have hden : (∏ p : S, ((p : ℕ) : ℝ)^((F n) p)) = (n : ℝ) := by
      exact_mod_cast hrec n hn
    rw [hden]
    congr 1
    dsimp only [F]
    rw [tau_factorization (k+1) n (hA n hn).1.ne', (hA n hn).2.2,
      Nat.cast_prod, Finset.prod_coe_sort S (fun p : ℕ => (tau (k+1) (p^(n.factorization p)) : ℝ))]
  calc
    _ = ∑ e ∈ A.image F, w e := by
      rw [sum_image hinj]
      exact sum_congr rfl he
    _ ≤ ∑ e ∈ B, w e := sum_le_sum_of_subset_of_nonneg hmap
      (fun e _ _ => by dsimp [w]; positivity)
    _ = ∏ p : S, ∑ e ∈ Icc 1 z,
        (tau (k+1) ((p : ℕ)^e) : ℝ)/((p : ℕ) : ℝ)^e := by
      exact Finset.sum_prod_piFinset (Icc 1 z)
        (fun (p : S) (e : ℕ) => (tau (k+1) ((p : ℕ)^e) : ℝ)/((p : ℕ) : ℝ)^e)
    _ ≤ ∏ p : S, (1/(1-((p : ℕ) : ℝ)⁻¹)^(k+1)-1) := by
      apply Finset.prod_le_prod
      · intro p _; positivity
      · intro p _
        exact positive_prime_power_tau_sum_le k p z (hS p p.property)
    _ = _ := Finset.prod_coe_sort S
      (fun p : ℕ => (1/(1-(p : ℝ)⁻¹)^(k+1)-1))

lemma two_prime_power_factor_le (p : ℕ) (hp : 2 < p) :
    1/(1-(p : ℝ)⁻¹)^2-1 ≤ (2 : ℝ)/((p : ℝ)-2) := by
  have hpR : (2 : ℝ) < p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have h1 : 0 < (p : ℝ)-1 := by linarith
  have h2 : 0 < (p : ℝ)-2 := by linarith
  have hid : 1/(1-(p : ℝ)⁻¹)^2-1 = (2*(p : ℝ)-1)/((p : ℝ)-1)^2 := by
    field_simp
    ring
  rw [hid]
  apply (div_le_div_iff₀ (sq_pos_of_pos h1) h2).mpr
  nlinarith only [hpR]

end Erdos821.HigherDivisors
