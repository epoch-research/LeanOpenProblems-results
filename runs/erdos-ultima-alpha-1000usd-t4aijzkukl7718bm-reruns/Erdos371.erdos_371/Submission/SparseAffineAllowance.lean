import FormalConjecturesUtil
import Submission.TwoSidedPrimeDeletion
import Submission.ReflectionRange
import Submission.TerminalCompression

/-! A sufficient affine-prefix bound with sparse allowances. The required
prefix bounds are hypotheses, not unconditional estimates for Erdős 371. -/

namespace Erdos371SparseAffineAllowance

open Finset Filter Erdos371PrimeDeletion Erdos371TwoSidedPrimeDeletion
open Erdos371ReflectionRange Erdos371TerminalCompression

/-- Ordered pairs of primes with product at most `N` have multiplicity at most
two over their product. -/
lemma sum_primeCounting_div_le (N : ℕ) :
    (∑ p ∈ N.primesBelow, Nat.primeCounting (N/p)) ≤ 2*N := by
  let S : Finset (Σ _ : ℕ, ℕ) :=
    N.primesBelow.sigma (fun p => (N/p+1).primesBelow)
  have hS : S.card = ∑ p ∈ N.primesBelow, Nat.primeCounting (N/p) := by
    simp only [S, Finset.card_sigma, Nat.primesBelow_card_eq_primeCounting']
    rfl
  let f : (Σ _ : ℕ, ℕ) → ℕ × Bool := fun z => (z.1*z.2, decide (z.1 < z.2))
  have hc : S.card ≤ ((Icc 1 N).product (univ : Finset Bool)).card := by
    apply Finset.card_le_card_of_injOn f
    · intro z hz
      obtain ⟨hpS, hqS⟩ := mem_sigma.mp hz
      obtain ⟨hpN, hp⟩ := Nat.mem_primesBelow.mp hpS
      obtain ⟨hqN, hq⟩ := Nat.mem_primesBelow.mp hqS
      have hqle : z.2 ≤ N/z.1 := by omega
      have hprod : z.1*z.2 ≤ N := by
        simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hp.pos).mp hqle
      exact mem_product.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hp.pos hq.pos, hprod⟩, mem_univ _⟩
    · intro z hz w hw he
      obtain ⟨hpS, hqS⟩ := mem_sigma.mp hz
      obtain ⟨hrS, hsS⟩ := mem_sigma.mp hw
      have hp := Nat.prime_of_mem_primesBelow hpS
      have hq := Nat.prime_of_mem_primesBelow hqS
      have hr := Nat.prime_of_mem_primesBelow hrS
      have hs := Nat.prime_of_mem_primesBelow hsS
      have hprod : z.1*z.2 = w.1*w.2 := congrArg Prod.fst he
      have hord : decide (z.1 < z.2) = decide (w.1 < w.2) := congrArg Prod.snd he
      obtain ⟨h1, h2⟩ := prime_factors_determined_by_product_and_order hp hq hr hs hprod (decide_eq_decide.mp hord)
      exact Sigma.ext h1 (heq_of_eq h2)
  rw [hS] at hc
  simpa [Nat.mul_comm] using hc

lemma sum_prime_square_allowance_le (N : ℕ) :
    (∑ p ∈ N.primesBelow, ((N/p : ℕ) : ℝ)/(p:ℝ)) ≤ 2*N := by
  have hs : (∑ p ∈ N.primesBelow, 1/(p:ℝ)^2) ≤ 2 := by
    have hsub : N.primesBelow ⊆ Ico 1 N := by
      intro p hp
      have hh := Nat.mem_primesBelow.mp hp
      exact mem_Ico.mpr ⟨hh.2.pos, hh.1⟩
    exact (sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)).trans
      (by simpa using sum_reciprocal_sq (K := 1) (by omega) N)
  calc
    _ ≤ ∑ p ∈ N.primesBelow, (N:ℝ)/(p:ℝ)/(p:ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact div_le_div_of_nonneg_right Nat.cast_div_le (Nat.cast_nonneg p)
    _ = (N:ℝ)*(∑ p ∈ N.primesBelow, 1/(p:ℝ)^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ (N:ℝ)*2 := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg N)
    _ = _ := by ring

lemma primesBelow_card_le (N : ℕ) : N.primesBelow.card ≤ N := by
  have hsub : N.primesBelow ⊆ range N := fun p hp => mem_range.mpr (Nat.mem_primesBelow.mp hp).1
  simpa using Finset.card_le_card hsub

lemma sum_allowance_le {C D E : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E) (N : ℕ) :
    (∑ p ∈ N.primesBelow, (C*((N/p : ℕ) : ℝ)/(p:ℝ) + D*Nat.primeCounting (N/p) + E)) ≤
      (2*C+2*D+E)*N := by
  have h1 := mul_le_mul_of_nonneg_left (sum_prime_square_allowance_le N) hC
  have h2 : (∑ p ∈ N.primesBelow, (Nat.primeCounting (N/p):ℝ)) ≤ 2*N := by
    exact_mod_cast sum_primeCounting_div_le N
  have h3 : (N.primesBelow.card:ℝ) ≤ N := Nat.cast_le.mpr (primesBelow_card_le N)
  simp only [sum_add_distrib, mul_div_assoc, ← mul_sum, sum_const, nsmul_eq_mul]
  nlinarith [mul_le_mul_of_nonneg_left h2 hD, mul_le_mul_of_nonneg_right h3 hE]

/-- Both affine prefix sums may have allowances of size `A/p`, `π(A)`, and a
constant, with uniform coefficients. Such bounds would suffice, but are not
proved in this file. -/
theorem density_half_of_sparse_prefix_allowance {C D E : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hm : ∀ p : ℕ, p.Prime → ∀ A : ℕ,
      (∑ a ∈ Icc 1 A, Erdos371PrimeDeletion.compare (P (a*p-1)) (P a)) ≤ C*A/p + D*Nat.primeCounting A + E)
    (hp : ∀ p : ℕ, p.Prime → ∀ A : ℕ,
      (∑ a ∈ Icc 1 A, Erdos371PrimeDeletion.compare (P (a*p+1)) (P a)) ≤ C*A/p + D*Nat.primeCounting A + E) :
    {n | Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)}.HasDensity (1/2) := by
  apply density_half_of_affine_upper_bounds (2*C+2*D+E)
  apply Eventually.of_forall
  intro N
  constructor
  · exact (sum_le_sum (fun p hp => hm p (Nat.prime_of_mem_primesBelow hp) (N/p))).trans
      (sum_allowance_le hC hD hE N)
  · exact (sum_le_sum (fun p hp' => hp p (Nat.prime_of_mem_primesBelow hp') (N/p))).trans
      (sum_allowance_le hC hD hE N)

end Erdos371SparseAffineAllowance

#print axioms Erdos371SparseAffineAllowance.sum_primeCounting_div_le
#print axioms Erdos371SparseAffineAllowance.density_half_of_sparse_prefix_allowance
