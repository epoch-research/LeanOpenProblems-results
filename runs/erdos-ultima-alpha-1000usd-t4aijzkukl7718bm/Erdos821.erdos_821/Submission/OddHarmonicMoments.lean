import Submission.HarmonicDivisorLower

/-!
# Harmonic divisor moments on odd inputs

Removing the power of two costs at most 2^k in the harmonic moment of order
k. The resulting factorial lower bound concerns integers, not shifted primes.
-/

open Nat Filter ArithmeticFunction
open scoped Classical BigOperators ArithmeticFunction.zeta Topology

namespace Erdos821.HigherDivisors

noncomputable def oddHarmonicMoment (k A : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 A).filter Odd, (tau k n : ℝ)/(n : ℝ)

lemma oddHarmonicMoment_nonneg (k A : ℕ) : 0 ≤ oddHarmonicMoment k A := by
  apply Finset.sum_nonneg
  intro n hn
  positivity

lemma hasSum_two_power_tau (k : ℕ) :
    HasSum (fun a : ℕ => (tau (k+1) (2^a) : ℝ)/(2 : ℝ)^a) ((2 : ℝ)^(k+1)) := by
  have h := hasSum_choose_mul_geometric_of_norm_lt_one k (r := (1/2 : ℝ)) (by norm_num)
  convert h using 1
  · funext a
    rw [tau_prime_pow k a 2 Nat.prime_two]
    simp [div_eq_mul_inv, inv_pow]
  · rw [show (1 : ℝ)-1/2 = 1/2 by norm_num]
    simp [one_div, ← inv_pow]

lemma two_power_tau_sum_le (k A : ℕ) :
    (∑ a ∈ Finset.range (A+1), (tau (k+1) (2^a) : ℝ)/(2 : ℝ)^a) ≤ (2 : ℝ)^(k+1) := by
  have h := hasSum_two_power_tau k
  exact h.tsum_eq ▸ h.summable.sum_le_tsum _ (fun a _ => by positivity)

lemma harmonicMoment_le_two_pow_odd (k A : ℕ) :
    harmonicMoment (k+1) A ≤ (2 : ℝ)^(k+1) * oddHarmonicMoment (k+1) A := by
  let F : ℕ → ℕ × ℕ := fun n => (n.factorization 2, n/2^(n.factorization 2))
  let S := (Finset.Icc 1 A).filter Odd
  let w : ℕ × ℕ → ℝ := fun ab =>
    ((tau (k+1) (2^ab.1) : ℝ)/(2 : ℝ)^ab.1) * ((tau (k+1) ab.2 : ℝ)/(ab.2 : ℝ))
  have reconstruct (n : ℕ) : 2^(F n).1*(F n).2 = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have hi : Function.Injective F := by
    intro n m h
    calc
      n = 2^(F n).1*(F n).2 := (reconstruct n).symm
      _ = 2^(F m).1*(F m).2 := by rw [h]
      _ = m := reconstruct m
  have hmap : (Finset.Icc 1 A).image F ⊆ Finset.range (A+1) ×ˢ S := by
    intro ab hab
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hab
    obtain ⟨hn1, hnA⟩ := Finset.mem_Icc.mp hn
    have hn0 : n ≠ 0 := by omega
    have ha : n.factorization 2 ≤ A :=
      Nat.factorization_le_of_le_pow (hnA.trans Nat.lt_two_pow_self.le)
    have hb : 0 < n/2^(n.factorization 2) := Nat.ordCompl_pos 2 hn0
    have ho : Odd (n/2^(n.factorization 2)) :=
      Nat.coprime_two_right.mp (Nat.coprime_ordCompl Nat.prime_two hn0).symm
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by dsimp [F]; omega),
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hb,
        (Nat.div_le_self n _).trans hnA⟩, ho⟩⟩
  have he : harmonicMoment (k+1) A = ∑ ab ∈ (Finset.Icc 1 A).image F, w ab := by
    rw [Finset.sum_image hi.injOn]
    unfold harmonicMoment
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
    have hc := (Nat.coprime_ordCompl Nat.prime_two hn0).pow_left (n.factorization 2)
    have ht := tau_mul_coprime (k+1) hc
    have hr := reconstruct n
    change tau (k+1) (2^(F n).1*(F n).2) =
      tau (k+1) (2^(F n).1)*tau (k+1) (F n).2 at ht
    change _ = ((tau (k+1) (2^(F n).1) : ℝ)/(2 : ℝ)^(F n).1) *
      ((tau (k+1) (F n).2 : ℝ)/((F n).2 : ℝ))
    conv_lhs => rw [← hr, ht, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    ring
  rw [he]
  calc
    _ ≤ ∑ ab ∈ Finset.range (A+1) ×ˢ S, w ab :=
      Finset.sum_le_sum_of_subset_of_nonneg hmap (fun ab _ _ => by dsimp [w]; positivity)
    _ = (∑ a ∈ Finset.range (A+1), (tau (k+1) (2^a) : ℝ)/(2 : ℝ)^a) *
        oddHarmonicMoment (k+1) A := by
      simp only [w, Finset.sum_product, oddHarmonicMoment, S, Finset.sum_mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_right (two_power_tau_sum_le k A) (oddHarmonicMoment_nonneg _ _)

/-- A factorial-scale lower bound on odd inputs, with the exact parity
factor retained. -/
theorem oddHarmonicMoment_factorial_lower (k A : ℕ) (hA : 1 ≤ A) :
    (Real.log (A+1 : ℝ))^k/((2 : ℝ)^k*(k.factorial : ℝ)) ≤ oddHarmonicMoment k A := by
  cases k with
  | zero =>
    simp [oddHarmonicMoment, tau, ArithmeticFunction.one_apply, ite_div, hA]
  | succ k =>
    have hl := harmonicMoment_factorial_lower (k+1) A hA
    have hu := harmonicMoment_le_two_pow_odd k A
    have hp : (0 : ℝ) < 2^(k+1) := by positivity
    rw [mul_comm] at hu
    have h := (div_le_iff₀ hp).mpr (hl.trans hu)
    convert h using 1
    rw [div_div]
    congr 1
    ring

end Erdos821.HigherDivisors
