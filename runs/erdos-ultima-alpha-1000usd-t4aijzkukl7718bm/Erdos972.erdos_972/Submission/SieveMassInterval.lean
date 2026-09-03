import Submission.SieveMassUpper

/-! Short multiplicative-interval bounds for the Selberg normalizing sum,
and the resulting upper bounds on individual local sieve costs. -/
namespace Erdos972SieveMassInterval

open Finset ArithmeticFunction
open Erdos972SelbergWeights Erdos972SelbergLocalCost Erdos972SieveMassUpper

set_option maxHeartbeats 1500000

lemma sum_multiples_Ioc {p : ℕ} (hp : 0 < p) {L R : ℕ} (hLR : L ≤ R) (f : ℕ → ℝ) :
    (∑ n ∈ Ioc L R, if p ∣ n then f n else 0) = ∑ k ∈ Ioc (L/p) (R/p), f (p*k) := by
  have h₁ := sum_Ioc_consecutive (fun n => if p ∣ n then f n else 0) (Nat.zero_le L) hLR
  have h₂ := sum_Ioc_consecutive (fun k => f (p*k)) (Nat.zero_le (L/p)) (Nat.div_le_div_right hLR)
  rw [sum_multiples hp L, sum_multiples hp R] at h₁
  linarith only [h₁, h₂]

lemma reciprocal_Ioc_bound {b p : ℕ} (hp : 0 < p) :
    (∑ k ∈ Ioc (b/p) b, (1:ℝ)/k) ≤ 1+Real.log p := by
  by_cases hb : b = 0
  · simp only [hb, Nat.zero_div, Ioc_self, sum_empty]
    positivity [Real.log_natCast_nonneg p]
  have hbR : (0:ℝ) < b := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hb)
  have hpR : (0:ℝ) < p := Nat.cast_pos.mpr hp
  have he : (∑ k ∈ Ioc (b/p) b, (1:ℝ)/k) = (harmonic b : ℝ)-harmonic (b/p) := by
    have h := sum_Ioc_consecutive (fun k : ℕ => (1:ℝ)/k) (Nat.zero_le (b/p)) (Nat.div_le_self b p)
    have hsum (x : ℕ) : (∑ k ∈ Ioc 0 x, (1:ℝ)/k) = (harmonic x : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
      rfl
    rw [hsum, hsum] at h
    linarith only [h]
  rw [he]
  have hu := harmonic_le_one_add_log b
  have hl := log_le_harmonic_floor ((b:ℝ)/p) (by positivity)
  rw [Nat.floor_div_natCast, Nat.floor_natCast, Real.log_div hbR.ne' hpR.ne'] at hl
  linarith only [hu, hl]

lemma divisor_sum_prefix {n R : ℕ} (hn : 0 < n) (hnR : n ≤ R) :
    (∑ d ∈ n.divisors, sieveAtom d) = ∑ d ∈ Ioc 0 R, if d ∣ n then sieveAtom d else 0 := by
  rw [← sum_filter]
  congr 1
  ext d
  simp only [Nat.mem_divisors, mem_filter, mem_Ioc]
  constructor
  · rintro ⟨hdn, _⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hdn hn, (Nat.le_of_dvd hn hdn).trans hnR⟩, hdn⟩
  · rintro ⟨_, hdn⟩
    exact ⟨hdn, hn.ne'⟩

lemma sieveAtom_Ioc_bound {R p : ℕ} (hp : 0 < p) :
    (∑ n ∈ Ioc (R/p) R, sieveAtom n) ≤ 3*(1+Real.log p) := by
  have hlog : 0 ≤ 1+Real.log p := by positivity [Real.log_natCast_nonneg p]
  calc
    _ ≤ ∑ n ∈ Ioc (R/p) R, (1/(n:ℝ))*(∑ d ∈ n.divisors, sieveAtom d) := by
      apply sum_le_sum
      intro n hn
      exact sieveAtom_le_divisors ((Nat.zero_le (R/p)).trans_lt (mem_Ioc.mp hn).1)
    _ = ∑ d ∈ Ioc 0 R, ∑ n ∈ Ioc (R/p) R, if d ∣ n then sieveAtom d/n else 0 := by
      rw [sum_comm]
      apply sum_congr rfl
      intro n hn
      rw [divisor_sum_prefix ((Nat.zero_le (R/p)).trans_lt (mem_Ioc.mp hn).1) (mem_Ioc.mp hn).2, mul_sum]
      apply sum_congr rfl
      intro d hd
      split_ifs <;> simp [div_eq_mul_inv, mul_comm]
    _ = ∑ d ∈ Ioc 0 R, (sieveAtom d/d)*∑ k ∈ Ioc ((R/d)/p) (R/d), (1:ℝ)/k := by
      apply sum_congr rfl
      intro d hd
      rw [sum_multiples_Ioc (mem_Ioc.mp hd).1 (Nat.div_le_self R p)]
      have he : (R/p)/d = (R/d)/p := by rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm p d]
      rw [he, mul_sum]
      apply sum_congr rfl
      intro k hk
      push_cast
      ring
    _ ≤ ∑ d ∈ Ioc 0 R, (sieveAtom d/d)*(1+Real.log p) := by
      apply sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left (reciprocal_Ioc_bound hp)
        (div_nonneg (sieveAtom_nonneg _) (Nat.cast_nonneg _))
    _ = (∑ d ∈ Ioc 0 R, sieveAtom d/d)*(1+Real.log p) := (sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (sum_sieveAtom_div_le_three R) hlog

lemma coprimeMass_sub_le {R p : ℕ} (hp : 0 < p) :
    coprimeMass R p-coprimeMass (R/p) p ≤ 3*(1+Real.log p) := by
  have he := sum_Ioc_consecutive (fun r => if p ∣ r then 0 else sieveAtom r)
    (Nat.zero_le (R/p)) (Nat.div_le_self R p)
  change coprimeMass (R/p) p+_ = coprimeMass R p at he
  rw [← he, add_sub_cancel_left]
  apply le_trans _ (sieveAtom_Ioc_bound (R := R) hp)
  apply sum_le_sum
  intro r hr
  split_ifs
  · exact sieveAtom_nonneg r
  · rfl

/-- The local cost is logarithmic in p, divided by p G(R)^2. -/
theorem localMain_upper {R p : ℕ} (hR : 1 ≤ R) (hp : p.Prime) :
    localMain R p ≤ 3*(1+Real.log p)/((p:ℝ)*(sieveMass R)^2) := by
  rw [localMain_exact hR hp]
  exact div_le_div_of_nonneg_right (coprimeMass_sub_le hp.pos) (by positivity)

#print axioms sieveAtom_Ioc_bound
#print axioms localMain_upper

end Erdos972SieveMassInterval
