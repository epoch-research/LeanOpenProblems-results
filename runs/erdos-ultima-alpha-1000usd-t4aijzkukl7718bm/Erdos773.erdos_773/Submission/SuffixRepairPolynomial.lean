import FormalConjecturesUtil

/-! A numerical constraint on one proposed suffix-repair counting polynomial.
No entropy-compression algorithm or upper bound for arbitrary Sidon sets is
asserted in this file. -/
namespace Erdos773.SuffixRepairPolynomial
open Finset
set_option maxHeartbeats 1000000

noncomputable def cost (S : Finset ℕ) (K D z : ℝ) : ℝ :=
  1+D*∑ d ∈ S, K^(d-2)*z^d

/-- Charging every suffix length d by D*K^(d-2) has a quadratic length cost,
even though the two erased collision roots need not be recorded separately. -/
theorem length_cost {S : Finset ℕ} {K D z : ℝ}
    (hS : ∀ d ∈ S, 2≤d) (hK : 0<K) (hD : 0≤D) (hz : 0≤z)
    (hcost : cost S K D z < K*z) : D*(∑ d ∈ S, (d:ℝ)) < K^2 := by
  have hnon : 0≤D*∑ d ∈ S, K^(d-2)*z^d := by positivity
  have ht : 1<K*z := by unfold cost at hcost; linarith
  have hidentity : K^2 * cost S K D z = K^2+D*∑ d ∈ S, (K*z)^d := by
    have he : K^2*(∑ d ∈ S, K^(d-2)*z^d) = ∑ d ∈ S, (K*z)^d := by
      rw [mul_sum]
      apply sum_congr rfl
      intro d hd
      rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le (hS d hd), mul_pow]
    unfold cost
    linear_combination D*he
  have hupper : D*(∑ d ∈ S, (K*z)^d) < K^2*(K*z-1) := by
    have hh := mul_lt_mul_of_pos_left hcost (pow_pos hK 2)
    rw [hidentity] at hh
    nlinarith
  have hlower : (∑ d ∈ S, (d:ℝ))*(K*z-1) ≤ ∑ d ∈ S, (K*z)^d := by
    rw [sum_mul]
    apply sum_le_sum
    intro d hd
    have hh := one_add_mul_sub_le_pow (by linarith : (-1:ℝ)≤K*z) d
    linarith
  have hh := (mul_le_mul_of_nonneg_left hlower hD).trans_lt hupper
  rw [← mul_assoc] at hh
  exact lt_of_mul_lt_mul_right hh (by linarith : 0≤K*z-1)

lemma interval_length_sum (m : ℕ) (hm : 3 ≤ m) :
    (m:ℝ)^2 ≤ ∑ d ∈ Icc 4 (2*m), (d:ℝ) := by
  have hsub : Icc (m+1) (2*m) ⊆ Icc 4 (2*m) := by
    intro d hd
    simp only [mem_Icc] at hd ⊢
    omega
  have hc : (Icc (m+1) (2*m)).card=m := by
    rw [Nat.card_Icc]
    omega
  calc
    _ = ∑ _d ∈ Icc (m+1) (2*m), (m:ℝ) := by simp [hc, pow_two]
    _ ≤ ∑ d ∈ Icc (m+1) (2*m), (d:ℝ) := by
      apply sum_le_sum
      intro d hd
      exact_mod_cast (show m≤d from by have := (mem_Icc.mp hd).1; omega)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => by positivity)

/-- With all suffix lengths through 2m admitted in this uniform polynomial,
its strict criterion requires K>m as soon as D>=1. -/
theorem choices_exceed_half_slots {m : ℕ} {K D z : ℝ}
    (hm : 3 ≤ m) (hK : 0<K) (hD : 1≤D) (hz : 0≤z)
    (hcost : cost (Icc 4 (2*m)) K D z < K*z) : (m:ℝ)<K := by
  have hs := length_cost (fun d hd => by have := (mem_Icc.mp hd).1; omega)
    hK (by linarith : 0≤D) hz hcost
  have hb := interval_length_sum m hm
  have hsum : 0≤∑ d ∈ Icc 4 (2*m), (d:ℝ) := by positivity
  have he : (m:ℝ)^2<K^2 := by nlinarith [mul_le_mul_of_nonneg_right hD hsum]
  nlinarith [sq_nonneg (K-(m:ℝ))]

/-- On the declared height N=(2m)K, this particular criterion cannot certify
more than a constant times the square-root scale of occupied slots. -/
theorem slot_height_bound {m : ℕ} {K D z : ℝ}
    (hm : 3 ≤ m) (hK : 0<K) (hD : 1≤D) (hz : 0≤z)
    (hcost : cost (Icc 4 (2*m)) K D z < K*z) :
    (2*(m:ℝ))^4 < 4*((2*(m:ℝ))*K)^2 := by
  have hh := choices_exceed_half_slots hm hK hD hz hcost
  have hm0 : (0:ℝ)< m := by exact_mod_cast (show 0< m by omega)
  have hs : (m:ℝ)^2<K^2 := by nlinarith [sq_nonneg (K-(m:ℝ))]
  have ht := mul_lt_mul_of_pos_left hs (show (0:ℝ)<16*(m:ℝ)^2 by positivity)
  nlinarith only [ht]

#print axioms length_cost
#print axioms interval_length_sum
#print axioms choices_exceed_half_slots
#print axioms slot_height_bound
end Erdos773.SuffixRepairPolynomial
