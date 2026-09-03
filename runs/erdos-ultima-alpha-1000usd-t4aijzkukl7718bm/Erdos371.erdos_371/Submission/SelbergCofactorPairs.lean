import Submission.TwoLinearSelberg
import Submission.LargePrimeNearTies

/-! Averaging the polynomial-error Selberg bound over all small cofactors. -/

namespace Erdos371
namespace FiniteSieve
open Finset

lemma cofactorPrimePairSet_selberg_bound (N a b z : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hz : 1 ≤ z) :
    ((cofactorPrimePairSet N a b z).card : ℝ) ≤
      2*Real.exp 2*slopeSieveFactor (2*(a*b))*((N/(a*b)+1 : ℕ) : ℝ)/(Real.log (z+1 : ℝ))^2 +
        2*(z+1 : ℝ)^64 := by
  by_cases hab : a.Coprime b
  · have hdet : (adjacentRoot a b hab/a)*a+1=b*((adjacentRoot a b hab+1)/b) := by
      rw [Nat.div_mul_cancel (adjacentRoot_dvd_left a b hab),
        Nat.mul_div_cancel' (adjacentRoot_dvd_right a b hab hb)]
    have h := twoLinear_prime_count_selberg_bound b (adjacentRoot a b hab/a)
      a ((adjacentRoot a b hab+1)/b) (N/(a*b)+1) z hb ha hz (Or.inr hdet)
    have hcard := (Nat.cast_le (α := ℝ)).mpr (cofactorPrimePairSet_card_le_linear N a b z ha hb hab)
    exact hcard.trans (by simpa only [Nat.mul_comm b a] using h)
  · rw [cofactorPrimePairSet_empty_of_not_coprime N a b z hab,card_empty,Nat.cast_zero]
    unfold slopeSieveFactor
    positivity

lemma slopeSieveFactor_two : slopeSieveFactor 2=Real.exp 1 := by
  norm_num [slopeSieveFactor,slopePrimeMass]

lemma cofactorPrimePairSet_selberg_bound_of_product_le (N a b z : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hz : 1 ≤ z) (habN : a*b ≤ N) :
    ((cofactorPrimePairSet N a b z).card : ℝ) ≤
      (4*Real.exp 3*N/(Real.log (z+1 : ℝ))^2)*(slopeSieveFactor (a*b)/((a : ℝ)*b)) +
        2*(z+1 : ℝ)^64 := by
  have hab0 : (0 : ℝ) < (a : ℝ)*b := by exact_mod_cast Nat.mul_pos ha hb
  have hN : (a : ℝ)*b ≤ N := by exact_mod_cast habN
  have hdiv : ((N/(a*b)+1 : ℕ) : ℝ) ≤ 2*(N : ℝ)/((a : ℝ)*b) := by
    have hfloor := Nat.cast_div_le (m := N) (n := a*b) (α := ℝ)
    have hone : (1 : ℝ) ≤ N/((a : ℝ)*b) := (le_div_iff₀ hab0).mpr (by simpa using hN)
    push_cast at hfloor ⊢
    convert add_le_add hfloor hone using 1 <;> ring
  have hslope : slopeSieveFactor (2*(a*b)) ≤ Real.exp 1*slopeSieveFactor (a*b) := by
    simpa only [slopeSieveFactor_two] using slopeSieveFactor_mul_le 2 (a*b) (by decide) (Nat.mul_pos ha hb).ne'
  have hp := mul_le_mul hslope hdiv (by positivity)
    (show 0 ≤ Real.exp 1*slopeSieveFactor (a*b) by unfold slopeSieveFactor; positivity)
  have h := mul_le_mul_of_nonneg_left hp (show 0 ≤ 2*Real.exp 2/(Real.log (z+1 : ℝ))^2 by positivity)
  have he : Real.exp 3=Real.exp 2*Real.exp 1 := by rw [← Real.exp_add]; norm_num
  refine (cofactorPrimePairSet_selberg_bound N a b z ha hb hz).trans (add_le_add ?_ le_rfl)
  rw [he]
  convert h using 1 <;> ring

lemma reciprocal_sum_Icc_eq_harmonic (N : ℕ) :
    (∑ n ∈ Icc 1 N, (1 : ℝ)/n)=(harmonic N : ℝ) := by
  simp [harmonic_eq_sum_Icc,one_div]

lemma unrestrictedSlopeSum_bound (X : ℕ) :
    (∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X, slopeSieveFactor (a*b)/((a : ℝ)*b)) ≤
      Real.exp 16*(1+Real.log X)^2 := by
  let A := ∑ a ∈ Icc 1 X, (slopeSieveFactor a)^2/(a : ℝ)
  let H := ∑ a ∈ Icc 1 X, (1 : ℝ)/a
  have hpoint (a b : ℕ) (ha : a ∈ Icc 1 X) (hb : b ∈ Icc 1 X) :
      2*slopeSieveFactor (a*b)/((a : ℝ)*b) ≤
        ((slopeSieveFactor a)^2/(a : ℝ))*((1 : ℝ)/b) +
          ((1 : ℝ)/a)*((slopeSieveFactor b)^2/(b : ℝ)) := by
    have hprod := slopeSieveFactor_mul_le a b (by have := (mem_Icc.mp ha).1; omega)
      (by have := (mem_Icc.mp hb).1; omega)
    have hsq : 2*slopeSieveFactor (a*b) ≤ (slopeSieveFactor a)^2+(slopeSieveFactor b)^2 := by
      nlinarith [sq_nonneg (slopeSieveFactor a-slopeSieveFactor b)]
    convert div_le_div_of_nonneg_right hsq (show (0 : ℝ) ≤ (a : ℝ)*b by positivity) using 1 <;> ring
  have hsum := sum_le_sum (fun a ha => sum_le_sum (fun b hb => hpoint a b ha hb))
  have hleft : (∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X, 2*slopeSieveFactor (a*b)/((a : ℝ)*b)) =
      2*(∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X, slopeSieveFactor (a*b)/((a : ℝ)*b)) := by
    simp only [mul_div_assoc,← mul_sum]
  have hright : (∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
        (((slopeSieveFactor a)^2/(a : ℝ))*((1 : ℝ)/b) +
          ((1 : ℝ)/a)*((slopeSieveFactor b)^2/(b : ℝ)))) = A*H+H*A := by
    simp only [sum_add_distrib,← mul_sum,← sum_mul,A,H]
  rw [hleft,hright] at hsum
  have hAH : A*H ≤ Real.exp 16*H^2 := by
    have h := slopeSieveFactor_weighted_second_moment X
    rw [← reciprocal_sum_Icc_eq_harmonic] at h
    have hH : 0 ≤ H := sum_nonneg fun _ _ => by positivity
    have hm := mul_le_mul_of_nonneg_right h hH
    convert hm using 1 <;> ring
  have hH : H ≤ 1+Real.log X := by
    rw [show H=(harmonic X : ℝ) from reciprocal_sum_Icc_eq_harmonic X]
    exact harmonic_le_one_add_log X
  have hH0 : 0 ≤ H := sum_nonneg fun _ _ => by positivity
  have hsq := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hH0 hH 2) (Real.exp_nonneg 16)
  nlinarith

noncomputable def allCofactorPrimeSet (N X z : ℕ) : Finset ℕ :=
  (Icc 1 X).biUnion fun a => (Icc 1 X).biUnion fun b => cofactorPrimePairSet N a b z

lemma allCofactorPrimeSet_bound (N X z : ℕ) (hz : 1 ≤ z) (hXN : X^2 ≤ N) :
    ((allCofactorPrimeSet N X z).card : ℝ) ≤
      4*Real.exp 19*N*(1+Real.log X)^2/(Real.log (z+1 : ℝ))^2 +
        2*(X : ℝ)^2*(z+1 : ℝ)^64 := by
  have hc : (allCofactorPrimeSet N X z).card ≤
      ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X, (cofactorPrimePairSet N a b z).card := by
    exact card_biUnion_le.trans (sum_le_sum fun _ _ => card_biUnion_le)
  have hcr := (Nat.cast_le (α := ℝ)).mpr hc
  simp only [Nat.cast_sum] at hcr
  let K : ℝ := 4*Real.exp 3*N/(Real.log (z+1 : ℝ))^2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hs : (∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X, ((cofactorPrimePairSet N a b z).card : ℝ)) ≤
      K*(∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X, slopeSieveFactor (a*b)/((a : ℝ)*b)) +
        2*(X : ℝ)^2*(z+1 : ℝ)^64 := by
    calc
      _ ≤ ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
          (K*(slopeSieveFactor (a*b)/((a : ℝ)*b))+2*(z+1 : ℝ)^64) := by
        apply sum_le_sum
        intro a ha
        apply sum_le_sum
        intro b hb
        exact cofactorPrimePairSet_selberg_bound_of_product_le N a b z (mem_Icc.mp ha).1
          (mem_Icc.mp hb).1 hz ((Nat.mul_le_mul (mem_Icc.mp ha).2 (mem_Icc.mp hb).2).trans (by simpa [sq] using hXN))
      _ = _ := by
        simp only [sum_add_distrib,← mul_sum,sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul]
        ring
  have hm := mul_le_mul_of_nonneg_left (unrestrictedSlopeSum_bound X) hK
  refine (hcr.trans hs).trans (add_le_add (hm.trans_eq ?_) le_rfl)
  dsimp [K]
  rw [show Real.exp 19=Real.exp 3*Real.exp 16 by rw [← Real.exp_add]; norm_num]
  ring

#print axioms unrestrictedSlopeSum_bound
#print axioms allCofactorPrimeSet_bound
end FiniteSieve
end Erdos371
