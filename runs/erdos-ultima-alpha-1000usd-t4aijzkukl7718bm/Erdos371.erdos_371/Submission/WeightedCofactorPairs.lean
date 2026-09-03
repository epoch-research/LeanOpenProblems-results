import Submission.SelbergCofactorPairs

/-! A weighted cofactor-pair sieve bound. Keeping the maximum cofactor inside
the sum saves one logarithm compared with its pointwise maximum. No signed
cancellation is asserted here. -/
namespace Erdos371
namespace FiniteSieve
open Finset

lemma slopeSieveFactor_second_moment_Icc (X : ℕ) :
    (∑ a ∈ Icc 1 X, (slopeSieveFactor a)^2) ≤ X*Real.exp 16 := by
  have he := sum_Ico_add' (fun n : ℕ => (slopeSieveFactor n)^2) 0 X 1
  simp only [Nat.zero_add,Nat.Ico_zero_eq_range,Ico_add_one_right_eq_Icc] at he
  rw [← he]
  exact slopeSieveFactor_second_moment X

lemma weightedSlopeTerm_bound (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    2*(max a b : ℕ)*slopeSieveFactor (a*b)/((a : ℝ)*b) ≤
      ((slopeSieveFactor a)^2+(slopeSieveFactor b)^2)*
        ((1 : ℝ)/a+1/b) := by
  have hf := slopeSieveFactor_mul_le a b ha.ne' hb.ne'
  have hs : 2*slopeSieveFactor (a*b) ≤
      (slopeSieveFactor a)^2+(slopeSieveFactor b)^2 := by
    nlinarith [sq_nonneg (slopeSieveFactor a-slopeSieveFactor b)]
  have hm : (max a b : ℕ) ≤ a+b := Nat.max_le.mpr ⟨by omega,by omega⟩
  have hmr : (max a b : ℝ) ≤ (a : ℝ)+b := by exact_mod_cast hm
  have hmax : ((max a b : ℕ) : ℝ) = max (a : ℝ) b := by simp
  rw [hmax]
  have hs0 : 0 ≤ slopeSieveFactor (a*b) := by unfold slopeSieveFactor; positivity
  have h1 := mul_le_mul_of_nonneg_right hmr (by positivity : 0 ≤ 2*slopeSieveFactor (a*b))
  have h2 := mul_le_mul_of_nonneg_left hs (show 0 ≤ (a : ℝ)+b by positivity)
  have hd := div_le_div_of_nonneg_right (h1.trans h2)
    (show 0 ≤ (a : ℝ)*b by positivity)
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  convert hd using 1 <;> field_simp
  ring

/-- The maximum cofactor has mean of order X, not X*log X, against
this two-dimensional reciprocal weight. -/
theorem weightedSlopeSum_bound (X : ℕ) :
    (∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
      (max a b : ℕ)*slopeSieveFactor (a*b)/((a : ℝ)*b)) ≤
        2*Real.exp 16*X*(1+Real.log X) := by
  let A := ∑ a ∈ Icc 1 X, (slopeSieveFactor a)^2/(a : ℝ)
  let B := ∑ a ∈ Icc 1 X, (slopeSieveFactor a)^2
  let H := ∑ a ∈ Icc 1 X, (1 : ℝ)/a
  have hA : A ≤ Real.exp 16*H := by
    simpa only [← reciprocal_sum_Icc_eq_harmonic] using
      slopeSieveFactor_weighted_second_moment X
  have hB : B ≤ (X : ℝ)*Real.exp 16 := slopeSieveFactor_second_moment_Icc X
  have hH0 : 0 ≤ H := sum_nonneg fun _ _ => by positivity
  have hH : H ≤ 1+Real.log X := by
    rw [show H = (harmonic X : ℝ) from reciprocal_sum_Icc_eq_harmonic X]
    exact harmonic_le_one_add_log X
  have hsum := sum_le_sum (s := Icc 1 X) (fun a ha =>
    sum_le_sum (s := Icc 1 X) (fun b hb =>
      weightedSlopeTerm_bound a b (mem_Icc.mp ha).1 (mem_Icc.mp hb).1))
  have hl : (∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
      2*(max a b : ℕ)*slopeSieveFactor (a*b)/((a : ℝ)*b)) =
      2*(∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
        (max a b : ℕ)*slopeSieveFactor (a*b)/((a : ℝ)*b)) := by
    simp only [mul_assoc,mul_div_assoc,← mul_sum]
  have hr : (∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
      ((slopeSieveFactor a)^2+(slopeSieveFactor b)^2)*((1 : ℝ)/a+1/b)) =
      2*(X : ℝ)*A+2*H*B := by
    dsimp only [A,B,H]
    simp only [add_mul,mul_add,sum_add_distrib,← mul_sum,← sum_mul,
      sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul]
    simp only [div_eq_mul_inv,one_mul,mul_assoc,mul_comm,← mul_sum]
    ring
  rw [hl,hr] at hsum
  have hA' := mul_le_mul_of_nonneg_left hA (show 0 ≤ (X : ℝ) by positivity)
  have hB' := mul_le_mul_of_nonneg_left hB hH0
  have hH' := mul_le_mul_of_nonneg_left hH
    (show 0 ≤ 2*Real.exp 16*(X : ℝ) by positivity)
  nlinarith

noncomputable def cofactorWeightedPrimePairCount (N X z : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
    (max a b : ℕ)*(cofactorPrimePairSet N a b z).card

/-- A finite bound retaining the weight max(a,b) within the cofactor sum.
The main term is O(N*X*log X/log(z)^2). -/
theorem cofactorWeightedPrimePairCount_bound (N X z : ℕ)
    (hz : 1 ≤ z) (hXN : X^2 ≤ N) :
    cofactorWeightedPrimePairCount N X z ≤
      8*Real.exp 19*N*X*(1+Real.log X)/(Real.log (z+1 : ℝ))^2+
        2*(X : ℝ)^3*(z+1 : ℝ)^64 := by
  let C : ℝ := 4*Real.exp 3*N/(Real.log (z+1 : ℝ))^2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hrow (a b : ℕ) (ha : a ∈ Icc 1 X) (hb : b ∈ Icc 1 X) :
      (max a b : ℕ)*((cofactorPrimePairSet N a b z).card : ℝ) ≤
        C*((max a b : ℕ)*slopeSieveFactor (a*b)/((a : ℝ)*b))+
          2*(X : ℝ)*(z+1 : ℝ)^64 := by
    have hs := cofactorPrimePairSet_selberg_bound_of_product_le N a b z
      (mem_Icc.mp ha).1 (mem_Icc.mp hb).1 hz
      ((Nat.mul_le_mul (mem_Icc.mp ha).2 (mem_Icc.mp hb).2).trans
        (by simpa only [pow_two] using hXN))
    have hm : (max a b : ℕ) ≤ X := max_le (mem_Icc.mp ha).2 (mem_Icc.mp hb).2
    have hm' : ((max a b : ℕ) : ℝ) ≤ X := by exact_mod_cast hm
    have hs' := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (α := ℝ) (max a b))
    have he := mul_le_mul_of_nonneg_right hm' (show 0 ≤ 2*(z+1 : ℝ)^64 by positivity)
    calc
      _ ≤ C*((max a b : ℕ)*slopeSieveFactor (a*b)/((a : ℝ)*b))+
          (max a b : ℕ)*(2*(z+1 : ℝ)^64) := by
        dsimp only [C]
        convert hs' using 1
        ring
      _ ≤ _ := by linarith
  have hsum := sum_le_sum (s := Icc 1 X) (fun a ha =>
    sum_le_sum (s := Icc 1 X) (fun b hb => hrow a b ha hb))
  have he : (∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
      (C*((max a b : ℕ)*slopeSieveFactor (a*b)/((a : ℝ)*b))+
        2*(X : ℝ)*(z+1 : ℝ)^64)) =
      C*(∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
        (max a b : ℕ)*slopeSieveFactor (a*b)/((a : ℝ)*b))+
          2*(X : ℝ)^3*(z+1 : ℝ)^64 := by
    simp only [sum_add_distrib,← mul_sum,sum_const,Nat.card_Icc,
      Nat.add_sub_cancel,nsmul_eq_mul]
    ring
  rw [he] at hsum
  have hm := mul_le_mul_of_nonneg_left (weightedSlopeSum_bound X) hC
  have h19 : Real.exp 19 = Real.exp 3*Real.exp 16 := by
    rw [← Real.exp_add]
    norm_num
  unfold cofactorWeightedPrimePairCount
  refine hsum.trans (add_le_add (hm.trans_eq ?_) le_rfl)
  dsimp only [C]
  rw [h19]
  ring

#print axioms weightedSlopeSum_bound
#print axioms cofactorWeightedPrimePairCount_bound
end FiniteSieve
end Erdos371
