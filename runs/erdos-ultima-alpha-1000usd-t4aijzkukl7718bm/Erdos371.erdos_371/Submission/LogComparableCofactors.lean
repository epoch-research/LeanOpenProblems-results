import Submission.SelbergCofactorPairs

/-! A logarithmic, rather than quadratic, dependence on the multiplicative
width in comparable-cofactor harmonic sums. -/

namespace Erdos371
namespace FiniteSieve
open Finset

lemma reciprocal_interval_log_bound (A D : ℕ) (hA : 0 < A) (hAD : A ≤ D) :
    (∑ b ∈ Icc A D, (1 : ℝ)/b) ≤ 1+Real.log D-Real.log A := by
  have he := sum_Ico_consecutive (fun b : ℕ => (1 : ℝ)/b) (show 1 ≤ A from hA) (show A ≤ D+1 by omega)
  have hfirst : Ico 1 A=Icc 1 (A-1) := by ext b; simp only [mem_Ico,mem_Icc]; omega
  rw [hfirst,Ico_add_one_right_eq_Icc,Ico_add_one_right_eq_Icc,
    reciprocal_sum_Icc_eq_harmonic,reciprocal_sum_Icc_eq_harmonic] at he
  have hlo := log_add_one_le_harmonic (A-1)
  rw [Nat.sub_add_cancel hA] at hlo
  have hhi := harmonic_le_one_add_log D
  linarith

lemma comparable_reciprocal_row_log_bound (C X a : ℕ) (hC : 1 ≤ C) (ha : 0 < a) :
    (∑ b ∈ Icc 1 X, if a ≤ C*b ∧ b ≤ C*a then (1 : ℝ)/b else 0) ≤
      1+2*Real.log C := by
  classical
  let A := ⌈(a : ℝ)/(C : ℝ)⌉₊
  let D := C*a
  have hC0 : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hA : 0 < A := Nat.ceil_pos.mpr (div_pos ha0 hC0)
  have hAa : A ≤ a := Nat.ceil_le.mpr ((div_le_iff₀ hC0).mpr (by
    have hC1 : (1 : ℝ) ≤ C := by exact_mod_cast hC
    nlinarith))
  have hAD : A ≤ D := hAa.trans (by dsimp [D]; nlinarith)
  have hsub : (Icc 1 X).filter (fun b => a ≤ C*b ∧ b ≤ C*a) ⊆ Icc A D := by
    intro b hb
    obtain ⟨_,hab,hba⟩ := mem_filter.mp hb
    refine mem_Icc.mpr ⟨Nat.ceil_le.mpr ?_,hba⟩
    apply (div_le_iff₀ hC0).mpr
    have h : (a : ℝ) ≤ C*(b : ℝ) := by exact_mod_cast hab
    nlinarith
  have hscale : (D : ℝ) ≤ (C : ℝ)^2*A := by
    have hceil := Nat.le_ceil ((a : ℝ)/(C : ℝ))
    have h := (div_le_iff₀ hC0).mp hceil
    dsimp only [D]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left h hC0.le]
  have hlog : Real.log D ≤ 2*Real.log C+Real.log A := by
    have hD0 : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by dsimp [D]; positivity)
    have h := Real.log_le_log hD0 hscale
    rw [Real.log_mul (pow_ne_zero _ hC0.ne') (by exact_mod_cast hA.ne'),Real.log_pow] at h
    simpa only [Nat.cast_ofNat] using h
  rw [← sum_filter]
  refine (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans ?_
  exact (reciprocal_interval_log_bound A D hA hAD).trans (by linarith)

lemma comparableSlopeSum_le_row_bound (C X : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (hrow : ∀ a ∈ Icc 1 X,
      (∑ b ∈ Icc 1 X, if a ≤ C*b ∧ b ≤ C*a then (1 : ℝ)/b else 0) ≤ L) :
    comparableSlopeSum C X ≤ L*Real.exp 16*(harmonic X : ℝ) := by
  classical
  let A : ℝ := ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
    if a ≤ C*b ∧ b ≤ C*a then (slopeSieveFactor a)^2/((a : ℝ)*b) else 0
  have hswap : (∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
      if a ≤ C*b ∧ b ≤ C*a then (slopeSieveFactor b)^2/((a : ℝ)*b) else 0)=A := by
    rw [sum_comm]
    apply sum_congr rfl
    intro a ha
    apply sum_congr rfl
    intro b hb
    simp only [and_comm,mul_comm]
  have hpoint : 2*comparableSlopeSum C X ≤ A+A := by
    unfold comparableSlopeSum
    conv_rhs => rhs; rw [← hswap]
    dsimp only [A]
    simp only [mul_sum,← sum_add_distrib]
    apply sum_le_sum
    intro a ha
    apply sum_le_sum
    intro b hb
    have ha0 : 0 < a := (mem_Icc.mp ha).1
    have hb0 : 0 < b := (mem_Icc.mp hb).1
    split_ifs
    · have hprod := slopeSieveFactor_mul_le a b ha0.ne' hb0.ne'
      have hsq : 2*slopeSieveFactor (a*b) ≤ (slopeSieveFactor a)^2+(slopeSieveFactor b)^2 := by
        nlinarith [sq_nonneg (slopeSieveFactor a-slopeSieveFactor b)]
      convert div_le_div_of_nonneg_right hsq (show (0 : ℝ) ≤ (a : ℝ)*b by positivity) using 1 <;> ring
    · simp
  have hA : A ≤ L*(∑ a ∈ Icc 1 X, (slopeSieveFactor a)^2/(a : ℝ)) := by
    dsimp only [A]
    rw [mul_sum]
    apply sum_le_sum
    intro a ha
    have he : (∑ b ∈ Icc 1 X,
        if a ≤ C*b ∧ b ≤ C*a then (slopeSieveFactor a)^2/((a : ℝ)*b) else 0) =
        ((slopeSieveFactor a)^2/(a : ℝ)) *
          (∑ b ∈ Icc 1 X, if a ≤ C*b ∧ b ≤ C*a then (1 : ℝ)/b else 0) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro b hb
      split_ifs <;> ring
    rw [he,mul_comm L]
    exact mul_le_mul_of_nonneg_left (hrow a ha) (by positivity)
  have hW := mul_le_mul_of_nonneg_left (slopeSieveFactor_weighted_second_moment X) hL
  nlinarith

/-- Comparable pairs incur `1+2*log C`, rather than the old factor `C^2`. -/
lemma comparableSlopeSum_logarithmic_bound (C X : ℕ) (hC : 1 ≤ C) :
    comparableSlopeSum C X ≤ (1+2*Real.log C)*Real.exp 16*(1+Real.log X) := by
  have hL : 0 ≤ 1+2*Real.log C := by have := Real.log_natCast_nonneg C; positivity
  have h := comparableSlopeSum_le_row_bound C X (1+2*Real.log C) hL
    (fun a ha => comparable_reciprocal_row_log_bound C X a hC (mem_Icc.mp ha).1)
  exact h.trans (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log X) (by positivity))

lemma comparableCofactorPrimeSet_selberg_bound (N C X z : ℕ)
    (hC : 1 ≤ C) (hz : 1 ≤ z) (hXN : X^2 ≤ N) :
    ((comparableCofactorPrimeSet N C X z).card : ℝ) ≤
      4*Real.exp 19*N*(1+2*Real.log C)*(1+Real.log X)/(Real.log (z+1 : ℝ))^2 +
        2*(X : ℝ)^2*(z+1 : ℝ)^64 := by
  let K : ℝ := 4*Real.exp 3*N/(Real.log (z+1 : ℝ))^2
  let E : ℝ := 2*(z+1 : ℝ)^64
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hcount : ((comparableCofactorPrimeSet N C X z).card : ℝ) ≤
      ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
        if a ≤ C*b ∧ b ≤ C*a then ((cofactorPrimePairSet N a b z).card : ℝ) else 0 := by
    exact_mod_cast comparableCofactorPrimeSet_card_le N C X z
  have hsum : (∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
      if a ≤ C*b ∧ b ≤ C*a then ((cofactorPrimePairSet N a b z).card : ℝ) else 0) ≤
        K*comparableSlopeSum C X+(X : ℝ)^2*E := by
    calc
      _ ≤ ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
          (K*(if a ≤ C*b ∧ b ≤ C*a then slopeSieveFactor (a*b)/((a : ℝ)*b) else 0)+E) := by
        apply sum_le_sum
        intro a ha
        apply sum_le_sum
        intro b hb
        split_ifs with hcomp
        · exact cofactorPrimePairSet_selberg_bound_of_product_le N a b z (mem_Icc.mp ha).1
            (mem_Icc.mp hb).1 hz ((Nat.mul_le_mul (mem_Icc.mp ha).2 (mem_Icc.mp hb).2).trans (by simpa [sq] using hXN))
        · simpa using hE
      _ = _ := by
        simp only [sum_add_distrib,← mul_sum,sum_const,Nat.card_Icc,Nat.add_sub_cancel,
          nsmul_eq_mul,comparableSlopeSum]
        ring
  have hmain := mul_le_mul_of_nonneg_left (comparableSlopeSum_logarithmic_bound C X hC) hK
  refine (hcount.trans hsum).trans (add_le_add (hmain.trans_eq ?_) ?_)
  · dsimp only [K]
    rw [show Real.exp 19=Real.exp 3*Real.exp 16 by rw [← Real.exp_add]; norm_num]
    ring
  · dsimp only [E]
    ring_nf
    rfl

#print axioms comparableSlopeSum_logarithmic_bound
#print axioms comparableCofactorPrimeSet_selberg_bound
end FiniteSieve
end Erdos371
