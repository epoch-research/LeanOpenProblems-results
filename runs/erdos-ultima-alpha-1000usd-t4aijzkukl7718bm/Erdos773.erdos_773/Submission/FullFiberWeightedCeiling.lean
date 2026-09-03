import Submission.FullFiberOverlapCount

/-!
A two-thirds ceiling for the nonuniform alteration *expression* on full
unit-residue fibers of index length q, under modular pair matching.
This is NOT an upper bound for the largest Sidon subset of these fibers,
nor for arbitrary square subsets, nor for partial-fiber selection schemes.
-/
namespace Erdos773.FullFiberWeightedCeiling
open Finset PartialResidueFibers PartialFiberSelection MatchedResidueLifting FullFiberOverlapCount
set_option maxHeartbeats 3000000

/-- The full-fiber overlap budget controls the fourth power of total
probability mass. -/
theorem quartic_mass_bound (q : ℕ) (R : Finset ℕ) (hq : q.Prime) (hq10 : 10 ≤ q)
    (hR : ∀ r ∈ R, r < q) (hunit : ∀ r ∈ R, q.Coprime (2*r))
    (hM : PairMatching q R) (p : ℕ → ℝ)
    (hp : ∀ r ∈ R, 0 ≤ p r) (hp1 : ∀ r ∈ R, p r ≤ 1) :
    (∑ r ∈ R, p r)^4 ≤ 40*(q : ℝ)*(∑ r ∈ R, p r) +
      400*(∑ k ∈ crossKeys R (fun r => fiberValues q r (Icc 0 q)), p k.1.1^2*p k.1.2^2) := by
  let L := q/10
  let K : ℝ := (L+1 : ℕ)
  let S : ℝ := ∑ r ∈ R, p r
  let T : ℝ := ∑ r ∈ R, p r^2
  let U : ℝ := ∑ r ∈ R, p r^4
  let C : ℝ := ∑ k ∈ crossKeys R (fun r => fiberValues q r (Icc 0 q)), p k.1.1^2*p k.1.2^2
  have hL : 0 < L := by dsimp [L]; omega
  have hqL : 10*L ≤ q := Nat.mul_div_le q 10
  have hKloN : q ≤ 10*(L+1) := by dsimp [L]; omega
  have hKhiN : 5*(L+1) ≤ q := by dsimp [L]; omega
  have hKlo : (q : ℝ) ≤ 10*K := by dsimp [K]; exact_mod_cast hKloN
  have hKhi : 5*K ≤ (q : ℝ) := by dsimp [K]; exact_mod_cast hKhiN
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq.pos
  have hT0 : 0 ≤ T := sum_nonneg (fun r _ => sq_nonneg (p r))
  have hT : T ≤ S := by
    apply sum_le_sum
    intro r hr
    nlinarith only [hp r hr,hp1 r hr]
  have hU : U ≤ T := by
    apply sum_le_sum
    intro r hr
    have hpp : p r^2 ≤ 1 := by nlinarith only [hp r hr,hp1 r hr]
    nlinarith only [sq_nonneg (p r),hpp,mul_nonneg (sq_nonneg (p r)) (sub_nonneg.mpr hpp)]
  have hpig := full_weight_pigeonhole q L R hq hL hqL hR hunit p
  change (K*T)^2 ≤ (q : ℝ)*(K*U+2*C) at hpig
  have hKU : 5*K*U ≤ (q : ℝ)*T := by
    calc
      _ ≤ 5*K*T := mul_le_mul_of_nonneg_left hU (by positivity)
      _ ≤ (q : ℝ)*T := mul_le_mul_of_nonneg_right hKhi hT0
  have hKsq : (q : ℝ)^2 ≤ 100*K^2 := by nlinarith only [hKlo,hK0,hq0]
  have hlow := mul_le_mul_of_nonneg_right hKsq (sq_nonneg T)
  have hhigh := mul_le_mul_of_nonneg_left hKU (show (0:ℝ) ≤ 20*q by positivity)
  have hQT : (q : ℝ)*T^2 ≤ 20*q*T+200*C := by
    apply (mul_le_mul_iff_right₀ hq0).mp
    nlinarith only [hlow,hpig,hhigh]
  have hCS := sum_mul_sq_le_sq_mul_sq R (fun _ => (1:ℝ)) p
  simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one] at hCS
  change S^2 ≤ (R.card : ℝ)*T at hCS
  have hRcard : (R.card : ℝ)^2 ≤ 2*q := by exact_mod_cast pairMatching_card q R hq.pos hM
  have hCSsq := pow_le_pow_left₀ (sq_nonneg S) hCS 2
  have hRmul := mul_le_mul_of_nonneg_right hRcard (sq_nonneg T)
  have hTS := mul_le_mul_of_nonneg_left hT (show (0:ℝ) ≤ 40*q by positivity)
  change S^4 ≤ 40*(q : ℝ)*S+400*C
  nlinarith only [hCSsq,hRmul,hQT,hTS]

/-- Cubic form of the two-thirds ceiling. The expression can be negative;
no assertion is made that it equals the actual Sidon maximum. -/
theorem expression_cubic_ceiling (q : ℕ) (R : Finset ℕ) (hq : q.Prime) (hq10 : 10 ≤ q)
    (hR : ∀ r ∈ R, r < q) (hunit : ∀ r ∈ R, q.Coprime (2*r))
    (hM : PairMatching q R) (p : ℕ → ℝ)
    (hp : ∀ r ∈ R, 0 ≤ p r) (hp1 : ∀ r ∈ R, p r ≤ 1) :
    (((q+1 : ℕ) : ℝ)*(∑ r ∈ R, p r) -
      (∑ k ∈ crossKeys R (fun r => fiberValues q r (Icc 0 q)), p k.1.1^2*p k.1.2^2))^3 ≤
        8000*(q : ℝ)^4 := by
  let S : ℝ := ∑ r ∈ R, p r
  let C : ℝ := ∑ k ∈ crossKeys R (fun r => fiberValues q r (Icc 0 q)), p k.1.1^2*p k.1.2^2
  let F : ℝ := ((q+1 : ℕ) : ℝ)*S-C
  have hS : 0 ≤ S := sum_nonneg hp
  have hC : 0 ≤ C := sum_nonneg (fun k _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hq0 : (0:ℝ) ≤ q := Nat.cast_nonneg q
  have hF : F ≤ 2*q*S := by dsimp [F]; push_cast; nlinarith only [hC,mul_le_mul_of_nonneg_right hq1 hS]
  change F^3 ≤ 8000*(q : ℝ)^4
  by_cases hf0 : F ≤ 0
  · have hf3 : F^3 ≤ 0 := by nlinarith only [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg F) hf0]
    exact hf3.trans (by positivity)
  have hfpos : 0 < F := lt_of_not_ge hf0
  have hSpos : 0 < S := by nlinarith only [hfpos,hF,hS]
  have hquartic := quartic_mass_bound q R hq hq10 hR hunit hM p hp hp1
  change S^4 ≤ 40*(q : ℝ)*S+400*C at hquartic
  have hCb : C ≤ 2*q*S := by
    have hh : 0 ≤ F := hfpos.le
    dsimp [F] at hh
    push_cast at hh
    nlinarith only [hh,mul_le_mul_of_nonneg_right hq1 hS]
  have hS3 : S^3 ≤ 1000*(q : ℝ) := by
    apply (mul_le_mul_iff_left₀ hSpos).mp
    nlinarith only [hquartic,hCb,mul_nonneg hq0 hS]
  calc
    F^3 ≤ (2*q*S)^3 := pow_le_pow_left₀ hfpos.le hF 3
    _ = 8*(q : ℝ)^3*S^3 := by ring
    _ ≤ 8*(q : ℝ)^3*(1000*q) := mul_le_mul_of_nonneg_left hS3 (by positivity)
    _ = 8000*(q : ℝ)^4 := by ring

/-- N=q(q+1) is the root-height bound for positive canonical residues. -/
theorem expression_height_ceiling (q : ℕ) (R : Finset ℕ) (hq : q.Prime) (hq10 : 10 ≤ q)
    (hR : ∀ r ∈ R, r < q) (hunit : ∀ r ∈ R, q.Coprime (2*r))
    (hM : PairMatching q R) (p : ℕ → ℝ)
    (hp : ∀ r ∈ R, 0 ≤ p r) (hp1 : ∀ r ∈ R, p r ≤ 1) :
    (((q+1 : ℕ) : ℝ)*(∑ r ∈ R, p r) -
      (∑ k ∈ crossKeys R (fun r => fiberValues q r (Icc 0 q)), p k.1.1^2*p k.1.2^2))^3 ≤
        8000*((q*(q+1) : ℕ) : ℝ)^2 := by
  have hh := expression_cubic_ceiling q R hq hq10 hR hunit hM p hp hp1
  have hq0 : (0:ℝ) ≤ q := Nat.cast_nonneg q
  have hs : (q : ℝ)^2 ≤ q*(q+1) := by nlinarith only [hq0]
  have hs2 := pow_le_pow_left₀ (sq_nonneg (q : ℝ)) hs 2
  push_cast at hh ⊢
  nlinarith only [hh,hs2]

/-- Explicit root-height form: this particular nonuniform certificate is
at most 20 N^(2/3), where N=q(q+1). -/
theorem expression_height_bound (q : ℕ) (R : Finset ℕ) (hq : q.Prime) (hq10 : 10 ≤ q)
    (hR : ∀ r ∈ R, r < q) (hunit : ∀ r ∈ R, q.Coprime (2*r))
    (hM : PairMatching q R) (p : ℕ → ℝ)
    (hp : ∀ r ∈ R, 0 ≤ p r) (hp1 : ∀ r ∈ R, p r ≤ 1) :
    ((q+1 : ℕ) : ℝ)*(∑ r ∈ R, p r) -
      (∑ k ∈ crossKeys R (fun r => fiberValues q r (Icc 0 q)), p k.1.1^2*p k.1.2^2) ≤
        20*((q*(q+1) : ℕ) : ℝ)^(2/3 : ℝ) := by
  have hh := expression_height_ceiling q R hq hq10 hR hunit hM p hp hp1
  have he : (20*((q*(q+1) : ℕ) : ℝ)^(2/3 : ℝ))^3 = 8000*((q*(q+1) : ℕ) : ℝ)^2 := by
    rw [mul_pow,← Real.rpow_mul_natCast (Nat.cast_nonneg _) ]
    norm_num
  apply (Odd.strictMono_pow (by decide : Odd 3)).le_iff_le.mp
  rw [he]
  exact hh

/-- Same ceiling with the mass written using the actual value-fiber cards. -/
theorem full_expression_height_bound (q : ℕ) (R : Finset ℕ) (hq : q.Prime) (hq10 : 10 ≤ q)
    (hR : ∀ r ∈ R, r < q) (hunit : ∀ r ∈ R, q.Coprime (2*r))
    (hM : PairMatching q R) (p : ℕ → ℝ)
    (hp : ∀ r ∈ R, 0 ≤ p r) (hp1 : ∀ r ∈ R, p r ≤ 1) :
    (∑ r ∈ R, p r*(fiberValues q r (Icc 0 q)).card) -
      (∑ k ∈ crossKeys R (fun r => fiberValues q r (Icc 0 q)), p k.1.1^2*p k.1.2^2) ≤
        20*((q*(q+1) : ℕ) : ℝ)^(2/3 : ℝ) := by
  have hc (r : ℕ) : (fiberValues q r (Icc 0 q)).card=q+1 := by
    rw [fiberValues, card_image_of_injective]
    · simp
    · intro a b he
      have hh := Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0) he
      nlinarith only [hh,hq.pos]
  simp_rw [hc]
  rw [← sum_mul,mul_comm (∑ r ∈ R, p r)]
  exact expression_height_bound q R hq hq10 hR hunit hM p hp hp1

#print axioms quartic_mass_bound
#print axioms expression_cubic_ceiling
#print axioms expression_height_ceiling
#print axioms full_expression_height_bound
end Erdos773.FullFiberWeightedCeiling
