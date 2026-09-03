import Submission.ShortFullFiberOverlap

/-! A two-thirds ceiling for common-length full-fiber selection expressions,
including an eightfold mass allowance for grouping unequal lengths. This is
not an upper bound for the actual Sidon maximum. -/
namespace Erdos773.ShortFullFiberWeightedCeiling
open Finset PartialResidueFibers PartialFiberSelection MatchedResidueLifting ShortFullFiberOverlap
set_option maxHeartbeats 3000000

/-- The full-fiber overlap budget controls the fourth power of total
probability mass. -/
theorem quartic_mass_bound (q H : ℕ) (R : Finset ℕ) (hq : q.Prime) (hH10 : 10 ≤ H) (hHq : H ≤ q)
    (hR : ∀ r ∈ R, r < q) (hunit : ∀ r ∈ R, q.Coprime (2*r))
    (hM : PairMatching q R) (p : ℕ → ℝ)
    (hp : ∀ r ∈ R, 0 ≤ p r) (hp1 : ∀ r ∈ R, p r ≤ 1) :
    (H : ℝ)^2*(∑ r ∈ R, p r)^4 ≤ 40*(q : ℝ)^2*H*(∑ r ∈ R, p r) +
      400*(q : ℝ)^2*(∑ k ∈ crossKeys R (fun r => fiberValues q r (Icc 0 H)), p k.1.1^2*p k.1.2^2) := by
  let L := H/10
  let K : ℝ := (L+1 : ℕ)
  let S : ℝ := ∑ r ∈ R, p r
  let T : ℝ := ∑ r ∈ R, p r^2
  let U : ℝ := ∑ r ∈ R, p r^4
  let C : ℝ := ∑ k ∈ crossKeys R (fun r => fiberValues q r (Icc 0 H)), p k.1.1^2*p k.1.2^2
  have hL : 0 < L := by dsimp [L]; omega
  have hHL : 10*L ≤ H := Nat.mul_div_le H 10
  have hKloN : H ≤ 10*(L+1) := by dsimp [L]; omega
  have hKhiN : 5*(L+1) ≤ H := by dsimp [L]; omega
  have hKlo : (H : ℝ) ≤ 10*K := by dsimp [K]; exact_mod_cast hKloN
  have hKhi : 5*K ≤ (H : ℝ) := by dsimp [K]; exact_mod_cast hKhiN
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq.pos
  have hH0 : (0:ℝ) ≤ H := Nat.cast_nonneg H
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
  have hpig := full_weight_pigeonhole q H L R hq hL hHL hHq hR hunit p
  change (K*T)^2 ≤ (q : ℝ)*(K*U+2*C) at hpig
  have hKU : 5*K*U ≤ (H : ℝ)*T := by
    calc
      _ ≤ 5*K*T := mul_le_mul_of_nonneg_left hU (by positivity)
      _ ≤ (H : ℝ)*T := mul_le_mul_of_nonneg_right hKhi hT0
  have hKsq : (H : ℝ)^2 ≤ 100*K^2 := by nlinarith only [hKlo,hK0,hH0]
  have hlow := mul_le_mul_of_nonneg_right hKsq (sq_nonneg T)
  have hhigh := mul_le_mul_of_nonneg_left hKU (show (0:ℝ) ≤ 20*q by positivity)
  have hHT : (H : ℝ)^2*T^2 ≤ 20*q*H*T+200*q*C := by
    nlinarith only [hlow,hpig,hhigh]
  have hCS := sum_mul_sq_le_sq_mul_sq R (fun _ => (1:ℝ)) p
  simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one] at hCS
  change S^2 ≤ (R.card : ℝ)*T at hCS
  have hRcard : (R.card : ℝ)^2 ≤ 2*q := by exact_mod_cast pairMatching_card q R hq.pos hM
  have hCSsq := pow_le_pow_left₀ (sq_nonneg S) hCS 2
  have hRmul := mul_le_mul_of_nonneg_right hRcard (sq_nonneg T)
  have hS4 : S^4 ≤ 2*(q : ℝ)*T^2 := by nlinarith only [hCSsq,hRmul]
  have hTS := mul_le_mul_of_nonneg_left hT (show (0:ℝ) ≤ 40*(q : ℝ)^2*H by positivity)
  have hS4' := mul_le_mul_of_nonneg_left hS4 (sq_nonneg (H : ℝ))
  have hHT' := mul_le_mul_of_nonneg_left hHT (show (0:ℝ) ≤ 2*q by positivity)
  change (H : ℝ)^2*S^4 ≤ 40*(q : ℝ)^2*H*S+400*(q : ℝ)^2*C
  nlinarith only [hS4',hHT',hTS]

/-- The factor eight in the mass permits comparison with a whole length bin
whose longest fiber is at most eight times its shortest retained prefix. -/
theorem eightfold_cubic_ceiling (q H : ℕ) (R : Finset ℕ) (hq : q.Prime) (hHq : H ≤ q)
    (hR : ∀ r ∈ R, r < q) (hunit : ∀ r ∈ R, q.Coprime (2*r))
    (hM : PairMatching q R) (p : ℕ → ℝ)
    (hp : ∀ r ∈ R, 0 ≤ p r) (hp1 : ∀ r ∈ R, p r ≤ 1) :
    (8*((H+1 : ℕ) : ℝ)*(∑ r ∈ R, p r) -
      (∑ k ∈ crossKeys R (fun r => fiberValues q r (Icc 0 H)), p k.1.1^2*p k.1.2^2))^3 ≤
        320^3*((q*(H+1) : ℕ) : ℝ)^2 := by
  let S : ℝ := ∑ r ∈ R, p r
  let C : ℝ := ∑ k ∈ crossKeys R (fun r => fiberValues q r (Icc 0 H)), p k.1.1^2*p k.1.2^2
  let F : ℝ := 8*((H+1 : ℕ) : ℝ)*S-C
  have hS : 0 ≤ S := sum_nonneg hp
  have hC : 0 ≤ C := sum_nonneg (fun k _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hq0 : (0:ℝ) ≤ q := Nat.cast_nonneg q
  have hH0 : (0:ℝ) ≤ H := Nat.cast_nonneg H
  change F^3 ≤ 320^3*((q*(H+1) : ℕ) : ℝ)^2
  by_cases hf0 : F ≤ 0
  · have hf3 : F^3 ≤ 0 := by nlinarith only [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg F) hf0]
    exact hf3.trans (by positivity)
  have hfpos : 0 < F := lt_of_not_ge hf0
  by_cases hH10 : 10 ≤ H
  · have hH1 : (1:ℝ) ≤ H := by exact_mod_cast (show 1 ≤ H by omega)
    have hHpos : (0:ℝ) < H := by linarith only [hH1]
    have hF : F ≤ 16*H*S := by
      dsimp [F]; push_cast
      nlinarith only [hC,mul_le_mul_of_nonneg_right hH1 hS]
    have hSpos : 0 < S := by nlinarith only [hfpos,hF,hS]
    have hquartic := quartic_mass_bound q H R hq hH10 hHq hR hunit hM p hp hp1
    change (H : ℝ)^2*S^4 ≤ 40*(q : ℝ)^2*H*S+400*(q : ℝ)^2*C at hquartic
    have hCb : C ≤ 16*H*S := by
      have hh : 0 ≤ F := hfpos.le
      dsimp [F] at hh
      push_cast at hh
      nlinarith only [hh,mul_le_mul_of_nonneg_right hH1 hS]
    have hS3 : (H : ℝ)*S^3 ≤ 8000*(q : ℝ)^2 := by
      apply (mul_le_mul_iff_right₀ (mul_pos hHpos hSpos)).mp
      have hc := mul_le_mul_of_nonneg_left hCb (show (0:ℝ) ≤ 400*(q : ℝ)^2 by positivity)
      have hn : 0 ≤ (q : ℝ)^2*H*S := by positivity
      nlinarith only [hquartic,hc,hn]
    have hF3 := pow_le_pow_left₀ hfpos.le hF 3
    have hs := mul_le_mul_of_nonneg_left hS3 (show (0:ℝ) ≤ 4096*(H : ℝ)^2 by positivity)
    have hHH : (H : ℝ)^2 ≤ (H+1)^2 := by nlinarith only [hH0]
    have hHH' := mul_le_mul_of_nonneg_left hHH (show (0:ℝ) ≤ 320^3*(q : ℝ)^2 by positivity)
    push_cast
    nlinarith only [hF3,hs,hHH']
  · have hHsmall : ((H+1 : ℕ) : ℝ) ≤ 10 := by exact_mod_cast (show H+1 ≤ 10 by omega)
    have hSR : S ≤ (R.card : ℝ) := by
      calc
        S ≤ ∑ _r ∈ R, (1:ℝ) := sum_le_sum hp1
        _ = _ := by simp
    have hR1N : R.card ≤ q := by
      have hh := card_le_card (show R ⊆ range q from fun r hr => mem_range.mpr (hR r hr))
      simpa using hh
    have hR1 : (R.card : ℝ) ≤ q := by exact_mod_cast hR1N
    have hR2 : (R.card : ℝ)^2 ≤ 2*q := by exact_mod_cast pairMatching_card q R hq.pos hM
    have hR3 : (R.card : ℝ)^3 ≤ 2*(q : ℝ)^2 := by
      have hh := mul_le_mul hR2 hR1 (Nat.cast_nonneg R.card : (0:ℝ) ≤ R.card) (by positivity : (0:ℝ) ≤ 2*q)
      nlinarith only [hh]
    have hF : F ≤ 8*((H+1 : ℕ) : ℝ)*R.card := by
      dsimp [F]
      nlinarith only [hC,mul_le_mul_of_nonneg_left hSR (show (0:ℝ) ≤ 8*((H+1 : ℕ) : ℝ) by positivity)]
    have hF3 := pow_le_pow_left₀ hfpos.le hF 3
    have hR3' := mul_le_mul_of_nonneg_left hR3 (show (0:ℝ) ≤ 512*((H+1 : ℕ) : ℝ)^3 by positivity)
    have hHs := mul_le_mul_of_nonneg_left hHsmall (show (0:ℝ) ≤ 1024*(q : ℝ)^2*((H+1 : ℕ) : ℝ)^2 by positivity)
    have hn : 0 ≤ (q : ℝ)^2*((H+1 : ℕ) : ℝ)^2 := by positivity
    push_cast at hF3 hR3' hHs hn ⊢
    nlinarith only [hF3,hR3',hHs,hn]

/-- The common-length certificate is bounded even with an eightfold mass
allowance. This remains a bound on the expression only. -/
theorem eightfold_height_bound (q H : ℕ) (R : Finset ℕ) (hq : q.Prime) (hHq : H ≤ q)
    (hR : ∀ r ∈ R, r < q) (hunit : ∀ r ∈ R, q.Coprime (2*r))
    (hM : PairMatching q R) (p : ℕ → ℝ)
    (hp : ∀ r ∈ R, 0 ≤ p r) (hp1 : ∀ r ∈ R, p r ≤ 1) :
    8*((H+1 : ℕ) : ℝ)*(∑ r ∈ R, p r) -
      (∑ k ∈ crossKeys R (fun r => fiberValues q r (Icc 0 H)), p k.1.1^2*p k.1.2^2) ≤
        320*((q*(H+1) : ℕ) : ℝ)^(2/3 : ℝ) := by
  have hh := eightfold_cubic_ceiling q H R hq hHq hR hunit hM p hp hp1
  have he : (320*((q*(H+1) : ℕ) : ℝ)^(2/3 : ℝ))^3 = 320^3*((q*(H+1) : ℕ) : ℝ)^2 := by
    rw [mul_pow,← Real.rpow_mul_natCast (Nat.cast_nonneg _)]
    norm_num
  apply (Odd.strictMono_pow (by decide : Odd 3)).le_iff_le.mp
  rw [he]
  exact hh

#print axioms quartic_mass_bound
#print axioms eightfold_cubic_ceiling
#print axioms eightfold_height_bound
end Erdos773.ShortFullFiberWeightedCeiling
