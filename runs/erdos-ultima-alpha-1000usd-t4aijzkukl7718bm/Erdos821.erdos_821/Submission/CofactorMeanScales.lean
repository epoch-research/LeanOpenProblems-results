import Submission.CofactorAllModulusMean
import Submission.DensityCutoffRefinement

/-!
# Polynomial cofactor intervals and an all-modulus strict-half-level saving

The residue can vary with the modulus and with the scale. The conclusion
retains the exact principal cofactor term, and does not assert prime pairs.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 4000000

def cofactorScale (t m : ℕ) : ℕ := progressionScaleN (t*(4*m))

lemma cofactorScale_pos (t m : ℕ) : 0 < cofactorScale t m := by
  unfold cofactorScale progressionScaleN
  positivity

lemma cofactorScale_cast (t m : ℕ) : (cofactorScale t m : ℝ) = (2 : ℝ)^(256*t*m) := by
  simp only [cofactorScale,progressionScaleN,Nat.cast_pow,Nat.cast_ofNat]
  congr 1
  ring

lemma cofactorScale_log_le (t m : ℕ) : Real.log (cofactorScale t m : ℝ) ≤ 256*(t : ℝ)*((m : ℝ)+1) := by
  have hh := log_two_pow_le (256*t*m)
  have he : cofactorScale t m=2^(256*t*m) := by unfold cofactorScale progressionScaleN; congr 1; ring
  rw [← he] at hh
  push_cast at hh
  have htm : 0 ≤ (256 : ℝ)*t := by positivity
  nlinarith only [hh,htm]

lemma cofactorScale_natLog_le (t m : ℕ) : (Nat.log 2 (cofactorScale t m) : ℝ) ≤ 256*(t : ℝ)*((m : ℝ)+1) := by
  simp only [cofactorScale,progressionScaleN,Nat.log_pow (by decide : 1<2),Nat.cast_mul,Nat.cast_ofNat]
  have ht : 0 ≤ (t : ℝ) := Nat.cast_nonneg _
  nlinarith only [ht]

lemma cofactorScale_harmonic_le (t m : ℕ) :
    (harmonic (cofactorScale t m) : ℝ) ≤ (256*(t : ℝ)+1)*((m : ℝ)+1) := by
  have hh := harmonic_le_one_add_log (cofactorScale t m)
  have hl := cofactorScale_log_le t m
  nlinarith only [hh,hl,Nat.cast_nonneg (α := ℝ) m]

lemma cofactorScale_rpow (b m : ℕ) (hb : 1 ≤ b) :
    (cofactorScale b m : ℝ)^(1/(256*(b : ℝ))) = (2 : ℝ)^m := by
  rw [cofactorScale_cast,← Real.rpow_natCast_mul (by norm_num)]
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  have he : ((256*b*m : ℕ) : ℝ)*(1/(256*(b : ℝ))) = (m : ℝ) := by push_cast; field_simp
  rw [he,Real.rpow_natCast]

lemma cofactorScale_small_saving (a l m : ℕ) (hl : 2*a+1 ≤ l) :
    ((2 : ℝ)^m)^2*(cofactorScale a m : ℝ)*Real.sqrt (cofactorScale a m) ≤ cofactorScale l m := by
  have hR1 : (1 : ℝ) ≤ cofactorScale a m := by exact_mod_cast cofactorScale_pos a m
  have hroot : Real.sqrt (cofactorScale a m) ≤ (cofactorScale a m : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by linarith only [hR1],by nlinarith only [hR1]⟩
  have hbound : ((2 : ℝ)^m)^2*(cofactorScale a m : ℝ)^2 ≤ cofactorScale l m := by
    simp only [cofactorScale_cast,← pow_mul,← pow_add]
    apply pow_le_pow_right₀ (by norm_num)
    have hh := Nat.mul_le_mul_right m hl
    nlinarith only [hh,Nat.zero_le m]
  apply le_trans _ hbound
  have hh := mul_le_mul_of_nonneg_left hroot
    (show 0 ≤ ((2 : ℝ)^m)^2*(cofactorScale a m : ℝ) by positivity)
  convert hh using 1; ring

lemma cofactorScale_lift_saving (b t m : ℕ) (hbt : b+1 ≤ t) :
    ((2 : ℝ)^m)^2*(cofactorScale b m : ℝ) ≤ cofactorScale t m := by
  simp only [cofactorScale_cast,← pow_mul,← pow_add]
  apply pow_le_pow_right₀ (by norm_num)
  have hh := Nat.mul_le_mul_right m hbt
  nlinarith only [hh,Nat.zero_le m]

lemma cofactorScale_primitive_saving (a b t m : ℕ) (ha : 1 ≤ a) (hab : a ≤ b)
    (ht : 22 ≤ t) (hlevel : 2*b+5 ≤ t) :
    ((2 : ℝ)^m)^2*primitivePoolMean (Ioc (cofactorScale a m) (cofactorScale b m)) (cofactorScale t m) ≤
      (((b-a : ℕ) : ℝ)*(wideMeanConstant t : ℝ)*1024*((m : ℝ)+1)^5)*(cofactorScale t m : ℝ) := by
  have hh := primitive_full_interval_mean_bound a b t (4*m) ha hab ht hlevel
  have hp : ((2 : ℝ)^m)^2*(2 : ℝ)^((64*t-1)*(4*m)) ≤ cofactorScale t m := by
    rw [cofactorScale_cast,← pow_mul,← pow_add]
    apply pow_le_pow_right₀ (by norm_num)
    have he := Nat.sub_add_cancel (show 1 ≤ 64*t by omega)
    nlinarith only [congrArg (fun z : ℕ => z*m) he,Nat.zero_le m]
  have hpoly : ((4*m : ℕ) : ℝ)+1 ≤ 4*((m : ℝ)+1) := by push_cast; linarith
  calc
    _ ≤ ((2 : ℝ)^m)^2*(((b-a : ℕ) : ℝ)*(wideMeanConstant t : ℝ)*
        (((4*m : ℕ) : ℝ)+1)^5*(2 : ℝ)^((64*t-1)*(4*m))) := by
      exact mul_le_mul_of_nonneg_left hh (by positivity)
    _ = (((b-a : ℕ) : ℝ)*(wideMeanConstant t : ℝ)*(((4*m : ℕ) : ℝ)+1)^5)*
        (((2 : ℝ)^m)^2*(2 : ℝ)^((64*t-1)*(4*m))) := by ring
    _ ≤ (((b-a : ℕ) : ℝ)*(wideMeanConstant t : ℝ)*(4*((m : ℝ)+1))^5)*(cofactorScale t m : ℝ) := by gcongr
    _ = _ := by ring

/-- A purely algebraic normalization of the three error terms. -/
lemma cofactor_error_normalize (E C Z L N S H R T P Q J K W : ℝ)
    (hC : 0 ≤ C) (hZ : 0 ≤ Z) (hL : 0 ≤ L) (hN : 0 ≤ N) (_hS : 0 ≤ S)
    (hH : 0 ≤ H) (hR : 0 ≤ R) (hT : 0 ≤ T) (hJ : 0 ≤ J) (hK : 0 ≤ K)
    (hE : E ≤ C*Z*(S*H*R*T+L*H*P+L*Q*J*K))
    (hSN : S ≤ 6*N) (hsmall : Z^2*R ≤ L) (hlarge : Z^2*P ≤ W*N) (hlift : Z^2*Q ≤ N) :
    Z*E ≤ C*L*N*(6*H*T+H*W+J*K) := by
  have hEZ := mul_le_mul_of_nonneg_left hE hZ
  have hs := mul_le_mul_of_nonneg_right
    (mul_le_mul hSN hsmall (mul_nonneg (sq_nonneg Z) hR) (by positivity))
    (mul_nonneg hH hT)
  have hl := mul_le_mul_of_nonneg_left hlarge (mul_nonneg hL hH)
  have hi := mul_le_mul_of_nonneg_left hlift (mul_nonneg (mul_nonneg hL hJ) hK)
  have hsum := mul_le_mul_of_nonneg_left (_root_.add_le_add (_root_.add_le_add hs hl) hi) hC
  nlinarith only [hEZ,hsum]

lemma cofactor_polynomial_error_bound (a b t m : ℕ) :
    let H := (harmonic (cofactorScale b m) : ℝ)
    let T := 1+Real.log (cofactorScale a m)
    let W := ((b-a : ℕ) : ℝ)*(wideMeanConstant t : ℝ)*1024*((m : ℝ)+1)^5
    let J := (Nat.log 2 (cofactorScale t m) : ℝ)
    let K := Real.log (cofactorScale b m)
    6*H*T+H*W+J*K ≤
      (6*(256*(b : ℝ)+1)*(256*(a : ℝ)+1)+
        (256*(b : ℝ)+1)*((b-a : ℕ) : ℝ)*(wideMeanConstant t : ℝ)*1024+
          (256*(t : ℝ))*(256*(b : ℝ)))*((m : ℝ)+1)^6 := by
  dsimp only
  have hm : 1 ≤ (m : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) m]
  have hH := cofactorScale_harmonic_le b m
  have hT : 1+Real.log (cofactorScale a m) ≤ (256*(a : ℝ)+1)*((m : ℝ)+1) := by
    have hh := cofactorScale_log_le a m
    nlinarith only [hh,Nat.cast_nonneg (α := ℝ) m]
  have hJ := cofactorScale_natLog_le t m
  have hK := cofactorScale_log_le b m
  have hpow : ((m : ℝ)+1)^2 ≤ ((m : ℝ)+1)^6 := pow_le_pow_right₀ hm (by decide)
  have hsmall := mul_le_mul_of_nonneg_left (mul_le_mul hH hT
    (by linarith [Real.log_natCast_nonneg (cofactorScale a m)]) (by positivity)) (show (0 : ℝ)≤6 by norm_num)
  have hlarge := mul_le_mul_of_nonneg_right hH
    (show 0 ≤ ((b-a : ℕ) : ℝ)*(wideMeanConstant t : ℝ)*1024*((m : ℝ)+1)^5 by positivity)
  have hlift := mul_le_mul hJ hK (Real.log_natCast_nonneg _) (by positivity)
  have hsmall' := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ 6*(256*(b : ℝ)+1)*(256*(a : ℝ)+1) by positivity)
  have hlift' := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ (256*(t : ℝ))*(256*(b : ℝ)) by positivity)
  nlinarith only [hsmall,hlarge,hlift,hsmall',hlift']

/-- A power-saving all-modulus error, uniform in interval endpoints and residues. -/
theorem exists_cofactor_all_modulus_power_saving (a b t l : ℕ) (ha : 1 ≤ a)
    (hab : a ≤ b) (ht : 22 ≤ t) (hlevel : 2*b+5 ≤ t) (hl : 2*a+1 ≤ l) :
    ∃ K : ℝ, 0 < K ∧ ∀ m A B : ℕ, cofactorScale l m ≤ B-A →
      ∀ u : ∀ d : ℕ, (ZMod d)ˣ,
        (∑ d ∈ Icc 1 (cofactorScale b m), |cofactorCongruenceWeight d (u d) A B (cofactorScale t m)-
          cofactorPrincipalMain d A B (cofactorScale t m)|) ≤
            K*((m : ℝ)+1)^6/(2 : ℝ)^m*((B-A : ℕ) : ℝ)*(cofactorScale t m : ℝ) := by
  let ε : ℝ := 1/(256*(b : ℝ))
  have hb : 1 ≤ b := ha.trans hab
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨C,hC,HC⟩ := exists_cofactor_all_modulus_mean_bound ε hε
  let D : ℝ := 6*(256*(b : ℝ)+1)*(256*(a : ℝ)+1)+
    (256*(b : ℝ)+1)*((b-a : ℕ) : ℝ)*(wideMeanConstant t : ℝ)*1024+(256*(t : ℝ))*(256*(b : ℝ))
  refine ⟨C*D,mul_pos hC (by dsimp [D]; positivity),?_⟩
  intro m A B hAB u
  let E := ∑ d ∈ Icc 1 (cofactorScale b m), |cofactorCongruenceWeight d (u d) A B (cofactorScale t m)-
    cofactorPrincipalMain d A B (cofactorScale t m)|
  let L : ℝ := (B-A : ℕ)
  let N : ℝ := cofactorScale t m
  let Z : ℝ := (2 : ℝ)^m
  have hL : 0 ≤ L := Nat.cast_nonneg _
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hZ : 0 < Z := by dsimp [Z]; positivity
  have hmain := HC (cofactorScale b m) (cofactorScale a m) A B (cofactorScale t m) u
  rw [show ε=1/(256*(b : ℝ)) from rfl,cofactorScale_rpow b m hb] at hmain
  have hsmall := (cofactorScale_small_saving a l m hl).trans (show (cofactorScale l m : ℝ) ≤ L by dsimp [L]; exact_mod_cast hAB)
  have hnorm := cofactor_error_normalize E C Z L N (mangoldtSum (cofactorScale t m))
    (harmonic (cofactorScale b m)) ((cofactorScale a m : ℝ)*Real.sqrt (cofactorScale a m))
    (1+Real.log (cofactorScale a m)) (primitivePoolMean (Ioc (cofactorScale a m) (cofactorScale b m)) (cofactorScale t m))
    (cofactorScale b m) (Nat.log 2 (cofactorScale t m)) (Real.log (cofactorScale b m))
    (((b-a : ℕ) : ℝ)*(wideMeanConstant t : ℝ)*1024*((m : ℝ)+1)^5)
    hC.le hZ.le hL hN (mangoldtSum_nonneg _) (harmonic_natCast_nonneg _) (by positivity)
    (by linarith [Real.log_natCast_nonneg (cofactorScale a m)]) (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
    (by convert hmain using 1; dsimp [E,L,N,Z]; ring)
    (Erdos821.mangoldtSum_le_six_mul _) (by convert hsmall using 1; dsimp [Z]; ring)
    (cofactorScale_primitive_saving a b t m ha hab ht hlevel) (cofactorScale_lift_saving b t m (by omega))
  have hpoly := mul_le_mul_of_nonneg_left (cofactor_polynomial_error_bound a b t m)
    (show 0 ≤ C*L*N by positivity)
  have hscaled : Z*E ≤ C*L*N*D*((m : ℝ)+1)^6 := by
    have hh := hnorm.trans hpoly
    convert hh using 1; dsimp [D]; ring
  change E ≤ (C*D*((m : ℝ)+1)^6/Z)*L*N
  apply (mul_le_mul_iff_right₀ hZ).mp
  apply hscaled.trans_eq
  field_simp

/-- Arbitrarily small relative error, with no hypothesis of cancellation in
small-conductor prime-weighted character sums. -/
theorem eventually_cofactor_all_modulus_relative_error (a b t l : ℕ) (ha : 1 ≤ a)
    (hab : a ≤ b) (ht : 22 ≤ t) (hlevel : 2*b+5 ≤ t) (hl : 2*a+1 ≤ l)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, ∀ A B : ℕ, cofactorScale l m ≤ B-A →
      ∀ u : ∀ d : ℕ, (ZMod d)ˣ,
        (∑ d ∈ Icc 1 (cofactorScale b m), |cofactorCongruenceWeight d (u d) A B (cofactorScale t m)-
          cofactorPrincipalMain d A B (cofactorScale t m)|) ≤
            δ*((B-A : ℕ) : ℝ)*(cofactorScale t m : ℝ) := by
  obtain ⟨K,hK,HK⟩ := exists_cofactor_all_modulus_power_saving a b t l ha hab ht hlevel hl
  have hlim := (Erdos821.tendsto_succ_pow_div_two_pow 6).const_mul K
  simp only [mul_zero] at hlim
  filter_upwards [hlim.eventually (eventually_le_nhds hδ)] with m hm
  intro A B hAB u
  have hm' : K*((m : ℝ)+1)^6/(2 : ℝ)^m ≤ δ := by convert hm using 1; ring
  exact (HK m A B hAB u).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hm' (Nat.cast_nonneg _)) (Nat.cast_nonneg _))

end Erdos821.AnalyticSieve
