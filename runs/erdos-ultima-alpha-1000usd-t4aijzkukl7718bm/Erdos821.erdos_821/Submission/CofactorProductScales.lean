import Submission.CofactorBilinearKernel
import Submission.CofactorMeanScales

/-!
# Product-half-level scales for the retained bilinear mean
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 3000000

lemma cofactorScale_eq (t m : ℕ) : cofactorScale t m = 2^(256*t*m) := by
  unfold cofactorScale progressionScaleN
  congr 1
  ring

lemma sqrt_cofactorScale (t m : ℕ) : Real.sqrt (cofactorScale t m) = (2 : ℝ)^(128*t*m) := by
  rw [cofactorScale_cast]
  have he : 256*t*m=(128*t*m)*2 := by ring
  rw [he,pow_mul,Real.sqrt_sq (by positivity)]

lemma cofactorScale_root_saving (t m : ℕ) (ht : 1 ≤ t) :
    ((2 : ℝ)^m)^2 ≤ Real.sqrt (cofactorScale t m) := by
  rw [sqrt_cofactorScale,← pow_mul]
  exact pow_le_pow_right₀ (by norm_num) (by nlinarith only [Nat.mul_le_mul_right m ht])

lemma cofactorScale_product_level_saving (b l t m : ℕ) (hlevel : 2*b+1 ≤ l+t) :
    ((2 : ℝ)^m)^2*(cofactorScale b m : ℝ) ≤
      Real.sqrt (cofactorScale l m)*Real.sqrt (cofactorScale t m) := by
  rw [cofactorScale_cast,sqrt_cofactorScale,sqrt_cofactorScale,← pow_mul,← pow_add,← pow_add]
  apply pow_le_pow_right₀ (by norm_num)
  have hh := Nat.mul_le_mul_right m hlevel
  nlinarith only [hh,Nat.zero_le m]

lemma cofactorScale_modulus_saving (a m : ℕ) (ha : 1 ≤ a) :
    ((2 : ℝ)^m)^2 ≤ cofactorScale a m := by
  have hh := cofactorScale_lift_saving 0 a m ha
  simpa [cofactorScale,progressionScaleN] using hh

lemma cofactorScale_log_add_two_le (v m B : ℕ) (hB : B ≤ cofactorScale v m) :
    2+Real.log ((B : ℝ)+2) ≤ (256*(v : ℝ)+4)*((m : ℝ)+1) := by
  have hS : (1 : ℝ) ≤ cofactorScale v m := by exact_mod_cast cofactorScale_pos v m
  have hBS : (B : ℝ) ≤ cofactorScale v m := by exact_mod_cast hB
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (B : ℝ)+2)
    (show (B : ℝ)+2 ≤ 3*(cofactorScale v m : ℝ) by linarith)
  rw [Real.log_mul (by norm_num) (by positivity : (cofactorScale v m : ℝ) ≠ 0)] at hlog
  have h3 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
  nlinarith only [hlog,h3,cofactorScale_log_le v m,Nat.cast_nonneg (α := ℝ) m]

lemma cofactorBilinearShape_mono_right (Q R B X N : ℕ) (hXN : X ≤ N) :
    cofactorBilinearShape Q R B X ≤ cofactorBilinearShape Q R B N := by
  unfold cofactorBilinearShape
  have hx : (X : ℝ) ≤ N := by exact_mod_cast hXN
  gcongr

/-- Each of the four terms has a power saving relative to the full product. -/
lemma cofactorScale_bilinear_shape_saving (a b l t m B : ℕ)
    (ha : 1 ≤ a) (hl : 1 ≤ l) (ht : 1 ≤ t) (hlevel : 2*b+1 ≤ l+t)
    (hB : cofactorScale l m ≤ B) :
    ((2 : ℝ)^m)^2*cofactorBilinearShape (cofactorScale b m) (cofactorScale a m) B (cofactorScale t m) ≤
      4*(B : ℝ)*(cofactorScale t m : ℝ) := by
  let Z : ℝ := (2 : ℝ)^m
  let N : ℝ := cofactorScale t m
  let R : ℝ := cofactorScale a m
  let Q : ℝ := cofactorScale b m
  have hBN : (cofactorScale l m : ℝ) ≤ B := by exact_mod_cast hB
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hR0 : 0 < R := by dsimp [R]; exact_mod_cast cofactorScale_pos a m
  have hsB := Real.sq_sqrt hB0
  have hsN := Real.sq_sqrt hN0
  have hroot : Real.sqrt (cofactorScale l m) ≤ Real.sqrt B := Real.sqrt_le_sqrt hBN
  have hQ : Z^2*Q ≤ Real.sqrt B*Real.sqrt N :=
    (cofactorScale_product_level_saving b l t m hlevel).trans
      (mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg _))
  have hZB : Z^2 ≤ Real.sqrt B := (cofactorScale_root_saving l m hl).trans hroot
  have hZN : Z^2 ≤ Real.sqrt N := cofactorScale_root_saving t m ht
  have hZR : Z^2 ≤ R := cofactorScale_modulus_saving a m ha
  have hfirst : Z^2*(Q*Real.sqrt B*Real.sqrt N) ≤ (B : ℝ)*N := by
    have hh := mul_le_mul_of_nonneg_right hQ (mul_nonneg (Real.sqrt_nonneg (B : ℝ)) (Real.sqrt_nonneg N))
    calc
      _ ≤ (Real.sqrt B)^2*(Real.sqrt N)^2 := by convert hh using 1 <;> ring
      _ = _ := by rw [hsB,hsN]
  have hsecond : Z^2*((B : ℝ)*Real.sqrt N) ≤ (B : ℝ)*N := by
    have hh := mul_le_mul_of_nonneg_right hZN (mul_nonneg hB0 (Real.sqrt_nonneg N))
    calc
      _ ≤ (B : ℝ)*(Real.sqrt N)^2 := by convert hh using 1; ring
      _ = _ := by rw [hsN]
  have hthird : Z^2*(N*Real.sqrt B) ≤ (B : ℝ)*N := by
    have hh := mul_le_mul_of_nonneg_right hZB (mul_nonneg hN0 (Real.sqrt_nonneg (B : ℝ)))
    calc
      _ ≤ (Real.sqrt B)^2*N := by convert hh using 1; ring
      _ = _ := by rw [hsB]
  have hfourth : Z^2*((B : ℝ)*N/R) ≤ (B : ℝ)*N := by
    have hh := mul_le_mul_of_nonneg_right hZR (div_nonneg (mul_nonneg hB0 hN0) hR0.le)
    apply hh.trans_eq
    field_simp
  change Z^2*cofactorBilinearShape _ _ _ _ ≤ 4*(B : ℝ)*N
  change Z^2*(Q*Real.sqrt B*Real.sqrt N+(B : ℝ)*Real.sqrt N+N*Real.sqrt B+(B : ℝ)*N/R) ≤ _
  linarith only [hfirst,hsecond,hthird,hfourth]

end Erdos821.AnalyticSieve
