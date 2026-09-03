import Submission.PolynomialProgressionThresholds

/-! An explicit coefficient for the polynomial progression-increment threshold.
All estimates here concern the existing four-term increment, not reciprocal
summability. -/
namespace Erdos3ExplicitProgressionThresholds
open Erdos3PolynomialProgressionThresholds Erdos3ProgressionIncrementParameters
  Erdos3SimultaneousQuadraticRecurrence Erdos3BohrQuadraticFlattening
  Erdos3RelativeStableBohr
open scoped Classical
set_option maxHeartbeats 3000000
set_option maxRecDepth 3000

lemma product_succ_le (a b : ℕ) : a*b+1 ≤ (a+1)*(b+1) := by nlinarith
lemma power_succ_le (a k : ℕ) : a^k+1 ≤ 2*(a+1)^k := by
  have h1 : 1 ≤ (a+1)^k := Nat.one_le_pow _ _ (by omega)
  have h2 := Nat.pow_le_pow_left (show a ≤ a+1 by omega) k
  omega

lemma mul_monomials (X P a b c d : ℕ) :
    (X^a*P^b)*(X^c*P^d) = X^(a+c)*P^(b+d) := by
  rw [pow_add,pow_add]
  ring

lemma pow_monomial (X P a b k : ℕ) :
    (X^a*P^b)^k = X^(a*k)*P^(b*k) := by rw [mul_pow,pow_mul,pow_mul]

lemma double_monomial_le {X P a b : ℕ} (hX : 2 ≤ X) :
    2*(X^a*P^b) ≤ X^(a+1)*P^b := by
  rw [pow_succ]
  nlinarith only [Nat.mul_le_mul_right (X^a*P^b) hX]

lemma recurrence_flatten_base_bound {X Z : ℕ}
    (hX : 2^100 ≤ X) (hZ : Z+2 ≤ X) :
    2^(11*Nat.clog 2 Z+72)+2 ≤ X^12 := by
  have h2 : 2 ≤ X := (by norm_num : 2 ≤ 2^100).trans hX
  have hp := pow_clog_two_le Z
  have he : 2^(11*Nat.clog 2 Z+72) = 2^72*(2^(Nat.clog 2 Z))^11 := by
    rw [Nat.add_comm, pow_add, Nat.mul_comm 11, pow_mul]
  rw [he]
  calc
    _ ≤ 2^72*(2*(Z+1))^11+2*(Z+1)^11 := by
      apply Nat.add_le_add
      · exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hp 11)
      · exact Nat.mul_le_mul_left 2 (Nat.one_le_pow _ _ (by omega))
    _ = (2^83+2)*(Z+1)^11 := by rw [mul_pow]; ring
    _ ≤ X*X^11 := by
      apply Nat.mul_le_mul
      · exact (by norm_num : 2^83+2 ≤ 2^100).trans hX
      · exact Nat.pow_le_pow_left (by omega) _
    _ = _ := by ring

/-- A common base controls rank and the reciprocal-gain scale. The coefficient
of the length polynomial is bounded explicitly by X^(500*(D+1)). -/
theorem incrementThreshold_explicit {D L X : ℕ} (r : ℝ)
    (hX : 2^100 ≤ X) (hZ : incrementPrecision r+2 ≤ X) (hD : D+1 ≤ X) :
    incrementThreshold D L r+1 ≤ X^(500*(D+1))*(L+1)^(69*(2*D+1)) := by
  let Z := incrementPrecision r
  generalize hPdef : L+1 = P
  let n := incrementLinearMesh L r
  let M := incrementLocalLength L r
  let R := recurrenceBound 1 (incrementAccuracy L r)
  let K := incrementCoarseLength L r
  let W := windowDenominator D Z
  let n₀ := incrementCoarseMesh D L r
  have h2 : 2 ≤ X := (by norm_num : 2 ≤ 2^100).trans hX
  have h28 : 28 ≤ X := (by norm_num : 28 ≤ 2^100).trans hX
  have h258 : 258 ≤ X := (by norm_num : 258 ≤ 2^100).trans hX
  have hX1 : 1 ≤ X := by omega
  have hP : 1 ≤ P := by omega
  have hn : n+1 ≤ X^1*P^1 := by
    have hh := roundedScale_nat_bound L r
    apply hh.trans
    simpa only [pow_one,← hPdef] using Nat.mul_le_mul_right P hZ
  have hn' : (2*n+1)+1 ≤ X^2*P^1 := by
    calc
      _ = 2*(n+1) := by omega
      _ ≤ 2*(X^1*P^1) := Nat.mul_le_mul_left 2 hn
      _ ≤ _ := double_monomial_le h2
  have hpow : (2*n+1)^2+1 ≤ X^5*P^2 := by
    calc
      _ ≤ 2*((2*n+1)+1)^2 := power_succ_le _ _
      _ ≤ 2*(X^2*P^1)^2 := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hn' 2)
      _ = 2*(X^4*P^2) := by rw [pow_monomial]
      _ ≤ _ := double_monomial_le h2
  have hM : M+1 ≤ X^6*P^3 := by
    have hA : ((2*n+1)^2*L)+1 ≤ X^5*P^3 := by
      calc
        _ ≤ ((2*n+1)^2+1)*(L+1) := product_succ_le _ _
        _ ≤ (X^5*P^2)*P := by simpa only [hPdef] using Nat.mul_le_mul_right P hpow
        _ = _ := by ring
    have hh := roundedScale_nat_bound ((2*n+1)^2*L) r
    have he : roundedScale (((2*n+1)^2*L : ℕ) : ℝ) r = M := by
      simp only [M,n,incrementLocalLength,Nat.cast_mul]
    rw [he] at hh
    calc
      _ ≤ (Z+2)*(((2*n+1)^2*L)+1) := hh
      _ ≤ X*(X^5*P^3) := Nat.mul_le_mul hZ hA
      _ = _ := by ring
  have hR : R+1 ≤ X^144*P^66 := by
    have hh := recurrence_flatten_bound M (Nat.clog 2 Z)
    change R+1 ≤ _ at hh
    calc
      _ ≤ (2^(11*Nat.clog 2 Z+72)+2)*(M+1)^22 := hh
      _ ≤ X^12*(X^6*P^3)^22 := Nat.mul_le_mul
        (recurrence_flatten_base_bound hX hZ) (Nat.pow_le_pow_left hM 22)
      _ = _ := by rw [pow_monomial]; ring
  have hK : K+1 ≤ X^151*P^69 := by
    have hh := roundedScale_nat_bound (R*M) r
    have he : roundedScale ((R*M : ℕ) : ℝ) r = K := by
      simp only [K,R,M,incrementCoarseLength,Nat.cast_mul]
    rw [he] at hh
    calc
      _ ≤ (Z+2)*(R*M+1) := hh
      _ ≤ X*((R+1)*(M+1)) := Nat.mul_le_mul hZ (product_succ_le _ _)
      _ ≤ X*((X^144*P^66)*(X^6*P^3)) := Nat.mul_le_mul_left X (Nat.mul_le_mul hR hM)
      _ = _ := by rw [mul_monomials]; ring
  have hW : W ≤ X^3 := by
    have hZ' : Z ≤ X := by change Z+2 ≤ X at hZ; omega
    have hD' : 7*D+1 ≤ 7*X := by omega
    calc
      _ = 4*Z*(7*D+1) := rfl
      _ ≤ 4*X*(7*X) := Nat.mul_le_mul (Nat.mul_le_mul_left 4 hZ') hD'
      _ = 28*X^2 := by ring
      _ ≤ X*X^2 := Nat.mul_le_mul_right (X^2) h28
      _ = _ := by ring
  have hn₀ : n₀+1 ≤ X^155*P^69 := by
    have hcoef : 256*W+2 ≤ X^4 := by
      have hX3 : 1 ≤ X^3 := Nat.one_le_pow _ _ hX1
      calc
        _ ≤ 258*X^3 := by nlinarith only [hW,hX3]
        _ ≤ X*X^3 := Nat.mul_le_mul_right (X^3) h258
        _ = _ := by ring
    calc
      _ = 256*K*W+2 := by change 256*K*W+1+1 = 256*K*W+2; omega
      _ ≤ (256*W+2)*(K+1) := by nlinarith only [Nat.zero_le K,Nat.zero_le (256*W)]
      _ ≤ X^4*(X^151*P^69) := Nat.mul_le_mul hcoef hK
      _ = _ := by ring
  have hn₀' : (2*n₀+1)+1 ≤ X^156*P^69 := by
    calc
      _ = 2*(n₀+1) := by omega
      _ ≤ 2*(X^155*P^69) := Nat.mul_le_mul_left 2 hn₀
      _ ≤ _ := double_monomial_le h2
  have hp₀ : (2*n₀+1)^(2*D)+1 ≤ X^(312*D+1)*P^(138*D) := by
    calc
      _ ≤ 2*((2*n₀+1)+1)^(2*D) := power_succ_le _ _
      _ ≤ 2*(X^156*P^69)^(2*D) := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hn₀' _)
      _ = 2*(X^(312*D)*P^(138*D)) := by rw [pow_monomial,show 156*(2*D) = 312*D by omega,show 69*(2*D) = 138*D by omega]
      _ ≤ _ := double_monomial_le h2
  have h257 : 257^(2*D)+1 ≤ X^(2*D+1) := by
    calc
      _ ≤ X^(2*D)+X^(2*D) := Nat.add_le_add
        (Nat.pow_le_pow_left (by omega : 257 ≤ X) _) (Nat.one_le_pow _ _ hX1)
      _ ≤ _ := by rw [pow_succ]; nlinarith only [Nat.mul_le_mul_right (X^(2*D)) h2]
  have hT : incrementTerminalCost D L r+1 ≤ X^(314*D+153)*P^(138*D+69) := by
    calc
      _ ≤ (((2*n₀+1)^(2*D)*K)+1)*(257^(2*D)+1) := product_succ_le _ _
      _ ≤ (((2*n₀+1)^(2*D)+1)*(K+1))*(257^(2*D)+1) :=
        Nat.mul_le_mul_right _ (product_succ_le _ _)
      _ ≤ ((X^(312*D+1)*P^(138*D))*(X^151*P^69))*(X^(2*D+1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul hp₀ hK) h257
      _ = _ := by
        rw [mul_monomials]
        rw [show X^(2*D+1) = X^(2*D+1)*P^0 by simp, mul_monomials]
        rw [show 312*D+1+151+(2*D+1) = 314*D+153 by omega, Nat.add_zero]
  calc
    _ ≤ (Z+2)*(incrementTerminalCost D L r+1) := roundedScale_nat_bound _ r
    _ ≤ X*(X^(314*D+153)*P^(138*D+69)) := Nat.mul_le_mul hZ hT
    _ = X^(314*D+154)*P^(69*(2*D+1)) := by
      rw [show 69*(2*D+1) = 138*D+69 by omega, pow_succ]
      ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hX1 (by omega))

#print axioms incrementThreshold_explicit
end Erdos3ExplicitProgressionThresholds
