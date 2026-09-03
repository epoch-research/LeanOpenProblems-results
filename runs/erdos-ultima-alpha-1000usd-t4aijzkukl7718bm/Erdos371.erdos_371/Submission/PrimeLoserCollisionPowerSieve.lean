import Submission.PrimeHarmonicLogEnvelope

/-! A power-sieve form of the collision estimate, with all dependence on
the cofactor cutoff explicit. -/
namespace Erdos371
open Finset FiniteSieve

noncomputable def collisionLogConstant : ℝ := 32*Real.exp 3*Real.exp 144*(6 : ℝ)^72
noncomputable def collisionPowerConstant : ℝ := collisionLogConstant*(1024 : ℝ)^3

lemma primeLoserCollisions_log_ratio_bound (B N X z : ℕ)
    (hN : 0<N) (hB : 1 ≤ B) (hz : 1 ≤ z) (hzB : z ≤ B)
    (hX0 : 1 ≤ X) (hX : N/(B+1) ≤ X) (hXN : X ≤ N) :
    ((primeLoserCollisions B N).card : ℝ)/N ≤
      collisionLogConstant*X*(1+Real.log X)^75/(Real.log (z+1 : ℝ))^3+
        8*(X : ℝ)^20*(z+1 : ℝ)^96/N := by
  have hN0 : (0 : ℝ)<N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log (z+1 : ℝ) := Real.log_nonneg (by norm_cast; omega)
  have hb := div_le_div_of_nonneg_right (primeLoserCollisions_sieve_bound B N X z hB hz hzB hX hXN) hN0.le
  have hw := mul_le_mul_of_nonneg_left (collision_primeHarmonic_weight_bound X hX0)
    (show (0 : ℝ) ≤ 32*Real.exp 3*X/(Real.log (z+1 : ℝ))^3 by positivity)
  calc
    _ ≤ (32*Real.exp 3*X/(Real.log (z+1 : ℝ))^3)*
        (Real.exp (3*primeHarmonic (3+2*X^2))*(harmonic X : ℝ)^3)+
        8*(X : ℝ)^20*(z+1 : ℝ)^96/N := by
      convert hb using 1
      field_simp
    _ ≤ _ := by
      convert add_le_add_right hw (8*(X : ℝ)^20*(z+1 : ℝ)^96/N) using 1 <;>
        dsimp only [collisionLogConstant] <;> ring

/-- With z=floor(N^(1/1024)), the collision count has a cubic logarithmic
saving and a power-saving rounding error. -/
theorem primeLoserCollisions_power_sieve_ratio (B N X : ℕ)
    (hN : 1<N) (hX0 : 1 ≤ X) (hX : N/(B+1) ≤ X) (hXN : X ≤ N)
    (hB : (N : ℝ)^(1/2 : ℝ) ≤ B) :
    ((primeLoserCollisions B N).card : ℝ)/N ≤
      collisionPowerConstant*X*(1+Real.log X)^75/(Real.log N)^3+
        (8*(2 : ℝ)^96)*(X : ℝ)^20/(N : ℝ)^(1/2 : ℝ) := by
  let z := ⌊(N : ℝ)^(1/1024 : ℝ)⌋₊
  have hN0 : (0 : ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN.le
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hB1 : 1 ≤ B := by
    exact_mod_cast (Real.one_le_rpow hN1 (by norm_num : (0 : ℝ) ≤ 1/2)).trans hB
  have hz1 : 1 ≤ z := (Nat.one_le_floor_iff _).mpr (Real.one_le_rpow hN1 (by norm_num))
  have hzB : z ≤ B := by
    have hh := (Nat.floor_le (Real.rpow_nonneg hN0.le (1/1024 : ℝ))).trans
      ((Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num : (1/1024 : ℝ) ≤ 1/2)).trans hB)
    exact_mod_cast hh
  have hzupper : (z+1 : ℝ) ≤ 2*(N : ℝ)^(1/1024 : ℝ) := by
    have hz := Nat.floor_le (Real.rpow_nonneg hN0.le (1/1024 : ℝ))
    have ho := Real.one_le_rpow hN1 (by norm_num : (0 : ℝ) ≤ 1/1024)
    dsimp only [z]
    linarith
  have hlogz : Real.log N/1024 ≤ Real.log (z+1 : ℝ) := by
    have hh := Real.log_le_log (Real.rpow_pos_of_pos hN0 (1/1024 : ℝ))
      (Nat.lt_floor_add_one ((N : ℝ)^(1/1024 : ℝ))).le
    rw [Real.log_rpow hN0] at hh
    convert hh using 1
    ring
  have hcube : (Real.log N/1024)^3 ≤ (Real.log (z+1 : ℝ))^3 :=
    pow_le_pow_left₀ (by positivity) hlogz 3
  have hXlog : 0 ≤ 1+Real.log X := by have := Real.log_natCast_nonneg X; positivity
  have hmain := div_le_div_of_nonneg_left
    (show 0 ≤ collisionLogConstant*X*(1+Real.log X)^75 by unfold collisionLogConstant; positivity)
    (by positivity : 0 < (Real.log N/1024)^3) hcube
  have hzpow : (z+1 : ℝ)^96 ≤ (2 : ℝ)^96*(N : ℝ)^(1/2 : ℝ) := by
    calc
      _ ≤ (2*(N : ℝ)^(1/1024 : ℝ))^96 := pow_le_pow_left₀ (by positivity) hzupper 96
      _ = (2 : ℝ)^96*(N : ℝ)^(3/32 : ℝ) := by
        rw [mul_pow]
        congr 1
        rw [← Real.rpow_natCast,← Real.rpow_mul hN0.le]
        norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num : (3/32 : ℝ) ≤ 1/2)) (by positivity)
  have herr := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hzpow (show 0 ≤ 8*(X : ℝ)^20 by positivity)) hN0.le
  have hpowers : (N : ℝ)^(1/2 : ℝ)/N=1/(N : ℝ)^(1/2 : ℝ) := by
    calc
      _ = (N : ℝ)^(1/2 : ℝ)/(N : ℝ)^(1 : ℝ) := by rw [Real.rpow_one]
      _ = (N : ℝ)^(-(1/2 : ℝ)) := by rw [← Real.rpow_sub hN0]; norm_num
      _ = _ := by rw [Real.rpow_neg hN0.le]; simp only [one_div]
  apply (primeLoserCollisions_log_ratio_bound B N X z (by omega) hB1 hz1 hzB hX0 hX hXN).trans
  apply add_le_add
  · apply hmain.trans_eq
    unfold collisionPowerConstant
    ring
  · apply herr.trans_eq
    calc
      _ = (8*(2 : ℝ)^96)*(X : ℝ)^20*((N : ℝ)^(1/2 : ℝ)/N) := by ring
      _ = _ := by rw [hpowers]; ring

#print axioms primeLoserCollisions_power_sieve_ratio
end Erdos371
