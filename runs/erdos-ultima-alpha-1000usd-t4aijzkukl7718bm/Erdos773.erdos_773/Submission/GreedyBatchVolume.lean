import Submission.GreedyBatchDensityProfile

/-! Polynomial forward volumes for repeated mixed regularization. Coarse
exponents are used because only exp(m^5) total volume is required. -/
namespace Erdos773.GreedyBatchVolume
open GreedyBatchProfiles GreedyBatchProfileConditions GreedyBatchDensityStep
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option exponentiation.threshold 2048
noncomputable section

def increment (A : ℕ) : ℕ := 30*A+100
def volume (m A i : ℕ) : ℕ := m^(A+increment A*i)

lemma nat_power_slack (m i j c : ℕ) (hm : 100≤  m) (hc : c≤ 100) (hij : i<j) : c*m^i≤  m^j := by
  have hh := power_slack m i j c hm (by exact_mod_cast hc) hij
  exact_mod_cast hh

lemma degree_power (m A : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) (hd : d≤ (m:ℝ)^A) :
    (caps m d t C P).D2≤  m^(3*A+7) ∧ (caps m d t C P).D3≤  m^(3*A+7) ∧
    (caps m d t C P).D4≤  m^(3*A+7) := by
  let R : ℝ := (m:ℝ)^(A+2)
  have hdR : d≤ R := hd.trans (pow_le_pow_right₀ h.m_one (by omega))
  have htR : t≤ R := h.t_upper.trans (by
    simpa only [pow_one] using pow_le_pow_right₀ h.m_one (by omega : 1≤ A+2))
  have hd0 := h.d_pos.le
  have ht0 : 0≤ t := by have := h.t_one; linarith
  have hR0 : 0≤ R := by dsimp [R]; positivity
  have h2 := mul_le_mul hdR (pow_le_pow_left₀ ht0 htR 2) (sq_nonneg t) hR0
  have h3 := mul_le_mul (pow_le_pow_left₀ hd0 hdR 2) htR ht0 (sq_nonneg R)
  have h4 := pow_le_pow_left₀ hd0 hdR 3
  have he : R^3=(m:ℝ)^(3*A+6) := by dsimp [R]; rw [← pow_mul]; congr 1; omega
  have hs := power_slack m (3*A+6) (3*A+7) 4 h.large (by norm_num) (by omega)
  rw [← he] at hs
  obtain ⟨h2l,h2u,h3l,h3u,h4l,h4u,_⟩ := cap_bounds m d t C P h
  have hc2 : ((caps m d t C P).D2:ℝ)≤ (m:ℝ)^(3*A+7) := by nlinarith only [h2u,h2,hs]
  have hc3 : ((caps m d t C P).D3:ℝ)≤ (m:ℝ)^(3*A+7) := by nlinarith only [h3u,h3,hs]
  have hc4 : ((caps m d t C P).D4:ℝ)≤ (m:ℝ)^(3*A+7) := by nlinarith only [h4u,h4,hs,pow_nonneg hR0 3]
  exact ⟨by exact_mod_cast hc2,by exact_mod_cast hc3,by exact_mod_cast hc4⟩

/-- The exact mixed regularization factor is bounded by one fixed polynomial
in m, uniformly along a profile with d<=m^A. -/
theorem copies_bound (m A : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) (hd : d≤ (m:ℝ)^A) :
    copies (caps m d t C P)≤  m^(increment A) := by
  obtain ⟨h2,h3,h4⟩ := degree_power m A d t C P h hd
  have hm : 1≤  m := by have := h.large; omega
  have hpow : 1≤  m^(3*A+7) := one_le_pow₀ hm
  have h2plus : (caps m d t C P).D2+1≤  m^(3*A+8) := by
    have hh := nat_power_slack m (3*A+7) (3*A+8) 2 h.large (by decide) (by omega)
    omega
  have hheight : PolynomialSidonSlopes.height (caps m d t C P).D2≤  m^(9*A+25) := by
    have hh := Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left h2plus 3)
    have he : (m^(3*A+8))^3=m^(9*A+24) := by rw [← pow_mul]; congr 1; omega
    rw [he] at hh
    exact hh.trans (nat_power_slack m (9*A+24) (9*A+25) 3 h.large (by decide) (by omega))
  have hcap2 : 2*PolynomialSidonSlopes.height (caps m d t C P).D2+5≤  m^(9*A+26) := by
    have hpow : 1≤  m^(9*A+25) := one_le_pow₀ hm
    have hh := nat_power_slack m (9*A+25) (9*A+26) 7 h.large (by decide) (by omega)
    omega
  have hcap : MixedLayerRegularization.cap (caps m d t C P).D2 (caps m d t C P).D3
      (caps m d t C P).D4≤  m^(9*A+26) := by
    apply max_le (max_le _ _) hcap2
    · exact h3.trans (Nat.pow_le_pow_right (by omega) (by omega))
    · exact h4.trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hc2 : 2*MixedLayerRegularization.cap (caps m d t C P).D2 (caps m d t C P).D3
      (caps m d t C P).D4≤  m^(9*A+27) :=
    (Nat.mul_le_mul_left 2 hcap).trans (nat_power_slack m (9*A+26) (9*A+27) 2 h.large (by decide) (by omega))
  have hh := Nat.mul_le_mul_left 24 (Nat.pow_le_pow_left hc2 3)
  have he : (m^(9*A+27))^3=m^(27*A+81) := by rw [← pow_mul]; congr 1; omega
  rw [he] at hh
  apply hh.trans
  apply (nat_power_slack m (27*A+81) (27*A+82) 24 h.large (by decide) (by omega)).trans
  exact Nat.pow_le_pow_right (by omega) (by dsimp [increment]; omega)

lemma volume_step (m A i K : ℕ) (hK : K≤  m^(increment A)) : K*volume m A i≤ volume m A (i+1) := by
  apply (Nat.mul_le_mul_right _ hK).trans_eq
  dsimp [volume]
  rw [← pow_add]
  congr 1
  ring

lemma volume_exponent (m A i : ℕ) (hm : 3*increment A≤  m) (hi : i≤ 2*m^3) :
    A+increment A*i≤  m^4 := by
  have hA : A≤ increment A := by dsimp [increment]; omega
  have hinc : 100≤ increment A := by dsimp [increment]; omega
  have hm1 : 1≤ m := by omega
  have hp : 1≤  m^3 := one_le_pow₀ hm1
  have h1 := Nat.mul_le_mul_left (increment A) hi
  have h2 := Nat.mul_le_mul_right (m^3) hm
  have h3 := Nat.mul_le_mul_left (increment A) hp
  nlinarith only [hA,h1,h2,h3]

/-- All forward volumes stay below exp(m^5) for at most 2m^3 batches. -/
theorem volume_exp (m A i : ℕ) (hm : 3*increment A≤  m) (hi : i≤ 2*m^3) :
    (volume m A i:ℝ)≤ Real.exp ((m:ℝ)^5) := by
  have hinc : 100≤ increment A := by dsimp [increment]; omega
  have hmN : 1≤ m := by omega
  have hm0 : (0:ℝ)< m := by exact_mod_cast (show 0< m by omega)
  have hm1 : (1:ℝ)≤  m := by exact_mod_cast hmN
  have he : (A+increment A*i:ℕ)≤  m^4 := volume_exponent m A i hm hi
  have heR : ((A+increment A*i:ℕ):ℝ)≤ (m:ℝ)^4 := by exact_mod_cast he
  have hlog : Real.log (m:ℝ)≤  m := (Real.log_le_sub_one_of_pos hm0).trans (by linarith)
  have hh := mul_le_mul heR hlog (Real.log_nonneg hm1) (pow_nonneg hm0.le 4)
  calc
    _ = Real.exp (((A+increment A*i:ℕ):ℝ)*Real.log (m:ℝ)) := by
      rw [Real.exp_nat_mul,Real.exp_log hm0]
      norm_cast
    _ ≤  _ := Real.exp_le_exp.mpr (by nlinarith only [hh])

#print axioms degree_power
#print axioms copies_bound
#print axioms volume_step
#print axioms volume_exponent
#print axioms volume_exp
end
end Erdos773.GreedyBatchVolume
