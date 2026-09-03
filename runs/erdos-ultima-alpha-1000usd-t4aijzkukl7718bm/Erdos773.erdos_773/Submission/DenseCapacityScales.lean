import Submission.DenseSidonSeedWitnesses

/-! Exact reward bookkeeping for the density-strengthened generic obstruction. -/
namespace Erdos773.DenseCapacityScales
open DenseSidonSeedWitnesses
set_option maxHeartbeats 3000000

lemma capacity_cost (x u : ℝ) (hx : 0<x) (hu : 0<u) (g : ℕ)
    (he : u=x^(2*g)) :
    (1/(4*u*x))^(2*(g+1))*(u^2)^(g+2) = u/(4^(2*(g+1))*x^2) := by
  have hp : (u^2)^(g+2) = u^(2*(g+1))*u^2 := by
    rw [← pow_mul,← pow_add]
    congr 1
  rw [hp,div_pow,one_pow,mul_pow,mul_pow]
  have hc : 1/(4^(2*(g+1))*u^(2*(g+1))*x^(2*(g+1))) *
      (u^(2*(g+1))*u^2) = u^2/(4^(2*(g+1))*x^(2*(g+1))) := by
    field_simp
  rw [hc,show 2*(g+1)=2*g+2 by omega,pow_add x,← he]
  field_simp

lemma reward_scales {n R g : ℕ} (hn : 1000 ≤ n) (hR : 0<R) (hg : 1≤g)
    (he : (R:ℝ)^50=(n:ℝ)^(2*g)) :
    (R:ℝ)^50/(8*n) ≤ density n R*(R:ℝ)^100-
      (density n R)^3*(R:ℝ)^200-
      (density n R)^(2*(g+1))*((R:ℝ)^100)^(g+2)-1 := by
  have hnR : (1000:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith only [hnR]
  have hR0 : (0:ℝ)<R := by exact_mod_cast hR
  let u : ℝ := (R:ℝ)^50
  have hu : 0<u := by dsimp [u]; positivity
  have hu2 : (R:ℝ)^100=u^2 := by dsimp [u]; ring
  have hu4 : (R:ℝ)^200=u^4 := by dsimp [u]; ring
  have h₁ : density n R*(R:ℝ)^100=u/(4*n) := by
    unfold density
    rw [hu2]
    change 1/(4*u*n)*u^2=u/(4*n)
    field_simp
  have h₂ : (density n R)^3*(R:ℝ)^200=u/(64*(n:ℝ)^3) := by
    unfold density
    rw [hu4]
    change (1/(4*u*n))^3*u^4=u/(64*(n:ℝ)^3)
    field_simp
    ring
  have h₃ : (density n R)^(2*(g+1))*((R:ℝ)^100)^(g+2) =
      u/((4:ℝ)^(2*(g+1))*(n:ℝ)^2) := by
    unfold density
    rw [hu2]
    exact capacity_cost (n:ℝ) u hn0 hu g he
  have hpow : (n:ℝ)^2 ≤ u := by
    rw [show u=(n:ℝ)^(2*g) from he]
    exact pow_le_pow_right₀ (by linarith only [hnR]) (by omega)
  have hn1 : (1:ℝ) ≤ n := by linarith only [hnR]
  have hn2 : (1:ℝ) ≤ (n:ℝ)^2 := one_le_pow₀ hn1
  have h4 : (16:ℝ) ≤ (4:ℝ)^(2*(g+1)) := by
    have hh := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 4) (show 2≤2*(g+1) by omega)
    norm_num at hh ⊢
    exact hh
  have hcost₂ : u/(64*(n:ℝ)^3) ≤ (u/(n:ℝ))/64 := by
    rw [div_div]
    apply div_le_div_of_nonneg_left hu.le (by positivity)
    have hh := mul_le_mul_of_nonneg_left hn2 hn0.le
    nlinarith only [hh]
  have hcost₃ : u/((4:ℝ)^(2*(g+1))*(n:ℝ)^2) ≤ (u/(n:ℝ))/64 := by
    have hden : (64:ℝ)*n ≤ (4:ℝ)^(2*(g+1))*(n:ℝ)^2 := by
      have hh := mul_le_mul_of_nonneg_right h4 (sq_nonneg (n:ℝ))
      have hn4 := mul_nonneg (show (0:ℝ) ≤ (n:ℝ)-4 by linarith only [hnR]) hn0.le
      nlinarith only [hh,hn4]
    rw [div_div]
    exact div_le_div_of_nonneg_left hu.le (by positivity) (by nlinarith only [hden])
  have hmass : (16:ℝ) ≤ u/(n:ℝ) := by
    apply (le_div_iff₀ hn0).mpr
    have hh := mul_nonneg (show (0:ℝ) ≤ (n:ℝ)-16 by linarith only [hnR]) hn0.le
    nlinarith only [hh,hpow]
  rw [h₁,h₂,h₃]
  change u/(8*n) ≤ _
  have hm1 : u/(4*n)=(u/n)/4 := by ring
  have hm2 : u/(8*n)=(u/n)/8 := by ring
  rw [hm1,hm2]
  linarith only [hcost₂,hcost₃,hmass]

lemma capacity_cost_endpoint (x u : ℝ) (hx : 0<x) (hu : 0<u) (g : ℕ)
    (he : u=x^(2*g+1)) :
    (1/(4*u*x))^(2*(g+1))*(u^2)^(g+2) = u/(4^(2*(g+1))*x) := by
  have hp : (u^2)^(g+2) = u^(2*(g+1))*u^2 := by
    rw [← pow_mul,← pow_add]
    congr 1
  rw [hp,div_pow,one_pow,mul_pow,mul_pow]
  have hc : 1/(4^(2*(g+1))*u^(2*(g+1))*x^(2*(g+1))) *
      (u^(2*(g+1))*u^2) = u^2/(4^(2*(g+1))*x^(2*(g+1))) := by
    field_simp
  rw [hc,show 2*(g+1)=(2*g+1)+1 by omega,pow_add x,← he]
  field_simp

lemma reward_scales_endpoint {n R g : ℕ} (hn : 1000 ≤ n) (hR : 0<R) (hg : 1≤g)
    (he : (R:ℝ)^50=(n:ℝ)^(2*g+1)) :
    (R:ℝ)^50/(8*n) ≤ density n R*(R:ℝ)^100-
      (density n R)^3*(R:ℝ)^200-
      (density n R)^(2*(g+1))*((R:ℝ)^100)^(g+2)-1 := by
  have hnR : (1000:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith only [hnR]
  have hR0 : (0:ℝ)<R := by exact_mod_cast hR
  let u : ℝ := (R:ℝ)^50
  have hu : 0<u := by dsimp [u]; positivity
  have hu2 : (R:ℝ)^100=u^2 := by dsimp [u]; ring
  have hu4 : (R:ℝ)^200=u^4 := by dsimp [u]; ring
  have h₁ : density n R*(R:ℝ)^100=u/(4*n) := by
    unfold density
    rw [hu2]
    change 1/(4*u*n)*u^2=u/(4*n)
    field_simp
  have h₂ : (density n R)^3*(R:ℝ)^200=u/(64*(n:ℝ)^3) := by
    unfold density
    rw [hu4]
    change (1/(4*u*n))^3*u^4=u/(64*(n:ℝ)^3)
    field_simp
    ring
  have h₃ : (density n R)^(2*(g+1))*((R:ℝ)^100)^(g+2) =
      u/((4:ℝ)^(2*(g+1))*n) := by
    unfold density
    rw [hu2]
    exact capacity_cost_endpoint (n:ℝ) u hn0 hu g he
  have hpow : (n:ℝ)^2 ≤ u := by
    rw [show u=(n:ℝ)^(2*g+1) from he]
    exact pow_le_pow_right₀ (by linarith only [hnR]) (by omega)
  have hn1 : (1:ℝ) ≤ n := by linarith only [hnR]
  have hn2 : (1:ℝ) ≤ (n:ℝ)^2 := one_le_pow₀ hn1
  have h4 : (64:ℝ) ≤ (4:ℝ)^(2*(g+1)) := by
    have hh := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 4) (show 3≤2*(g+1) by omega)
    norm_num at hh ⊢
    exact hh
  have hcost₂ : u/(64*(n:ℝ)^3) ≤ (u/(n:ℝ))/64 := by
    rw [div_div]
    apply div_le_div_of_nonneg_left hu.le (by positivity)
    have hh := mul_le_mul_of_nonneg_left hn2 hn0.le
    nlinarith only [hh]
  have hcost₃ : u/((4:ℝ)^(2*(g+1))*n) ≤ (u/(n:ℝ))/64 := by
    rw [div_div]
    apply div_le_div_of_nonneg_left hu.le (by positivity)
    nlinarith only [mul_le_mul_of_nonneg_right h4 hn0.le]
  have hmass : (16:ℝ) ≤ u/(n:ℝ) := by
    apply (le_div_iff₀ hn0).mpr
    have hh := mul_nonneg (show (0:ℝ) ≤ (n:ℝ)-16 by linarith only [hnR]) hn0.le
    nlinarith only [hh,hpow]
  rw [h₁,h₂,h₃]
  change u/(8*n) ≤ _
  have hm1 : u/(4*n)=(u/n)/4 := by ring
  have hm2 : u/(8*n)=(u/n)/8 := by ring
  rw [hm1,hm2]
  linarith only [hcost₂,hcost₃,hmass]

#print axioms capacity_cost
#print axioms reward_scales
#print axioms capacity_cost_endpoint
#print axioms reward_scales_endpoint
end Erdos773.DenseCapacityScales
