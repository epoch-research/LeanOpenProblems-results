import Submission.GaussianDirectionSum

/-! A uniform O(N log N) bound, with leading coefficient below one third,
for the actual four-root square-collision degree. -/
namespace Erdos773.GaussianIncidentDegree
open Finset Filter GaussianIncidentEncoding GaussianDirectionSum GaussianRadialCounting
open SquareCollisionCodegrees
set_option maxHeartbeats 2000000
noncomputable section

lemma log_sqrt_bound {N : ℕ} (hN : 1 ≤ N) :
    2*Real.log (Nat.sqrt (2*N):ℝ) ≤ Real.log (2*(N:ℝ)) := by
  have hs : 0<Nat.sqrt (2*N) := Nat.sqrt_pos.mpr (by omega)
  have hsR : (0:ℝ)<Nat.sqrt (2*N) := by exact_mod_cast hs
  have hb : (Nat.sqrt (2*N):ℝ)^2 ≤ 2*(N:ℝ) := by exact_mod_cast Nat.sqrt_le' (2*N)
  have hl := Real.log_le_log (sq_pos_of_pos hsR) hb
  simpa only [Real.log_pow,Nat.cast_ofNat] using hl

lemma reciprocal_log_bound {N : ℕ} (hN : 1 ≤ N) :
    (∑ p ∈ directions N, 1/(normSq p:ℝ)) ≤ (83/250:ℝ)*Real.log (2*(N:ℝ))+28002 := by
  have hs := reciprocal_sum_bound N
  have ht := triangle_sum_bound (M := Nat.sqrt (2*N)) (Nat.sqrt_pos.mpr (by omega))
  have hl := log_sqrt_bound hN
  nlinarith only [hs,ht,hl]

/-- Finite bound, uniform in the incident root. -/
theorem finite_degree_bound {a N : ℕ} (ha : 0<a) (haN : a ≤ N) :
    (HypergraphDegreeTrim.degree (edges (Icc 1 N)) a:ℝ) ≤
      (N:ℝ)*((83/250:ℝ)*Real.log (2*(N:ℝ))+28006) := by
  have hd := GaussianIncidentCounting.degree_bound ha haN
  have he : (∑ p ∈ directions N, ((N:ℝ)/normSq p+1)) =
      (N:ℝ)*(∑ p ∈ directions N, 1/(normSq p:ℝ))+(directions N).card := by
    rw [sum_add_distrib,mul_sum]
    simp only [mul_one_div,sum_const,nsmul_eq_mul,mul_one]
  rw [he] at hd
  have hr := mul_le_mul_of_nonneg_left (reciprocal_log_bound (by omega : 1 ≤ N))
    (Nat.cast_nonneg N : (0:ℝ) ≤ N)
  have hc : ((directions N).card:ℝ) ≤ 4*(N:ℝ) := by exact_mod_cast directions_card N
  nlinarith only [hd,hr,hc]

/-- A uniform eventual maximum-degree estimate for the actual four-support
square-collision hypergraph. This is not an independent-set bound. -/
theorem eventual_degree_bound : ∀ᶠ N : ℕ in atTop, ∀ a ∈ Icc 1 N,
    (HypergraphDegreeTrim.degree (edges (Icc 1 N)) a:ℝ) ≤
      (333/1000:ℝ)*(N:ℝ)*Real.log (N:ℝ) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 1,
    hlog.eventually_ge_atTop (1000*((83/250:ℝ)*Real.log 2+28006))] with N hN hL
  intro a ha
  obtain ⟨ha,haN⟩ := mem_Icc.mp ha
  have h := finite_degree_bound ha haN
  have hNR : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  rw [Real.log_mul (by norm_num) hNR.ne'] at h
  have hh : (83/250:ℝ)*(Real.log 2+Real.log (N:ℝ))+28006 ≤
      (333/1000:ℝ)*Real.log (N:ℝ) := by linarith only [hL]
  have hm := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg N : (0:ℝ) ≤ N)
  nlinarith only [h,hm]

#print axioms log_sqrt_bound
#print axioms reciprocal_log_bound
#print axioms finite_degree_bound
#print axioms eventual_degree_bound
end
end Erdos773.GaussianIncidentDegree
