import Submission.RoughReciprocalBand
import Submission.DiagonalFullRoughCutoff

/-! A fixed small power sieve scale suitable for thin endpoint bands. -/
namespace Erdos371
open Filter
open scoped Topology

lemma nat_pow_le_of_log_le (z N r : ℕ) (hz : 0 < z) (hN : 0 < N)
    (hlog : (r : ℝ)*Real.log z ≤ Real.log N) : z^r ≤ N := by
  have hzR : (0 : ℝ) < z := by exact_mod_cast hz
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hh : Real.log ((z : ℝ)^r) ≤ Real.log N := by simpa only [Real.log_pow] using hlog
  have he := (Real.log_le_log_iff (by positivity : (0 : ℝ) < (z : ℝ)^r) hNR).mp hh
  exact_mod_cast he

lemma rootRoughCutoff_succ_power_eventually_le (k r : ℕ) (hr : 2*r ≤ k+1) :
    ∀ᶠ N : ℕ in atTop, (rootRoughCutoff k N+1)^r ≤ N := by
  filter_upwards [rootRoughCutoff_log_eventually_le k,eventually_gt_atTop (1 : ℕ)] with N hh hN
  apply nat_pow_le_of_log_le _ N r (by omega) (by omega)
  simp only [Nat.cast_add,Nat.cast_one]
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hb := (div_le_iff₀ hlogN).mp hh
  have hrR : (r : ℝ)*(2/(k+1 : ℝ)) ≤ 1 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < k+1)).mpr
    simpa only [one_mul,mul_comm,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one] using
      (show ((2*r : ℕ) : ℝ) ≤ ((k+1 : ℕ) : ℝ) by exact_mod_cast hr)
  have ht := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (α := ℝ) r)
  calc
    _ ≤ (r : ℝ)*(2/(k+1 : ℝ)*Real.log N) := ht
    _ = ((r : ℝ)*(2/(k+1 : ℝ)))*Real.log N := by ring
    _ ≤ Real.log N := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hrR hlogN.le

/-- K and the scale are fixed from L, not chosen with a moving exponent. -/
theorem exists_rough_endpoint_scale (W : ℕ → ℕ) (L : ℕ) (hL : 0 < L)
    (hW : ∀ᶠ N : ℕ in atTop, N ≤ (W N)^L) :
    ∃ K : ℕ, ∃ z : ℕ → ℕ, Tendsto z atTop atTop ∧
      (∀ᶠ N : ℕ in atTop, 1 ≤ z N ∧ z N ≤ W N ∧ N ≤ (z N+1)^K ∧ (z N+1)^128 ≤ N) := by
  let k := 256*(L+1)-1
  let z := rootRoughCutoff k
  have he : k+1=256*(L+1) := by dsimp [k]; omega
  have ht : Tendsto z atTop atTop := rootRoughCutoff_atTop k
  refine ⟨k+1,z,ht,?_⟩
  filter_upwards [ht.eventually_ge_atTop 1,hW,
    rootRoughCutoff_succ_power_eventually_le k L (by rw [he]; omega),
    rootRoughCutoff_succ_power_eventually_le k 128 (by rw [he]; omega)] with N hz hw hzL hz128
  refine ⟨hz,?_,?_,hz128⟩
  · have hp : (z N)^L ≤ (W N)^L :=
      (Nat.pow_le_pow_left (Nat.le_succ (z N)) L).trans (hzL.trans hw)
    exact (Nat.pow_le_pow_iff_left hL.ne').mp hp
  · exact (rootRoughCutoff_power k N).trans (Nat.pow_le_pow_left (Nat.le_succ _) _)

#print axioms exists_rough_endpoint_scale
end Erdos371
