import Submission.PoolSupplyBudget

/-!
# Variable prime-variable bands for the retained multiplier pool

The initial progression pool is unchanged. Only the successor-sieve
parameters vary between finitely many prime-variable bands.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 5000000

lemma eventually_cofactor_prefix_threshold (t l v h : ℕ) (ht : 1 ≤ t)
    (hv : v ≤ h) (hscale : l*v < t*(h-v)) :
    ∀ᶠ m : ℕ in atTop, ∀ H : ℕ, 2^(128*h*m) ≤ H →
      cofactorScale l (2*cofactorDyadicIndex t (128*v*m)) ≤ H/2^(128*v*m) := by
  filter_upwards [eventually_ge_atTop (4*l*t)] with m hm
  intro H hH
  have hb := (cofactorDyadicIndex_bounds t (128*v*m) ht).2
  have he : 512*l*cofactorDyadicIndex t (128*v*m) ≤ 128*(h-v)*m := by
    have hmul := Nat.mul_le_mul_left l hb
    have hgap := Nat.mul_le_mul_right m (Nat.succ_le_iff.mpr hscale)
    apply Nat.le_of_mul_le_mul_left (c := t) _ (by omega)
    nlinarith only [hm,hmul,hgap]
  apply (show cofactorScale l (2*cofactorDyadicIndex t (128*v*m)) ≤ 2^(128*(h-v)*m) by
    rw [cofactorScale_double_index_eq]
    exact Nat.pow_le_pow_right (by decide) he).trans
  apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2^(128*v*m))).mpr
  apply le_trans _ hH
  rw [← pow_add]
  apply Nat.pow_le_pow_right (by decide)
  have hh := congrArg (fun n : ℕ => 128*n*m) (Nat.sub_add_cancel hv)
  nlinarith only [hh]

lemma eventually_pool_band_product_lower (l v : ℕ) (hv : v ≤ 10000007)
    (hscale : l*v < 100000000*(20000009-v)) :
    ∀ᶠ m : ℕ in atTop, ∀ X C D : ℕ, independentN 40000020 m ≤ X → 0 < C → C ≤ D →
      C ≤ 2^(64*20000004*m+1) →
      cofactorScale l (2*cofactorDyadicIndex 100000000 (128*v*m)) ≤ D*((X/C)/2^(128*v*m)) := by
  filter_upwards [eventually_cofactor_prefix_threshold 100000000 l v 20000009 (by decide) (by omega) hscale,
    eventually_ge_atTop 1] with m hm hm1
  intro X C D hX hC hCD hCup
  have hhalf : 2^(128*20000009*m) ≤ X/2 := by
    apply (Nat.le_div_iff_mul_le (by decide : 0<2)).mpr
    apply le_trans _ hX
    rw [← pow_succ]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hCQ : C*2^(128*v*m) ≤ X := by
    apply (Nat.mul_le_mul hCup (Nat.pow_le_pow_right (by decide : 1 ≤ 2)
      (Nat.mul_le_mul_right m (Nat.mul_le_mul_left 128 hv)))).trans
    apply le_trans _ hX
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have h := hm (X/2) hhalf
  rw [Nat.div_div_eq_div_mul] at h
  exact h.trans (multiplier_floor_half X C D (2^(128*v*m)) hC (by positivity) hCD hCQ)

lemma pool_band_product_upper (u m X C D : ℕ) (hu : 20000011 ≤ 3*u)
    (hX : X ≤ independentN 40000021 m) (hDC : D ≤ 2*C) :
    D*((X/C)/2^(128*u*m)) ≤
      cofactorScale 200000000 (2*cofactorDyadicIndex 100000000 (128*u*m+1)) := by
  have hh := (cofactorDyadicIndex_bounds 100000000 (128*u*m+1) (by decide)).1
  apply (multiplier_floor_upper X C D (2^(128*u*m)) (by positivity) hDC).trans
  have hs : X ≤ 2^(256*u*m)*2^(128*u*m) := by
    apply hX.trans
    rw [← pow_add]
    apply Nat.pow_le_pow_right (by decide)
    have he := Nat.mul_le_mul_right m hu
    nlinarith only [he]
  have hquot : X/2^(128*u*m) ≤ 2^(256*u*m) := by
    apply (Nat.div_le_div_right hs).trans_eq
    exact Nat.mul_div_cancel _ (by positivity)
  apply (Nat.mul_le_mul_left 2 hquot).trans
  rw [show 2*2^(256*u*m)=(2 : ℕ)^(256*u*m+1) by rw [pow_succ]; omega,cofactorScale_double_index_eq]
  apply Nat.pow_le_pow_right (by decide)
  nlinarith only [hh]

lemma eventually_pool_band_sieve_cutoff (b v : ℕ) (hscale : b*v < 100000000*10000000) :
    ∀ᶠ m : ℕ in atTop,
      cofactorScale b (cofactorDyadicIndex 100000000 (128*v*m)) < independentN 10000000 m := by
  filter_upwards [eventually_ge_atTop (4*b*100000000+1)] with m hm
  have hb := Nat.mul_le_mul_left b (cofactorDyadicIndex_bounds 100000000 (128*v*m) (by decide)).2
  have hg := Nat.mul_le_mul_right m (Nat.succ_le_iff.mpr hscale)
  have he : 256*b*cofactorDyadicIndex 100000000 (128*v*m) < 64*10000000*m := by
    apply Nat.lt_of_mul_lt_mul_left (a := 2*100000000)
    nlinarith only [hb,hg,hm]
  rw [cofactorScale_eq]
  exact Nat.pow_lt_pow_right (by decide) he

lemma widePairPool_rough_below (m z : ℕ) (hz : z < independentN 10000000 m) :
    ∀ c ∈ widePairPool 10000000 m, ∀ p : ℕ, p.Prime → p ≤ z → ¬p ∣ c := by
  intro c hc p hp hpz hpc
  obtain ⟨⟨u,v⟩,huv,rfl⟩ := mem_image.mp hc
  obtain ⟨hu,hv⟩ := mem_product.mp huv
  rcases hp.dvd_mul.mp hpc with hpu | hpv
  · have he := (Nat.prime_dvd_prime_iff_eq hp (widePairLeft_prime 10000000 m u hu)).mp hpu
    have hb := (widePairPools_bounds 10000000 m u (Or.inl hu)).2.1
    omega
  · have he := (Nat.prime_dvd_prime_iff_eq hp (widePairRight_prime 10000000 m v hv)).mp hpv
    have hb := (widePairPools_bounds 10000000 m v (Or.inr hv)).2.1
    omega

lemma pool_band_short_prefix (v m X C : ℕ) (hv : v ≤ 10000007) (hm : 1000000 ≤ m)
    (hX : independentN 40000020 m ≤ X) (hC : 0<C) (hCup : C ≤ 2^(64*20000004*m+1)) :
    cofactorScale 3 (2*cofactorDyadicIndex 100000000 (128*v*m)) ≤ (X/C)/2^(128*v*m) := by
  have h := pool_supply_short_prefix m X C hm hX hC hCup
  have hq : 128*v*m ≤ 64*20000014*m := by
    have hmul := Nat.mul_le_mul_right m hv
    nlinarith only [hmul]
  exact ((cofactorScale_mono_right 3 (Nat.mul_le_mul_left 2 (cofactorDyadicIndex_mono 100000000 hq))).trans h).trans
    (Nat.div_le_div_left (Nat.pow_le_pow_right (by decide) hq) (by positivity))

end Erdos821.AnalyticSieve
