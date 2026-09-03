import Submission.PrimeAllocationRetention
import Submission.PrimeBandDensity

/-! Uniform rarity of two large prime divisors of the same integer that are
close on the logarithmic scale. No neighboring-integer independence is used. -/
namespace Erdos371
open Finset Filter
open scoped Topology
namespace FiniteSieve

noncomputable def gapLargePrimes (N : ℕ) (v : ℝ) : Finset ℕ := by
  classical
  exact (N+1).primesBelow.filter fun p => (N : ℝ)^v ≤ p

noncomputable def gapNearbyPrimes (N p : ℕ) (η : ℝ) : Finset ℕ := by
  classical
  exact (N+1).primesBelow.filter fun q => q < p ∧ (p : ℝ) ≤ (N : ℝ)^η*q

def sameIntegerPrimeGapEvent (N : ℕ) (v η : ℝ) (m : ℕ) : Prop :=
  ∃ p ∈ gapLargePrimes N v, ∃ q ∈ gapNearbyPrimes N p η, p*q ∣ m

noncomputable def sameIntegerPrimeGapSet (N : ℕ) (v η : ℝ) : Finset ℕ := by
  classical
  exact (range N).filter fun n => sameIntegerPrimeGapEvent N v η (n+1)

lemma sameIntegerPrimeGapSet_card_bound (N : ℕ) (v η : ℝ) :
    ((sameIntegerPrimeGapSet N v η).card : ℝ) ≤
      N * ∑ p ∈ gapLargePrimes N v, (1 : ℝ)/p *
        ∑ q ∈ gapNearbyPrimes N p η, (1 : ℝ)/q := by
  classical
  have hs : sameIntegerPrimeGapSet N v η ⊆
      (gapLargePrimes N v).biUnion (fun p => (gapNearbyPrimes N p η).biUnion
        (fun q => (range N).filter fun n => p*q ∣ n+1)) := by
    intro n hn
    obtain ⟨hn,p,hp,q,hq,hd⟩ := mem_filter.mp hn
    exact mem_biUnion.mpr ⟨p,hp,mem_biUnion.mpr ⟨q,hq,mem_filter.mpr ⟨hn,hd⟩⟩⟩
  have hc : (sameIntegerPrimeGapSet N v η).card ≤
      ∑ p ∈ gapLargePrimes N v, ∑ q ∈ gapNearbyPrimes N p η,
        ((range N).filter fun n => p*q ∣ n+1).card :=
    (card_le_card hs).trans (card_biUnion_le.trans (sum_le_sum fun p hp => card_biUnion_le))
  have hc' := (Nat.cast_le (α := ℝ)).mpr hc
  simp only [Nat.cast_sum,Nat.card_multiples] at hc'
  refine hc'.trans ?_
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  rw [← mul_assoc,mul_sum]
  apply sum_le_sum
  intro q hq
  convert (Nat.cast_div_le (m := N) (n := p*q) (α := ℝ)) using 1 <;> push_cast <;> ring

lemma gapLargePrimes_reciprocal_bound (N : ℕ) (v : ℝ)
    (hv : 0 < v) (hv1 : v ≤ 1) (hN : 1 < N)
    (hscale : 2 ≤ v*(Real.log N/Real.log 2)) :
    (∑ p ∈ gapLargePrimes N v, (1 : ℝ)/p) ≤
      8/v + 16/(v*(Real.log N/Real.log 2)) := by
  classical
  have hb := prime_real_band_reciprocal_bound (gapLargePrimes N v) N v 1 hv hv1 hN hscale
    (fun p hp => by
      obtain ⟨hp,hpv⟩ := mem_filter.mp hp
      obtain ⟨hpN,hpp⟩ := Nat.mem_primesBelow.mp hp
      refine ⟨hpp,hpv,?_⟩
      simpa only [Real.rpow_one] using (show (p : ℝ) ≤ N by exact_mod_cast (by omega : p ≤ N)))
  have hh : 8*(1-v)/v ≤ 8/v := div_le_div_of_nonneg_right (by linarith) hv.le
  linarith

lemma gapNearbyPrimes_reciprocal_bound (N p : ℕ) (v η : ℝ)
    (hv : 0 < v) (hη : 0 ≤ η) (hηv : η ≤ v/2) (hN : 1 < N)
    (hp : p.Prime) (hpv : (N : ℝ)^v ≤ p)
    (hscale : 2 ≤ (v/2)*(Real.log N/Real.log 2)) :
    (∑ q ∈ gapNearbyPrimes N p η, (1 : ℝ)/q) ≤
      16*η/v + 32/(v*(Real.log N/Real.log 2)) := by
  classical
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hH : 0 < Real.log N/Real.log 2 := div_pos hlog (Real.log_pos (by norm_num))
  let α : ℝ := Real.log p / Real.log N
  have hvα : v ≤ α := by
    apply (le_div_iff₀ hlog).mpr
    have hh := Real.log_le_log (Real.rpow_pos_of_pos hNr v) hpv
    simpa only [Real.log_rpow hNr] using hh
  have hu : 0 < α-η := by linarith
  have hu2 : v/2 ≤ α-η := by linarith
  have hscale' : 2 ≤ (α-η)*(Real.log N/Real.log 2) :=
    hscale.trans (mul_le_mul_of_nonneg_right hu2 hH.le)
  have hband : ∀ q ∈ gapNearbyPrimes N p η,
      q.Prime ∧ (N : ℝ)^(α-η) ≤ q ∧ (q : ℝ) ≤ (N : ℝ)^α := by
    intro q hq
    obtain ⟨hq,hqp,hclose⟩ := mem_filter.mp hq
    have hqq := (Nat.mem_primesBelow.mp hq).2
    have he : (N : ℝ)^α = p := RandomBins.rpow_log_quotient N p hN hp.pos
    refine ⟨hqq,?_,by rw [he]; exact_mod_cast hqp.le⟩
    rw [Real.rpow_sub hNr,he]
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hNr η)).mpr (by simpa only [mul_comm] using hclose)
  have hb := prime_real_band_reciprocal_bound (gapNearbyPrimes N p η) N (α-η) α
    hu (by linarith) hN hscale' hband
  have hc : 8*(α-(α-η))/(α-η) ≤ 16*η/v := by
    calc
      _ = 8*η/(α-η) := by ring
      _ ≤ 8*η/(v/2) := div_le_div_of_nonneg_left (by positivity) (by positivity) hu2
      _ = _ := by ring
  have he : 16/((α-η)*(Real.log N/Real.log 2)) ≤
      32/(v*(Real.log N/Real.log 2)) := by
    calc
      _ ≤ 16/((v/2)*(Real.log N/Real.log 2)) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity)
          (mul_le_mul_of_nonneg_right hu2 hH.le)
      _ = _ := by ring
  linarith

lemma sameIntegerPrimeGapSet_ratio_bound (N : ℕ) (v η : ℝ)
    (hv : 0 < v) (hv1 : v ≤ 1) (hη : 0 ≤ η) (hηv : η ≤ v/2) (hN : 1 < N)
    (hscale : 2 ≤ (v/2)*(Real.log N/Real.log 2)) :
    ((sameIntegerPrimeGapSet N v η).card : ℝ)/N ≤
      (8/v + 16/(v*(Real.log N/Real.log 2))) *
      (16*η/v + 32/(v*(Real.log N/Real.log 2))) := by
  classical
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hH : 0 < Real.log N/Real.log 2 :=
    div_pos (Real.log_pos (by exact_mod_cast hN)) (Real.log_pos (by norm_num))
  have hscale' : 2 ≤ v*(Real.log N/Real.log 2) := by nlinarith
  have hbase : ((sameIntegerPrimeGapSet N v η).card : ℝ)/N ≤
      ∑ p ∈ gapLargePrimes N v, (1 : ℝ)/p * ∑ q ∈ gapNearbyPrimes N p η, (1 : ℝ)/q := by
    apply (div_le_iff₀ hNr).mpr
    simpa only [mul_comm] using sameIntegerPrimeGapSet_card_bound N v η
  refine hbase.trans ?_
  calc
    _ ≤ ∑ p ∈ gapLargePrimes N v, (1 : ℝ)/p *
        (16*η/v+32/(v*(Real.log N/Real.log 2))) := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hpp,hpv⟩ := mem_filter.mp hp
      exact mul_le_mul_of_nonneg_left (gapNearbyPrimes_reciprocal_bound N p v η
        hv hη hηv hN (Nat.mem_primesBelow.mp hpp).2 hpv hscale) (by positivity)
    _ = (∑ p ∈ gapLargePrimes N v, (1 : ℝ)/p) *
        (16*η/v+32/(v*(Real.log N/Real.log 2))) := (sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (gapLargePrimes_reciprocal_bound N v hv hv1 hN hscale') (by positivity)

/-- The upper proportion is O(η/v²), with an explicit constant. -/
theorem sameIntegerPrimeGapSet_eventually_le (v η : ℝ)
    (hv : 0 < v) (hv1 : v ≤ 1) (hη : 0 ≤ η) (hηv : η ≤ v/2)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ((sameIntegerPrimeGapSet N v η).card : ℝ)/N ≤
      128*η/v^2+ε := by
  have hH := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const
    (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  have hscale := hH.const_mul_atTop (show 0 < v/2 by positivity)
  have hden := hH.const_mul_atTop hv
  have h16 : Tendsto (fun N : ℕ => 16/(v*(Real.log N/Real.log 2))) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hden
  have h32 : Tendsto (fun N : ℕ => 32/(v*(Real.log N/Real.log 2))) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hden
  have ht := (h16.const_add (8/v)).mul (h32.const_add (16*η/v))
  simp only [add_zero] at ht
  have he : 8/v*(16*η/v) = 128*η/v^2 := by ring
  rw [he] at ht
  filter_upwards [ht.eventually_lt_const (by linarith : 128*η/v^2 < 128*η/v^2+ε),
    hscale.eventually_ge_atTop 2,eventually_gt_atTop (1 : ℕ)] with N ht hs hN
  exact (sameIntegerPrimeGapSet_ratio_bound N v η hv hv1 hη hηv hN hs).trans ht.le

/-- Choose a fixed positive logarithmic gap with arbitrarily small exceptional
proportion. This concerns two divisors of ONE integer. -/
theorem sameIntegerPrimeGapSet_uniform_rarity (v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ η ≤ v/2 ∧ ∀ᶠ N : ℕ in atTop,
      ((sameIntegerPrimeGapSet N v η).card : ℝ)/N ≤ ε := by
  let η : ℝ := min (v/2) (ε*v^2/512)
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hηv : η ≤ v/2 := min_le_left _ _
  have hηe : η ≤ ε*v^2/512 := min_le_right _ _
  have hmain : 128*η/v^2 ≤ ε/4 := by
    apply (div_le_iff₀ (sq_pos_of_pos hv)).mpr
    nlinarith
  refine ⟨η,hη,hηv,?_⟩
  filter_upwards [sameIntegerPrimeGapSet_eventually_le v η hv hv1 hη.le hηv (ε/2) (by positivity)]
    with N hN
  linarith

#print axioms sameIntegerPrimeGapSet_eventually_le
#print axioms sameIntegerPrimeGapSet_uniform_rarity
end FiniteSieve
end Erdos371
