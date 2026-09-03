import Submission.SmallNearTieDensity

/-! Upper-density bounds for a narrow band of normalized logarithmic
largest-prime-factor sizes. -/

namespace Erdos371
namespace FiniteSieve
open Finset Filter

lemma prime_real_band_reciprocal_bound (S : Finset ℕ) (N : ℕ) (u v : ℝ)
    (hu : 0 < u) (huv : u ≤ v) (hN : 1 < N)
    (hscale : 2 ≤ u*(Real.log N/Real.log 2))
    (hS : ∀ p ∈ S, p.Prime ∧ (N : ℝ)^u ≤ (p : ℕ) ∧ (p : ℝ) ≤ (N : ℝ)^v) :
    (∑ p ∈ S, (1 : ℝ)/p) ≤ 8*(v-u)/u + 16/(u*(Real.log N/Real.log 2)) := by
  let H := Real.log N/Real.log 2
  let A := ⌊u*H⌋₊
  let B := ⌊v*H⌋₊
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hH : 0 < H := div_pos (Real.log_pos (by exact_mod_cast hN)) hl2
  have huH : 0 < u*H := mul_pos hu hH
  have hAf : u*H < (A : ℝ)+1 := Nat.lt_floor_add_one _
  have hBf : (B : ℝ) ≤ v*H := Nat.floor_le (mul_nonneg (hu.le.trans huv) hH.le)
  have hAB : A ≤ B := Nat.floor_mono (mul_le_mul_of_nonneg_right huv hH.le)
  have hA : 0 < A := by
    by_contra h
    have hz : A = 0 := by omega
    rw [hz,Nat.cast_zero] at hAf
    change 2 ≤ u*H at hscale
    linarith
  have hAhalf : u*H/2 ≤ (A : ℝ) := by
    change 2 ≤ u*H at hscale
    linarith
  have hband : ∀ p ∈ S, p.Prime ∧ 2^A ≤ p ∧ p < 2^(B+1) := by
    intro p hp
    obtain ⟨hpp,hpl,hpu⟩ := hS p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hlogl : u*Real.log N ≤ Real.log p := by
      simpa only [Real.log_rpow hN0] using Real.log_le_log (Real.rpow_pos_of_pos hN0 u) hpl
    have hlogu : Real.log p ≤ v*Real.log N := by
      simpa only [Real.log_rpow hN0] using Real.log_le_log hp0 hpu
    have hlo : u*H ≤ Real.logb 2 p := by
      unfold Real.logb
      dsimp [H]
      convert div_le_div_of_nonneg_right hlogl hl2.le using 1 <;> ring
    have hup : Real.logb 2 p ≤ v*H := by
      unfold Real.logb
      dsimp [H]
      convert div_le_div_of_nonneg_right hlogu hl2.le using 1 <;> ring
    have hfloor : ⌊Real.logb 2 (p : ℝ)⌋₊ = Nat.log 2 p := by
      simpa only [Nat.cast_ofNat] using Real.natFloor_logb_natCast 2 p
    have hAl : A ≤ Nat.log 2 p := by simpa only [hfloor] using Nat.floor_mono hlo
    have hlB : Nat.log 2 p ≤ B := by simpa only [hfloor] using Nat.floor_mono hup
    exact ⟨hpp,(Nat.le_log_iff_pow_le (by decide) hpp.ne_zero).mp hAl,
      (Nat.log_lt_iff_lt_pow (by decide) hpp.ne_zero).mp (by omega)⟩
  have hnum : ((B+1-A : ℕ) : ℝ) ≤ (v-u)*H+2 := by
    rw [Nat.cast_sub (by omega : A ≤ B+1),Nat.cast_add,Nat.cast_one]
    linarith
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  calc
    _ ≤ 4*(B+1-A : ℕ)/(A : ℝ) := prime_band_reciprocal_le S A B hA hband
    _ ≤ 4*((v-u)*H+2)/(A : ℝ) := div_le_div_of_nonneg_right (by linarith) hA0.le
    _ ≤ 4*((v-u)*H+2)/(u*H/2) := div_le_div_of_nonneg_left
      (by have := sub_nonneg.mpr huv; positivity) (by positivity) hAhalf
    _ = _ := by change _ = 8*(v-u)/u+16/(u*H); field_simp; ring

noncomputable def primeDivisorBandSet (N : ℕ) (u v : ℝ) : Finset ℕ := by
  classical
  exact (range N).filter fun n => ∃ p ∈ (N+1).primesBelow,
    (N : ℝ)^u ≤ (p : ℕ) ∧ (p : ℝ) ≤ (N : ℝ)^v ∧ p ∣ n+1

lemma primeDivisorBandSet_card_le (N : ℕ) (u v : ℝ) :
    ((primeDivisorBandSet N u v).card : ℝ) ≤
      N * (∑ p ∈ (N+1).primesBelow with (N : ℝ)^u ≤ (p : ℕ) ∧ (p : ℝ) ≤ (N : ℝ)^v, (1 : ℝ)/p) := by
  classical
  let S : Finset ℕ := (N+1).primesBelow.filter fun p => (N : ℝ)^u ≤ (p : ℕ) ∧ (p : ℝ) ≤ (N : ℝ)^v
  have hs : primeDivisorBandSet N u v ⊆ S.biUnion (fun p => (range N).filter fun n => p ∣ n+1) := by
    intro n hn
    obtain ⟨hnN,p,hp,hpl,hpu,hpn⟩ := mem_filter.mp hn
    exact mem_biUnion.mpr ⟨p,mem_filter.mpr ⟨hp,hpl,hpu⟩,mem_filter.mpr ⟨hnN,hpn⟩⟩
  have hc := (Nat.cast_le (α := ℝ)).mpr ((card_le_card hs).trans card_biUnion_le)
  simp only [Nat.cast_sum,Nat.card_multiples] at hc
  refine hc.trans ?_
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  simpa only [mul_one_div] using (Nat.cast_div_le (m := N) (n := p) (α := ℝ))

lemma primeDivisorBandSet_ratio_bound (N : ℕ) (u v : ℝ)
    (hu : 0 < u) (huv : u ≤ v) (hN : 1 < N)
    (hscale : 2 ≤ u*(Real.log N/Real.log 2)) :
    ((primeDivisorBandSet N u v).card : ℝ)/N ≤
      8*(v-u)/u + 16/(u*(Real.log N/Real.log 2)) := by
  classical
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcount' : ((primeDivisorBandSet N u v).card : ℝ)/N ≤
      ∑ p ∈ (N+1).primesBelow with (N : ℝ)^u ≤ (p : ℕ) ∧ (p : ℝ) ≤ (N : ℝ)^v, (1 : ℝ)/p := by
    apply (div_le_iff₀ hN0).mpr
    simpa only [mul_comm] using primeDivisorBandSet_card_le N u v
  refine hcount'.trans (prime_real_band_reciprocal_bound _ N u v hu huv hN hscale ?_)
  intro p hp
  obtain ⟨hp,hpl,hpu⟩ := mem_filter.mp hp
  exact ⟨(Nat.mem_primesBelow.mp hp).2,hpl,hpu⟩

def logPrimeBandEvent (u v : ℝ) (n : ℕ) : Prop :=
  1 < n ∧ (n : ℝ)^u ≤ Nat.maxPrimeFac n ∧ (Nat.maxPrimeFac n : ℝ) ≤ (n : ℝ)^v

noncomputable instance (u v : ℝ) (n : ℕ) : Decidable (logPrimeBandEvent u v n) := Classical.propDecidable _

/-- Discard a subpower initial segment to replace the pointwise scale by
the averaging endpoint. -/
lemma logPrimeBandEvent_card_bound (N : ℕ) (u v t : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (((range N).filter (logPrimeBandEvent u v)).card : ℝ) ≤
      (N : ℝ)^t+1 + (primeDivisorBandSet N (t*u) v).card := by
  classical
  let K := ⌈(N : ℝ)^t⌉₊
  let S := ((range N).filter (logPrimeBandEvent u v)).filter fun n => K ≤ n
  have hsub : (range N).filter (logPrimeBandEvent u v) ⊆ range K ∪ S := by
    intro n hn
    by_cases h : n < K
    · exact mem_union_left _ (mem_range.mpr h)
    · exact mem_union_right _ (mem_filter.mpr ⟨hn,by omega⟩)
  have hS : S.card ≤ (primeDivisorBandSet N (t*u) v).card := by
    apply card_le_card_of_injOn (fun n => n-1)
    · intro n hn
      simp only [mem_coe] at hn ⊢
      simp only [S,mem_filter,mem_range,logPrimeBandEvent] at hn
      obtain ⟨⟨hnN,hn1,hpl,hpu⟩,hKn⟩ := hn
      have hscale : (N : ℝ)^t ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hKn)
      have hlo : (N : ℝ)^(t*u) ≤ (Nat.maxPrimeFac n : ℝ) := by
        rw [Real.rpow_mul (Nat.cast_nonneg N)]
        exact (Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg N) _) hscale hu).trans hpl
      have hup : (Nat.maxPrimeFac n : ℝ) ≤ (N : ℝ)^v := hpu.trans
        (Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hnN.le) hv)
      apply mem_filter.mpr
      refine ⟨mem_range.mpr (by omega),Nat.maxPrimeFac n,?_,hlo,hup,?_⟩
      · exact Nat.mem_primesBelow.mpr ⟨(Nat.maxPrimeFac_le (n := n)).trans_lt (by omega),
          Nat.prime_maxPrimeFac_of_one_lt n hn1⟩
      · simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using (Nat.maxPrimeFac_dvd (n := n))
    · intro n hn m hm h
      simp only [mem_coe,S,mem_filter,mem_range,logPrimeBandEvent] at hn hm
      have hn1 := hn.1.2.1
      have hm1 := hm.1.2.1
      dsimp at h
      omega
  have hc := (Nat.cast_le (α := ℝ)).mpr ((card_le_card hsub).trans (card_union_le _ _))
  simp only [card_range,Nat.cast_add] at hc
  have hK : (K : ℝ) ≤ (N : ℝ)^t+1 := (Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg N) _)).le
  have hS' := (Nat.cast_le (α := ℝ)).mpr hS
  linarith

/-- The upper density of a logarithmic band is controlled by its width.
The parameter `t<1` pays for a negligible initial segment. -/
theorem logPrimeBandEvent_eventually_ratio_le (u v t : ℝ)
    (hu : 0 < u) (huv : u ≤ v) (ht : 0 < t) (ht1 : t < 1) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (((range N).filter (logPrimeBandEvent u v)).card : ℝ)/N ≤
        8*(v-t*u)/(t*u) + ε := by
  have htu : 0 < t*u := mul_pos ht hu
  have htv : t*u ≤ v := (by nlinarith : t*u ≤ u).trans huv
  have hH := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const
    (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  have hscale := hH.const_mul_atTop htu
  have htail : Tendsto (fun N : ℕ => 16/((t*u)*(Real.log N/Real.log 2))) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv,Function.comp_def,mul_zero] using (tendsto_inv_atTop_zero.comp hscale).const_mul (16 : ℝ)
  have hpow : Tendsto (fun N : ℕ => (N : ℝ)^t/N) atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop (show 0 < 1-t by linarith)).comp tendsto_natCast_atTop_atTop
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    dsimp only [Function.comp_def]
    rw [show -(1-t) = t-1 by ring,Real.rpow_sub (by exact_mod_cast hN : (0 : ℝ) < N),Real.rpow_one]
  have he := (hpow.add tendsto_one_div_atTop_nhds_zero_nat).add htail
  simp only [add_zero] at he
  filter_upwards [(he.eventually (gt_mem_nhds hε)),hscale.eventually_ge_atTop 2,
    eventually_gt_atTop (1 : ℕ)] with N heN hscaleN hN
  have hc := div_le_div_of_nonneg_right (logPrimeBandEvent_card_bound N u v t hu.le (hu.le.trans huv))
    (Nat.cast_nonneg N)
  have hb := primeDivisorBandSet_ratio_bound N (t*u) v htu htv hN hscaleN
  rw [add_div,add_div] at hc
  linarith

#print axioms logPrimeBandEvent_eventually_ratio_le
end FiniteSieve
end Erdos371
