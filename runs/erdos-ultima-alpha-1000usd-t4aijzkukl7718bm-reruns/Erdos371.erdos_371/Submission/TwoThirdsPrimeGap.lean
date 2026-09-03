import FormalConjecturesUtil
import Submission.DivisorGapSwitch
import Submission.SquareRootPrimeGap

/-! A divisor-switched counting approach for the gap condition
`dist(P n, P(n+1))^3 ≤ min(P n, P(n+1))^2`.
No claim about the density of either orientation is made. -/

namespace Erdos371TwoThirdsPrimeGap

open Erdos371Cofactor Erdos371BoundedPrimeGap Erdos371DivisorGapSwitch
open Erdos371TerminalCompression

lemma cube_block_card_bound {k : ℕ} (hk : 0 < k) (N : ℕ) :
    ((cover (k^3) ((k+1)^3) ((k+1)^2) N).card : ℝ) ≤
      56 * (N : ℝ) / (k : ℝ)^2 + 56 * (k : ℝ)^4 := by
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hb : (k + 1)^3 - k^3 ≤ 7 * k^2 := by
    have he : (k + 1)^3 = k^3 + (3*k^2 + 3*k + 1) := by ring
    have hs : (k + 1)^3 - k^3 = 3*k^2 + 3*k + 1 := by omega
    rw [hs]
    nlinarith
  have hh : (k+1)^2 ≤ 4*k^2 := by nlinarith
  have hc : (cover (k^3) ((k+1)^3) ((k+1)^2) N).card ≤
      ((k+1)^3-k^3) * (k+1)^2 * (2 * (N / k^6 + 1)) := by
    apply Finset.card_biUnion_le.trans
    calc
      _ ≤ ∑ p ∈ Finset.Ico (k^3) ((k+1)^3),
          (k+1)^2 * (2 * (N / k^6 + 1)) := by
        apply Finset.sum_le_sum
        intro p hp
        have hkp := (Finset.mem_Ico.mp hp).1
        have hp0 : 0 < p := (Nat.pow_pos hk).trans_le hkp
        apply Finset.card_biUnion_le.trans
        calc
          _ ≤ ∑ c ∈ Finset.Icc 1 ((k+1)^2), 2 * (N / k^6 + 1) := by
            apply Finset.sum_le_sum
            intro c hc
            have hden : k^6 ≤ p * (p+1) := by
              have he := Nat.pow_le_pow_left hkp 2
              nlinarith [he]
            have hd := Nat.div_le_div_left (a := N) hden (Nat.pow_pos hk)
            have hh := primePairs_card_le hp0 c N
            omega
          _ = _ := by simp
      _ = _ := by simp [mul_assoc]
  have hm : ((k+1)^3-k^3) * (k+1)^2 ≤ 28*k^4 := by
    have hm := Nat.mul_le_mul hb hh
    nlinarith [hm]
  have hc' : (cover (k^3) ((k+1)^3) ((k+1)^2) N).card ≤
      56*k^4*(N/k^6+1) := by
    have hm' := Nat.mul_le_mul_right (2 * (N / k^6 + 1)) hm
    nlinarith [hc.trans hm']
  calc
    _ ≤ 56*(k:ℝ)^4*(((N/k^6:ℕ):ℝ)+1) := by exact_mod_cast hc'
    _ ≤ 56*(k:ℝ)^4*((N:ℝ)/(k:ℝ)^6+1) := by
      have hd : ((N/k^6:ℕ):ℝ) ≤ (N:ℝ)/((k^6:ℕ):ℝ) := Nat.cast_div_le
      push_cast at hd
      gcongr
    _ = _ := by field_simp

def lowCover (K T N : ℕ) : Finset ℕ :=
  (Finset.Ico K T).biUnion fun k => cover (k^3) ((k+1)^3) ((k+1)^2) N

lemma lowCover_card_bound {K : ℕ} (hK : 0 < K) (T N : ℕ) :
    ((lowCover K T N).card : ℝ) ≤ 112 * (N : ℝ) / K + 56 * (T : ℝ)^5 := by
  have hs : (∑ k ∈ Finset.Ico K T, (k : ℝ)^4) ≤ (T : ℝ)^5 := by
    calc
      _ ≤ ∑ _k ∈ Finset.Ico K T, (T : ℝ)^4 := by
        apply Finset.sum_le_sum
        intro k hk
        exact_mod_cast Nat.pow_le_pow_left (Finset.mem_Ico.mp hk).2.le 4
      _ = ((T-K:ℕ):ℝ) * (T:ℝ)^4 := by simp
      _ ≤ (T:ℝ) * (T:ℝ)^4 := mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr (Nat.sub_le _ _)) (by positivity)
      _ = _ := by ring
  have hc : (lowCover K T N).card ≤
      ∑ k ∈ Finset.Ico K T, (cover (k^3) ((k+1)^3) ((k+1)^2) N).card :=
    Finset.card_biUnion_le
  calc
    _ ≤ ∑ k ∈ Finset.Ico K T,
        ((cover (k^3) ((k+1)^3) ((k+1)^2) N).card : ℝ) := by exact_mod_cast hc
    _ ≤ ∑ k ∈ Finset.Ico K T,
        (56 * (N:ℝ) / (k:ℝ)^2 + 56 * (k:ℝ)^4) :=
      Finset.sum_le_sum (fun k hk => cube_block_card_bound
        (hK.trans_le (Finset.mem_Ico.mp hk).1) N)
    _ = 56 * (N:ℝ) * (∑ k ∈ Finset.Ico K T, 1 / (k:ℝ)^2) +
        56 * (∑ k ∈ Finset.Ico K T, (k:ℝ)^4) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ 56 * (N:ℝ) * (2 / (K:ℝ)) + 56 * (T:ℝ)^5 := by
      gcongr
      exact sum_reciprocal_sq hK T
    _ = _ := by ring

def twoThirdsGapSet : Set ℕ :=
  {n | (Nat.dist (P n) (P (n+1)))^3 ≤ (min (P n) (P (n+1)))^2}

lemma high_gap_in_switch {T n : ℕ} (hT : 2 ≤ T) (hn : 3 ≤ n) (hnN : n < T^6)
    (hgap : n ∈ twoThirdsGapSet) (hhigh : T^3 ≤ min (P n) (P (n+1))) :
    n ∈ switchCover (T^3) T (T^6) := by
  have hT0 : 0 < T := by omega
  have hpow : T < T^3 := by
    have hh : 2 ≤ T^2 := by nlinarith
    have hm := Nat.mul_le_mul_left T hh
    nlinarith
  apply mem_switchCover_of_close hn hnN hT0
  · have hpn : T^3 ≤ P n := hhigh.trans (min_le_left _ _)
    have hnprod := cofactor_mul n
    have hmul := Nat.mul_le_mul_left (cofactor n) hpn
    have hc : cofactor n ≤ T^3 := by
      by_contra hh
      have hb := Nat.mul_le_mul_right (T^3) (show T^3 + 1 ≤ cofactor n by omega)
      nlinarith [Nat.pow_pos hT0 (n := 3)]
    exact (min_le_left _ _).trans hc
  · exact hpow.trans_le hhigh
  · let q := min (P n) (P (n+1))
    let c := Nat.dist (P n) (P (n+1))
    change c * T ≤ q
    have hg : c^3 ≤ q^2 := hgap
    have h1 := Nat.mul_le_mul_right (T^3) hg
    have h2 := Nat.mul_le_mul_left (q^2) hhigh
    change q^2*T^3 ≤ q^2*q at h2
    have h3 : (c*T)^3 ≤ q^3 := by nlinarith [h1,h2]
    exact (Nat.pow_le_pow_iff_left (by decide : (3:ℕ) ≠ 0)).mp h3

lemma own_primePair_mem {n N : ℕ} (hn : 3 ≤ n) (hnN : n < N) :
    n ∈ primePairs (min (P n) (P (n+1))) (Nat.dist (P n) (P (n+1))) N := by
  have hp := Nat.prime_maxPrimeFac_of_one_lt n (by omega)
  have hq := Nat.prime_maxPrimeFac_of_one_lt (n+1) (by omega)
  have hne := Erdos371PrimeDiscrepancy.consecutive_ne n
  change P (n+1) ≠ P n at hne
  by_cases h : P n < P (n+1)
  · rw [min_eq_left h.le, Nat.dist_eq_sub_of_le h.le]
    have he : P n + (P (n+1) - P n) = P (n+1) := by omega
    rw [primePairs, if_pos (show (P n).Prime ∧ (P n + (P (n+1)-P n)).Prime ∧
        0 < P (n+1)-P n from ⟨hp, by rwa [he], by omega⟩)]
    apply Finset.mem_union_left
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hnN, Nat.maxPrimeFac_dvd,
      by rw [he]; exact Nat.maxPrimeFac_dvd⟩
  · have h' : P (n+1) < P n := by omega
    rw [min_eq_right h'.le, Nat.dist_comm, Nat.dist_eq_sub_of_le h'.le]
    have he : P (n+1) + (P n - P (n+1)) = P n := by omega
    rw [primePairs, if_pos (show (P (n+1)).Prime ∧ (P (n+1) + (P n-P (n+1))).Prime ∧
        0 < P n-P (n+1) from ⟨hq, by rwa [he], by omega⟩)]
    apply Finset.mem_union_right
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hnN,
      by rw [he]; exact Nat.maxPrimeFac_dvd, Nat.maxPrimeFac_dvd⟩

lemma exists_cube_block (q : ℕ) : ∃ k : ℕ, k^3 ≤ q ∧ q < (k+1)^3 := by
  have hex : ∃ r : ℕ, q < r^3 := by
    refine ⟨q+1, ?_⟩
    have hb : q+1 ≤ (q+1)^3 := by
      simpa using Nat.pow_le_pow_right (by omega : 0 < q+1) (by decide : 1 ≤ 3)
    omega
  let r := Nat.find hex
  have hr : q < r^3 := Nat.find_spec hex
  have hrpos : 0 < r := by
    by_contra hh
    have he : r = 0 := by omega
    simp [he] at hr
  refine ⟨r-1, ?_, ?_⟩
  · have hm := Nat.find_min hex (show r-1 < r by omega)
    omega
  · simpa only [Nat.sub_add_cancel hrpos] using hr

lemma low_gap_in_cover {K T n N : ℕ} (hn : 3 ≤ n) (hnN : n < N)
    (hgap : n ∈ twoThirdsGapSet)
    (hlo : K^3 ≤ min (P n) (P (n+1))) (hhi : min (P n) (P (n+1)) < T^3) :
    n ∈ lowCover K T N := by
  let q := min (P n) (P (n+1))
  let c := Nat.dist (P n) (P (n+1))
  obtain ⟨k, hkq, hqk⟩ := exists_cube_block q
  have hKk : K ≤ k := by
    by_contra hh
    have hb := Nat.pow_le_pow_left (show k+1 ≤ K by omega) 3
    omega
  have hkT : k < T := by
    by_contra hh
    have hb := Nat.pow_le_pow_left (show T ≤ k by omega) 3
    omega
  have hc : c ≤ (k+1)^2 := by
    have hg : c^3 ≤ q^2 := hgap
    have hs := Nat.pow_le_pow_left hqk.le 2
    apply (Nat.pow_le_pow_iff_left (by decide : (3:ℕ) ≠ 0)).mp
    nlinarith [hg,hs]
  have hcpos : 0 < c := by
    have hn' := Erdos371PrimeDiscrepancy.consecutive_ne n
    change P (n+1) ≠ P n at hn'
    apply Nat.pos_of_ne_zero
    intro he
    have he' := Nat.eq_of_dist_eq_zero he
    exact hn' he'.symm
  apply Finset.mem_biUnion.mpr
  refine ⟨k, Finset.mem_Ico.mpr ⟨hKk,hkT⟩, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨q, Finset.mem_Ico.mpr ⟨hkq,hqk⟩, ?_⟩
  apply Finset.mem_biUnion.mpr
  exact ⟨c, Finset.mem_Icc.mpr ⟨hcpos,hc⟩, own_primePair_mem hn hnN⟩

lemma sixth_power_density_bound {K T : ℕ} (hK : 0 < K) (hT : 2 ≤ T) :
    twoThirdsGapSet.partialDensity Set.univ (T^6) ≤
      3 / (T^6 : ℕ) + (lowSet (K^3)).partialDensity Set.univ (T^6) +
      112 / (K:ℝ) + 58 / (T:ℝ) + 2 * H (T^3) / T := by
  let N := T^6
  let G := (Finset.range N).filter (fun n =>
    (Nat.dist (P n) (P (n+1)))^3 ≤ (min (P n) (P (n+1)))^2)
  let L := (Finset.range N).filter (fun n => P n ≤ K^3 ∨ P (n+1) ≤ K^3)
  have hsub : G ⊆ ((Finset.range 3 ∪ L) ∪ lowCover K T N) ∪ switchCover (T^3) T N := by
    intro n hn
    obtain ⟨hnN,hg⟩ := Finset.mem_filter.mp hn
    have hnN' := Finset.mem_range.mp hnN
    by_cases hn3 : n < 3
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_range.mpr hn3)))
    by_cases hlo : P n ≤ K^3 ∨ P (n+1) ≤ K^3
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hnN,hlo⟩)))
    by_cases hhi : min (P n) (P (n+1)) < T^3
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (low_gap_in_cover (by omega) hnN' hg (by omega) hhi))
    · exact Finset.mem_union_right _ (high_gap_in_switch hT (by omega) hnN' hg (by omega))
  have hc : G.card ≤ 3 + L.card + (lowCover K T N).card + (switchCover (T^3) T N).card := by
    have h0 := Finset.card_le_card hsub
    have h1 := Finset.card_union_le ((Finset.range 3 ∪ L) ∪ lowCover K T N) (switchCover (T^3) T N)
    have h2 := Finset.card_union_le (Finset.range 3 ∪ L) (lowCover K T N)
    have h3 := Finset.card_union_le (Finset.range 3) L
    simp only [Finset.card_range] at h3
    omega
  have hc' : (G.card:ℝ) ≤ 3 + L.card + (lowCover K T N).card + (switchCover (T^3) T N).card :=
    by exact_mod_cast hc
  have hlow := lowCover_card_bound hK T N
  have hswitch := switchCover_card_bound (by omega : 0 < T) (T^3) N
  have hg : twoThirdsGapSet.partialDensity Set.univ N = (G.card:ℝ)/N := partialDensity_filter _ _
  have hl : (lowSet (K^3)).partialDensity Set.univ N = (L.card:ℝ)/N := partialDensity_filter _ _
  rw [hg,hl]
  have ht : (T:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hk : (K:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  calc
    _ ≤ (3 + L.card + (112*(N:ℝ)/K + 56*(T:ℝ)^5) +
        (2*(N:ℝ)/T*H (T^3) + 2*((T^3:ℕ):ℝ)^2/T)) / N :=
      div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
    _ = _ := by
      dsimp [N]
      push_cast
      field_simp
      ring

open Filter
open scoped Topology

lemma harmonic_cubes_div_tendsto_zero :
    Tendsto (fun T : ℕ => H (T^3) / (T:ℝ)) atTop (𝓝 0) := by
  have hl : Tendsto (fun T : ℕ => Real.log (T:ℝ) / T) atTop (𝓝 0) := by
    simpa using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hu : Tendsto (fun T : ℕ => 1 / (T:ℝ) + 3 * (Real.log (T:ℝ) / T))
      atTop (𝓝 0) := by
    simpa using tendsto_one_div_atTop_nhds_zero_nat.add (tendsto_const_nhds.mul hl)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
  · intro T
    exact div_nonneg (H_nonneg _) (Nat.cast_nonneg _)
  · intro T
    have hh := H_le_log (T^3)
    push_cast at hh
    rw [Real.log_pow] at hh
    have hd := div_le_div_of_nonneg_right hh (Nat.cast_nonneg T)
    convert hd using 1 <;> ring

lemma twoThirds_gap_density_sixth_powers :
    Tendsto (fun T : ℕ => twoThirdsGapSet.partialDensity Set.univ (T^6)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K,hK,hsmallK⟩ := ((eventually_gt_atTop 0).and
    ((tendsto_const_div_atTop_nhds_zero_nat (112:ℝ)).eventually (gt_mem_nhds (half_pos hε)))).exists
  have hp : Tendsto (fun T : ℕ => T^6) atTop atTop := tendsto_pow_atTop (by decide)
  have hu : Tendsto (fun T : ℕ => 3 / (T^6 : ℕ) +
      (lowSet (K^3)).partialDensity Set.univ (T^6) + 58 / (T:ℝ) +
      2 * (H (T^3) / (T:ℝ))) atTop (𝓝 0) := by
    simpa using ((((tendsto_const_div_atTop_nhds_zero_nat (3:ℝ)).comp hp).add
      ((lowSet_hasDensity_zero (K^3)).comp hp)).add
      (tendsto_const_div_atTop_nhds_zero_nat (58:ℝ))).add
      (tendsto_const_nhds.mul harmonic_cubes_div_tendsto_zero)
  obtain ⟨T₀,hT₀⟩ := eventually_atTop.mp (hu.eventually (gt_mem_nhds (half_pos hε)))
  refine ⟨max T₀ 2, fun T hT => ?_⟩
  have hb := sixth_power_density_bound hK (by omega : 2 ≤ T)
  have hh := hT₀ T (by omega)
  simp only [mul_div_assoc] at hb
  change 112 / (K:ℝ) < ε/2 at hsmallK
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by unfold Set.partialDensity; positivity)]
  linarith

lemma exists_sixth_power_bracket {N : ℕ} (hN : 0 < N) :
    ∃ T : ℕ, 0 < T ∧ N ≤ T^6 ∧ T^6 ≤ 64*N := by
  have hex : ∃ T : ℕ, N ≤ T^6 := by
    refine ⟨N, ?_⟩
    simpa using Nat.pow_le_pow_right hN (by decide : 1 ≤ 6)
  let T := Nat.find hex
  have hNT : N ≤ T^6 := Nat.find_spec hex
  have hT : 0 < T := by
    by_contra hh
    have he : T = 0 := by omega
    simp [he] at hNT
    omega
  refine ⟨T,hT,hNT,?_⟩
  by_cases h1 : T = 1
  · rw [h1]
    norm_num
    omega
  · have hlo : (T-1)^6 < N := by
      have hh := Nat.find_min hex (show T-1 < T by omega)
      omega
    have h2 : T ≤ 2*(T-1) := by omega
    have hh := Nat.pow_le_pow_left h2 6
    nlinarith [hh]

lemma hasDensity_zero_of_sixth_powers (S : Set ℕ)
    (h : Tendsto (fun T : ℕ => S.partialDensity Set.univ (T^6)) atTop (𝓝 0)) :
    S.HasDensity 0 := by
  rw [Set.HasDensity, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T₀,hT₀⟩ := eventually_atTop.mp (h.eventually (gt_mem_nhds (show 0 < ε/64 by positivity)))
  refine ⟨T₀^6+1, fun N hN => ?_⟩
  obtain ⟨T,hT,hNT,hTN⟩ := exists_sixth_power_bracket (N := N) (by omega)
  have hTbig : T₀ ≤ T := by
    by_contra hh
    have hb := Nat.pow_le_pow_left (show T ≤ T₀ by omega) 6
    omega
  have hs := hT₀ T hTbig
  have hb : S.partialDensity Set.univ N ≤ 64 * S.partialDensity Set.univ (T^6) := by
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio]
    have hn : (0:ℝ) < N := Nat.cast_pos.mpr (by omega)
    have hm : (0:ℝ) < (T^6:ℕ) := Nat.cast_pos.mpr (Nat.pow_pos hT)
    have hc : (S ∩ Set.Iio N).ncard ≤ (S ∩ Set.Iio (T^6)).ncard :=
      Set.ncard_le_ncard (Set.inter_subset_inter_right _ (Set.Iio_subset_Iio hNT))
    have hr : ((T^6:ℕ):ℝ) / N ≤ 64 := (div_le_iff₀ hn).mpr (by exact_mod_cast hTN)
    calc
      _ ≤ ((S ∩ Set.Iio (T^6)).ncard:ℝ) / N :=
        div_le_div_of_nonneg_right (Nat.cast_le.mpr hc) hn.le
      _ = (((S ∩ Set.Iio (T^6)).ncard:ℝ) / (T^6:ℕ)) * (((T^6:ℕ):ℝ) / N) := by field_simp
      _ ≤ (((S ∩ Set.Iio (T^6)).ncard:ℝ) / (T^6:ℕ)) * 64 :=
        mul_le_mul_of_nonneg_left hr (by positivity)
      _ = _ := by ring
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by unfold Set.partialDensity; positivity)]
  linarith

/-- The gap is larger than the two-thirds power of the smaller prime
outside a set of natural density zero. This does not determine its sign. -/
lemma twoThirds_prime_gap_hasDensity_zero : twoThirdsGapSet.HasDensity 0 :=
  hasDensity_zero_of_sixth_powers _ twoThirds_gap_density_sixth_powers

end Erdos371TwoThirdsPrimeGap

#print axioms Erdos371TwoThirdsPrimeGap.twoThirds_prime_gap_hasDensity_zero

