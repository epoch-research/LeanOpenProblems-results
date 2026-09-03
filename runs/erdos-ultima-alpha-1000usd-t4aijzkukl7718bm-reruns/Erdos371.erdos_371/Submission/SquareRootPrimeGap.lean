import FormalConjecturesUtil
import Submission.BoundedPrimeGap

/-! Square-root separation of neighboring largest prime factors.
This does not determine the density of either orientation. -/

namespace Erdos371SquareRootPrimeGap

open Erdos371Cofactor Erdos371BoundedPrimeGap

def rootGapSet : Set ℕ :=
  {n | Nat.dist (P n) (P (n + 1)) ≤ Nat.sqrt (min (P n) (P (n + 1)))}

lemma sqrt_reciprocal_step {p : ℕ} (hp : 0 < p) :
    Real.sqrt p / ((p : ℝ) * (p + 1)) ≤
      2 * (1 / Real.sqrt p - 1 / Real.sqrt (p + 1)) := by
  let x : ℝ := Real.sqrt p
  let y : ℝ := Real.sqrt (p + 1)
  have hx : 0 < x := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hp)
  have hy : 0 < y := Real.sqrt_pos.mpr (by positivity)
  have hx2 : x ^ 2 = p := Real.sq_sqrt (Nat.cast_nonneg p)
  have hy2 : y ^ 2 = p + 1 := Real.sq_sqrt (by positivity)
  have hb : 1 ≤ 2 * y * (y - x) := by nlinarith [sq_nonneg (y - x)]
  change x / ((p : ℝ) * (p + 1)) ≤ 2 * (1 / x - 1 / y)
  rw [← hy2, ← hx2]
  have hl : x / (x ^ 2 * y ^ 2) = 1 / (x * y ^ 2) := by field_simp
  have hr : 2 * (1 / x - 1 / y) = 2 * (y - x) / (x * y) := by field_simp
  rw [hl, hr]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hh := mul_le_mul_of_nonneg_left hb (show 0 ≤ x * y by positivity)
  nlinarith

lemma sqrt_reciprocal_sum {K : ℕ} (hK : 0 < K) (B : ℕ) :
    (∑ p ∈ Finset.Ico K B, Real.sqrt p / ((p : ℝ) * (p + 1))) ≤
      2 / Real.sqrt K := by
  by_cases hKB : K ≤ B
  · calc
      _ ≤ ∑ p ∈ Finset.Ico K B,
          2 * ((-1 / Real.sqrt (p + 1 : ℕ)) - (-1 / Real.sqrt p)) := by
        apply Finset.sum_le_sum
        intro p hp
        have hp0 : 0 < p := hK.trans_le (Finset.mem_Ico.mp hp).1
        convert sqrt_reciprocal_step hp0 using 1 <;> push_cast <;> ring
      _ = 2 * ((-1 / Real.sqrt B) - (-1 / Real.sqrt K)) := by
        rw [← Finset.mul_sum, Finset.sum_Ico_sub (fun p : ℕ => -1 / Real.sqrt p) hKB]
      _ ≤ _ := by
        have hb : 0 ≤ 1 / Real.sqrt B := by positivity
        simp only [neg_div] at *
        have hk : 2 / Real.sqrt K = 2 * (1 / Real.sqrt K) := by ring
        rw [hk]
        linarith
  · rw [Finset.Ico_eq_empty_of_le (by omega), Finset.sum_empty]
    positivity

lemma cubic_cutoff {p T : ℕ} (hT : 0 < T)
    (h : p ^ 2 ≤ (Nat.sqrt p + 1) * T ^ 3) : p < 4 * T ^ 2 := by
  by_contra hn
  have hp : (2 * T) ^ 2 ≤ p := by nlinarith
  have hs : 2 * T ≤ Nat.sqrt p := Nat.le_sqrt'.mpr hp
  have hsq : (Nat.sqrt p) ^ 2 ≤ p := Nat.le_sqrt'.mp le_rfl
  have h4 : (Nat.sqrt p) ^ 4 ≤ p ^ 2 := by nlinarith [sq_nonneg (p - (Nat.sqrt p)^2 : ℤ)]
  have h4' : (Nat.sqrt p) ^ 4 ≤ (Nat.sqrt p) * (2 * T ^ 3) := by nlinarith
  have h3 : (Nat.sqrt p) ^ 3 ≤ 2 * T ^ 3 := by
    apply Nat.le_of_mul_le_mul_left (c := Nat.sqrt p) _ (by omega)
    nlinarith [h4']
  have hlo := Nat.pow_le_pow_left hs 3
  nlinarith [Nat.pow_pos hT (n := 3)]

def rootCover (K B N : ℕ) : Finset ℕ :=
  ((B + 1).primesBelow.filter (K ≤ ·)).biUnion fun p =>
    (Finset.Icc 1 (Nat.sqrt p)).biUnion fun c => primePairs p c N

lemma rootCover_card_bound {K : ℕ} (hK : 0 < K) (B N : ℕ) :
    ((rootCover K B N).card : ℝ) ≤
      4 * N / Real.sqrt K + 2 * Real.sqrt B * Nat.primeCounting B := by
  let s := (B + 1).primesBelow.filter (K ≤ ·)
  have hs (p : ℕ) (hp : p ∈ s) : K ≤ p ∧ p ≤ B := by
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hp
    exact ⟨h2, by have := (Nat.mem_primesBelow.mp h1).1; omega⟩
  have hc : (rootCover K B N).card ≤
      ∑ p ∈ s, ∑ c ∈ Finset.Icc 1 (Nat.sqrt p), (primePairs p c N).card := by
    apply Finset.card_biUnion_le.trans
    exact Finset.sum_le_sum (fun _ _ => Finset.card_biUnion_le)
  have h1 : ((rootCover K B N).card : ℝ) ≤
      ∑ p ∈ s, 2 * Real.sqrt p * ((N : ℝ) / ((p : ℝ) * (p + 1)) + 1) := by
    calc
      _ ≤ ∑ p ∈ s, ∑ c ∈ Finset.Icc 1 (Nat.sqrt p), ((primePairs p c N).card : ℝ) := by
        exact_mod_cast hc
      _ ≤ ∑ p ∈ s, 2 * Real.sqrt p * ((N : ℝ) / ((p : ℝ) * (p + 1)) + 1) := by
        apply Finset.sum_le_sum
        intro p hp
        have hp0 : 0 < p := hK.trans_le (hs p hp).1
        calc
          _ ≤ ∑ _c ∈ Finset.Icc 1 (Nat.sqrt p),
              2 * ((N : ℝ) / ((p : ℝ) * (p + 1)) + 1) := by
            apply Finset.sum_le_sum
            intro c hc
            have hcard : ((primePairs p c N).card : ℝ) ≤
                2 * (((N / (p * (p + 1)) : ℕ) : ℝ) + 1) := by
              exact_mod_cast primePairs_card_le hp0 c N
            have hdiv : ((N / (p * (p + 1)) : ℕ) : ℝ) ≤
                (N : ℝ) / ((p : ℝ) * (p + 1)) := by
              simpa using (Nat.cast_div_le (α := ℝ) (m := N) (n := p * (p + 1)))
            linarith
          _ = 2 * (Nat.sqrt p : ℕ) * ((N : ℝ) / ((p : ℝ) * (p + 1)) + 1) := by simp; ring
          _ ≤ _ := by
            have hb := Real.nat_sqrt_le_real_sqrt (a := p)
            gcongr
  have hsum : (∑ p ∈ s, Real.sqrt p / ((p : ℝ) * (p + 1))) ≤ 2 / Real.sqrt K := by
    apply le_trans _ (sqrt_reciprocal_sum hK (B + 1))
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      exact Finset.mem_Ico.mpr ⟨(hs p hp).1, by have := (hs p hp).2; omega⟩
    · intro p hp hps
      positivity
  have hsum2 : (∑ p ∈ s, Real.sqrt p) ≤ Real.sqrt B * Nat.primeCounting B := by
    calc
      _ ≤ ∑ _p ∈ s, Real.sqrt B := by
        apply Finset.sum_le_sum
        intro p hp
        exact Real.sqrt_le_sqrt (Nat.cast_le.mpr (hs p hp).2)
      _ = Real.sqrt B * s.card := by simp; ring
      _ ≤ Real.sqrt B * ((B + 1).primesBelow.card : ℕ) := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        exact_mod_cast Finset.card_filter_le (B + 1).primesBelow (K ≤ ·)
      _ = _ := by rw [Nat.primesBelow_card_eq_primeCounting']; rfl
  have he : (∑ p ∈ s, 2 * Real.sqrt p * ((N : ℝ) / ((p : ℝ) * (p + 1)) + 1)) =
      2 * N * (∑ p ∈ s, Real.sqrt p / ((p : ℝ) * (p + 1))) +
      2 * ∑ p ∈ s, Real.sqrt p := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  rw [he] at h1
  calc
    _ ≤ 2 * N * (2 / Real.sqrt K) + 2 * (Real.sqrt B * Nat.primeCounting B) := by
      nlinarith [mul_le_mul_of_nonneg_left hsum (show 0 ≤ 2 * (N : ℝ) by positivity)]
    _ = _ := by ring

lemma mem_rootCover {K B N n : ℕ} (hnN : n < N) (hn : 3 ≤ n)
    (hK : K ≤ min (P n) (P (n + 1))) (hb : min (P n) (P (n + 1)) ≤ B)
    (hgap : n ∈ rootGapSet) : n ∈ rootCover K B N := by
  have hp := Nat.prime_maxPrimeFac_of_one_lt n (by omega)
  have hq := Nat.prime_maxPrimeFac_of_one_lt (n + 1) (by omega)
  have hne := Erdos371PrimeDiscrepancy.consecutive_ne n
  change P (n + 1) ≠ P n at hne
  change Nat.dist (P n) (P (n + 1)) ≤ Nat.sqrt (min (P n) (P (n + 1))) at hgap
  unfold rootCover
  by_cases h : P n < P (n + 1)
  · have hd : P n + (P (n + 1) - P n) = P (n + 1) := by omega
    rw [min_eq_left h.le] at hK hb hgap
    rw [Nat.dist_eq_sub_of_le h.le] at hgap
    apply Finset.mem_biUnion.mpr
    refine ⟨P n, Finset.mem_filter.mpr ⟨Nat.mem_primesBelow.mpr ⟨by omega, hp⟩, hK⟩, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨P (n + 1) - P n, Finset.mem_Icc.mpr ⟨by omega, hgap⟩, ?_⟩
    have hh : (P n).Prime ∧ (P n + (P (n + 1) - P n)).Prime ∧ 0 < P (n + 1) - P n := by
      exact ⟨hp, by rw [hd]; exact hq, by omega⟩
    rw [primePairs, if_pos hh]
    apply Finset.mem_union_left
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hnN,
      Nat.maxPrimeFac_dvd, by rw [hd]; exact Nat.maxPrimeFac_dvd⟩
  · have h' : P (n + 1) < P n := by omega
    have hd : P (n + 1) + (P n - P (n + 1)) = P n := by omega
    rw [min_eq_right h'.le] at hK hb hgap
    rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h'.le] at hgap
    apply Finset.mem_biUnion.mpr
    refine ⟨P (n + 1), Finset.mem_filter.mpr ⟨Nat.mem_primesBelow.mpr ⟨by omega, hq⟩, hK⟩, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨P n - P (n + 1), Finset.mem_Icc.mpr ⟨by omega, hgap⟩, ?_⟩
    have hh : (P (n + 1)).Prime ∧ (P (n + 1) + (P n - P (n + 1))).Prime ∧
        0 < P n - P (n + 1) := by exact ⟨hq, by rw [hd]; exact hp, by omega⟩
    rw [primePairs, if_pos hh]
    apply Finset.mem_union_right
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hnN,
      by rw [hd]; exact Nat.maxPrimeFac_dvd, Nat.maxPrimeFac_dvd⟩

lemma root_gap_cubic_bound {K T : ℕ} (hK : 0 < K) (hT : 0 < T) :
    rootGapSet.partialDensity Set.univ (T ^ 3) ≤
      3 / (T ^ 3 : ℕ) + (lowSet K).partialDensity Set.univ (T ^ 3) +
      4 / Real.sqrt K + 16 * ((Nat.primeCounting (4 * T ^ 2) : ℝ) / (4 * T ^ 2 : ℕ)) := by
  let N := T ^ 3
  let B := 4 * T ^ 2
  let G := (Finset.range N).filter (fun n => Nat.dist (P n) (P (n + 1)) ≤ Nat.sqrt (min (P n) (P (n + 1))))
  let L := (Finset.range N).filter (fun n => P n ≤ K ∨ P (n + 1) ≤ K)
  have hsub : G ⊆ (Finset.range 3 ∪ L) ∪ rootCover K B N := by
    intro n hn
    obtain ⟨hnN, hgap⟩ := Finset.mem_filter.mp hn
    have hnN' := Finset.mem_range.mp hnN
    by_cases hn3 : n < 3
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_range.mpr hn3))
    by_cases hlo : n ∈ lowSet K
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hnN, hlo⟩))
    · apply Finset.mem_union_right
      apply mem_rootCover hnN' (by omega) _ _ hgap
      · change ¬(P n ≤ K ∨ P (n + 1) ≤ K) at hlo
        omega
      · apply (cubic_cutoff hT _).le
        exact (min_prime_sq_le (by omega) hgap).trans (Nat.mul_le_mul_left _ (by omega))
  have hc : G.card ≤ 3 + L.card + (rootCover K B N).card := by
    calc
      G.card ≤ ((Finset.range 3 ∪ L) ∪ rootCover K B N).card := Finset.card_le_card hsub
      _ ≤ (Finset.range 3 ∪ L).card + (rootCover K B N).card := Finset.card_union_le _ _
      _ ≤ (Finset.range 3).card + L.card + (rootCover K B N).card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ = _ := by simp
  have hc' : (G.card : ℝ) ≤ 3 + L.card + (rootCover K B N).card := by exact_mod_cast hc
  have hu := rootCover_card_bound hK B N
  have hg : rootGapSet.partialDensity Set.univ N = (G.card : ℝ) / N :=
    partialDensity_filter _ N
  have hl : (lowSet K).partialDensity Set.univ N = (L.card : ℝ) / N :=
    partialDensity_filter _ N
  change rootGapSet.partialDensity Set.univ N ≤ _
  rw [hg, hl]
  calc
    _ ≤ (3 + L.card + 4 * N / Real.sqrt K + 2 * Real.sqrt B * Nat.primeCounting B) / N :=
      div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg N)
    _ = _ := by
      have ht : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
      have hk : Real.sqrt K ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hK)).ne'
      have hb : Real.sqrt (B : ℝ) = 2 * T := by
        dsimp [B]
        push_cast
        rw [show (4 : ℝ) * T ^ 2 = (2 * T) ^ 2 by ring,
          Real.sqrt_sq (by positivity)]
      rw [hb]
      dsimp [N, B]
      push_cast
      field_simp
      ring

open Filter
open scoped Topology

lemma root_gap_density_cubes :
    Tendsto (fun T : ℕ => rootGapSet.partialDensity Set.univ (T ^ 3)) atTop (𝓝 0) := by
  have hsqrt : Tendsto (fun K : ℕ => 4 / Real.sqrt K) atTop (𝓝 0) := by
    have ht : Tendsto (fun K : ℕ => Real.sqrt K) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp ht) :
        Tendsto (fun K : ℕ => (4 : ℝ) * (Real.sqrt K)⁻¹) atTop (𝓝 (4 * 0)))
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K, hK, hsmallK⟩ := ((eventually_gt_atTop 0).and
    (hsqrt.eventually (gt_mem_nhds (half_pos hε)))).exists
  have hcube : Tendsto (fun T : ℕ => T ^ 3) atTop atTop := tendsto_pow_atTop (by decide)
  have hquad : Tendsto (fun T : ℕ => 4 * T ^ 2) atTop atTop := by
    apply tendsto_atTop_mono (f := fun T : ℕ => T) _ tendsto_id
    intro T
    nlinarith
  have he : Tendsto (fun T : ℕ =>
      3 / (T ^ 3 : ℕ) + (lowSet K).partialDensity Set.univ (T ^ 3) +
      16 * ((Nat.primeCounting (4 * T ^ 2) : ℝ) / (4 * T ^ 2 : ℕ))) atTop (𝓝 0) := by
    simpa using (((tendsto_const_div_atTop_nhds_zero_nat (3 : ℝ)).comp hcube).add
      ((lowSet_hasDensity_zero K).comp hcube)).add
      (tendsto_const_nhds.mul (Erdos371CofactorDensity.primeCounting_ratio_tendsto_zero.comp hquad))
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (he.eventually (gt_mem_nhds (half_pos hε)))
  refine ⟨max T₀ 1, fun T hT => ?_⟩
  have hb := root_gap_cubic_bound hK (T := T) (by omega)
  have hh := hT₀ T (by omega)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by unfold Set.partialDensity; positivity)]
  change 4 / Real.sqrt K < ε / 2 at hsmallK
  linarith

lemma exists_cubic_bracket {N : ℕ} (hN : 0 < N) :
    ∃ T : ℕ, 0 < T ∧ N ≤ T ^ 3 ∧ T ^ 3 ≤ 8 * N := by
  have hex : ∃ T : ℕ, N ≤ T ^ 3 := by
    refine ⟨N, ?_⟩
    simpa using (Nat.pow_le_pow_right hN (by decide : 1 ≤ 3))
  let T := Nat.find hex
  have hNT : N ≤ T ^ 3 := Nat.find_spec hex
  have hT : 0 < T := by
    by_contra hh
    have hz : T = 0 := by omega
    simp [hz] at hNT
    omega
  refine ⟨T, hT, hNT, ?_⟩
  by_cases h1 : T = 1
  · rw [h1]
    norm_num
    omega
  · have hlow : (T - 1) ^ 3 < N := by
      have hn := Nat.find_min hex (show T - 1 < T by omega)
      omega
    have h2 : T ≤ 2 * (T - 1) := by omega
    have hpow := Nat.pow_le_pow_left h2 3
    nlinarith

lemma partialDensity_le_eight_of_bracket (S : Set ℕ) {N M : ℕ}
    (hN : 0 < N) (hNM : N ≤ M) (hMN : M ≤ 8 * N) :
    S.partialDensity Set.univ N ≤ 8 * S.partialDensity Set.univ M := by
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio]
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hm : (0 : ℝ) < M := Nat.cast_pos.mpr (hN.trans_le hNM)
  have hc : (S ∩ Set.Iio N).ncard ≤ (S ∩ Set.Iio M).ncard :=
    Set.ncard_le_ncard (Set.inter_subset_inter_right _ (Set.Iio_subset_Iio hNM))
  have hr : (M : ℝ) / N ≤ 8 := (div_le_iff₀ hn).mpr (by exact_mod_cast hMN)
  calc
    _ ≤ ((S ∩ Set.Iio M).ncard : ℝ) / N :=
      div_le_div_of_nonneg_right (Nat.cast_le.mpr hc) hn.le
    _ = (((S ∩ Set.Iio M).ncard : ℝ) / M) * ((M : ℝ) / N) := by
      field_simp
    _ ≤ (((S ∩ Set.Iio M).ncard : ℝ) / M) * 8 :=
      mul_le_mul_of_nonneg_left hr (by positivity)
    _ = _ := by ring

lemma hasDensity_zero_of_cubes (S : Set ℕ)
    (h : Tendsto (fun T : ℕ => S.partialDensity Set.univ (T ^ 3)) atTop (𝓝 0)) :
    S.HasDensity 0 := by
  rw [Set.HasDensity, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp
    (h.eventually (gt_mem_nhds (show 0 < ε / 8 by positivity)))
  refine ⟨T₀ ^ 3 + 1, fun N hN => ?_⟩
  obtain ⟨T, hT, hNT, hTN⟩ := exists_cubic_bracket (N := N) (by omega)
  have hTbig : T₀ ≤ T := by
    by_contra hh
    have he := Nat.pow_le_pow_left (show T ≤ T₀ by omega) 3
    omega
  have hs := hT₀ T hTbig
  have hb := partialDensity_le_eight_of_bracket S (by omega : 0 < N) hNT hTN
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by unfold Set.partialDensity; positivity)]
  linarith

/-- Comparisons with prime gap at most the square root of the smaller prime
have natural density zero. -/
lemma square_root_prime_gap_hasDensity_zero : rootGapSet.HasDensity 0 :=
  hasDensity_zero_of_cubes rootGapSet root_gap_density_cubes

end Erdos371SquareRootPrimeGap

#print axioms Erdos371SquareRootPrimeGap.square_root_prime_gap_hasDensity_zero
#print axioms Erdos371SquareRootPrimeGap.rootCover_card_bound
#print axioms Erdos371SquareRootPrimeGap.cubic_cutoff
