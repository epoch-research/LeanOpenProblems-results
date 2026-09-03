import FormalConjecturesUtil
import Submission.CofactorReflection
import Submission.PrimeDiscrepancy
import Submission.CofactorDensity
import Submission.SmoothDensity

/-! Counting comparisons whose largest prime factors have bounded additive difference.
This does not determine which orientation has density one half. -/

namespace Erdos371BoundedPrimeGap

open Erdos371Cofactor

lemma min_prime_sq_le {H n : ℕ} (hn : 3 ≤ n)
    (hgap : Nat.dist (P n) (P (n + 1)) ≤ H) :
    (min (P n) (P (n + 1))) ^ 2 ≤ (H + 1) * (n + 1) := by
  have ha := cofactor_mul n
  have hb := cofactor_mul (n + 1)
  have hne := Erdos371PrimeDiscrepancy.consecutive_ne n
  change P (n + 1) ≠ P n at hne
  by_cases h : P n < P (n + 1)
  · have hba := (comparison_iff_cofactor_reverse hn).mp h
    have hq : P (n + 1) ≤ P n + H := by
      rw [Nat.dist_eq_sub_of_le h.le] at hgap
      omega
    have h1 := Nat.mul_le_mul_right (P n) hba
    have h2 := Nat.mul_le_mul_left (cofactor (n + 1)) hq
    have hp : P n ≤ H * cofactor (n + 1) := by nlinarith
    rw [min_eq_left h.le]
    calc
      (P n)^2 ≤ (H * cofactor (n + 1)) * P n := by
        simpa [pow_two] using Nat.mul_le_mul_right (P n) hp
      _ = H * (cofactor (n + 1) * P n) := by ring
      _ ≤ H * n := Nat.mul_le_mul_left H (by
        calc
          cofactor (n + 1) * P n ≤ cofactor n * P n := Nat.mul_le_mul_right _ hba.le
          _ = n := ha)
      _ ≤ (H + 1) * (n + 1) := by nlinarith
  · have hqp : P (n + 1) < P n := by omega
    have hab : cofactor n < cofactor (n + 1) := by
      have hnc := cofactor_consecutive_ne hn
      have hh : ¬cofactor (n + 1) < cofactor n :=
        fun hh => h ((comparison_iff_cofactor_reverse hn).mpr hh)
      omega
    have hp : P n ≤ P (n + 1) + H := by
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hqp.le] at hgap
      omega
    have h1 := Nat.mul_le_mul_right (P (n + 1)) hab
    have h2 := Nat.mul_le_mul_left (cofactor n) hp
    have hq : P (n + 1) ≤ H * cofactor n + 1 := by nlinarith
    rw [min_eq_right hqp.le]
    calc
      (P (n + 1))^2 ≤ (H * cofactor n + 1) * P (n + 1) := by
        simpa [pow_two] using Nat.mul_le_mul_right (P (n + 1)) hq
      _ = H * (cofactor n * P (n + 1)) + P (n + 1) := by ring
      _ ≤ H * n + (n + 1) := Nat.add_le_add
        (Nat.mul_le_mul_left H (by
          calc
            cofactor n * P (n + 1) ≤ cofactor n * P n := Nat.mul_le_mul_left _ hqp.le
            _ = n := ha)) Nat.maxPrimeFac_le
      _ ≤ (H + 1) * (n + 1) := by nlinarith

/-- A two-congruence class has at most one member in each block of length `p*q`. -/
def solutions (p q N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun n => p ∣ n ∧ q ∣ n + 1)

lemma solutions_card_le {p q : ℕ} (hpq : p.Coprime q) (N : ℕ) :
    (solutions p q N).card ≤ N / (p * q) + 1 := by
  by_cases hz : p * q = 0
  · have hs : solutions p q N ⊆ {0} := by
      intro n hn
      obtain ⟨_, hpn, hqn⟩ := Finset.mem_filter.mp hn
      rcases Nat.mul_eq_zero.mp hz with hp | hq
      · subst p
        simpa using hpn
      · subst q
        simp at hqn
    have hc := Finset.card_le_card hs
    simp only [Finset.card_singleton] at hc
    simpa [hz] using hc
  · calc
      (solutions p q N).card ≤ (Finset.range (N / (p * q) + 1)).card := by
        apply Finset.card_le_card_of_injOn (fun n => n / (p * q))
        · intro n hn
          have hnN := Finset.mem_range.mp (Finset.mem_filter.mp hn).1
          exact Finset.mem_range.mpr (by
            change n / (p * q) < N / (p * q) + 1
            have := Nat.div_le_div_right (show n ≤ N by omega) (c := p * q)
            omega)
        · intro n hn m hm hnm
          change n / (p * q) = m / (p * q) at hnm
          simp only [Finset.mem_coe, solutions, Finset.mem_filter] at hn hm
          obtain ⟨_, hpn, hqn⟩ := hn
          obtain ⟨_, hpm, hqm⟩ := hm
          have hmodp : Nat.ModEq p n m := by
            show n % p = m % p
            rw [Nat.mod_eq_zero_of_dvd hpn, Nat.mod_eq_zero_of_dvd hpm]
          have hmodq : Nat.ModEq q n m := by
            apply Nat.ModEq.add_right_cancel' 1
            show (n + 1) % q = (m + 1) % q
            rw [Nat.mod_eq_zero_of_dvd hqn, Nat.mod_eq_zero_of_dvd hqm]
          have hmod := (Nat.modEq_and_modEq_iff_modEq_mul hpq).mp ⟨hmodp, hmodq⟩
          have hnn := Nat.mod_add_div n (p * q)
          have hmm := Nat.mod_add_div m (p * q)
          change n % (p * q) = m % (p * q) at hmod
          rw [hmod, hnm] at hnn
          omega
      _ = N / (p * q) + 1 := Finset.card_range _

def primePairs (p c N : ℕ) : Finset ℕ :=
  if p.Prime ∧ (p + c).Prime ∧ 0 < c then
    solutions p (p + c) N ∪ solutions (p + c) p N else ∅

lemma primePairs_card_le {p : ℕ} (hp0 : 0 < p) (c N : ℕ) :
    (primePairs p c N).card ≤ 2 * (N / (p * (p + 1)) + 1) := by
  unfold primePairs
  split_ifs with h
  · obtain ⟨hp, hq, hc⟩ := h
    have hcop : p.Coprime (p + c) := (Nat.coprime_primes hp hq).mpr (by omega)
    have hden : 0 < p * (p + 1) := by positivity
    have hmul : p * (p + 1) ≤ p * (p + c) := Nat.mul_le_mul_left p (by omega)
    have hd := Nat.div_le_div_left (a := N) hmul hden
    have h1 := solutions_card_le hcop N
    have h2 := solutions_card_le hcop.symm N
    rw [Nat.mul_comm (p + c) p] at h2
    have hu := Finset.card_union_le (solutions p (p + c) N) (solutions (p + c) p N)
    omega
  · simp

lemma reciprocal_sum_bound {K : ℕ} (hK : 0 < K) (B N : ℕ) :
    (∑ p ∈ Finset.Ico K B, ((N : ℝ) / ((p : ℝ) * (p + 1)) + 1)) ≤
      (N : ℝ) / K + B := by
  by_cases hKB : K ≤ B
  · have he : (∑ p ∈ Finset.Ico K B, (N : ℝ) / ((p : ℝ) * (p + 1))) =
        ∑ p ∈ Finset.Ico K B, ((-(N : ℝ) / (p + 1 : ℕ)) - (-(N : ℝ) / p)) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hp0 : (p : ℝ) ≠ 0 := by
        apply Nat.cast_ne_zero.mpr
        have := (Finset.mem_Ico.mp hp).1
        omega
      push_cast
      field_simp
      ring
    rw [Finset.sum_add_distrib, he, Finset.sum_Ico_sub (fun p : ℕ => -(N : ℝ) / p) hKB]
    simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
    have hcard : ((B - K : ℕ) : ℝ) ≤ B := Nat.cast_le.mpr (Nat.sub_le _ _)
    have hnB : (0 : ℝ) ≤ (N : ℝ) / B := by positivity
    simp only [neg_div] at *
    linarith
  · have he : Finset.Ico K B = ∅ := Finset.Ico_eq_empty_of_le (by omega)
    rw [he, Finset.sum_empty]
    positivity

def cover (K B H N : ℕ) : Finset ℕ :=
  (Finset.Ico K B).biUnion fun p => (Finset.Icc 1 H).biUnion fun c => primePairs p c N

lemma cover_card_bound {K : ℕ} (hK : 0 < K) (B H N : ℕ) :
    ((cover K B H N).card : ℝ) ≤ 2 * H * ((N : ℝ) / K + B) := by
  have hc : (cover K B H N).card ≤
      ∑ p ∈ Finset.Ico K B, ∑ c ∈ Finset.Icc 1 H, (primePairs p c N).card := by
    apply Finset.card_biUnion_le.trans
    exact Finset.sum_le_sum (fun _ _ => Finset.card_biUnion_le)
  calc
    _ ≤ ∑ p ∈ Finset.Ico K B, ∑ c ∈ Finset.Icc 1 H, ((primePairs p c N).card : ℝ) := by
      exact_mod_cast hc
    _ ≤ ∑ p ∈ Finset.Ico K B, 2 * H * ((N : ℝ) / ((p : ℝ) * (p + 1)) + 1) := by
      apply Finset.sum_le_sum
      intro p hp
      have hp0 : 0 < p := hK.trans_le (Finset.mem_Ico.mp hp).1
      calc
        _ ≤ ∑ _c ∈ Finset.Icc 1 H,
            2 * ((N : ℝ) / ((p : ℝ) * (p + 1)) + 1) := by
          apply Finset.sum_le_sum
          intro c hc
          have hb : ((primePairs p c N).card : ℝ) ≤
              2 * (((N / (p * (p + 1)) : ℕ) : ℝ) + 1) := by
            exact_mod_cast primePairs_card_le hp0 c N
          apply hb.trans
          have hd : ((N / (p * (p + 1)) : ℕ) : ℝ) ≤
              (N : ℝ) / ((p : ℝ) * (p + 1)) := by
            simpa using (Nat.cast_div_le (α := ℝ) (m := N) (n := p * (p + 1)))
          linarith
        _ = _ := by simp; ring
    _ = (2 * H) * ∑ p ∈ Finset.Ico K B,
        ((N : ℝ) / ((p : ℝ) * (p + 1)) + 1) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (reciprocal_sum_bound hK B N) (by positivity)

lemma mem_cover_of_close {H K N n : ℕ} (hnN : n < N) (hn : 3 ≤ n)
    (hK : K ≤ min (P n) (P (n + 1)))
    (hgap : Nat.dist (P n) (P (n + 1)) ≤ H) :
    n ∈ cover K (Nat.sqrt ((H + 1) * N) + 1) H N := by
  have hb : min (P n) (P (n + 1)) ≤ Nat.sqrt ((H + 1) * N) := by
    apply Nat.le_sqrt'.mpr
    exact (min_prime_sq_le hn hgap).trans (Nat.mul_le_mul_left _ (by omega))
  have hp := Nat.prime_maxPrimeFac_of_one_lt n (by omega)
  have hq := Nat.prime_maxPrimeFac_of_one_lt (n + 1) (by omega)
  have hne := Erdos371PrimeDiscrepancy.consecutive_ne n
  change P (n + 1) ≠ P n at hne
  unfold cover
  by_cases h : P n < P (n + 1)
  · have hd : P n + (P (n + 1) - P n) = P (n + 1) := by omega
    rw [min_eq_left h.le] at hK hb
    rw [Nat.dist_eq_sub_of_le h.le] at hgap
    apply Finset.mem_biUnion.mpr
    refine ⟨P n, Finset.mem_Ico.mpr ⟨hK, by omega⟩, ?_⟩
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
    rw [min_eq_right h'.le] at hK hb
    rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h'.le] at hgap
    apply Finset.mem_biUnion.mpr
    refine ⟨P (n + 1), Finset.mem_Ico.mpr ⟨hK, by omega⟩, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨P n - P (n + 1), Finset.mem_Icc.mpr ⟨by omega, hgap⟩, ?_⟩
    have hh : (P (n + 1)).Prime ∧ (P (n + 1) + (P n - P (n + 1))).Prime ∧
        0 < P n - P (n + 1) := by exact ⟨hq, by rw [hd]; exact hp, by omega⟩
    rw [primePairs, if_pos hh]
    apply Finset.mem_union_right
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hnN,
      by rw [hd]; exact Nat.maxPrimeFac_dvd, Nat.maxPrimeFac_dvd⟩

def gapSet (H : ℕ) : Set ℕ := {n | Nat.dist (P n) (P (n + 1)) ≤ H}
def lowSet (K : ℕ) : Set ℕ := {n | P n ≤ K ∨ P (n + 1) ≤ K}

lemma partialDensity_filter (f : ℕ → Prop) [DecidablePred f] (N : ℕ) :
    {n | f n}.partialDensity Set.univ N =
      (((Finset.range N).filter f).card : ℝ) / N := by
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio]
  have he : {n | f n} ∩ Set.Iio N = ↑((Finset.range N).filter f) := by
    ext n
    simp [and_comm]
  rw [he, Set.ncard_coe_finset]

lemma gap_partialDensity_bound {K N : ℕ} (hK : 0 < K) (hN : 0 < N) (H : ℕ) :
    (gapSet H).partialDensity Set.univ N ≤
      3 / (N : ℝ) + (lowSet K).partialDensity Set.univ N +
      (2 * H : ℝ) / K +
      (2 * H : ℝ) * (((Nat.sqrt ((H + 1) * N) + 1 : ℕ) : ℝ) / N) := by
  let G := (Finset.range N).filter (fun n => Nat.dist (P n) (P (n + 1)) ≤ H)
  let L := (Finset.range N).filter (fun n => P n ≤ K ∨ P (n + 1) ≤ K)
  let B := Nat.sqrt ((H + 1) * N) + 1
  have hsub : G ⊆ (Finset.range 3 ∪ L) ∪ cover K B H N := by
    intro n hn
    obtain ⟨hnN, hgap⟩ := Finset.mem_filter.mp hn
    have hnN' := Finset.mem_range.mp hnN
    by_cases hn3 : n < 3
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_range.mpr hn3))
    by_cases hlo : P n ≤ K ∨ P (n + 1) ≤ K
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hnN, hlo⟩))
    · apply Finset.mem_union_right
      exact mem_cover_of_close hnN' (by omega) (by omega) hgap
  have hc : G.card ≤ 3 + L.card + (cover K B H N).card := by
    calc
      G.card ≤ ((Finset.range 3 ∪ L) ∪ cover K B H N).card := Finset.card_le_card hsub
      _ ≤ (Finset.range 3 ∪ L).card + (cover K B H N).card := Finset.card_union_le _ _
      _ ≤ (Finset.range 3).card + L.card + (cover K B H N).card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ = _ := by simp
  have hc' : (G.card : ℝ) ≤ 3 + L.card + (cover K B H N).card := by exact_mod_cast hc
  have hu := cover_card_bound hK B H N
  have hg : (gapSet H).partialDensity Set.univ N = (G.card : ℝ) / N :=
    partialDensity_filter _ N
  have hl : (lowSet K).partialDensity Set.univ N = (L.card : ℝ) / N :=
    partialDensity_filter _ N
  rw [hg, hl]
  calc
    (G.card : ℝ) / N ≤ (3 + L.card + 2 * H * ((N : ℝ) / K + B)) / N :=
      div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg N)
    _ = _ := by
      change _ = 3 / (N : ℝ) + (L.card : ℝ) / N + (2 * H : ℝ) / K + (2 * H : ℝ) * ((B : ℝ) / N)
      have hn : (N : ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
      have hk : (K : ℝ) ≠ 0 := (Nat.cast_pos.mpr hK).ne'
      field_simp
      ring

open Filter
open scoped Topology

lemma lowSet_hasDensity_zero (K : ℕ) : (lowSet K).HasDensity 0 := by
  have h1 : {n | P n ≤ K}.HasDensity 0 :=
    Erdos371Exploration.bounded_maxPrimeFac_hasDensity_zero K
  have h2 : {n | P (n + 1) ≤ K}.HasDensity 0 :=
    Erdos371CofactorDensity.density_zero_shift (S := {n | P n ≤ K}) h1
  exact Erdos371CofactorDensity.density_zero_union
    (S := {n | P n ≤ K}) (T := {n | P (n + 1) ≤ K}) h1 h2

lemma sqrt_cutoff_ratio_tendsto_zero (H : ℕ) :
    Tendsto (fun N : ℕ => (((Nat.sqrt ((H + 1) * N) + 1 : ℕ) : ℝ) / N))
      atTop (𝓝 0) := by
  have hs : Tendsto (fun N : ℕ => Real.sqrt N / N) atTop (𝓝 0) := by
    simp_rw [Real.sqrt_div_self]
    exact tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hu : Tendsto (fun N : ℕ =>
      (Real.sqrt (H + 1 : ℝ) * Real.sqrt N + 1) / N) atTop (𝓝 0) := by
    simpa [add_div, mul_div_assoc] using
      (tendsto_const_nhds.mul hs).add tendsto_one_div_atTop_nhds_zero_nat
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
  · intro N
    positivity
  · intro N
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    have hb := Real.nat_sqrt_le_real_sqrt (a := (H + 1) * N)
    push_cast at hb ⊢
    rw [Real.sqrt_mul (by positivity)] at hb
    linarith

/-- For every fixed additive gap, the exceptional comparisons have density zero. -/
lemma bounded_prime_gap_hasDensity_zero (H : ℕ) : (gapSet H).HasDensity 0 := by
  rw [Set.HasDensity]
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨K, hK, hsmallK⟩ := ((eventually_gt_atTop 0).and
    ((tendsto_const_div_atTop_nhds_zero_nat (2 * H : ℝ)).eventually
      (gt_mem_nhds (half_pos hε)))).exists
  have he : Tendsto (fun N : ℕ =>
      3 / (N : ℝ) + (lowSet K).partialDensity Set.univ N +
      (2 * H : ℝ) * (((Nat.sqrt ((H + 1) * N) + 1 : ℕ) : ℝ) / N))
      atTop (𝓝 0) := by
    simpa using ((tendsto_const_div_atTop_nhds_zero_nat (3 : ℝ)).add
      (lowSet_hasDensity_zero K)).add (tendsto_const_nhds.mul (sqrt_cutoff_ratio_tendsto_zero H))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (he.eventually (gt_mem_nhds (half_pos hε)))
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  have hb := gap_partialDensity_bound hK (N := N) (by omega) H
  have hh := hN₀ N (by omega)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by unfold Set.partialDensity; positivity)]
  change (2 * H : ℝ) / K < ε / 2 at hsmallK
  linarith

end Erdos371BoundedPrimeGap

#print axioms Erdos371BoundedPrimeGap.bounded_prime_gap_hasDensity_zero
#print axioms Erdos371BoundedPrimeGap.min_prime_sq_le
#print axioms Erdos371BoundedPrimeGap.solutions_card_le
#print axioms Erdos371BoundedPrimeGap.cover_card_bound
#print axioms Erdos371BoundedPrimeGap.mem_cover_of_close
