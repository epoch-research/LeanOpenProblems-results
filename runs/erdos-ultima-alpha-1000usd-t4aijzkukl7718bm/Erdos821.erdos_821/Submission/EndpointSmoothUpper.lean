import Submission.SharpLargeChild
import Submission.Density

/-!
# Endpoint upper bounds from a summable smooth-predecessor series

A finite cofactor sum gives an explicit omega(n) error at s=1-1/k.
The arithmetic summability/divergence question remains open here.
-/

open Nat Filter
open scoped Classical BigOperators

namespace Erdos821

set_option maxHeartbeats 2000000

lemma g_le_of_summable_smooth_shifted_sharp (k : ℕ) (hk : 1 ≤ k) (s : ℝ)
    (hs : 0 ≤ s) (hs1 : s < 1)
    (H : Summable ((smoothShiftedPredecessors k).indicator (fun d : ℕ => (d : ℝ) ^ (-s))))
    (n : ℕ) (hn : 0 < n) :
    (g n : ℝ) ≤ (n : ℝ) ^ s * Real.exp
      ((∑' d : ℕ, (smoothShiftedPredecessors k).indicator (fun d : ℕ => (d : ℝ) ^ (-s)) d) +
        (1/(1-s)) *
          ∑ q ∈ n.primeFactors, (q : ℝ) ^ ((k : ℝ)*(1-s)-1)) := by
  classical
  let P := shiftedPrimeDivisors n
  let D := P.image (fun p => p - 1)
  have hD (d : ℕ) (hd : d ∈ D) : 0 < d ∧ (d + 1).Prime ∧ d ∣ n := by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨_, hpprime, hpdvd⟩ := Finset.mem_filter.mp hp
    refine ⟨Nat.sub_pos_of_lt hpprime.one_lt, ?_, hpdvd⟩
    simpa only [Nat.sub_add_cancel hpprime.one_lt.le] using hpprime
  have hinj : Set.InjOn (fun p : ℕ => p - 1) (↑P : Set ℕ) := by
    intro p hp q hq h
    change p ∈ shiftedPrimeDivisors n at hp
    change q ∈ shiftedPrimeDivisors n at hq
    have hp2 := (Finset.mem_filter.mp hp).2.1.two_le
    have hq2 := (Finset.mem_filter.mp hq).2.1.two_le
    change p - 1 = q - 1 at h
    omega
  let E := D.filter (fun d => d ∉ smoothShiftedPredecessors k)
  have hrough := rough_divisor_weight_sum_sharp E n.primeFactors k hk s hs hs1
    (fun d hd => (hD d (Finset.mem_filter.mp hd).1).1)
    (fun q hq => Nat.pos_of_mem_primeFactors hq) (by
      intro d hd
      obtain ⟨hdD, hdns⟩ := Finset.mem_filter.mp hd
      have hdp := (hD d hdD).2.1
      have hnot : ¬∀ q ∈ d.primeFactors, q ^ k ≤ d := fun h => hdns ⟨hdp, h⟩
      push_neg at hnot
      obtain ⟨q, hq, hqd⟩ := hnot
      refine ⟨q, ?_, Nat.dvd_of_mem_primeFactors hq, hqd.le⟩
      exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hq,
        (Nat.dvd_of_mem_primeFactors hq).trans (hD d hdD).2.2, hn.ne'⟩)
  have hsmooth : (∑ d ∈ D with d ∈ smoothShiftedPredecessors k, (d : ℝ) ^ (-s)) ≤
      ∑' d : ℕ, (smoothShiftedPredecessors k).indicator (fun d : ℕ => (d : ℝ) ^ (-s)) d := by
    calc
      _ = ∑ d ∈ D, (smoothShiftedPredecessors k).indicator (fun d : ℕ => (d : ℝ) ^ (-s)) d := by
        simp only [Finset.sum_filter, Set.indicator_apply]
      _ ≤ _ := Summable.sum_le_tsum _ (fun d _ => Set.indicator_nonneg
        (fun d _ => Real.rpow_nonneg (Nat.cast_nonneg d) _) _) H
  have htotal : (∑ p ∈ P, ((p - 1 : ℕ) : ℝ) ^ (-s)) ≤
      (∑' d : ℕ, (smoothShiftedPredecessors k).indicator (fun d : ℕ => (d : ℝ) ^ (-s)) d) +
        (1/(1-s)) *
          ∑ q ∈ n.primeFactors, (q : ℝ) ^ ((k : ℝ)*(1-s)-1) := by
    rw [← Finset.sum_image (f := fun d : ℕ => (d : ℝ) ^ (-s)) hinj]
    change (∑ d ∈ D, (d : ℝ) ^ (-s)) ≤ _
    rw [← Finset.sum_filter_add_sum_filter_not D (fun d => d ∈ smoothShiftedPredecessors k)]
    exact add_le_add hsmooth hrough
  calc
    (g n : ℝ) ≤ Real.exp (∑ p ∈ P, ((p - 1 : ℕ) : ℝ) ^ (-s)) * (n : ℝ) ^ s :=
      g_le_rpow_mul_exp_shifted n hn s hs
    _ ≤ Real.exp _ * (n : ℝ) ^ s :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr htotal) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    _ = _ := mul_comm _ _

lemma exists_sum_primeFactors_rpow_nonpos_le_log (β C δ : ℝ) (hβ : 0 ≤ β)
    (hC : 0 ≤ C) (hδ : 0 < δ) :
    ∃ A : ℝ, ∀ n : ℕ, 0 < n →
      C * (∑ q ∈ n.primeFactors, (q : ℝ) ^ (-β)) ≤ A + δ * Real.log n := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlim : Tendsto (fun p : ℕ => δ * Real.log p) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hδ
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (hlim.eventually (eventually_ge_atTop C))
  refine ⟨C * K, ?_⟩
  intro n hn
  have hpoint (p : ℕ) (hp : p ∈ n.primeFactors) :
      C * (p : ℝ) ^ (-β) ≤ (if p < K then C else 0) + δ * Real.log p := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hlogp : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) hp2
    by_cases hpK : p < K
    · rw [if_pos hpK]
      have hpow := Real.rpow_le_one_of_one_le_of_nonpos
        (show (1 : ℝ) ≤ p by linarith) (show -β ≤ 0 by linarith)
      have := mul_le_mul_of_nonneg_left hpow hC
      have := mul_nonneg hδ.le (hlog2.le.trans hlogp)
      nlinarith
    · rw [if_neg hpK, zero_add]
      have hpow := Real.rpow_le_one_of_one_le_of_nonpos
        (show (1 : ℝ) ≤ p by linarith) (neg_nonpos.mpr hβ)
      have hpC : C * (p : ℝ)^(-β) ≤ C := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow hC
      exact hpC.trans (hK p (Nat.le_of_not_gt hpK))
  have hsmall : (∑ p ∈ n.primeFactors, if p < K then C else 0) ≤ C * K := by
    rw [← Finset.sum_filter]
    have hsub : n.primeFactors.filter (fun p => p < K) ⊆ Finset.range K := by
      intro p hp
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
    have hcard : (n.primeFactors.filter (fun p => p < K)).card ≤ K := by
      simpa only [Finset.card_range] using Finset.card_le_card hsub
    simp only [Finset.sum_const, nsmul_eq_mul]
    calc
      _ ≤ (K : ℝ) * C := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hC
      _ = _ := mul_comm _ _
  have hlogsum : (∑ p ∈ n.primeFactors, Real.log (p : ℝ)) ≤ Real.log n := by
    rw [← Real.log_prod (fun p hp => by exact_mod_cast (Nat.pos_of_mem_primeFactors hp).ne')]
    apply Real.log_le_log
    · exact Finset.prod_pos (fun p hp => by exact_mod_cast Nat.pos_of_mem_primeFactors hp)
    · rw [← Nat.cast_prod]
      exact_mod_cast Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)
  calc
    C * (∑ q ∈ n.primeFactors, (q : ℝ) ^ (-β)) =
        ∑ q ∈ n.primeFactors, C * (q : ℝ) ^ (-β) := Finset.mul_sum _ _ _
    _ ≤ ∑ q ∈ n.primeFactors, ((if q < K then C else 0) + δ * Real.log q) :=
      Finset.sum_le_sum hpoint
    _ = (∑ q ∈ n.primeFactors, if q < K then C else 0) +
        δ * (∑ q ∈ n.primeFactors, Real.log q) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := add_le_add hsmall (mul_le_mul_of_nonneg_left hlogsum hδ.le)

lemma eventually_g_le_rpow_of_summable_smooth_endpoint (k : ℕ) (hk : 1 ≤ k) (s t : ℝ)
    (hs : 0 ≤ s) (hs1 : s < 1) (hst : s < t)
    (hrough : (k : ℝ)*(1-s)-1 ≤ 0)
    (H : Summable ((smoothShiftedPredecessors k).indicator (fun d : ℕ => (d : ℝ) ^ (-s)))) :
    ∀ᶠ n : ℕ in atTop, (g n : ℝ) ≤ (n : ℝ) ^ t := by
  let δ := (t - s) / 2
  have hδ : 0 < δ := half_pos (sub_pos.mpr hst)
  let β := 1-(k : ℝ)*(1-s)
  have hβ : 0 ≤ β := by dsimp [β]; linarith
  let C := 1/(1-s)
  have hC : 0 ≤ C := div_nonneg (by norm_num) (by linarith)
  let M := ∑' d : ℕ, (smoothShiftedPredecessors k).indicator (fun d : ℕ => (d : ℝ) ^ (-s)) d
  obtain ⟨A, hA⟩ := exists_sum_primeFactors_rpow_nonpos_le_log β C δ hβ hC hδ
  let K := Real.exp (M + A)
  have hbound (n : ℕ) (hn : 0 < n) : (g n : ℝ) ≤ K * (n : ℝ) ^ (s + δ) := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hg := g_le_of_summable_smooth_shifted_sharp k hk s hs hs1 H n hn
    have heq : (k : ℝ)*(1-s)-1 = -β := by dsimp [β]; ring
    rw [heq] at hg
    have hExp : Real.exp (M + (A + δ * Real.log n)) = K * (n : ℝ) ^ δ := by
      rw [show M + (A + δ * Real.log n) = (M + A) + Real.log n * δ by ring,
        Real.exp_add, ← Real.rpow_def_of_pos hnR δ]
    calc
      (g n : ℝ) ≤ (n : ℝ) ^ s * Real.exp (M + C * ∑ q ∈ n.primeFactors, (q : ℝ) ^ (-β)) := hg
      _ ≤ (n : ℝ) ^ s * Real.exp (M + (A + δ * Real.log n)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (add_le_add le_rfl (hA n hn)))
          (Real.rpow_nonneg hnR.le _)
      _ = _ := by rw [hExp, Real.rpow_add hnR]; ring
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ δ) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually (eventually_ge_atTop K), eventually_ge_atTop 1]
    with n hnK hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  calc
    (g n : ℝ) ≤ K * (n : ℝ) ^ (s + δ) := hbound n (by omega)
    _ ≤ (n : ℝ) ^ δ * (n : ℝ) ^ (s + δ) :=
      mul_le_mul_of_nonneg_right hnK (Real.rpow_nonneg hnR.le _)
    _ = (n : ℝ) ^ t := by rw [← Real.rpow_add hnR]; congr 1; dsimp [δ]; ring


/-- At s=1-1/k, the whole rough contribution is bounded by k*omega(n). -/
theorem g_le_endpoint_exp_primeFactors (k : ℕ) (hk : 1 ≤ k)
    (H : Summable ((smoothShiftedPredecessors k).indicator
      (fun d : ℕ => (d : ℝ)^(-(1-1/(k : ℝ))))))
    (n : ℕ) (hn : 0 < n) :
    (g n : ℝ) ≤ (n : ℝ)^(1-1/(k : ℝ)) * Real.exp
      ((∑' d : ℕ, (smoothShiftedPredecessors k).indicator
        (fun d : ℕ => (d : ℝ)^(-(1-1/(k : ℝ)))) d) +
          (k : ℝ)*n.primeFactors.card) := by
  have hb := reciprocal_exponent_bounds k hk
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have he : (k : ℝ)*(1-(1-1/(k : ℝ)))-1 = 0 := by field_simp; ring
  have h := g_le_of_summable_smooth_shifted_sharp k hk
    (1-1/(k : ℝ)) hb.1 hb.2 H n hn
  rw [he] at h
  simpa only [Real.rpow_zero, Finset.sum_const, nsmul_eq_mul, mul_one,
    sub_sub_cancel, one_div_one_div] using h

/-- An attained exponent above 1-1/k forces divergence of the endpoint series. -/
theorem not_summable_smooth_endpoint_of_infinite_g_gt (k : ℕ) (hk : 1 ≤ k)
    (γ : ℝ) (hγ : 1-1/(k : ℝ) < γ)
    (H : {n : ℕ | (g n : ℝ) > (n : ℝ)^γ}.Infinite) :
    ¬Summable ((smoothShiftedPredecessors k).indicator
      (fun d : ℕ => (d : ℝ)^(-(1-1/(k : ℝ))))) := by
  intro hsum
  have hb := reciprocal_exponent_bounds k hk
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have he : (k : ℝ)*(1-(1-1/(k : ℝ)))-1 = 0 := by field_simp; ring
  have hbound := eventually_g_le_rpow_of_summable_smooth_endpoint k hk
    (1-1/(k : ℝ)) γ hb.1 hb.2 hγ he.le hsum
  obtain ⟨N,hN⟩ := eventually_atTop.mp hbound
  obtain ⟨n,hn,hnN⟩ := H.exists_gt N
  exact (hN n hnN.le).not_gt hn

/-- A sharpened diagonal series characterization; this is an equivalence,
not an assertion that the series on its right diverge. -/
theorem erdos_821_iff_endpoint_smooth_series :
    (∀ ε > (0 : ℝ), {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite) ↔
      ∀ k : ℕ, 2 ≤ k → ¬Summable ((smoothShiftedPredecessors k).indicator
        (fun d : ℕ => (d : ℝ)^(-(1-1/(k : ℝ))))) := by
  constructor
  · intro H k hk
    exact not_summable_smooth_shifted_all_exponents_of_erdos_821 H k (by omega)
      _ (reciprocal_exponent_bounds k (by omega)).2
  · intro H
    apply erdos_821_iff_smooth_shifted_nonsummable.mpr
    intro k hk hsum
    apply H (2*k) (by omega)
    have hsum' : Summable ((smoothShiftedPredecessors k).indicator
        (fun d : ℕ => (d : ℝ)^(-(1-1/((2*k : ℕ) : ℝ))))) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hsum
    apply hsum'.of_nonneg_of_le
      (fun d => Set.indicator_nonneg (fun d _ => Real.rpow_nonneg (Nat.cast_nonneg d) _) d)
    intro d
    by_cases hd : d ∈ smoothShiftedPredecessors (2*k)
    · rw [Set.indicator_of_mem hd,
        Set.indicator_of_mem (smoothShiftedPredecessors_antitone (by omega : k ≤ 2*k) hd)]
    · rw [Set.indicator_of_notMem hd]
      exact Set.indicator_nonneg (fun d _ => Real.rpow_nonneg (Nat.cast_nonneg d) _) d

end Erdos821
