import Submission.MertensPrimeLog

/-!
# Cofinal Mangoldt lower bounds with every constant below one

A logarithmic harmonic mean cannot coexist with an eventual linear bound
of slope less than one. This gives cofinally many good cutoffs, not a
prime number theorem and not a lower bound at every cutoff.
-/
open Nat Finset Filter ArithmeticFunction
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve
set_option maxHeartbeats 3000000

lemma weighted_prefix_sum_le (f g w : ℕ → ℝ) (N : ℕ)
    (hw : ∀ n, 0 ≤ w n) (hwanti : Antitone w)
    (H : ∀ k ≤ N, (∑ i ∈ range k, f i) ≤ ∑ i ∈ range k, g i) :
    (∑ i ∈ range N, w i*f i) ≤ ∑ i ∈ range N, w i*g i := by
  have hf := sum_range_by_parts w f N
  have hg := sum_range_by_parts w g N
  simp only [smul_eq_mul] at hf hg
  rw [hf,hg]
  apply sub_le_sub
  · exact mul_le_mul_of_nonneg_left (H N le_rfl) (hw _)
  · apply sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonpos_left (H (i+1) (by have := mem_range.mp hi; omega))
    exact sub_nonpos.mpr (hwanti (Nat.le_succ i))

lemma reciprocal_sum_le_of_prefix_linear (f : ℕ → ℝ) (c C : ℝ) (hC : 0 ≤ C)
    (H : ∀ k : ℕ, (∑ i ∈ range k, f i) ≤ c*k+C) (N : ℕ) :
    (∑ i ∈ range N, f i/((i : ℝ)+1)) ≤ c*(harmonic N : ℝ)+C := by
  let g : ℕ → ℝ := fun i => c+if i=0 then C else 0
  have hg (k : ℕ) : (∑ i ∈ range k, g i) = c*k+if k=0 then 0 else C := by
    by_cases hk : k=0
    · simp [hk]
    · have h0 : 0 ∈ range k := mem_range.mpr (by omega)
      simp [g,sum_add_distrib,sum_ite_eq',h0,hk,mul_comm]
  have hpre (k : ℕ) (_hk : k ≤ N) :
      (∑ i ∈ range k, f i) ≤ ∑ i ∈ range k, g i := by
    rw [hg]
    by_cases hk : k=0
    · simp [hk]
    · simpa only [if_neg hk] using H k
  have hw := weighted_prefix_sum_le f g (fun i => 1/((i : ℝ)+1)) N
    (fun i => by positivity) (by
      intro i j hij
      exact one_div_le_one_div_of_le (by positivity)
        (by exact_mod_cast Nat.succ_le_succ hij)) hpre
  have hsum : (∑ i ∈ range N, (1/((i : ℝ)+1))*g i) ≤ c*(harmonic N : ℝ)+C := by
    simp only [g,mul_add,sum_add_distrib]
    have he : (∑ i ∈ range N, (1/((i : ℝ)+1))*c) = c*(harmonic N : ℝ) := by
      simp only [harmonic,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,one_div]
      rw [mul_sum]
      apply sum_congr rfl
      intro i hi
      push_cast
      ring
    rw [he]
    apply _root_.add_le_add le_rfl
    by_cases hN : N=0
    · simp [hN,hC]
    · have h0 : 0 ∈ range N := mem_range.mpr (by omega)
      simp [mul_ite,sum_ite_eq',h0]
  have hw' : (∑ i ∈ range N, f i/((i : ℝ)+1)) ≤
      ∑ i ∈ range N, (1/((i : ℝ)+1))*g i := by
    simpa only [one_div,div_eq_mul_inv,one_mul,mul_comm] using hw
  exact hw'.trans hsum

lemma frequently_prefix_gt_linear_of_log_harmonic (f : ℕ → ℝ)
    (hf : ∀ n, 0 ≤ f n) (B : ℝ)
    (H : ∀ᶠ N : ℕ in atTop,
      Real.log (N : ℝ)-B ≤ ∑ i ∈ range N, f i/((i : ℝ)+1))
    (c : ℝ) (hc : c < 1) :
    ∃ᶠ N : ℕ in atTop, c*N < ∑ i ∈ range N, f i := by
  by_cases hc0 : c < 0
  · apply Eventually.frequently
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (mul_neg_of_neg_of_pos hc0 (by exact_mod_cast hN : (0 : ℝ)<N)).trans_le
      (sum_nonneg (fun i _ => hf i))
  have hc0 : 0 ≤ c := le_of_not_gt hc0
  by_contra hnot
  have he : ∀ᶠ N : ℕ in atTop, (∑ i ∈ range N, f i) ≤ c*N := by
    simpa only [not_lt] using (not_frequently.mp hnot)
  obtain ⟨K,hK⟩ := eventually_atTop.mp he
  let C : ℝ := ∑ i ∈ range K, f i
  have hC : 0 ≤ C := sum_nonneg (fun i _ => hf i)
  have hbound (N : ℕ) : (∑ i ∈ range N, f i) ≤ c*N+C := by
    by_cases hKN : K ≤ N
    · exact (hK N hKN).trans (le_add_of_nonneg_right hC)
    · have hs : (∑ i ∈ range N, f i) ≤ C :=
        sum_le_sum_of_subset_of_nonneg (range_mono (Nat.le_of_not_ge hKN)) (fun i _ _ => hf i)
      exact hs.trans (le_add_of_nonneg_left (mul_nonneg hc0 (Nat.cast_nonneg N)))
  have hlim : Tendsto (fun N : ℕ => (1-c)*Real.log (N : ℝ)) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (sub_pos.mpr hc)
  have hbad : ∀ᶠ N : ℕ in atTop, False := by
    filter_upwards [H,eventually_ge_atTop 1,hlim.eventually (eventually_gt_atTop (B+c+C))]
      with N hlow hN hlarge
    have hu := reciprocal_sum_le_of_prefix_linear f c C hC hbound N
    have hh := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N) hc0
    nlinarith only [hlow,hu,hh,hlarge]
  exact (Filter.Eventually.exists hbad).choose_spec

lemma mangoldt_shift_sum (N : ℕ) :
    (∑ i ∈ range N, vonMangoldt (i+1)) = mangoldtSum N := by
  unfold mangoldtSum
  simpa only [Nat.zero_add,Ico_zero_eq_range,Ico_add_one_right_eq_Icc] using
    (sum_Ico_add' (fun i : ℕ => vonMangoldt i) 0 N 1)

lemma mangoldt_shift_reciprocal_sum (N : ℕ) :
    (∑ i ∈ range N, vonMangoldt (i+1)/((i : ℝ)+1)) =
      ∑ n ∈ Icc 1 N, vonMangoldt n/(n : ℝ) := by
  have hh := (sum_Ico_add' (fun i : ℕ => vonMangoldt i/(i : ℝ)) 0 N 1)
  simpa only [Nat.zero_add,Nat.cast_add,Nat.cast_one,Ico_zero_eq_range,Ico_add_one_right_eq_Icc] using hh

lemma primeLogMass_le_mangoldt_harmonic (N : ℕ) :
    primeLogMass N ≤ ∑ d ∈ Icc 1 N, vonMangoldt d/(d : ℝ) := by
  have hsub : (N+1).primesBelow ⊆ Icc 1 N := by
    intro p hp
    obtain ⟨hpN,hpr⟩ := Nat.mem_primesBelow.mp hp
    exact mem_Icc.mpr ⟨hpr.pos,by omega⟩
  have he : primeLogMass N = ∑ p ∈ (N+1).primesBelow, vonMangoldt p/(p : ℝ) := by
    apply sum_congr rfl
    intro p hp
    rw [vonMangoldt_apply_prime (Nat.mem_primesBelow.mp hp).2]
  rw [he]
  exact sum_le_sum_of_subset_of_nonneg hsub
    (fun d _ _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _))

/-- The cutoffs with Mangoldt ratio above c are cofinal for every c<1. -/
theorem frequently_mangoldtSum_gt_linear (c : ℝ) (hc : c < 1) :
    ∃ᶠ N : ℕ in atTop, c*N < mangoldtSum N := by
  obtain ⟨B,hB,HB⟩ := exists_primeLogMass_log_bound
  have H := frequently_prefix_gt_linear_of_log_harmonic
    (fun i => vonMangoldt (i+1)) (fun i => vonMangoldt_nonneg) B (by
      filter_upwards [eventually_ge_atTop 1] with N hN
      rw [mangoldt_shift_reciprocal_sum]
      exact (by linarith only [(abs_le.mp (HB N hN)).1] :
        Real.log (N : ℝ)-B ≤ primeLogMass N).trans (primeLogMass_le_mangoldt_harmonic N)) c hc
  simpa only [mangoldt_shift_sum] using H

lemma prime_log_shift_sum (N : ℕ) :
    (∑ i ∈ range N, if (i+1).Prime then Real.log (i+1 : ℕ) else 0) =
      Chebyshev.theta (N : ℝ) := by
  rw [Sieve.theta_nat_eq_sum_primesBelow]
  have hshift := sum_Ico_add' (fun i : ℕ => if i.Prime then Real.log i else 0) 0 N 1
  rw [show (∑ i ∈ range N, if (i+1).Prime then Real.log (i+1 : ℕ) else 0) =
      ∑ i ∈ Icc 1 N, if i.Prime then Real.log i else 0 by
        simpa only [Nat.zero_add,Ico_zero_eq_range,Ico_add_one_right_eq_Icc] using hshift,
    ← sum_filter]
  congr 1
  ext p
  simp only [mem_filter,mem_Icc,Nat.mem_primesBelow]
  constructor
  · rintro ⟨⟨_,hpN⟩,hp⟩; exact ⟨by omega,hp⟩
  · rintro ⟨hpN,hp⟩; exact ⟨⟨hp.pos,by omega⟩,hp⟩

lemma prime_log_shift_reciprocal_sum (N : ℕ) :
    (∑ i ∈ range N, (if (i+1).Prime then Real.log (i+1 : ℕ) else 0)/((i : ℝ)+1)) =
      primeLogMass N := by
  have hshift := sum_Ico_add' (fun i : ℕ => (if i.Prime then Real.log i else 0)/(i : ℝ)) 0 N 1
  have hh : (∑ i ∈ range N, (if (i+1).Prime then Real.log (i+1 : ℕ) else 0)/((i : ℝ)+1)) =
      ∑ i ∈ Icc 1 N, (if i.Prime then Real.log i else 0)/(i : ℝ) := by
    simpa only [Nat.zero_add,Ico_zero_eq_range,Ico_add_one_right_eq_Icc,Nat.cast_add,Nat.cast_one] using hshift
  rw [hh]
  simp only [ite_div,zero_div,← sum_filter]
  unfold primeLogMass
  congr 1
  ext p
  simp only [mem_filter,mem_Icc,Nat.mem_primesBelow]
  constructor
  · rintro ⟨⟨_,hpN⟩,hp⟩; exact ⟨by omega,hp⟩
  · rintro ⟨hpN,hp⟩; exact ⟨⟨hp.pos,by omega⟩,hp⟩

/-- The same cofinal unit lower slope holds without proper prime powers. -/
theorem frequently_theta_gt_linear (c : ℝ) (hc : c < 1) :
    ∃ᶠ N : ℕ in atTop, c*N < Chebyshev.theta (N : ℝ) := by
  obtain ⟨B,hB,HB⟩ := exists_primeLogMass_log_bound
  have H := frequently_prefix_gt_linear_of_log_harmonic
    (fun i => if (i+1).Prime then Real.log (i+1 : ℕ) else 0)
    (fun i => by dsimp only; split_ifs; exact Real.log_natCast_nonneg _; exact le_rfl) B (by
      filter_upwards [eventually_ge_atTop 1] with N hN
      rw [prime_log_shift_reciprocal_sum]
      linarith only [(abs_le.mp (HB N hN)).1]) c hc
  simpa only [prime_log_shift_sum] using H

theorem frequently_prime_count_gt_unit (c : ℝ) (hc : c < 1) :
    ∃ᶠ N : ℕ in atTop, c*N < Real.log (N : ℝ)*((N+1).primesBelow.card : ℝ) := by
  apply (frequently_theta_gt_linear c hc).mono
  intro N hN
  apply hN.trans_le
  rw [Sieve.theta_nat_eq_sum_primesBelow]
  calc
    _ ≤ ∑ _p ∈ (N+1).primesBelow, Real.log (N : ℝ) := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hpN,hpr⟩ := Nat.mem_primesBelow.mp hp
      exact Real.log_le_log (by exact_mod_cast hpr.pos) (by exact_mod_cast (by omega : p ≤ N))
    _ = _ := by simp only [sum_const,nsmul_eq_mul,mul_comm]

end Erdos821
