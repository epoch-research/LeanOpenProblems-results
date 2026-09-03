import Submission.HigherDivisorSubpower

/-!
# An unconditional fixed-modulus lower bound for shifted divisor Dirichlet moments

The normalized Mangoldt-weighted moment has unbounded residue as s tends to
1 from above. This does not give the required quantitative rate or sharp
higher-order shifted-prime moments, and does not settle Erdős 821.
-/

open Nat Filter ArithmeticFunction
open scoped Classical BigOperators ArithmeticFunction.zeta Topology

namespace Erdos821.HigherDivisors

set_option maxHeartbeats 2000000

noncomputable def shiftedMangoldtDirichlet (k : ℕ) (s : ℝ) : ℝ :=
  ∑' n : ℕ, vonMangoldt n * (tau k (n-1) : ℝ)/(n : ℝ)^s

lemma shiftedMangoldtDirichlet_summable (k : ℕ) (s : ℝ) (hs : 1 < s) :
    Summable (fun n : ℕ => vonMangoldt n * (tau (k+1) (n-1) : ℝ)/(n : ℝ)^s) := by
  let a : ℝ := (s-1)/4
  have ha : 0 < a := by dsimp [a]; linarith
  obtain ⟨C,hC,ht⟩ := tau_succ_le_const_mul_rpow k a ha
  have he : 2*a-s < -1 := by dsimp [a]; linarith
  have H := (Real.summable_nat_rpow.mpr he).mul_left (C/a)
  apply H.of_nonneg_of_le (fun n => by positivity [vonMangoldt_nonneg (n := n)])
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [ArithmeticFunction.map_zero, zero_mul, zero_div]
    positivity
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have htn : (tau (k+1) (n-1) : ℝ) ≤ C*(n : ℝ)^a :=
    (ht (n-1)).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.sub_le n 1) ha.le)
      (by linarith : 0 ≤ C))
  calc
    _ ≤ ((n : ℝ)^a/a)*(C*(n : ℝ)^a)/(n : ℝ)^s := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul (vonMangoldt_le_log.trans (Real.log_le_rpow_div hnR.le ha)) htn
        (by positivity) (by positivity)
    _ = _ := by
      rw [show 2*a-s = a+a-s by ring, Real.rpow_sub hnR, Real.rpow_add hnR]
      ring

lemma truncated_residue_divisor_weight_le (k Q n : ℕ) :
    (∑ d ∈ Finset.Icc 1 Q, (tau k d : ℝ) * vonMangoldt.residueClass (1 : ZMod d) n) ≤
      vonMangoldt n * (tau (k+1) (n-1) : ℝ) := by
  by_cases hn0 : n = 0
  · subst n
    simp only [vonMangoldt.residueClass_apply_zero, mul_zero, Finset.sum_const_zero, ArithmeticFunction.map_zero, zero_mul, le_refl]
  by_cases hn1 : n = 1
  · subst n
    simp [vonMangoldt.residueClass, vonMangoldt_apply_one]
  have hn : 1 ≤ n := by omega
  have hpred : n-1 ≠ 0 := by omega
  have hsub : (Finset.Icc 1 Q).filter (fun d => d ∣ n-1) ⊆ (n-1).divisors := by
    intro d hd
    exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hd).2, hpred⟩
  calc
    _ = vonMangoldt n * ∑ d ∈ (Finset.Icc 1 Q).filter (fun d => d ∣ n-1), (tau k d : ℝ) := by
      rw [Finset.mul_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d hd
      simp only [vonMangoldt.residueClass, Set.indicator_apply, Set.mem_setOf_eq,
        AnalyticSieve.residue_one_iff_dvd_pred hn]
      split_ifs <;> ring
    _ ≤ vonMangoldt n * ∑ d ∈ (n-1).divisors, (tau k d : ℝ) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => Nat.cast_nonneg _))
        vonMangoldt_nonneg
    _ = _ := by rw [tau_succ, Nat.cast_sum]

lemma residueClass_real_summable (d : ℕ) (s : ℝ) (hs : 1 < s) :
    Summable (fun n : ℕ => vonMangoldt.residueClass (1 : ZMod d) n/(n : ℝ)^s) := by
  apply LSeries.summable_real_of_abscissaOfAbsConv_lt
  exact (vonMangoldt.abscissaOfAbsConv_residueClass_le_one (1 : ZMod d)).trans_lt
    (by exact_mod_cast hs)

/-- For each fixed finite modulus cutoff, the harmonic divisor mass is a
lower bound for the residue, up to a bounded error depending on the cutoff.
No uniform estimate in Q is claimed. -/
theorem shiftedMangoldtDirichlet_fixed_cutoff_lower (k Q : ℕ) :
    ∃ C : ℝ, ∀ s ∈ Set.Ioc (1 : ℝ) 2,
      harmonicMoment k Q/(s-1)-C ≤ shiftedMangoldtDirichlet (k+1) s := by
  have hconst (d : ℕ) (hd : d ∈ Finset.Icc 1 Q) : ∃ C : ℝ, ∀ s ∈ Set.Ioc (1 : ℝ) 2,
      (d.totient : ℝ)⁻¹/(s-1)-C ≤
        ∑' n : ℕ, vonMangoldt.residueClass (1 : ZMod d) n/(n : ℝ)^s := by
    letI : NeZero d := ⟨by have := (Finset.mem_Icc.mp hd).1; omega⟩
    obtain ⟨C,hC⟩ := vonMangoldt.LSeries_residueClass_lower_bound (isUnit_one : IsUnit (1 : ZMod d))
    exact ⟨C,fun s hs => hC hs⟩
  choose C hC using hconst
  refine ⟨∑ d ∈ (Finset.Icc 1 Q).attach, (tau k d : ℝ)*C d d.property, ?_⟩
  intro s hs
  let F : ℕ → ℕ → ℝ := fun d n => (tau k d : ℝ) *
    (vonMangoldt.residueClass (1 : ZMod d) n/(n : ℝ)^s)
  have hF (d : ℕ) (_hd : d ∈ Finset.Icc 1 Q) : Summable (F d) :=
    (residueClass_real_summable d s hs.1).mul_left (tau k d : ℝ)
  have hsum : (∑ d ∈ Finset.Icc 1 Q, ∑' n : ℕ, F d n) ≤ shiftedMangoldtDirichlet (k+1) s := by
    rw [← Summable.tsum_finsetSum hF]
    apply Summable.tsum_le_tsum
    · intro n
      dsimp [F]
      simp_rw [← mul_div_assoc]
      rw [← Finset.sum_div]
      exact div_le_div_of_nonneg_right (truncated_residue_divisor_weight_le k Q n) (by positivity)
    · exact (hasSum_sum (fun d hd => (hF d hd).hasSum)).summable
    · exact shiftedMangoldtDirichlet_summable k s hs.1
  apply le_trans _ hsum
  rw [← Finset.sum_attach (Finset.Icc 1 Q) (fun d => ∑' n : ℕ, F d n)]
  have hm : harmonicMoment k Q/(s-1) ≤
      ∑ d ∈ (Finset.Icc 1 Q).attach, (tau k d : ℝ)*(d.val.totient : ℝ)⁻¹/(s-1) := by
    unfold harmonicMoment
    rw [Finset.sum_div, ← Finset.sum_attach (Finset.Icc 1 Q) (fun d => (tau k d : ℝ)/(d : ℝ)/(s-1))]
    apply Finset.sum_le_sum
    intro d hd
    apply div_le_div_of_nonneg_right _ (by linarith [hs.1])
    have hd0 : 0 < d.val := (Finset.mem_Icc.mp d.property).1
    have hφ : (0 : ℝ) < d.val.totient := by exact_mod_cast Nat.totient_pos.mpr hd0
    simpa only [div_eq_mul_inv] using div_le_div_of_nonneg_left (Nat.cast_nonneg (tau k d)) hφ
      (by exact_mod_cast Nat.totient_le d.val)
  apply (sub_le_sub_right hm _).trans
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro d hd
  dsimp [F]
  rw [tsum_mul_left]
  have h := mul_le_mul_of_nonneg_left (hC d d.property s hs) (Nat.cast_nonneg (tau k d))
  simpa only [mul_sub, mul_div_assoc] using h

lemma harmonicMoment_one_le_succ (k Q : ℕ) : harmonicMoment 1 Q ≤ harmonicMoment (k+1) Q := by
  apply Finset.sum_le_sum
  intro n hn
  have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
  have hτ : tau 1 n = 1 := by simp [tau, zeta_apply_ne hn0]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  rw [hτ]
  exact_mod_cast tau_succ_pos k n hn0

lemma exists_harmonicMoment_gt (k : ℕ) (A : ℝ) : ∃ Q : ℕ, 1 ≤ Q ∧ A < harmonicMoment (k+1) Q := by
  obtain ⟨Q,hQ⟩ := exists_nat_gt (Real.exp A)
  have hQ0 : (0 : ℝ) < Q := (Real.exp_pos A).trans hQ
  have hQ1 : 1 ≤ Q := by exact_mod_cast (show 0 < Q by exact_mod_cast hQ0)
  have hlog : A < Real.log (Q+1 : ℝ) :=
    (Real.lt_log_iff_exp_lt (by positivity)).mpr (by linarith)
  refine ⟨Q,hQ1,hlog.trans_le ?_⟩
  have h := harmonicMoment_factorial_lower 1 Q hQ1
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one] at h
  exact h.trans (harmonicMoment_one_le_succ k Q)

/-- Every fixed order at least two has unbounded normalized residue. This
contains no quantitative rate as s tends to one. -/
theorem tendsto_shiftedMangoldtDirichlet_residue (k : ℕ) :
    Tendsto (fun s : ℝ => (s-1)*shiftedMangoldtDirichlet (k+2) s) (𝓝[>] 1) atTop := by
  apply tendsto_atTop.mpr
  intro A
  obtain ⟨Q,hQ,hlarge⟩ := exists_harmonicMoment_gt k (A+1)
  obtain ⟨C,hC⟩ := shiftedMangoldtDirichlet_fixed_cutoff_lower (k+1) Q
  have hc : ContinuousAt (fun s : ℝ => (s-1)*C) 1 := by fun_prop
  have ht : Tendsto (fun s : ℝ => (s-1)*C) (𝓝[>] 1) (𝓝 0) := by
    simpa only [sub_self, zero_mul] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have htwo : ∀ᶠ s : ℝ in 𝓝[>] 1, s < 2 :=
    (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2)).filter_mono nhdsWithin_le_nhds
  filter_upwards [eventually_mem_nhdsWithin, htwo, ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1)]
    with s hs hs2 hCs
  have hs1 : 1 < s := hs
  have hb := hC s ⟨hs1,hs2.le⟩
  have hb' := mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr hs1.le)
  have he : (s-1)*(harmonicMoment (k+1) Q/(s-1)-C) = harmonicMoment (k+1) Q-(s-1)*C := by
    field_simp [sub_ne_zero.mpr hs1.ne']
  rw [he] at hb'
  linarith

end Erdos821.HigherDivisors
