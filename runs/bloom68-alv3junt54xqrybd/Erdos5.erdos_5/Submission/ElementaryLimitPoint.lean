import Submission.GapBridge

/-!
# An elementary finite limit point of normalized consecutive-prime gaps

Only the unconditional elementary prime-counting estimate and logarithmic
normalization from `Submission.PrimeNormalization` are used.  In particular,
this module does not import `Submission.Spec` or assume a prime-gap theorem.

The basic `24/log 2` bound comes from telescoping gaps over dyadic index
intervals.  Longer index intervals and a vanishing-error selection sharpen
this to `3/log 2`.  Both results prove existence of one bounded subsequential
limit, not the assertion that every nonnegative real is a subsequential limit.
-/

open Filter Set
open scoped Topology

namespace Erdos5ElementaryLimitPoint

open Erdos5CoveredGapBridge (normalizedGap)

lemma log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

/-- The exact index-normalized gap is nonnegative, including at indices zero and one. -/
theorem normalizedGap_nonneg (n : ℕ) : 0 ≤ normalizedGap n := by
  exact div_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg n)

/-- A convenient eventual elementary upper bound for the zero-indexed nth prime. -/
theorem eventually_nth_prime_le :
    ∀ᶠ n : ℕ in atTop,
      (Nat.nth Nat.Prime n : ℝ) ≤ (6 / Real.log 2) * (n : ℝ) * Real.log (n : ℝ) := by
  have hratio : ∀ᶠ n : ℕ in atTop,
      Real.log (Nat.nth Nat.Prime n : ℝ) / Real.log (n : ℝ) < (4 / 3 : ℝ) :=
    Erdos5PrimeNormalization.tendsto_log_nth_prime_div_log_index.eventually_lt_const
      (by norm_num)
  filter_upwards [hratio, eventually_ge_atTop (2 : ℕ)] with n hr hn
  have hnreal : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hlogp : Real.log (Nat.nth Nat.Prime n : ℝ) ≤ (4 / 3 : ℝ) * Real.log (n : ℝ) :=
    ((div_lt_iff₀ hlogn).mp hr).le
  have hcount : ((n + 1 : ℕ) : ℝ) ≤ (3 / 2 : ℝ) * (n : ℝ) := by
    push_cast
    linarith
  have hcheb := Erdos5PrimeNormalization.weak_chebyshev_lower (Nat.nth Nat.Prime n)
    (Nat.prime_nth_prime n).two_le
  rw [Erdos5PrimeNormalization.primeCounting_nth_prime] at hcheb
  have hbound :
      (Real.log 2 / 3) * (Nat.nth Nat.Prime n : ℝ) ≤
        2 * (n : ℝ) * Real.log (n : ℝ) := by
    calc
      (Real.log 2 / 3) * (Nat.nth Nat.Prime n : ℝ) ≤
          ((n + 1 : ℕ) : ℝ) * Real.log (Nat.nth Nat.Prime n : ℝ) := hcheb
      _ ≤ ((3 / 2 : ℝ) * (n : ℝ)) * ((4 / 3 : ℝ) * Real.log (n : ℝ)) :=
        mul_le_mul hcount hlogp (Real.log_natCast_nonneg _) (by positivity)
      _ = 2 * (n : ℝ) * Real.log (n : ℝ) := by ring
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  apply (le_div_iff₀ log_two_pos).mpr
  nlinarith [hbound]

/-- Telescoping the actual natural-valued consecutive-prime gaps, after casting to the reals. -/
theorem sum_primeGap_Ico (m n : ℕ) (hmn : m ≤ n) :
    (∑ k ∈ Finset.Ico m n, (primeGap k : ℝ)) =
      (Nat.nth Nat.Prime n : ℝ) - (Nat.nth Nat.Prime m : ℝ) := by
  calc
    (∑ k ∈ Finset.Ico m n, (primeGap k : ℝ)) =
        ∑ k ∈ Finset.Ico m n,
          ((Nat.nth Nat.Prime (k + 1) : ℝ) - (Nat.nth Nat.Prime k : ℝ)) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [primeGap, Nat.cast_sub
        ((Nat.nth_strictMono Nat.infinite_setOf_prime).monotone (by omega))]
    _ = _ := Finset.sum_Ico_sub (fun k => (Nat.nth Nat.Prime k : ℝ)) hmn

/-- An elementary prime-growth bound at `2*N` supplies a bounded gap in `[N,2*N)`. -/
theorem exists_small_gap_in_dyadic_block (N : ℕ) (hN : 2 ≤ N)
    (hp : (Nat.nth Nat.Prime (2 * N) : ℝ) ≤
      (6 / Real.log 2) * (2 * N : ℕ) * Real.log (2 * N : ℕ)) :
    ∃ k : ℕ, N ≤ k ∧ k < 2 * N ∧ normalizedGap k ≤ 24 / Real.log 2 := by
  have hNreal : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : 0 < (N : ℝ) := by linarith
  have hlog2N : Real.log (2 * N : ℕ) ≤ 2 * Real.log (N : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) hNpos.ne']
    have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hNreal
    linarith
  have hsum : (∑ k ∈ Finset.Ico N (2 * N), (primeGap k : ℝ)) ≤
      ∑ _k ∈ Finset.Ico N (2 * N), (24 / Real.log 2) * Real.log (N : ℝ) := by
    rw [sum_primeGap_Ico N (2 * N) (by omega), Finset.sum_const, Nat.card_Ico,
      show 2 * N - N = N by omega, nsmul_eq_mul]
    calc
      (Nat.nth Nat.Prime (2 * N) : ℝ) - (Nat.nth Nat.Prime N : ℝ) ≤
          (Nat.nth Nat.Prime (2 * N) : ℝ) := sub_le_self _ (by positivity)
      _ ≤ (6 / Real.log 2) * (2 * N : ℕ) * Real.log (2 * N : ℕ) := hp
      _ ≤ (6 / Real.log 2) * (2 * N : ℕ) * (2 * Real.log (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog2N (by positivity)
      _ = (N : ℝ) * ((24 / Real.log 2) * Real.log (N : ℝ)) := by
        push_cast
        ring
  obtain ⟨k, hk, hgap⟩ := Finset.exists_le_of_sum_le
    (show (Finset.Ico N (2 * N)).Nonempty from ⟨N, by simp only [Finset.mem_Ico]; omega⟩)
    hsum
  have hki := Finset.mem_Ico.mp hk
  refine ⟨k, hki.1, hki.2, ?_⟩
  have hkreal : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast hki.1
  have hlogk : 0 < Real.log (k : ℝ) := Real.log_pos (by linarith)
  apply (div_le_iff₀ hlogk).mpr
  exact hgap.trans (mul_le_mul_of_nonneg_left (Real.log_le_log hNpos hkreal)
    (div_nonneg (by norm_num) log_two_pos.le))

/-- Normalized consecutive-prime gaps are at most `24/log 2` arbitrarily far out. -/
theorem frequently_normalizedGap_le :
    ∃ᶠ n : ℕ in atTop, normalizedGap n ≤ 24 / Real.log 2 := by
  obtain ⟨M, hM⟩ := eventually_atTop.mp eventually_nth_prime_le
  apply frequently_atTop.mpr
  intro A
  let N := max M (max A 2)
  have hMN : M ≤ N := le_max_left _ _
  have hAN : A ≤ N := (le_max_left A 2).trans (le_max_right M (max A 2))
  have hN : 2 ≤ N := (le_max_right A 2).trans (le_max_right M (max A 2))
  obtain ⟨k, hk, _, hbound⟩ := exists_small_gap_in_dyadic_block N hN
    (hM (2 * N) (hMN.trans (by omega)))
  exact ⟨k, hAN.trans hk, hbound⟩

/-- The normalized gaps enter a fixed compact interval infinitely often. -/
theorem frequently_normalizedGap_mem_Icc :
    ∃ᶠ n : ℕ in atTop, normalizedGap n ∈ Icc (0 : ℝ) (24 / Real.log 2) :=
  frequently_normalizedGap_le.mono fun n hn => ⟨normalizedGap_nonneg n, hn⟩

/-- Unconditionally, the exact normalized consecutive-prime gap has a finite
nonnegative subsequential limit bounded by `24/log 2`.  This is an existence
statement for one limit point, not the full assertion for every `C ≥ 0`. -/
theorem exists_bounded_subsequential_limit :
    ∃ C : ℝ, 0 ≤ C ∧ C ≤ 24 / Real.log 2 ∧
      ∃ n : ℕ → ℕ, StrictMono n ∧
        Tendsto (fun i => Erdos5CoveredGapBridge.normalizedGap (n i)) atTop (𝓝 C) := by
  obtain ⟨C, hC, n, hn, hlim⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) (24 / Real.log 2))).tendsto_subseq'
      frequently_normalizedGap_mem_Icc
  exact ⟨C, hC.1, hC.2, n, hn, hlim⟩

/-- The elementary prime bound can be made arbitrarily close to `3/log 2`. -/
theorem eventually_nth_prime_le_of_lt {B : ℝ} (hB : 3 / Real.log 2 < B) :
    ∀ᶠ n : ℕ in atTop,
      (Nat.nth Nat.Prime n : ℝ) ≤ B * (n : ℝ) * Real.log (n : ℝ) := by
  have hindex : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / (n : ℝ))
      atTop (𝓝 (1 : ℝ)) := by
    have heq : (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / (n : ℝ)) =ᶠ[atTop]
        (fun n : ℕ => 1 + 1 / (n : ℝ)) := by
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      have hnzero : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      rw [Nat.cast_add, Nat.cast_one, add_div, div_self hnzero]
    exact (tendsto_congr' heq).mpr
      (by simpa only [add_zero] using
        tendsto_const_nhds.add (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)))
  let u : ℕ → ℝ := fun n => (3 / Real.log 2) *
    (((n + 1 : ℕ) : ℝ) / (n : ℝ)) *
      (Real.log (Nat.nth Nat.Prime n : ℝ) / Real.log (n : ℝ))
  have hu : Tendsto u atTop (𝓝 (3 / Real.log 2)) := by
    simpa only [u, mul_one] using
      (tendsto_const_nhds.mul hindex).mul
        Erdos5PrimeNormalization.tendsto_log_nth_prime_div_log_index
  filter_upwards [hu.eventually_lt_const hB, eventually_ge_atTop (2 : ℕ)] with n hun hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hlogn : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hcheb := Erdos5PrimeNormalization.weak_chebyshev_lower (Nat.nth Nat.Prime n)
    (Nat.prime_nth_prime n).two_le
  rw [Erdos5PrimeNormalization.primeCounting_nth_prime] at hcheb
  calc
    (Nat.nth Nat.Prime n : ℝ) ≤
        (3 / Real.log 2) * ((n + 1 : ℕ) : ℝ) * Real.log (Nat.nth Nat.Prime n : ℝ) := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
      apply (le_div_iff₀ log_two_pos).mpr
      nlinarith [hcheb]
    _ = u n * (n : ℝ) * Real.log (n : ℝ) := by
      dsimp [u]
      field_simp [hnpos.ne', hlogn.ne']
    _ ≤ B * (n : ℝ) * Real.log (n : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hun.le hnpos.le) hlogn.le

/-- Multiplying the index by a fixed positive integer does not change its logarithmic scale. -/
theorem tendsto_log_mul_index_div_log_index (R : ℕ) (hR : 0 < R) :
    Tendsto (fun n : ℕ => Real.log (R * n : ℕ) / Real.log (n : ℝ))
      atTop (𝓝 (1 : ℝ)) := by
  have hsmall : Tendsto (fun n : ℕ => Real.log (R : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have heq : (fun n : ℕ => Real.log (R * n : ℕ) / Real.log (n : ℝ)) =ᶠ[atTop]
      (fun n : ℕ => Real.log (R : ℝ) / Real.log (n : ℝ) + 1) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hRpos : 0 < (R : ℝ) := by exact_mod_cast hR
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hlogn : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    rw [Nat.cast_mul, Real.log_mul hRpos.ne' hnpos.ne', add_div, div_self hlogn.ne']
  exact (tendsto_congr' heq).mpr (by simpa only [zero_add] using hsmall.add tendsto_const_nhds)

/-- Every threshold strictly above `3/log 2` is met by normalized gaps arbitrarily far out. -/
theorem frequently_normalizedGap_le_of_lt {K : ℝ} (hK : 3 / Real.log 2 < K) :
    ∃ᶠ n : ℕ in atTop, normalizedGap n ≤ K := by
  have ha : 0 < 3 / Real.log 2 := div_pos (by norm_num) log_two_pos
  have hKpos : 0 < K := ha.trans hK
  let B : ℝ := (3 / Real.log 2 + K) / 2
  have hB : 3 / Real.log 2 < B := by dsimp [B]; linarith
  have hBK : B < K := by dsimp [B]; linarith
  obtain ⟨R, hRlarge⟩ := exists_nat_gt (max (2 : ℝ) (K / (K - B)))
  have hRreal : (2 : ℝ) < (R : ℝ) := (le_max_left _ _).trans_lt hRlarge
  have hR : 2 ≤ R := by exact_mod_cast hRreal.le
  have hchoose : B * (R : ℝ) < K * ((R : ℝ) - 1) := by
    have hquot : K / (K - B) < (R : ℝ) := (le_max_right _ _).trans_lt hRlarge
    have hmul := (div_lt_iff₀ (sub_pos.mpr hBK)).mp hquot
    nlinarith
  by_contra hf
  have hlarge : ∀ᶠ n : ℕ in atTop, K < normalizedGap n := by
    simpa only [not_frequently, not_le] using hf
  obtain ⟨M, hM⟩ := eventually_atTop.mp hlarge
  obtain ⟨P, hP⟩ := eventually_atTop.mp (eventually_nth_prime_le_of_lt hB)
  have hblock : ∀ᶠ N : ℕ in atTop,
      K * ((R : ℝ) - 1) ≤
        (B * (R : ℝ)) * (Real.log (R * N : ℕ) / Real.log (N : ℝ)) := by
    filter_upwards [eventually_ge_atTop (max M (max P 2))] with N hbase
    have hMN : M ≤ N := (le_max_left M (max P 2)).trans hbase
    have hPN : P ≤ N := ((le_max_left P 2).trans (le_max_right M (max P 2))).trans hbase
    have hN : 2 ≤ N := ((le_max_right P 2).trans (le_max_right M (max P 2))).trans hbase
    have hNRN : N ≤ R * N := by
      calc
        N = 1 * N := by simp
        _ ≤ R * N := Nat.mul_le_mul_right N (by omega)
    have hNRNlt : N < R * N :=
      (show N < 2 * N by omega).trans_le (Nat.mul_le_mul_right N hR)
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hlogN : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hsum : (∑ _k ∈ Finset.Ico N (R * N), K * Real.log (N : ℝ)) <
        ∑ k ∈ Finset.Ico N (R * N), (primeGap k : ℝ) := by
      apply Finset.sum_lt_sum_of_nonempty ⟨N, Finset.mem_Ico.mpr ⟨le_rfl, hNRNlt⟩⟩
      intro k hk
      have hNk := (Finset.mem_Ico.mp hk).1
      have hklog : 0 < Real.log (k : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < k by omega))
      have hgap : K * Real.log (k : ℝ) < (primeGap k : ℝ) :=
        (lt_div_iff₀ hklog).mp (hM k (hMN.trans hNk))
      exact (mul_le_mul_of_nonneg_left
        (Real.log_le_log hNpos (by exact_mod_cast hNk)) hKpos.le).trans_lt hgap
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul,
      sum_primeGap_Ico N (R * N) hNRN, Nat.cast_sub hNRN, Nat.cast_mul] at hsum
    have hp := hP (R * N) (hPN.trans hNRN)
    rw [Nat.cast_mul] at hp
    have hsum_bound : ((R : ℝ) - 1) * (N : ℝ) * (K * Real.log (N : ℝ)) ≤
        B * (R : ℝ) * (N : ℝ) * Real.log (R * N : ℕ) := by
      calc
        ((R : ℝ) - 1) * (N : ℝ) * (K * Real.log (N : ℝ)) =
            ((R : ℝ) * (N : ℝ) - (N : ℝ)) * (K * Real.log (N : ℝ)) := by ring
        _ ≤ (Nat.nth Nat.Prime (R * N) : ℝ) - (Nat.nth Nat.Prime N : ℝ) := hsum.le
        _ ≤ (Nat.nth Nat.Prime (R * N) : ℝ) := sub_le_self _ (by positivity)
        _ ≤ B * (R : ℝ) * (N : ℝ) * Real.log (R * N : ℕ) := by
          simpa only [mul_assoc, Nat.cast_mul] using hp
    apply (mul_le_mul_iff_of_pos_right hlogN).mp
    rw [mul_assoc (B * (R : ℝ)), div_mul_cancel₀ _ hlogN.ne']
    apply (mul_le_mul_iff_of_pos_right hNpos).mp
    nlinarith only [hsum_bound]
  have hlim := (tendsto_log_mul_index_div_log_index R (by omega)).const_mul (B * (R : ℝ))
  have hle : K * ((R : ℝ) - 1) ≤ B * (R : ℝ) :=
    ge_of_tendsto (by simpa only [mul_one] using hlim) hblock
  exact (not_le_of_gt hchoose) hle

/-- The sharper unconditional existence result: some finite nonnegative
subsequential limit of the exact normalized gaps is at most `3/log 2`. -/
theorem exists_sharp_bounded_subsequential_limit :
    ∃ C : ℝ, 0 ≤ C ∧ C ≤ 3 / Real.log 2 ∧
      ∃ n : ℕ → ℕ, StrictMono n ∧
        Tendsto (fun i => Erdos5CoveredGapBridge.normalizedGap (n i)) atTop (𝓝 C) := by
  obtain ⟨φ, hφ, hbound⟩ := extraction_forall_of_frequently
    (P := fun i k : ℕ => normalizedGap k ≤ 3 / Real.log 2 + 1 / ((i : ℝ) + 1))
    (by
      intro i
      apply frequently_normalizedGap_le_of_lt
      have hi : 0 < 1 / ((i : ℝ) + 1) := by positivity
      linarith)
  have hmem : ∀ i : ℕ, normalizedGap (φ i) ∈ Icc (0 : ℝ) (3 / Real.log 2 + 1) := by
    intro i
    refine ⟨normalizedGap_nonneg _, (hbound i).trans ?_⟩
    apply add_le_add_right
    apply (div_le_one (by positivity : 0 < (i : ℝ) + 1)).mpr
    have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    linarith
  obtain ⟨C, hC, ψ, hψ, hlim⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) (3 / Real.log 2 + 1))).tendsto_subseq hmem
  have hupperlim : Tendsto (fun i : ℕ => 3 / Real.log 2 + 1 / ((ψ i : ℝ) + 1))
      atTop (𝓝 (3 / Real.log 2)) := by
    simpa only [Function.comp_def, add_zero] using
      (tendsto_const_nhds.add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).comp hψ.tendsto_atTop
  have hCle : C ≤ 3 / Real.log 2 :=
    le_of_tendsto_of_tendsto hlim hupperlim (Eventually.of_forall fun i => hbound (ψ i))
  exact ⟨C, hC.1, hCle, φ ∘ ψ, hφ.comp hψ, hlim⟩

end Erdos5ElementaryLimitPoint

#print axioms Erdos5ElementaryLimitPoint.log_two_pos
#print axioms Erdos5ElementaryLimitPoint.normalizedGap_nonneg
#print axioms Erdos5ElementaryLimitPoint.eventually_nth_prime_le
#print axioms Erdos5ElementaryLimitPoint.sum_primeGap_Ico
#print axioms Erdos5ElementaryLimitPoint.exists_small_gap_in_dyadic_block
#print axioms Erdos5ElementaryLimitPoint.frequently_normalizedGap_le
#print axioms Erdos5ElementaryLimitPoint.frequently_normalizedGap_mem_Icc
#print axioms Erdos5ElementaryLimitPoint.exists_bounded_subsequential_limit
#print axioms Erdos5ElementaryLimitPoint.eventually_nth_prime_le_of_lt
#print axioms Erdos5ElementaryLimitPoint.tendsto_log_mul_index_div_log_index
#print axioms Erdos5ElementaryLimitPoint.frequently_normalizedGap_le_of_lt
#print axioms Erdos5ElementaryLimitPoint.exists_sharp_bounded_subsequential_limit
