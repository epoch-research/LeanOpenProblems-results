import Submission.TauberianProfileExplore
import Submission.CumulativeExplore

/-! Sparse deletions can destroy pointwise representation lower bounds while
preserving the sharp counting profile. This does not settle Erdős 66. -/
namespace Erdos66DyadicDeletion
open Filter AdditiveCombinatorics Erdos66Counting Erdos66Explore
open scoped Topology
set_option maxHeartbeats 1000000

noncomputable def removed (A : Set ℕ) (k : ℕ) : Finset ℕ := by
  classical
  exact (((Finset.antidiagonal (2 ^ k)).filter
    (fun p : ℕ × ℕ ↦ p.1 ∈ A ∧ p.2 ∈ A ∧ p.2 ≤ p.1)).image Prod.fst)

lemma mem_removed {A : Set ℕ} {k a : ℕ} :
    a ∈ removed A k ↔ ∃ b ∈ A, a ∈ A ∧ a + b = 2 ^ k ∧ b ≤ a := by
  classical
  simp only [removed, Finset.mem_image, Finset.mem_filter, Finset.mem_antidiagonal]
  constructor
  · rintro ⟨⟨x, b⟩, ⟨hs, hx, hb, hba⟩, rfl⟩
    exact ⟨b, hb, hx, hs, hba⟩
  · rintro ⟨b, hb, ha, hs, hba⟩
    exact ⟨(a, b), ⟨hs, ha, hb, hba⟩, rfl⟩

lemma removed_card_le (A : Set ℕ) (k : ℕ) :
    (removed A k).card ≤ sumRep A (2 ^ k) := by
  classical
  apply Finset.card_image_le.trans
  rw [sumRep_def]
  apply Finset.card_le_card
  intro p hp
  obtain ⟨hp, ha, hb, hba⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨hp, ha, hb⟩

def pruned (A : Set ℕ) : Set ℕ := {a | a ∈ A ∧ ∀ k, a ∉ removed A k}

lemma pruned_subset (A : Set ℕ) : pruned A ⊆ A := fun _ ha ↦ ha.1

lemma pruned_hole (A : Set ℕ) (k : ℕ) : sumRep (pruned A) (2 ^ k) = 0 := by
  classical
  rw [sumRep_def, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p hp hmem
  have hs := Finset.mem_antidiagonal.mp hp
  rcases le_total p.2 p.1 with hh | hh
  · exact hmem.1.2 k (mem_removed.mpr ⟨p.2, hmem.2.1, hmem.1.1, hs, hh⟩)
  · exact hmem.2.2 k (mem_removed.mpr ⟨p.1, hmem.1.1, hmem.2.1, by omega, hh⟩)

lemma cutoff_pruned_subset (A : Set ℕ) (N : ℕ) :
    cutoff (pruned A) N ⊆ cutoff A N := by
  intro a ha
  obtain ⟨haN, ha⟩ := mem_cutoff.mp ha
  exact mem_cutoff.mpr ⟨haN, ha.1⟩

lemma discrepancy_bound (A : Set ℕ) (N : ℕ) :
    count A N - count (pruned A) N ≤
      ∑ k ∈ Finset.range (Nat.log 2 (2 * N) + 1), sumRep A (2 ^ k) := by
  classical
  let I := Finset.range (Nat.log 2 (2 * N) + 1)
  have hsub : cutoff A N \ cutoff (pruned A) N ⊆ I.biUnion (removed A) := by
    intro a ha
    obtain ⟨haA, haB⟩ := Finset.mem_sdiff.mp ha
    obtain ⟨haN, ha⟩ := mem_cutoff.mp haA
    have hn : ¬ ∀ k, a ∉ removed A k := by
      intro h
      exact haB (mem_cutoff.mpr ⟨haN, ha, h⟩)
    push_neg at hn
    obtain ⟨k, hk⟩ := hn
    obtain ⟨b, hb, ha, hs, hba⟩ := mem_removed.mp hk
    have hkN : 2 ^ k ≤ 2 * N := by omega
    have hki : k ∈ I := by
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_log_of_pow_le (by norm_num) hkN))
    exact Finset.mem_biUnion.mpr ⟨k, hki, hk⟩
  calc
    count A N - count (pruned A) N = (cutoff A N \ cutoff (pruned A) N).card := by
      rw [Finset.card_sdiff_of_subset (cutoff_pruned_subset A N)]
      rfl
    _ ≤ (I.biUnion (removed A)).card := Finset.card_le_card hsub
    _ ≤ ∑ k ∈ I, (removed A k).card := Finset.card_biUnion_le
    _ ≤ _ := Finset.sum_le_sum (fun k _ ↦ removed_card_le A k)

lemma log_discrepancy_bound {A : Set ℕ} {K C : ℝ} (hC : 0 ≤ C)
    (h : ∀ n : ℕ, (sumRep A n : ℝ) ≤ K + C * Real.log ((n : ℝ) + 2))
    (N : ℕ) (hN : 0 < N) :
    ((count A N - count (pruned A) N : ℕ) : ℝ) ≤
      ((Nat.log 2 (2 * N) : ℝ) + 1) * (K + C * Real.log (2 * (N : ℝ) + 2)) := by
  have hh : ((count A N - count (pruned A) N : ℕ) : ℝ) ≤
      ∑ k ∈ Finset.range (Nat.log 2 (2 * N) + 1), (sumRep A (2 ^ k) : ℝ) := by
    exact_mod_cast discrepancy_bound A N
  apply hh.trans
  calc
    _ ≤ ∑ _k ∈ Finset.range (Nat.log 2 (2 * N) + 1),
        (K + C * Real.log (2 * (N : ℝ) + 2)) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' : k ≤ Nat.log 2 (2 * N) := by simpa using hk
      have hn : 2 * N ≠ 0 := by omega
      have hpow := Nat.pow_le_of_le_log hn hk'
      apply (h (2 ^ k)).trans
      apply add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hC)
      apply Real.log_le_log (by positivity)
      exact_mod_cast (show 2 ^ k + 2 ≤ 2 * N + 2 by omega)
    _ = _ := by simp; ring

lemma quadratic_log_bound {A : Set ℕ} {K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (h : ∀ n : ℕ, (sumRep A n : ℝ) ≤ K + C * Real.log ((n : ℝ) + 2)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ, 2 ≤ N →
      ((count A N - count (pruned A) N : ℕ) : ℝ) ≤ D * (Real.log N) ^ 2 := by
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let D : ℝ := (3 / Real.log 2) * (K / Real.log 2 + 3 * C)
  refine ⟨D, by dsimp [D]; positivity, fun N hN ↦ ?_⟩
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlN : Real.log 2 ≤ Real.log (N : ℝ) := Real.log_le_log (by norm_num) hN2
  have hlNp : 0 < Real.log (N : ℝ) := hl2.trans_le hlN
  have hlogmul : Real.log (2 * (N : ℝ)) = Real.log 2 + Real.log N := by
    rw [Real.log_mul (by norm_num) hNp.ne']
  have hpow := Nat.pow_log_le_self 2 (show 2 * N ≠ 0 by omega)
  have hpow' : (2 : ℝ) ^ Nat.log 2 (2 * N) ≤ 2 * (N : ℝ) := by exact_mod_cast hpow
  have hlogpow := Real.log_le_log (show (0 : ℝ) < 2 ^ Nat.log 2 (2 * N) by positivity) hpow'
  rw [Real.log_pow, hlogmul] at hlogpow
  have hindex : ((Nat.log 2 (2 * N) : ℝ) + 1) ≤ (3 / Real.log 2) * Real.log N := by
    have hh : ((Nat.log 2 (2 * N) : ℝ) + 1) * Real.log 2 ≤ 3 * Real.log N := by linarith
    convert (le_div_iff₀ hl2).mpr hh using 1; ring
  have harg : 2 * (N : ℝ) + 2 ≤ 4 * N := by linarith
  have hlogarg := Real.log_le_log (show 0 < 2 * (N : ℝ) + 2 by positivity) harg
  have hlogfour : Real.log (4 * (N : ℝ)) = 2 * Real.log 2 + Real.log N := by
    rw [Real.log_mul (by norm_num) hNp.ne']
    have h4 : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [h4, Real.log_pow]
    norm_num
  rw [hlogfour] at hlogarg
  have hKbound : K ≤ K / Real.log 2 * Real.log N := by
    have hh := mul_le_mul_of_nonneg_left hlN (div_nonneg hK hl2.le)
    rwa [div_mul_cancel₀ K hl2.ne'] at hh
  have hterm : K + C * Real.log (2 * (N : ℝ) + 2) ≤
      (K / Real.log 2 + 3 * C) * Real.log N := by
    have hh := mul_le_mul_of_nonneg_left (show Real.log (2 * (N : ℝ) + 2) ≤ 3 * Real.log N by linarith) hC
    nlinarith
  have htermpos : 0 ≤ K + C * Real.log (2 * (N : ℝ) + 2) := by
    exact add_nonneg hK (mul_nonneg hC (Real.log_nonneg (by linarith)))
  calc
    _ ≤ ((Nat.log 2 (2 * N) : ℝ) + 1) * (K + C * Real.log (2 * (N : ℝ) + 2)) :=
      log_discrepancy_bound hC h N (by omega)
    _ ≤ ((3 / Real.log 2) * Real.log N) * ((K / Real.log 2 + 3 * C) * Real.log N) :=
      mul_le_mul hindex hterm htermpos (by positivity)
    _ = _ := by dsimp [D]; ring

lemma log_sq_div_sqrt_limit :
    Tendsto (fun N : ℕ ↦ (Real.log N) ^ 2 / Real.sqrt N) atTop (𝓝 0) := by
  have hh := ((isLittleO_log_rpow_rpow_atTop (2 : ℝ) (show 0 < (1 / 2 : ℝ) by norm_num)).tendsto_div_nhds_zero).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow] using hh

/-- The dyadic-hole modification changes the counting function by o(sqrt(N)). -/
theorem discrepancy_div_sqrt_limit {A : Set ℕ} {K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (h : ∀ n : ℕ, (sumRep A n : ℝ) ≤ K + C * Real.log ((n : ℝ) + 2)) :
    Tendsto (fun N : ℕ ↦ ((count A N : ℝ) - count (pruned A) N) / Real.sqrt N)
      atTop (𝓝 0) := by
  obtain ⟨D, hD, hbound⟩ := quadratic_log_bound hK hC h
  have hcount (N : ℕ) : count (pruned A) N ≤ count A N :=
    Finset.card_le_card (cutoff_pruned_subset A N)
  refine squeeze_zero' ?_ ?_ (by simpa using log_sq_div_sqrt_limit.const_mul D)
  · exact Eventually.of_forall (fun N ↦ div_nonneg (sub_nonneg.mpr (by exact_mod_cast hcount N)) (Real.sqrt_nonneg _))
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hb := hbound N hN
    rw [Nat.cast_sub (hcount N)] at hb
    have hh := div_le_div_of_nonneg_right hb (Real.sqrt_nonneg (N : ℝ))
    simpa only [mul_div_assoc] using hh

lemma discrepancy_normalized_limit {A : Set ℕ} {K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (h : ∀ n : ℕ, (sumRep A n : ℝ) ≤ K + C * Real.log ((n : ℝ) + 2)) :
    Tendsto (fun N : ℕ ↦ ((count A N : ℝ) - count (pruned A) N) /
      Real.sqrt ((N : ℝ) * Real.log N)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ ↦ Real.sqrt (Real.log N)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hh := (discrepancy_div_sqrt_limit hK hC h).div_atTop hlog
  apply hh.congr'
  filter_upwards [] with N
  rw [Real.sqrt_mul (Nat.cast_nonneg (α := ℝ) N), div_div]

/-- All counting limits at the natural square-root-logarithmic scale survive. -/
theorem pruned_counting_profile {A : Set ℕ} {K C d : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (h : ∀ n : ℕ, (sumRep A n : ℝ) ≤ K + C * Real.log ((n : ℝ) + 2))
    (hprofile : Tendsto (fun N : ℕ ↦ (count A N : ℝ) /
      Real.sqrt ((N : ℝ) * Real.log N)) atTop (𝓝 d)) :
    Tendsto (fun N : ℕ ↦ (count (pruned A) N : ℝ) /
      Real.sqrt ((N : ℝ) * Real.log N)) atTop (𝓝 d) := by
  have hh := hprofile.sub (discrepancy_normalized_limit hK hC h)
  simp only [sub_zero] at hh
  apply hh.congr'
  filter_upwards [] with N
  ring

lemma pruned_limit_eq_zero {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep (pruned A) n : ℝ) / Real.log n) atTop (𝓝 c)) : c = 0 := by
  have hp : Tendsto (fun k : ℕ ↦ (2 : ℕ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hh := h.comp hp
  simp only [Function.comp_def, pruned_hole, Nat.cast_zero, zero_div] at hh
  exact tendsto_nhds_unique hh tendsto_const_nhds

lemma count_square_profile {B : Set ℕ} {d : ℝ}
    (hprofile : Tendsto (fun N : ℕ ↦ (count B N : ℝ) /
      Real.sqrt ((N : ℝ) * Real.log N)) atTop (𝓝 d)) :
    Tendsto (fun N : ℕ ↦ (count B N : ℝ) ^ 2 / ((N : ℝ) * Real.log N)) atTop (𝓝 (d ^ 2)) := by
  apply (hprofile.pow 2).congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [div_pow, Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast hN)))]

/-- A nonzero counting profile rules out even a zero representation limit. -/
lemma pruned_no_limit {A : Set ℕ} {d : ℝ} (hd : d ≠ 0)
    (hprofile : Tendsto (fun N : ℕ ↦ (count (pruned A) N : ℝ) /
      Real.sqrt ((N : ℝ) * Real.log N)) atTop (𝓝 d)) :
    ¬ ∃ c : ℝ, Tendsto (fun n ↦ (sumRep (pruned A) n : ℝ) / Real.log n) atTop (𝓝 c) := by
  rintro ⟨c, hc⟩
  have hc0 := pruned_limit_eq_zero hc
  subst c
  have hd2 : 0 < d ^ 2 := sq_pos_of_ne_zero hd
  have hb := Erdos66Cumulative.normalized_count_bounds hc (half_pos hd2)
  have hle : d ^ 2 ≤ d ^ 2 / 2 := le_of_tendsto (count_square_profile hprofile) (by
    filter_upwards [hb] with N hN
    simpa using hN.2)
  linarith

/-- Thus sharp counting density plus an upper representation envelope is not,
by itself, a pointwise lower-bound principle. This is conditional on an input
set with the stated density, and is not a disproof of the existential conjecture. -/
theorem exists_same_density_and_holes {A : Set ℕ} {K C d : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hd : d ≠ 0)
    (h : ∀ n : ℕ, (sumRep A n : ℝ) ≤ K + C * Real.log ((n : ℝ) + 2))
    (hprofile : Tendsto (fun N : ℕ ↦ (count A N : ℝ) /
      Real.sqrt ((N : ℝ) * Real.log N)) atTop (𝓝 d)) :
    ∃ B : Set ℕ, B ⊆ A ∧
      (∀ n : ℕ, sumRep B n ≤ sumRep A n) ∧
      (∀ k : ℕ, sumRep B (2 ^ k) = 0) ∧
      Tendsto (fun N : ℕ ↦ (count B N : ℝ) /
        Real.sqrt ((N : ℝ) * Real.log N)) atTop (𝓝 d) ∧
      ¬ ∃ c : ℝ, Tendsto (fun n ↦ (sumRep B n : ℝ) / Real.log n) atTop (𝓝 c) := by
  have hp := pruned_counting_profile hK hC h hprofile
  exact ⟨pruned A, pruned_subset A, sumRep_mono (pruned_subset A), pruned_hole A,
    hp, pruned_no_limit hd hp⟩

/-- Every hypothetical witness has a subset with the same exact counting
asymptotic and no representation limit. This does not negate its existence. -/
theorem witness_has_same_density_nonconvergent_subset {A : Set ℕ} {c : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) :
    ∃ B : Set ℕ, B ⊆ A ∧
      (∀ n : ℕ, sumRep B n ≤ sumRep A n) ∧
      (∀ k : ℕ, sumRep B (2 ^ k) = 0) ∧
      Tendsto (fun N : ℕ ↦ (count B N : ℝ) /
        Real.sqrt ((N : ℝ) * Real.log N)) atTop (𝓝 (2 * Real.sqrt (c / Real.pi))) ∧
      ¬ ∃ d : ℝ, Tendsto (fun n ↦ (sumRep B n : ℝ) / Real.log n) atTop (𝓝 d) := by
  obtain ⟨K, C, hK, hC, hupper⟩ := global_log_upper_bound h
  have hcp := limit_pos hc h
  have hd : 2 * Real.sqrt (c / Real.pi) ≠ 0 := by positivity
  exact exists_same_density_and_holes hK hC.le hd hupper
    (Erdos66TauberianProfile.witness_counting_profile hc h)

end Erdos66DyadicDeletion
