import Submission.PredecessorPacketCapacityExplore
import Submission.ClippingBudgetTransferExplore
import Submission.TauberianProfileExplore

/-! Capacity restrictions when repair packets may reuse points. These are
necessary conditions on a correction scheme, not a solution of Erdős 66. -/
namespace Erdos66BoundedReuseRepair
open Filter AdditiveCombinatorics Erdos66Counting
  Erdos66PredecessorPacketCapacity Erdos66ClippingBudgetTransfer
  Erdos66TauberianProfile
open scoped Classical Topology
set_option maxHeartbeats 1800000

/-- Double counting incidences, with no disjointness or predecessor assumption. -/
lemma packet_incidence_bound {ι : Type*} (B : Set ℕ) (T : Finset ι)
    (P : ι → Finset ℕ) (N L : ℕ)
    (hsupp : ∀ i ∈ T, ∀ x ∈ P i, x < N ∧ x ∈ B)
    (hreuse : ∀ x < N, (T.filter (fun i ↦ x ∈ P i)).card ≤ L) :
    (∑ i ∈ T, (P i).card) ≤ L * count B N := by
  have he (i : ι) (hi : i ∈ T) :
      (cutoff B N).filter (fun x ↦ x ∈ P i) = P i := by
    ext x
    simp only [Finset.mem_filter, mem_cutoff]
    exact and_iff_right_of_imp (hsupp i hi x)
  calc
    _ = ∑ i ∈ T, ∑ x ∈ cutoff B N, if x ∈ P i then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_boole, he i hi]
      norm_cast
    _ = ∑ x ∈ cutoff B N, (T.filter (fun i ↦ x ∈ P i)).card := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      exact Finset.sum_boole _ _
    _ ≤ ∑ _x ∈ cutoff B N, L := by
      apply Finset.sum_le_sum
      intro x hx
      exact hreuse x (mem_cutoff.mp hx).1
    _ = _ := by simp [count, mul_comm]

lemma uniform_packet_incidence_bound {ι : Type*} (B : Set ℕ) (T : Finset ι)
    (P : ι → Finset ℕ) (N L : ℕ) (d : ℝ)
    (hsupp : ∀ i ∈ T, ∀ x ∈ P i, x < N ∧ x ∈ B)
    (hreuse : ∀ x < N, (T.filter (fun i ↦ x ∈ P i)).card ≤ L)
    (hsize : ∀ i ∈ T, d ≤ ((P i).card : ℝ)) :
    d * T.card ≤ (L : ℝ) * count B N := by
  have hh := Finset.sum_le_sum hsize
  have hc : (∑ i ∈ T, ((P i).card : ℝ)) ≤ (L : ℝ) * count B N := by
    exact_mod_cast packet_incidence_bound B T P N L hsupp hreuse
  have he : (∑ _i ∈ T, d) = d * T.card := by simp [mul_comm]
  rw [he] at hh
  exact hh.trans hc

/-- Every logarithmic-sized packet consumes incidences, even if its points
are shared. The reuse factor appears quadratically in the counting bound. -/
theorem logarithmic_packet_reuse_bound {ι : Type*} (B : Set ℕ) (T : Finset ι)
    (P : ι → Finset ℕ) (N L : ℕ) (δ K C : ℝ)
    (hδ : 0 < δ) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hB : ∀ z, (sumRep B z : ℝ) ≤ K + C * Real.log ((z : ℝ) + 2))
    (hN : 2 ≤ N) (hlog : 1 ≤ Real.log (N : ℝ))
    (hsupp : ∀ i ∈ T, ∀ x ∈ P i, x < 2*N ∧ x ∈ B)
    (hreuse : ∀ x < 2*N, (T.filter (fun i ↦ x ∈ P i)).card ≤ L)
    (hsize : ∀ i ∈ T, δ * Real.log N ≤ ((P i).card : ℝ)) :
    δ^2 * Real.log N * (T.card : ℝ)^2 ≤ 4*N*(K+4*C)*(L : ℝ)^2 := by
  have hc := uniform_packet_incidence_bound B T P (2*N) L
    (δ * Real.log N) hsupp hreuse hsize
  have hb := double_count_coarse_log B K C hK hC hB N hN hlog
  have hlogp : 0 < Real.log (N : ℝ) := by linarith
  have hs := pow_le_pow_left₀ (show (0 : ℝ) ≤ δ * Real.log N * T.card by positivity) hc 2
  have hm := mul_le_mul_of_nonneg_left hb (sq_nonneg (L : ℝ))
  apply le_of_mul_le_mul_right (a := Real.log (N : ℝ)) _ hlogp
  nlinarith only [hs, hm]

/-- Even growing reuse is insufficient at the square-root target scale
if it is little-o of sqrt(log N). No predecessor map is involved. -/
theorem slowly_reused_packet_count_zero {ι : Type*} (B : Set ℕ)
    (T : ℕ → Finset ι) (P : ℕ → ι → Finset ℕ) (L : ℕ → ℕ)
    (δ K C : ℝ) (hδ : 0 < δ) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hB : ∀ z, (sumRep B z : ℝ) ≤ K + C * Real.log ((z : ℝ) + 2))
    (hsmall : Tendsto (fun N : ℕ ↦ (L N : ℝ) / Real.sqrt (Real.log N))
      atTop (𝓝 0))
    (hpack : ∀ᶠ N : ℕ in atTop,
      (∀ i ∈ T N, ∀ x ∈ P N i, x < 2*N ∧ x ∈ B) ∧
      (∀ x < 2*N, ((T N).filter (fun i ↦ x ∈ P N i)).card ≤ L N) ∧
      (∀ i ∈ T N, δ * Real.log N ≤ ((P N i).card : ℝ))) :
    Tendsto (fun N ↦ ((T N).card : ℝ) / Real.sqrt N) atTop (𝓝 0) := by
  let H := 4 * (K + 4*C) / δ^2
  have hloglim : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun N : ℕ ↦
      Real.sqrt (H * ((L N : ℝ) / Real.sqrt (Real.log N))^2)) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, Real.sqrt_zero]
      using ((hsmall.pow 2).const_mul H).sqrt
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ by positivity)) ?_ hlim
  filter_upwards [hpack, eventually_ge_atTop 2, hloglim.eventually_ge_atTop 1]
    with N hp hN hlog
  obtain ⟨hsupp, hreuse, hsize⟩ := hp
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlp : 0 < Real.log (N : ℝ) := by linarith
  have hb := logarithmic_packet_reuse_bound B (T N) (P N) N (L N)
    δ K C hδ hK hC hB hN hlog hsupp hreuse hsize
  have hsq : (((T N).card : ℝ) / Real.sqrt N)^2 ≤
      H * ((L N : ℝ) / Real.sqrt (Real.log N))^2 := by
    rw [div_pow, div_pow, Real.sq_sqrt hNp.le, Real.sq_sqrt hlp.le, ← mul_div_assoc]
    apply (div_le_div_iff₀ hNp hlp).mpr
    have hh : ((T N).card : ℝ)^2 * Real.log N ≤
        (4*N*(K+4*C)*(L N : ℝ)^2) / δ^2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hδ)).mpr
      nlinarith only [hb]
    convert hh using 1 <;> dsimp [H] <;> ring
  have hh := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (show (0 : ℝ) ≤ ((T N).card : ℝ) / Real.sqrt N by positivity)] at hh

/-- If the two sets have the same normalized counting limit, their monotone
addition has negligible counting mass. -/
lemma added_count_limit_zero (A B : Set ℕ) (hAB : A ⊆ B) (R : ℕ → ℝ) (d : ℝ)
    (hA : Tendsto (fun N ↦ (count A N : ℝ) / R N) atTop (𝓝 d))
    (hB : Tendsto (fun N ↦ (count B N : ℝ) / R N) atTop (𝓝 d)) :
    Tendsto (fun N ↦ (count (B \ A) N : ℝ) / R N) atTop (𝓝 0) := by
  have hh := hB.sub hA
  simp only [sub_self] at hh
  apply hh.congr'
  filter_upwards [] with N
  have he : (count (B \ A) N : ℝ) + count A N = count B N := by
    exact_mod_cast count_diff_add B A hAB N
  rw [← sub_div]
  congr 1
  linarith

/-- Bounded reuse cannot hide a macroscopic packet mass in a negligible
monotone addition. Arbitrary packet shapes and varying packet costs are allowed. -/
theorem bounded_reuse_packet_mass_zero {ι : Type*} (A B : Set ℕ) (hAB : A ⊆ B)
    (T : ℕ → Finset ι) (P : ℕ → ι → Finset ℕ) (L : ℕ)
    (R d : ℕ → ℝ) (a : ℝ)
    (hR : ∀ᶠ N : ℕ in atTop, 0 < R N)
    (hd : ∀ᶠ N : ℕ in atTop, 0 ≤ d N)
    (hA : Tendsto (fun N ↦ (count A N : ℝ) / R N) atTop (𝓝 a))
    (hB : Tendsto (fun N ↦ (count B N : ℝ) / R N) atTop (𝓝 a))
    (hpack : ∀ᶠ N : ℕ in atTop,
      (∀ i ∈ T N, ∀ x ∈ P N i, x < N ∧ x ∈ B \ A) ∧
      (∀ x < N, ((T N).filter (fun i ↦ x ∈ P N i)).card ≤ L) ∧
      (∀ i ∈ T N, d N ≤ ((P N i).card : ℝ))) :
    Tendsto (fun N ↦ d N * (T N).card / R N) atTop (𝓝 0) := by
  have hlim := (added_count_limit_zero A B hAB R a hA hB).const_mul (L : ℝ)
  simp only [mul_zero] at hlim
  apply squeeze_zero' ?_ ?_ hlim
  · filter_upwards [hR, hd] with N hRN hdN
    positivity
  · filter_upwards [hR, hpack] with N hRN hp
    obtain ⟨hsupp, hreuse, hsize⟩ := hp
    have hh := uniform_packet_incidence_bound (B \ A) (T N) (P N) N L
      (d N) hsupp hreuse hsize
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hh hRN.le

/-- Specialization to a hypothetical completion with the same counting
profile as its base. This hypothesis is essential and is not a construction. -/
theorem same_coefficient_completion_packet_mass_zero {ι : Type*}
    (A B : Set ℕ) (hAB : A ⊆ B) (c : ℝ) (hc : c ≠ 0)
    (hB : Tendsto (fun n ↦ (sumRep B n : ℝ) / Real.log n) atTop (𝓝 c))
    (hA : Tendsto (fun N ↦ (count A N : ℝ) / Real.sqrt ((N : ℝ) * Real.log N))
      atTop (𝓝 (2 * Real.sqrt (c / Real.pi))))
    (T : ℕ → Finset ι) (P : ℕ → ι → Finset ℕ) (L : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hpack : ∀ᶠ N : ℕ in atTop,
      (∀ i ∈ T N, ∀ x ∈ P N i, x < N ∧ x ∈ B \ A) ∧
      (∀ x < N, ((T N).filter (fun i ↦ x ∈ P N i)).card ≤ L) ∧
      (∀ i ∈ T N, δ * Real.log N ≤ ((P N i).card : ℝ))) :
    Tendsto (fun N : ℕ ↦ δ * Real.log N * (T N).card /
      Real.sqrt ((N : ℝ) * Real.log N)) atTop (𝓝 0) := by
  apply bounded_reuse_packet_mass_zero A B hAB T P L
    (fun N ↦ Real.sqrt ((N : ℝ) * Real.log N)) (fun N ↦ δ * Real.log N)
    (2 * Real.sqrt (c / Real.pi)) _ _ hA (witness_counting_profile hc hB) hpack
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    exact Real.sqrt_pos.mpr (mul_pos (by linarith) (Real.log_pos hNr))
  · filter_upwards [eventually_ge_atTop 2] with N hN
    exact mul_nonneg hδ.le (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega)))

/-- The preceding same-coefficient condition has the sharper target-count
normalization sqrt(N/log N), rather than merely sqrt(N). -/
theorem same_coefficient_completion_target_count_zero {ι : Type*}
    (A B : Set ℕ) (hAB : A ⊆ B) (c : ℝ) (hc : c ≠ 0)
    (hB : Tendsto (fun n ↦ (sumRep B n : ℝ) / Real.log n) atTop (𝓝 c))
    (hA : Tendsto (fun N ↦ (count A N : ℝ) / Real.sqrt ((N : ℝ) * Real.log N))
      atTop (𝓝 (2 * Real.sqrt (c / Real.pi))))
    (T : ℕ → Finset ι) (P : ℕ → ι → Finset ℕ) (L : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hpack : ∀ᶠ N : ℕ in atTop,
      (∀ i ∈ T N, ∀ x ∈ P N i, x < N ∧ x ∈ B \ A) ∧
      (∀ x < N, ((T N).filter (fun i ↦ x ∈ P N i)).card ≤ L) ∧
      (∀ i ∈ T N, δ * Real.log N ≤ ((P N i).card : ℝ))) :
    Tendsto (fun N : ℕ ↦ ((T N).card : ℝ) * Real.sqrt (Real.log N) /
      Real.sqrt N) atTop (𝓝 0) := by
  have hh := (same_coefficient_completion_packet_mass_zero A B hAB c hc hB hA
    T P L δ hδ hpack).div_const δ
  simp only [zero_div] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlp : 0 < Real.log (N : ℝ) := Real.log_pos hNr
  have hsN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hsL : 0 < Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_pos.mpr hlp
  rw [Real.sqrt_mul (by linarith : (0 : ℝ) ≤ N)]
  have hsq := Real.sq_sqrt hlp.le
  field_simp
  nlinarith only [hsq]

end Erdos66BoundedReuseRepair
