import Submission.Spec

/-! Removing both common factors and the additive-triple locus. -/
namespace Erdos322Research.PrimitiveNonadditiveReduction

open Erdos322 Erdos322.QuarticAdditive Erdos322.PrimitiveNonadditive
open Erdos322.MomentReduction

/-- The discarded primitive representations are among the additive ones. -/
theorem primitive_count_le_additive_add (n : ℕ) :
    primitiveRepresentationCount 4 n ≤
      additiveQuarticCount n + primitiveNonadditiveCount n := by
  classical
  let S := Finset.univ.filter (fun a : Fin 4 → Fin (n+1) ↦
    (∑ i, (a i : ℕ)^4 = n) ∧ Finset.univ.gcd (fun i ↦ (a i : ℕ)) = 1)
  have hs : (S.filter HasAdditiveTriple).card ≤ additiveQuarticCount n := by
    apply Finset.card_le_card
    intro a ha
    simp only [S, Finset.mem_filter,
      Finset.mem_univ, true_and] at ha ⊢
    exact ⟨ha.1.1, ha.2⟩
  have ht : (S.filter (fun a ↦ ¬ HasAdditiveTriple a)).card =
      primitiveNonadditiveCount n := by
    unfold S primitiveNonadditiveCount
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hp := Finset.card_filter_add_card_filter_not (s := S) HasAdditiveTriple
  rw [ht] at hp
  change S.card ≤ _
  omega

/-- A subpolynomial bound on the primitive nonadditive part is equivalent to
one on the entire quartic representation count. Neither bound is asserted. -/
theorem primitive_nonadditive_bound_iff_full_bound :
    Subpolynomial primitiveNonadditiveCount ↔
      Subpolynomial (representationCount 4) := by
  constructor
  · intro h
    apply (primitive_bound_iff_full_bound (by decide : 0 < 4)).mp
    intro ε hε
    obtain ⟨A, hA, hpn⟩ := h ε hε
    obtain ⟨B, hB, hadd⟩ := additive_quartic_subpolynomial ε hε
    refine ⟨B+A, add_pos hB hA, fun n hn ↦ ?_⟩
    have hle : (primitiveRepresentationCount 4 n : ℝ) ≤
        (additiveQuarticCount n : ℝ) + primitiveNonadditiveCount n := by
      exact_mod_cast primitive_count_le_additive_add n
    calc
      (primitiveRepresentationCount 4 n : ℝ) ≤
          (additiveQuarticCount n : ℝ) + primitiveNonadditiveCount n := hle
      _ ≤ B*(n : ℝ)^ε + A*(n : ℝ)^ε :=
        add_le_add (hadd n (by omega)) (hpn n hn)
      _ = (B+A)*(n : ℝ)^ε := by ring
  · intro h ε hε
    obtain ⟨C, hC, hfull⟩ := h ε hε
    refine ⟨C, hC, fun n hn ↦ ?_⟩
    have hle : (primitiveNonadditiveCount n : ℝ) ≤ representationCount 4 n := by
      exact_mod_cast (primitiveNonadditiveCount_le_primitive n).trans
        (primitiveRepresentationCount_le 4 n)
    exact hle.trans (hfull n hn)

/-- Deleting the additive part from the primitive count preserves the existence
of power peaks, possibly with a smaller positive exponent. -/
theorem primitive_peaks_iff_primitive_nonadditive_peaks :
    (∃ c > (0 : ℝ),
      {n : ℕ | (n : ℝ)^c < primitiveRepresentationCount 4 n}.Infinite) ↔
    (∃ c > (0 : ℝ),
      {n : ℕ | (n : ℝ)^c < primitiveNonadditiveCount n}.Infinite) := by
  constructor
  · rintro ⟨c, hc, hi⟩
    have hh : 0 < c/2 := by linarith
    obtain ⟨C, hC, hadd⟩ := additive_quartic_subpolynomial (c/2) hh
    have ht : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ)^(c/2))
        Filter.atTop Filter.atTop :=
      (tendsto_rpow_atTop hh).comp tendsto_natCast_atTop_atTop
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (ht.eventually_ge_atTop (C+1))
    refine ⟨c/2, hh, (hi.diff (Set.finite_Iio (max N 1))).mono ?_⟩
    intro n hn
    have hlarge : max N 1 ≤ n := by
      simpa only [Set.mem_Iio, not_lt] using hn.2
    have hnpos : 0 < n := by omega
    have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hsmall := hadd n hnpos
    have hdom := hN n (by omega)
    have hsplit : (primitiveRepresentationCount 4 n : ℝ) ≤
        (additiveQuarticCount n : ℝ) + primitiveNonadditiveCount n := by
      exact_mod_cast primitive_count_le_additive_add n
    have hp : ((n : ℝ)^(c/2))^2 = (n : ℝ)^c := by
      rw [pow_two, ← Real.rpow_add hnr]
      congr 1
      ring
    have hmain := hn.1
    change (n : ℝ)^c < (primitiveRepresentationCount 4 n : ℝ) at hmain
    change (n : ℝ)^(c/2) < (primitiveNonadditiveCount n : ℝ)
    nlinarith [mul_nonneg (show 0 ≤ (n : ℝ)^(c/2) by positivity)
      (show 0 ≤ (n : ℝ)^(c/2) - (C+1) by linarith)]
  · rintro ⟨c, hc, hi⟩
    refine ⟨c, hc, hi.mono fun n hn ↦ ?_⟩
    have hle : (primitiveNonadditiveCount n : ℝ) ≤ primitiveRepresentationCount 4 n := by
      exact_mod_cast primitiveNonadditiveCount_le_primitive n
    exact hn.trans_le hle

/-- Exact quartic peak criterion after both reductions. -/
theorem quartic_peaks_iff_primitive_nonadditive_peaks :
    (∃ c > (0 : ℝ), {n : ℕ | (n : ℝ)^c < representationCount 4 n}.Infinite) ↔
    (∃ c > (0 : ℝ), {n : ℕ | (n : ℝ)^c < primitiveNonadditiveCount n}.Infinite) :=
  (primitive_peaks_iff_full_peaks (by decide : 0 < 4)).symm.trans
    primitive_peaks_iff_primitive_nonadditive_peaks

/-- The all-moment criterion can likewise be restricted to this part. -/
theorem quartic_subpolynomial_iff_primitive_nonadditive_moments :
    Subpolynomial (representationCount 4) ↔
      QuadraticMoments primitiveNonadditiveCount :=
  primitive_nonadditive_bound_iff_full_bound.symm.trans
    (subpolynomial_iff_quadratic_moments primitiveNonadditiveCount)

end Erdos322Research.PrimitiveNonadditiveReduction
