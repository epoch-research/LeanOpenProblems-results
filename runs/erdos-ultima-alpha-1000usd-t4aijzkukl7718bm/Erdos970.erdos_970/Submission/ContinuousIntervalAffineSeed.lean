import Submission.ContinuousIntervalSeedForcing

/-! Regular affine discrepancy seeds. A periodic wheel can supply the explicit
error E; this lemma does not bound E for growing numbers of primes. -/
namespace Erdos970.ContinuousInterval

noncomputable def affineLower (d E x : ℝ) : ℝ := max 0 (d * x - E)
noncomputable def affineUpper (d E x : ℝ) : ℝ := min x (d * x + E)

theorem affineSeed_regular (d E : ℝ) (hd : 0 ≤ d) (hd1 : d ≤ 1) (hE : 0 ≤ E) :
    Regular d (affineLower d E) (affineUpper d E) := by
  have hLc : ConvexOn ℝ Set.univ (fun x => d * x - E) := by
    simpa only [smul_eq_mul, sub_eq_add_neg] using
      ((convexOn_id (𝕜 := ℝ) convex_univ).smul hd).add_const (-E)
  have hUc : ConcaveOn ℝ (Set.Ici 0) (fun x => d * x + E) := by
    simpa only [smul_eq_mul] using
      ((concaveOn_id (𝕜 := ℝ) (convex_Ici 0)).smul hd).add_const E
  refine ⟨hd, fun x => le_max_left _ _, ?_, (convexOn_const 0 convex_univ).sup hLc,
    ?_, ?_, ?_, (concaveOn_id (convex_Ici 0)).inf hUc, ?_⟩
  · intro x hx
    exact max_eq_left (by nlinarith [mul_nonpos_of_nonneg_of_nonpos hd hx])
  · intro x y hxy
    apply max_le_max_left
    nlinarith [mul_nonneg hd (sub_nonneg.mpr hxy)]
  · intro x y hxy
    have hn : 0 ≤ d * (y - x) := mul_nonneg hd (sub_nonneg.mpr hxy)
    have hh := max_sub_max_le_max (0 : ℝ) (d * y - E) 0 (d * x - E)
    dsimp [affineLower]
    apply hh.trans
    exact max_le (by simpa using hn) (by ring_nf; rfl)
  · simp [affineUpper, min_eq_left hE]
  · intro x y hx hxy
    have h1 := min_le_left x (d * x + E)
    have h2 := min_le_right x (d * x + E)
    have hh := mul_nonneg (sub_nonneg.mpr hd1) (sub_nonneg.mpr hxy)
    dsimp [affineUpper]
    apply le_sub_iff_add_le.mpr
    exact le_min (by nlinarith) (by nlinarith)

#print axioms affineSeed_regular
end Erdos970.ContinuousInterval
