import Submission.TangentDefinitions

/-!
# Positive points recur along Good tangent sequences

Away from the positive quadrant, two consecutive nonpositive-quadrant points
force a uniform contraction of the real size.  The cubic equation supplies a
positive lower bound, so a Good tangent sequence cannot remain outside the
positive quadrant forever.  No preservation theorem for `Good` is used here:
that property is an explicit assumption on the sequence.
-/

namespace Erdos829Aux.Tangent

private theorem good_coords_ne_zero {p : Triple} (hp : Good p) :
    p.a ≠ 0 ∧ p.b ≠ 0 := by
  constructor
  · intro ha
    have hu : IsUnit p.b := isCoprime_zero_left.mp (ha ▸ hp.2.1)
    rcases Int.isUnit_iff.mp hu with hb | hb <;>
      have hc := hp.2.2 <;> simp [ha, hb] at hc <;> omega
  · intro hb
    have hu : IsUnit p.a := isCoprime_zero_right.mp (hb ▸ hp.2.1)
    rcases Int.isUnit_iff.mp hu with ha | ha <;>
      have hc := hp.2.2 <;> simp [ha, hb] at hc <;> omega

private theorem good_mixed_signs {p : Triple} (hp : Good p) (hn : ¬ Positive p) :
    (0 < p.a ∧ p.b < 0) ∨ (0 < p.b ∧ p.a < 0) := by
  obtain ⟨ha0, hb0⟩ := good_coords_ne_zero hp
  have hw3 : 0 < p.w ^ 3 := pow_pos hp.1 3
  by_cases ha : 0 < p.a
  · left
    refine ⟨ha, ?_⟩
    have hb : p.b ≤ 0 := le_of_not_gt fun hb => hn ⟨ha, hb⟩
    exact lt_of_le_of_ne hb hb0
  · right
    have ha' : p.a ≤ 0 := le_of_not_gt ha
    refine ⟨?_, lt_of_le_of_ne ha' ha0⟩
    by_contra! hb
    have ha3 : p.a ^ 3 ≤ 0 := by
      simpa using ((by decide : Odd (3 : ℕ)).pow_le_pow (a := p.a) (b := 0)).mpr ha'
    have hb3 : p.b ^ 3 ≤ 0 := by
      simpa using ((by decide : Odd (3 : ℕ)).pow_le_pow (a := p.b) (b := 0)).mpr hb
    nlinarith [hp.2.2]

private def swapCoords (p : Triple) : Triple := ⟨p.b, p.a, p.w⟩

private theorem good_swapCoords {p : Triple} (hp : Good p) : Good (swapCoords p) := by
  refine ⟨hp.1, hp.2.1.symm, ?_⟩
  simpa [swapCoords, add_comm] using hp.2.2

private theorem positive_swapCoords (p : Triple) :
    Positive (swapCoords p) ↔ Positive p := by
  simp [Positive, swapCoords, and_comm]

private theorem realSize_swapCoords (p : Triple) :
    realSize (swapCoords p) = realSize p := by
  dsimp [realSize, swapCoords]
  exact max_comm _ _

private theorem rawStep_w_pos_of_mixed {p : Triple} (hw : 0 < p.w)
    (ha : 0 < p.a) (hb : p.b < 0) : 0 < (rawStep p).w := by
  have ha3 : 0 < p.a ^ 3 := pow_pos ha 3
  have hb3 : p.b ^ 3 < 0 := by
    simpa using ((by decide : Odd (3 : ℕ)).pow_lt_pow (a := p.b) (b := 0)).mpr hb
  exact mul_pos hw (by change 0 < p.a ^ 3 - p.b ^ 3; linarith)

private theorem step_swapCoords_of_raw_w_pos {p : Triple}
    (hw : 0 < (rawStep p).w) : step (swapCoords p) = swapCoords (step p) := by
  have hs : (rawStep (swapCoords p)).w < 0 := by
    have he : (rawStep (swapCoords p)).w = -(rawStep p).w := by
      dsimp [rawStep, swapCoords]
      ring
    rw [he]
    exact neg_neg_of_pos hw
  simp only [step, if_pos hs, if_neg (not_lt.mpr hw.le)]
  dsimp [rawStep, swapCoords]
  congr 1 <;> ring

/-- The scalar estimate behind the tangent contraction. -/
private theorem mixed_real_contraction {u r : ℝ} (hu : 0 < u) (hr : 0 < r)
    (hr1 : r < 1)
    (hn : ¬ (0 < u * (1 - 2 * r ^ 3) / (1 + r ^ 3) ∧
      0 < u * r * (2 - r ^ 3) / (1 + r ^ 3))) :
    max |u * (1 - 2 * r ^ 3) / (1 + r ^ 3)|
      |u * r * (2 - r ^ 3) / (1 + r ^ 3)| ≤ (9 / 10 : ℝ) * u := by
  have hr3 : 0 < r ^ 3 := pow_pos hr 3
  have hr3_lt : r ^ 3 < 1 := by
    simpa using ((by decide : Odd (3 : ℕ)).pow_lt_pow (a := r) (b := 1)).mpr hr1
  have hd : 0 < 1 + r ^ 3 := by linarith
  have hB : 0 < u * r * (2 - r ^ 3) / (1 + r ^ 3) :=
    div_pos (mul_pos (mul_pos hu hr) (by linarith)) hd
  have hA : u * (1 - 2 * r ^ 3) / (1 + r ^ 3) ≤ 0 :=
    le_of_not_gt fun h => hn ⟨h, hB⟩
  have hhalf : 1 ≤ 2 * r ^ 3 := by
    by_contra! h
    have hpos : 0 < u * (1 - 2 * r ^ 3) / (1 + r ^ 3) :=
      div_pos (mul_pos hu (by linarith)) hd
    exact hn ⟨hpos, hB⟩
  have hfactor : r * (2 - r ^ 3) / (1 + r ^ 3) ≤ (9 / 10 : ℝ) := by
    apply (div_le_iff₀ hd).mpr
    by_cases hsmall : r ≤ (9 / 10 : ℝ)
    · calc
        r * (2 - r ^ 3) ≤ r * (1 + r ^ 3) :=
          mul_le_mul_of_nonneg_left (by linarith) hr.le
        _ ≤ (9 / 10 : ℝ) * (1 + r ^ 3) :=
          mul_le_mul_of_nonneg_right hsmall hd.le
    · have hlarge : (9 / 10 : ℝ) ≤ r := (lt_of_not_ge hsmall).le
      have hlarge3 : (9 / 10 : ℝ) ^ 3 ≤ r ^ 3 :=
        ((by decide : Odd (3 : ℕ)).pow_le_pow).mpr hlarge
      calc
        r * (2 - r ^ 3) ≤ 1 * (2 - r ^ 3) :=
          mul_le_mul_of_nonneg_right hr1.le (by linarith)
        _ ≤ (9 / 10 : ℝ) * (1 + r ^ 3) := by nlinarith [hlarge3]
  have hBbound : u * r * (2 - r ^ 3) / (1 + r ^ 3) ≤ (9 / 10 : ℝ) * u := by
    calc
      u * r * (2 - r ^ 3) / (1 + r ^ 3) =
          u * (r * (2 - r ^ 3) / (1 + r ^ 3)) := by ring
      _ ≤ u * (9 / 10 : ℝ) := mul_le_mul_of_nonneg_left hfactor hu.le
      _ = (9 / 10 : ℝ) * u := mul_comm _ _
  have hpoly : 0 ≤ (1 - 2 * r ^ 3) + r * (2 - r ^ 3) := by
    have hprod : 0 ≤ (1 - r) * (1 + r) ^ 3 :=
      mul_nonneg (by linarith) (pow_nonneg (by linarith) 3)
    nlinarith [hprod]
  have hsum : 0 ≤ u * (1 - 2 * r ^ 3) / (1 + r ^ 3) +
      u * r * (2 - r ^ 3) / (1 + r ^ 3) := by
    rw [← add_div]
    apply div_nonneg _ hd.le
    nlinarith [mul_nonneg hu.le hpoly]
  apply max_le
  · rw [abs_of_nonpos hA]
    linarith
  · rw [abs_of_pos hB]
    exact hBbound

private theorem realSize_step_le_of_a_pos_b_neg {p : Triple} (hp : Good p)
    (ha : 0 < p.a) (hb : p.b < 0) (hn : ¬ Positive (step p)) :
    realSize (step p) ≤ (9 / 10 : ℝ) * realSize p := by
  have hwR : 0 < (p.w : ℝ) := by exact_mod_cast hp.1
  have haR : 0 < (p.a : ℝ) := by exact_mod_cast ha
  have hbR : (p.b : ℝ) < 0 := by exact_mod_cast hb
  have hab : -p.b < p.a := by
    apply ((by decide : Odd (3 : ℕ)).pow_lt_pow).mp
    nlinarith [hp.2.2, pow_pos hp.1 3]
  have habR : -(p.b : ℝ) < (p.a : ℝ) := by exact_mod_cast hab
  let u : ℝ := (p.a : ℝ) / p.w
  let r : ℝ := -(p.b : ℝ) / p.a
  have hu : 0 < u := div_pos haR hwR
  have hr : 0 < r := div_pos (neg_pos.mpr hbR) haR
  have hr1 : r < 1 := (div_lt_one haR).mpr habR
  have hraw : 0 < (rawStep p).w := rawStep_w_pos_of_mixed hp.1 ha hb
  have he : step p = rawStep p := by
    simp only [step, if_neg (not_lt.mpr hraw.le)]
  have hqw : 0 < ((step p).w : ℝ) := by
    rw [he]
    exact_mod_cast hraw
  have hd : (p.a : ℝ) ^ 3 - (p.b : ℝ) ^ 3 ≠ 0 := by
    have hb3 : (p.b : ℝ) ^ 3 < 0 := by
      simpa using ((by decide : Odd (3 : ℕ)).pow_lt_pow
        (a := (p.b : ℝ)) (b := 0)).mpr hbR
    exact ne_of_gt (by nlinarith [pow_pos haR 3])
  have hA : ((step p).a : ℝ) / (step p).w =
      u * (1 - 2 * r ^ 3) / (1 + r ^ 3) := by
    rw [he]
    simp only [rawStep, Int.cast_mul, Int.cast_add, Int.cast_sub, Int.cast_pow,
      Int.cast_ofNat]
    dsimp [u, r]
    field_simp [haR.ne', hwR.ne', hd]
    ring_nf
    field_simp [hd]
    ring
  have hB : ((step p).b : ℝ) / (step p).w =
      u * r * (2 - r ^ 3) / (1 + r ^ 3) := by
    rw [he]
    simp only [rawStep, Int.cast_mul, Int.cast_add, Int.cast_sub, Int.cast_pow,
      Int.cast_neg, Int.cast_ofNat]
    dsimp [u, r]
    field_simp [haR.ne', hwR.ne', hd]
    ring_nf
    field_simp [hd, show -(p.b : ℝ) ^ 3 + (p.a : ℝ) ^ 3 ≠ 0 by
      simpa [sub_eq_add_neg, add_comm] using hd]
    ring
  have hnR : ¬ (0 < u * (1 - 2 * r ^ 3) / (1 + r ^ 3) ∧
      0 < u * r * (2 - r ^ 3) / (1 + r ^ 3)) := by
    intro h
    apply hn
    constructor
    · have hqa : 0 < ((step p).a : ℝ) / (step p).w := by
        rw [hA]
        exact h.1
      have hnum : 0 < ((step p).a : ℝ) := by
        simpa only [zero_mul] using (lt_div_iff₀ hqw).mp hqa
      exact_mod_cast hnum
    · have hqb : 0 < ((step p).b : ℝ) / (step p).w := by
        rw [hB]
        exact h.2
      have hnum : 0 < ((step p).b : ℝ) := by
        simpa only [zero_mul] using (lt_div_iff₀ hqw).mp hqb
      exact_mod_cast hnum
  have hsize : realSize p = u := by
    have hle : -(p.b : ℝ) / p.w ≤ (p.a : ℝ) / p.w :=
      div_le_div_of_nonneg_right habR.le hwR.le
    dsimp [realSize, u]
    rw [abs_of_pos (div_pos haR hwR),
      abs_of_neg (div_neg_of_neg_of_pos hbR hwR)]
    apply max_eq_left
    simpa only [neg_div] using hle
  rw [hsize]
  change max |((step p).a : ℝ) / (step p).w|
    |((step p).b : ℝ) / (step p).w| ≤ (9 / 10 : ℝ) * u
  rw [hA, hB]
  exact mixed_real_contraction hu hr hr1 hnR

/-- Two consecutive points outside the positive quadrant contract the real size.
The hypothesis `Good (step p)` is not required. -/
theorem realSize_step_le_of_not_positive {p : Triple} (hp : Good p)
    (hn : ¬ Positive p) (hnstep : ¬ Positive (step p)) :
    realSize (step p) ≤ (9 / 10 : ℝ) * realSize p := by
  rcases good_mixed_signs hp hn with ⟨ha, hb⟩ | ⟨hb, ha⟩
  · exact realSize_step_le_of_a_pos_b_neg hp ha hb hnstep
  · let s := swapCoords p
    have hsgood : Good s := good_swapCoords hp
    have hsa : 0 < s.a := hb
    have hsb : s.b < 0 := ha
    have hsw := step_swapCoords_of_raw_w_pos
      (rawStep_w_pos_of_mixed hsgood.1 hsa hsb)
    change step p = swapCoords (step s) at hsw
    have hns : ¬ Positive (step s) := by
      intro hs
      apply hnstep
      rw [hsw]
      exact (positive_swapCoords _).mpr hs
    calc
      realSize (step p) = realSize (step s) := by rw [hsw, realSize_swapCoords]
      _ ≤ (9 / 10 : ℝ) * realSize s :=
        realSize_step_le_of_a_pos_b_neg hsgood hsa hsb hns
      _ = (9 / 10 : ℝ) * realSize p := by
        change (9 / 10 : ℝ) * realSize (swapCoords p) = _
        rw [realSize_swapCoords]

private theorem good_real_cubic {p : Triple} (hp : Good p) :
    ((p.a : ℝ) / p.w) ^ 3 + ((p.b : ℝ) / p.w) ^ 3 = 9 := by
  have hw : (p.w : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hp.1)
  have hc : (p.a : ℝ) ^ 3 + (p.b : ℝ) ^ 3 = 9 * (p.w : ℝ) ^ 3 := by
    exact_mod_cast hp.2.2
  field_simp [hw]
  simpa only [mul_comm] using hc

/-- Every Good point has real size at least one. -/
theorem one_le_realSize {p : Triple} (hp : Good p) : (1 : ℝ) ≤ realSize p := by
  by_contra! h
  have ha : (p.a : ℝ) / p.w < 1 :=
    lt_of_le_of_lt (le_abs_self _) (lt_of_le_of_lt (le_max_left _ _) h)
  have hb : (p.b : ℝ) / p.w < 1 :=
    lt_of_le_of_lt (le_abs_self _) (lt_of_le_of_lt (le_max_right _ _) h)
  have ha3 : ((p.a : ℝ) / p.w) ^ 3 < 1 := by
    simpa using ((by decide : Odd (3 : ℕ)).pow_lt_pow).mpr ha
  have hb3 : ((p.b : ℝ) / p.w) ^ 3 < 1 := by
    simpa using ((by decide : Odd (3 : ℕ)).pow_lt_pow).mpr hb
  nlinarith [good_real_cubic hp]

/-- Every tail of a Good tangent sequence contains a positive point. -/
theorem positive_indices_unbounded (f : ℕ → Triple) (hgood : ∀ k, Good (f k))
    (hstep : ∀ k, f (k + 1) = step (f k)) :
    ∀ K, ∃ k, K ≤ k ∧ Positive (f k) := by
  intro K
  by_contra! hnone
  have hbound : ∀ j : ℕ,
      realSize (f (K + j)) ≤ (9 / 10 : ℝ) ^ j * realSize (f K) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hn : ¬ Positive (f (K + j)) := hnone _ (by omega)
      have hnstep : ¬ Positive (step (f (K + j))) := by
        rw [← hstep (K + j)]
        exact hnone _ (by omega)
      calc
        realSize (f (K + (j + 1))) = realSize (step (f (K + j))) := by
          rw [Nat.add_succ, hstep (K + j)]
        _ ≤ (9 / 10 : ℝ) * realSize (f (K + j)) :=
          realSize_step_le_of_not_positive (hgood _) hn hnstep
        _ ≤ (9 / 10 : ℝ) * ((9 / 10 : ℝ) ^ j * realSize (f K)) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (9 / 10 : ℝ) ^ (j + 1) * realSize (f K) := by
          rw [pow_succ]
          ring
  have hM : 0 < realSize (f K) := lt_of_lt_of_le zero_lt_one (one_le_realSize (hgood K))
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one
    (show (0 : ℝ) < 1 / realSize (f K) from div_pos zero_lt_one hM)
    (show (9 / 10 : ℝ) < 1 by norm_num)
  have hjM : (9 / 10 : ℝ) ^ j * realSize (f K) < 1 := (lt_div_iff₀ hM).mp hj
  have hlower := one_le_realSize (hgood (K + j))
  have hupper := hbound j
  linarith

/-- The positive indices of a Good tangent sequence form an infinite set. -/
theorem infinite_positive_indices (f : ℕ → Triple) (hgood : ∀ k, Good (f k))
    (hstep : ∀ k, f (k + 1) = step (f k)) :
    {k : ℕ | Positive (f k)}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro K
  obtain ⟨k, hk, hp⟩ := positive_indices_unbounded f hgood hstep (K + 1)
  exact ⟨k, hp, by omega⟩

end Erdos829Aux.Tangent
