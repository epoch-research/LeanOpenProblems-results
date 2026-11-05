import FormalConjecturesUtil
import Submission.Reductions

/-!
# Small open hitting sets from affine avoidance

These reductions are independent of `Submission.Spec`. Lebesgue density lets us
rescale a compact positive avoidance witness to cover almost all of any bounded
open interval. Its open complement meets every affine copy lying in that interval.
No assertion about avoidance of an arbitrary infinite set is made here.
-/

open Set MeasureTheory Metric Filter
open scoped ENNReal Topology

namespace Erdos120Aux

/-- A nonzero affine change of the target preserves its property of containing no
nonzero affine copy of `A`. This changes the witness, not the source set. -/
theorem affine_image_preserves_avoidance_witness {A K : Set ℝ}
    (hK : ∀ a b : ℝ, a ≠ 0 → ¬ Set.image (fun x => a * x + b) A ⊆ K)
    {c : ℝ} (hc : c ≠ 0) (d : ℝ) :
    ∀ a b : ℝ, a ≠ 0 →
      ¬ Set.image (fun x => a * x + b) A ⊆ Set.image (fun x => c * x + d) K := by
  intro a b ha hsub
  have hinv := Set.image_mono (f := fun x : ℝ => c⁻¹ * x + -(c⁻¹ * d)) hsub
  apply hK (c⁻¹ * a) (c⁻¹ * b + -(c⁻¹ * d)) (mul_ne_zero (inv_ne_zero hc) ha)
  simpa only [affine_image_comp, affine_image_inverse K hc d] using hinv

/-- The volume change under a nonzero real affine preimage. No measurability of
`S` is needed, since both maps involved are homeomorphisms. -/
theorem volume_affine_preimage (S : Set ℝ) {c : ℝ} (hc : c ≠ 0) (d : ℝ) :
    volume ((fun x => c * x + d) ⁻¹' S) = ENNReal.ofReal |c⁻¹| * volume S := by
  change volume ((fun x => c * x) ⁻¹' ((fun x => x + d) ⁻¹' S)) = _
  rw [Real.volume_preimage_mul_left hc, measure_preimage_add_right]

/-- The volume change under a nonzero real affine image. -/
theorem volume_affine_image (S : Set ℝ) {c : ℝ} (hc : c ≠ 0) (d : ℝ) :
    volume (Set.image (fun x => c * x + d) S) = ENNReal.ofReal |c| * volume S := by
  have hleft : Function.LeftInverse (fun x : ℝ => c⁻¹ * x + -(c⁻¹ * d))
      (fun x : ℝ => c * x + d) := by
    intro x
    simp [mul_add, hc]
  have hright : Function.RightInverse (fun x : ℝ => c⁻¹ * x + -(c⁻¹ * d))
      (fun x : ℝ => c * x + d) := by
    intro x
    simp [mul_add, hc]
  rw [Set.image_eq_preimage_of_inverse hleft hright,
    volume_affine_preimage S (inv_ne_zero hc)]
  simp

/-- Every measurable positive-volume real set occupies an arbitrarily large
fraction of some positive-radius closed ball. -/
theorem exists_high_density_closedBall {E : Set ℝ} (hE : MeasurableSet E)
    (hpos : 0 < volume E) {η : ℝ} (hη : 0 < η) :
    ∃ x ∈ E, ∃ r : ℝ, 0 < r ∧
      volume (closedBall x r \ E) < ENNReal.ofReal η * volume (closedBall x r) := by
  obtain ⟨x, hxE, hx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos.ne'
    (IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div (volume : Measure ℝ) E 1)
  have hlim : Tendsto
      (fun r : ℝ => volume (E ∩ closedBall x r) / volume (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    apply hx (fun _ : ℝ => x) (fun r : ℝ => r) tendsto_id
    filter_upwards [self_mem_nhdsWithin] with r hr
    simpa only [one_mul] using (mem_closedBall_self (x := x) (le_of_lt hr))
  have hcompl : Tendsto
      (fun r : ℝ => 1 - volume (E ∩ closedBall x r) / volume (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
    simpa using ((ENNReal.continuous_sub_left (by simp : (1 : ℝ≥0∞) ≠ ⊤)).tendsto 1).comp hlim
  have hevent := hcompl.eventually (eventually_lt_nhds (ENNReal.ofReal_pos.mpr hη))
  have hpos_event : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), 0 < r := self_mem_nhdsWithin
  obtain ⟨r, hr, hratio⟩ := (hpos_event.and hevent).exists
  have hrpos : 0 < r := hr
  have hvol0 : volume (closedBall x r) ≠ 0 := by
    rw [Real.volume_closedBall]
    exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hvoltop : volume (closedBall x r) ≠ ⊤ := by
    rw [Real.volume_closedBall]
    exact ENNReal.ofReal_ne_top
  have hdiff : volume (closedBall x r \ E) =
      volume (closedBall x r) - volume (E ∩ closedBall x r) := by
    have hset : closedBall x r \ E = closedBall x r \ (E ∩ closedBall x r) := by
      ext y
      simp only [mem_diff, mem_inter_iff]
      tauto
    rw [hset]
    exact measure_diff inter_subset_right (hE.inter measurableSet_closedBall).nullMeasurableSet
      (measure_ne_top_of_subset inter_subset_right hvoltop)
  refine ⟨x, hxE, r, hrpos, (ENNReal.div_lt_iff (Or.inl hvol0) (Or.inl hvoltop)).mp ?_⟩
  rw [hdiff, ENNReal.sub_div (fun _ _ => hvol0), ENNReal.div_self hvol0 hvoltop]
  exact hratio

/-- An interval version of the positive-set density reduction, with an arbitrarily
tight prescribed upper bound for the fraction missing from the set. -/
theorem exists_high_density_interval {E : Set ℝ} (hE : MeasurableSet E)
    (hpos : 0 < volume E) {η : ℝ} (hη : 0 < η) :
    ∃ p q : ℝ, p < q ∧
      volume (Ioo p q \ E) < ENNReal.ofReal η * ENNReal.ofReal (q - p) := by
  obtain ⟨x, _, r, hr, hdense⟩ := exists_high_density_closedBall hE hpos hη
  refine ⟨x - r, x + r, by linarith, ?_⟩
  have hsub : Ioo (x - r) (x + r) \ E ⊆ closedBall x r \ E := by
    rw [← Real.ball_eq_Ioo]
    exact Set.diff_subset_diff_left ball_subset_closedBall
  have hlen : x + r - (x - r) = 2 * r := by ring
  simpa only [Real.volume_closedBall, hlen] using (measure_mono hsub).trans_lt hdense


/-- An affine image of any measurable positive-volume real set occupies all but
an arbitrarily small amount of any given nonempty bounded open interval. -/
theorem exists_affine_image_almost_full_interval {E : Set ℝ} (hE : MeasurableSet E)
    (hpos : 0 < volume E) {u v ε : ℝ} (huv : u < v) (hε : 0 < ε) :
    ∃ c d : ℝ, 0 < c ∧
      volume (Ioo u v \ Set.image (fun x => c * x + d) E) < ENNReal.ofReal ε := by
  let η : ℝ := ε / (v - u)
  have hη : 0 < η := div_pos hε (sub_pos.mpr huv)
  obtain ⟨p, q, hpq, hdense⟩ := exists_high_density_interval hE hpos hη
  let c : ℝ := (v - u) / (q - p)
  let d : ℝ := u - c * p
  have hc : 0 < c := div_pos (sub_pos.mpr huv) (sub_pos.mpr hpq)
  have hscale : c * (q - p) = v - u := by
    exact div_mul_cancel₀ (v - u) (sub_ne_zero.mpr hpq.ne')
  have hp : c * p + d = u := by dsimp [d]; ring
  have hq : c * q + d = v := by dsimp [d]; nlinarith [hscale]
  have himage : Set.image (fun x => c * x + d) (Ioo p q) = Ioo u v := by
    rw [Set.image_affine_Ioo hc, hp, hq]
  have hinj : Function.Injective (fun x : ℝ => c * x + d) := by
    intro x y h
    exact mul_left_cancel₀ hc.ne' (add_right_cancel h)
  have hdiff : Ioo u v \ Set.image (fun x => c * x + d) E =
      Set.image (fun x => c * x + d) (Ioo p q \ E) := by
    rw [Set.image_diff hinj, himage]
  have hcancel : (c * η) * (q - p) = ε := by
    calc
      (c * η) * (q - p) = η * (c * (q - p)) := by ring
      _ = ε := by rw [hscale]; exact div_mul_cancel₀ ε (sub_ne_zero.mpr huv.ne')
  refine ⟨c, d, hc, ?_⟩
  rw [hdiff, volume_affine_image _ hc.ne' d, abs_of_pos hc]
  calc
    ENNReal.ofReal c * volume (Ioo p q \ E) <
        ENNReal.ofReal c * (ENNReal.ofReal η * ENNReal.ofReal (q - p)) :=
      ENNReal.mul_lt_mul_right (ENNReal.ofReal_pos.mpr hc).ne' ENNReal.ofReal_ne_top hdense
    _ = ENNReal.ofReal ((c * η) * (q - p)) := by
      rw [ENNReal.ofReal_mul (mul_nonneg hc.le hη.le), ENNReal.ofReal_mul hc.le, mul_assoc]
    _ = ENNReal.ofReal ε := by rw [hcancel]

/-- A compact positive avoidance witness can be made to fill any fixed bounded
open interval up to an arbitrarily small volume error. -/
theorem Avoidance.exists_compact_almost_full_interval {A : Set ℝ} (hA : Avoidance A)
    {u v ε : ℝ} (huv : u < v) (hε : 0 < ε) :
    ∃ F : Set ℝ, IsCompact F ∧ 0 < volume F ∧
      volume (Ioo u v \ F) < ENNReal.ofReal ε ∧
      ∀ a b : ℝ, a ≠ 0 → ¬ Set.image (fun x => a * x + b) A ⊆ F := by
  obtain ⟨K, hK, hpos, havoid⟩ := avoidance_iff_exists_compact.mp hA
  obtain ⟨c, d, hc, hsmall⟩ :=
    exists_affine_image_almost_full_interval hK.measurableSet hpos huv hε
  refine ⟨Set.image (fun x => c * x + d) K,
    hK.image ((continuous_const.mul continuous_id).add continuous_const), ?_, hsmall,
    affine_image_preserves_avoidance_witness havoid hc.ne' d⟩
  rw [volume_affine_image K hc.ne' d, abs_of_pos hc]
  exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hc).ne' hpos.ne'

/-- For every positive budget, one open set inside `Ioo u v` meets every nonzero
affine copy of `A` contained in that interval, provided `A` has avoidance. -/
theorem Avoidance.exists_open_small_hitting_set_in_interval {A : Set ℝ} (hA : Avoidance A)
    {u v ε : ℝ} (huv : u < v) (hε : 0 < ε) :
    ∃ G : Set ℝ, IsOpen G ∧ G ⊆ Ioo u v ∧ volume G < ENNReal.ofReal ε ∧
      ∀ a b : ℝ, a ≠ 0 → Set.image (fun x => a * x + b) A ⊆ Ioo u v →
        ∃ x ∈ A, a * x + b ∈ G := by
  obtain ⟨F, hF, _, hsmall, havoid⟩ := hA.exists_compact_almost_full_interval huv hε
  refine ⟨Ioo u v \ F, isOpen_Ioo.sdiff hF.isClosed, Set.diff_subset, hsmall, ?_⟩
  intro a b ha hsub
  obtain ⟨y, hy, hyF⟩ := Set.not_subset.mp (havoid a b ha)
  obtain ⟨x, hxA, rfl⟩ := hy
  exact ⟨x, hxA, hsub ⟨x, hxA, rfl⟩, hyF⟩

/-- All affine copies of a bounded set with slope in `[1, 2]` and translation in
`[0, 1]` lie in one fixed nonempty bounded open interval. -/
theorem exists_interval_containing_bounded_affine_copies {A : Set ℝ}
    (hA : Bornology.IsBounded A) :
    ∃ u v : ℝ, u < v ∧ ∀ a b : ℝ, a ∈ Icc (1 : ℝ) 2 → b ∈ Icc (0 : ℝ) 1 →
      Set.image (fun x => a * x + b) A ⊆ Ioo u v := by
  obtain ⟨R, hR⟩ := hA.subset_closedBall (0 : ℝ)
  let M : ℝ := max R 1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right R 1)
  have hRM : R ≤ M := le_max_left R 1
  refine ⟨-(2 * M + 2), 2 * M + 2, by linarith, ?_⟩
  intro a b ha hb y hy
  obtain ⟨x, hxA, rfl⟩ := hy
  have hxR : -R ≤ x ∧ x ≤ R := by
    simpa only [Real.closedBall_eq_Icc, zero_sub, zero_add, mem_Icc] using hR hxA
  have hxM : -M ≤ x ∧ x ≤ M := by constructor <;> linarith [hxR.1, hxR.2]
  have ha0 : 0 ≤ a := by linarith [ha.1]
  have ham : a * M ≤ 2 * M := mul_le_mul_of_nonneg_right ha.2 hM.le
  have hu : a * x ≤ a * M := mul_le_mul_of_nonneg_left hxM.2 ha0
  have hl : a * (-M) ≤ a * x := mul_le_mul_of_nonneg_left hxM.1 ha0
  constructor <;> nlinarith [hb.1, hb.2]

/-- The bounded-parameter covering reduction: for a bounded `A` with avoidance,
an arbitrarily cheap open set hits all copies with `a ∈ [1, 2]`, `b ∈ [0, 1]`. -/
theorem Avoidance.exists_open_small_hitting_set_bounded_parameters {A : Set ℝ}
    (havoid : Avoidance A) (hbounded : Bornology.IsBounded A) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : Set ℝ, IsOpen G ∧ volume G < ENNReal.ofReal ε ∧
      ∀ a b : ℝ, a ∈ Icc (1 : ℝ) 2 → b ∈ Icc (0 : ℝ) 1 →
        ∃ x ∈ A, a * x + b ∈ G := by
  obtain ⟨u, v, huv, hinterval⟩ := exists_interval_containing_bounded_affine_copies hbounded
  obtain ⟨G, hG, _, hsmall, hhit⟩ := havoid.exists_open_small_hitting_set_in_interval huv hε
  refine ⟨G, hG, hsmall, ?_⟩
  intro a b ha hb
  exact hhit a b (by linarith [ha.1]) (hinterval a b ha hb)

end Erdos120Aux
