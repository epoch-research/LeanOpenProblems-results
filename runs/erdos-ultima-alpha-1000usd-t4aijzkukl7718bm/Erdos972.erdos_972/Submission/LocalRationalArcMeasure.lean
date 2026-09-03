import FormalConjecturesUtil

/-!
Local measure bounds for finite rational arcs. These are geometric estimates;
no prime-pair moment estimate is asserted.
-/
namespace Erdos972LocalRationalArcMeasure

open Set Finset MeasureTheory

lemma spaced_card_bound {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (hx : ∀ i ∈ s, a ≤ x i ∧ x i ≤ b)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |x i - x j|) :
    (s.card : ℝ) ≤ (b - a) / δ + 1 := by
  classical
  let U : ι → Set ℝ := fun i => Ioo (x i - δ / 2) (x i + δ / 2)
  have hdisj : Set.PairwiseDisjoint (↑s : Set ι) U := by
    intro i hi j hj hij
    apply Set.disjoint_left.mpr
    intro z hzi hzj
    have hdist : |x i - x j| < δ := by
      change x i - δ / 2 < z ∧ z < x i + δ / 2 at hzi
      change x j - δ / 2 < z ∧ z < x j + δ / 2 at hzj
      apply abs_lt.mpr
      constructor <;> linarith
    exact (not_lt_of_ge (hsep i hi j hj hij)) hdist
  have hu (i : ι) : volume.real (U i) = δ := by
    dsimp only [U]
    rw [Real.volume_real_Ioo,
      show x i + δ / 2 - (x i - δ / 2) = δ by ring,
      max_eq_left hδ.le]
  have he : volume.real (⋃ i ∈ s, U i) = (s.card : ℝ) * δ := by
    rw [measureReal_biUnion_finset hdisj
      (fun _ _ => measurableSet_Ioo)
      (fun i _ => by dsimp [U]; rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)]
    simp only [hu, sum_const, nsmul_eq_mul]
  have hsub : (⋃ i ∈ s, U i) ⊆ Ioo (a - δ / 2) (b + δ / 2) := by
    intro z hz
    obtain ⟨i, hi, hz⟩ := mem_iUnion₂.mp hz
    obtain ⟨hlo, hhi⟩ := hx i hi
    change x i - δ / 2 < z ∧ z < x i + δ / 2 at hz
    constructor <;> linarith
  have hm := measureReal_mono hsub
    (show volume (Ioo (a - δ / 2) (b + δ / 2)) ≠ ⊤ by
      rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  rw [he, Real.volume_real_Ioo,
    show b + δ / 2 - (a - δ / 2) = b - a + δ by ring,
    max_eq_left (by linarith)] at hm
  have heq : ((b - a) / δ + 1) * δ = b - a + δ := by
    field_simp
  nlinarith

lemma rational_separation {r s : ℚ} (hne : r ≠ s) :
    1 / ((r.den : ℝ) * s.den) ≤ |(r : ℝ) - s| := by
  have hd₁ : (0 : ℝ) < r.den := Nat.cast_pos.mpr r.pos
  have hd₂ : (0 : ℝ) < s.den := Nat.cast_pos.mpr s.pos
  have hn : r.num * (s.den : ℤ) - s.num * (r.den : ℤ) ≠ 0 := by
    apply sub_ne_zero.mpr
    exact mt Rat.eq_iff_mul_eq_mul.mpr hne
  have hnum : (1 : ℝ) ≤ |(r.num : ℝ) * s.den - (s.num : ℝ) * r.den| := by
    exact_mod_cast Int.one_le_abs hn
  have hr : (r : ℝ) = (r.num : ℝ) / r.den := by
    exact_mod_cast r.num_div_den.symm
  have hs : (s : ℝ) = (s.num : ℝ) / s.den := by
    exact_mod_cast s.num_div_den.symm
  have he : (r : ℝ) - s =
      ((r.num : ℝ) * s.den - (s.num : ℝ) * r.den) / ((r.den : ℝ) * s.den) := by
    rw [hr, hs]
    field_simp
  rw [he, abs_div, abs_of_pos (mul_pos hd₁ hd₂)]
  exact div_le_div_of_nonneg_right hnum (by positivity)

noncomputable def rationalArc (Q : ℝ) (r : ℚ) : Set ℝ :=
  Icc ((r : ℝ) - 1 / (Q * r.den)) ((r : ℝ) + 1 / (Q * r.den))

lemma rationalArc_measure {Q : ℝ} (hQ : 0 < Q) (r : ℚ) :
    volume.real (rationalArc Q r) = 2 / (Q * r.den) := by
  rw [rationalArc, Real.volume_real_Icc,
    show (r : ℝ) + 1 / (Q * r.den) - ((r : ℝ) - 1 / (Q * r.den)) =
      2 / (Q * r.den) by ring,
    max_eq_left (by positivity)]

/-- In a denominator band `[D,2D]`, the local arc measure consists of an
interval-length term and explicit endpoint terms. The estimate is uniform
in the finite rational set and the position of the interval. -/
theorem rational_band_local_measure (S : Finset ℚ) {a b D Q : ℝ}
    (hab : a ≤ b) (hD : 0 < D) (hQ : 0 < Q)
    (hden : ∀ r ∈ S, D ≤ (r.den : ℝ) ∧ (r.den : ℝ) ≤ 2 * D) :
    volume.real (Ioo a b ∩ ⋃ r ∈ S, rationalArc Q r) ≤
      (8 * D / Q) * (b - a) + 16 / Q ^ 2 + 2 / (D * Q) := by
  classical
  let R : ℝ := 1 / (Q * D)
  let δ : ℝ := 1 / (4 * D ^ 2)
  let T : Finset ℚ := S.filter (fun r => a - R ≤ (r : ℝ) ∧ (r : ℝ) ≤ b + R)
  have hR : 0 < R := by dsimp [R]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hradius (r : ℚ) (hr : r ∈ S) : 1 / (Q * (r.den : ℝ)) ≤ R := by
    exact one_div_le_one_div_of_le (mul_pos hQ hD)
      (mul_le_mul_of_nonneg_left (hden r hr).1 hQ.le)
  have hsub : (Ioo a b ∩ ⋃ r ∈ S, rationalArc Q r) ⊆ ⋃ r ∈ T, rationalArc Q r := by
    intro β hβ
    obtain ⟨r, hr, hβr⟩ := mem_iUnion₂.mp hβ.2
    have hbds : (r : ℝ) - 1 / (Q * r.den) ≤ β ∧ β ≤ (r : ℝ) + 1 / (Q * r.den) := hβr
    have hrad := hradius r hr
    apply mem_iUnion₂.mpr
    refine ⟨r, mem_filter.mpr ⟨hr, ?_⟩, hβr⟩
    constructor <;> linarith [hβ.1.1, hβ.1.2]
  have hsep : ∀ r ∈ T, ∀ s ∈ T, r ≠ s → δ ≤ |(r : ℝ) - s| := by
    intro r hr s hs hrs
    have hrS := (mem_filter.mp hr).1
    have hsS := (mem_filter.mp hs).1
    have hprod : (r.den : ℝ) * s.den ≤ 4 * D ^ 2 := by
      have h := mul_le_mul (hden r hrS).2 (hden s hsS).2
        (Nat.cast_nonneg _) (by positivity : (0 : ℝ) ≤ 2 * D)
      nlinarith
    exact (one_div_le_one_div_of_le
      (mul_pos (Nat.cast_pos.mpr r.pos) (Nat.cast_pos.mpr s.pos)) hprod).trans
      (rational_separation hrs)
  have hcard := spaced_card_bound T (fun r : ℚ => (r : ℝ))
    (show a - R ≤ b + R by linarith) hδ
    (fun r hr => (mem_filter.mp hr).2) hsep
  have hfin : volume (⋃ r ∈ T, rationalArc Q r) ≠ ⊤ := by
    apply (T.isCompact_biUnion (fun r _ => isCompact_Icc)).measure_lt_top.ne
  have hm := (measureReal_mono hsub hfin).trans
    (measureReal_biUnion_finset_le T (rationalArc Q))
  have hsum : (∑ r ∈ T, volume.real (rationalArc Q r)) ≤ (T.card : ℝ) * (2 * R) := by
    calc
      _ ≤ ∑ _r ∈ T, 2 * R := by
        apply sum_le_sum
        intro r hr
        rw [rationalArc_measure hQ]
        have hh := hradius r (mem_filter.mp hr).1
        convert mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 2) using 1; ring
      _ = _ := by simp
  have hbound := hm.trans hsum
  calc
    _ ≤ (T.card : ℝ) * (2 * R) := hbound
    _ ≤ (((b + R) - (a - R)) / δ + 1) * (2 * R) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by
      dsimp [R, δ]
      field_simp
      ring

#print axioms spaced_card_bound
#print axioms rational_separation
#print axioms rational_band_local_measure

end Erdos972LocalRationalArcMeasure
