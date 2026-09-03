import Submission.TailTopology

/-!
A quantitative one-sided consequence of a finite prime-pair set.
This does not prove that the exceptional set is empty.
-/
namespace Erdos972OneSidedPrimePairHole

open Set MeasureTheory Filter
open scoped Topology
open Erdos972Topology

/-- A finite-input prime-pair tail with half the original output window. -/
def narrowTail (B N : ℕ) : Set ℝ :=
  {β | ∃ p q : ℕ, B < p ∧ p ≤ N ∧ p.Prime ∧ q.Prime ∧
    (q : ℝ) < β * p ∧ β * p < (q : ℝ) + 1 / 2}

lemma isOpen_narrowTail (B N : ℕ) : IsOpen (narrowTail B N) := by
  rw [isOpen_iff_mem_nhds]
  rintro β ⟨p, q, hBp, hpN, hp, hq, hlo, hhi⟩
  have ho : IsOpen ((fun x : ℝ => x * p) ⁻¹' Ioo (q : ℝ) (q + 1 / 2)) :=
    isOpen_Ioo.preimage (continuous_id.mul continuous_const)
  apply Filter.mem_of_superset (ho.mem_nhds ⟨hlo, hhi⟩)
  intro γ hγ
  exact ⟨p, q, hBp, hpN, hp, hq, hγ.1, hγ.2⟩

/-- Moving the slope to the right by less than `1/(2N)` transfers a
half-window pair with input at most `N` to an original floor-prime pair. -/
lemma transfer_from_left {α β : ℝ} {N p q : ℕ} (hN : 0 < N)
    (hpN : p ≤ N) (hp : p.Prime) (hq : q.Prime)
    (hβα : β < α) (hclose : α - 1 / (2 * (N : ℝ)) < β)
    (hlo : (q : ℝ) < β * p) (hhi : β * p < (q : ℝ) + 1 / 2) :
    p ∈ primeSet α := by
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hpNR : (p : ℝ) ≤ N := Nat.cast_le.mpr hpN
  have hd : 0 < α - β := sub_pos.mpr hβα
  have hsmall : (α - β) * (N : ℝ) < 1 / 2 := by
    have he : α - β < 1 / (2 * (N : ℝ)) := by linarith
    have hh := (lt_div_iff₀ (show (0 : ℝ) < 2 * N by positivity)).mp he
    nlinarith
  have hdiff : (α - β) * (p : ℝ) < 1 / 2 :=
    (mul_le_mul_of_nonneg_left hpNR hd.le).trans_lt hsmall
  have hlow : (q : ℝ) ≤ α * p := by nlinarith
  have hupp : α * p < (q : ℝ) + 1 := by nlinarith
  have hf : ⌊α * p⌋₊ = q :=
    (Nat.floor_eq_iff' hq.ne_zero).mpr ⟨hlow, hupp⟩
  exact ⟨hp, by simpa only [hf] using hq⟩

/-- No new pairs at one slope forces an entire one-sided interval of
missing half-window pairs, rather than merely a missing point. -/
lemma left_interval_subset_compl {α : ℝ} {B N : ℕ} (hN : 0 < N)
    (hno : ∀ p ∈ primeSet α, p ≤ B) :
    Ioo (α - 1 / (2 * (N : ℝ))) α ⊆ (narrowTail B N)ᶜ := by
  intro β hβ hpair
  obtain ⟨p, q, hBp, hpN, hp, hq, hlo, hhi⟩ := hpair
  exact (not_le_of_gt hBp) (hno p
    (transfer_from_left hN hpN hp hq hβ.2 hβ.1 hlo hhi))

lemma left_interval_measure {α : ℝ} {N : ℕ} (hN : 0 < N) :
    volume.real (Ioo (α - 1 / (2 * (N : ℝ))) α) = 1 / (2 * (N : ℝ)) := by
  rw [Real.volume_real_Ioo,
    show α - (α - 1 / (2 * (N : ℝ))) = 1 / (2 * (N : ℝ)) by ring,
    max_eq_left (by positivity)]

/-- A finite-scale lower bound on the measure of the missing half-window
pairs inside any ambient interval containing the one-sided hole. -/
lemma missing_measure_lower {a b α : ℝ} {B N : ℕ} (hN : 0 < N)
    (ha : a ≤ α - 1 / (2 * (N : ℝ))) (hb : α ≤ b)
    (hno : ∀ p ∈ primeSet α, p ≤ B) :
    1 / (2 * (N : ℝ)) ≤ volume.real (Ioo a b \ narrowTail B N) := by
  have hsub : Ioo (α - 1 / (2 * (N : ℝ))) α ⊆ Ioo a b \ narrowTail B N := by
    intro β hβ
    exact ⟨⟨ha.trans_lt hβ.1, hβ.2.trans_le hb⟩,
      left_interval_subset_compl hN hno hβ⟩
  have hfin : volume (Ioo a b \ narrowTail B N) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (show volume (Ioo a b) ≠ ⊤ by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_ne_top)
    exact measure_mono diff_subset
  simpa only [left_interval_measure hN] using measureReal_mono hsub hfin

/-- For a finite prime-pair set, the same input threshold works at every
sufficiently large scale. The lower bound is of order `1/N`, not just
positivity of the exceptional measure. -/
theorem finite_primeSet_forces_missing_measure {α a b : ℝ}
    (ha : a < α) (hb : α < b) (hfin : (primeSet α).Finite) :
    ∃ B : ℕ, ∀ᶠ N : ℕ in atTop,
      0 < N ∧ 1 / (2 * (N : ℝ)) ≤ volume.real (Ioo a b \ narrowTail B N) := by
  obtain ⟨B, hB⟩ := hfin.bddAbove
  refine ⟨B, ?_⟩
  have he : ∀ᶠ N : ℕ in atTop, (1 / 2 : ℝ) / N < α - a :=
    (tendsto_order.mp (tendsto_const_div_atTop_nhds_zero_nat (1 / 2 : ℝ))).2
      (α - a) (sub_pos.mpr ha)
  filter_upwards [he, eventually_ge_atTop (1 : ℕ)] with N hsmall hN
  have hN0 : 0 < N := hN
  refine ⟨hN0, missing_measure_lower hN0 ?_ hb.le hB⟩
  rw [div_div] at hsmall
  linarith

/-- A hypothetical moment estimate must also control the one-sided hole.
The excluded set `E` may vary with the scale, but this assertion requires
the whole hole to lie outside it. No moment upper bound is claimed. -/
lemma moment_lower_outside {a b α c : ℝ} {B N k : ℕ} {E : Set ℝ}
    {F : ℝ → ℝ} (hN : 0 < N) (hc : 0 ≤ c)
    (ha : a ≤ α - 1 / (2 * (N : ℝ))) (hb : α ≤ b)
    (hno : ∀ p ∈ primeSet α, p ≤ B)
    (hclean : ∀ β ∈ Ioo (α - 1 / (2 * (N : ℝ))) α, β ∉ E)
    (hzero : ∀ β ∉ narrowTail B N, F β = 0)
    (hF : IntegrableOn (fun β => |F β - c * N| ^ k) (Ioo a b \ E)) :
    (c * (N : ℝ)) ^ k / (2 * (N : ℝ)) ≤
      ∫ β in Ioo a b \ E, |F β - c * N| ^ k := by
  have hsub : Ioo (α - 1 / (2 * (N : ℝ))) α ⊆ Ioo a b \ E := by
    intro β hβ
    exact ⟨⟨ha.trans_lt hβ.1, hβ.2.trans_le hb⟩, hclean β hβ⟩
  have heq : (∫ β in Ioo (α - 1 / (2 * (N : ℝ))) α, |F β - c * N| ^ k) =
      (c * (N : ℝ)) ^ k / (2 * (N : ℝ)) := by
    calc
      _ = ∫ _β in Ioo (α - 1 / (2 * (N : ℝ))) α, (c * (N : ℝ)) ^ k := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro β hβ
        dsimp only
        rw [hzero β (left_interval_subset_compl hN hno hβ), zero_sub, abs_neg,
          abs_of_nonneg (mul_nonneg hc (Nat.cast_nonneg N))]
      _ = _ := by
        rw [setIntegral_const, left_interval_measure hN]
        simp only [smul_eq_mul]
        ring
  rw [← heq]
  exact setIntegral_mono_set hF (Eventually.of_forall (fun β => by positivity))
    (Eventually.of_forall hsub)

/-- The moment obstruction only needs the part of the hole left after
removing the excluded set. In particular, complete disjointness is unnecessary. -/
lemma moment_lower_remaining {a b α c : ℝ} {B N k : ℕ} {E : Set ℝ}
    {F : ℝ → ℝ} (hN : 0 < N) (hc : 0 ≤ c) (hE : MeasurableSet E)
    (ha : a ≤ α - 1 / (2 * (N : ℝ))) (hb : α ≤ b)
    (hno : ∀ p ∈ primeSet α, p ≤ B)
    (hzero : ∀ β ∉ narrowTail B N, F β = 0)
    (hF : IntegrableOn (fun β => |F β - c * N| ^ k) (Ioo a b \ E)) :
    volume.real (Ioo (α - 1 / (2 * (N : ℝ))) α \ E) * (c * (N : ℝ)) ^ k ≤
      ∫ β in Ioo a b \ E, |F β - c * N| ^ k := by
  have hsub : Ioo (α - 1 / (2 * (N : ℝ))) α \ E ⊆ Ioo a b \ E := by
    intro β hβ
    exact ⟨⟨ha.trans_lt hβ.1.1, hβ.1.2.trans_le hb⟩, hβ.2⟩
  have heq : (∫ β in Ioo (α - 1 / (2 * (N : ℝ))) α \ E, |F β - c * N| ^ k) =
      volume.real (Ioo (α - 1 / (2 * (N : ℝ))) α \ E) * (c * (N : ℝ)) ^ k := by
    calc
      _ = ∫ _β in Ioo (α - 1 / (2 * (N : ℝ))) α \ E, (c * (N : ℝ)) ^ k := by
        apply setIntegral_congr_fun (measurableSet_Ioo.diff hE)
        intro β hβ
        dsimp only
        rw [hzero β (left_interval_subset_compl hN hno hβ.1), zero_sub, abs_neg,
          abs_of_nonneg (mul_nonneg hc (Nat.cast_nonneg N))]
      _ = _ := by rw [setIntegral_const]; rfl
  rw [← heq]
  exact setIntegral_mono_set hF (Eventually.of_forall (fun β => by positivity))
    (Eventually.of_forall hsub)

/-- Losing at most half of the hole still gives a moment lower bound
of order `N^(k-1)`. The local measure assumption is not replaced by a
qualitative assertion that the global excluded measure tends to zero. -/
lemma moment_lower_of_half_hole {a b α c : ℝ} {B N k : ℕ} {E : Set ℝ}
    {F : ℝ → ℝ} (hN : 0 < N) (hc : 0 ≤ c) (hE : MeasurableSet E)
    (ha : a ≤ α - 1 / (2 * (N : ℝ))) (hb : α ≤ b)
    (hno : ∀ p ∈ primeSet α, p ≤ B)
    (hloss : volume.real (Ioo (α - 1 / (2 * (N : ℝ))) α ∩ E) ≤ 1 / (4 * (N : ℝ)))
    (hzero : ∀ β ∉ narrowTail B N, F β = 0)
    (hF : IntegrableOn (fun β => |F β - c * N| ^ k) (Ioo a b \ E)) :
    (c * (N : ℝ)) ^ k / (4 * (N : ℝ)) ≤
      ∫ β in Ioo a b \ E, |F β - c * N| ^ k := by
  have hadd := measureReal_inter_add_diff (μ := volume)
    (s := Ioo (α - 1 / (2 * (N : ℝ))) α) hE
    (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  rw [left_interval_measure hN] at hadd
  have hremain : 1 / (4 * (N : ℝ)) ≤
      volume.real (Ioo (α - 1 / (2 * (N : ℝ))) α \ E) := by
    have he : 1 / (2 * (N : ℝ)) = 2 * (1 / (4 * (N : ℝ))) := by ring
    linarith
  calc
    _ = (1 / (4 * (N : ℝ))) * (c * (N : ℝ)) ^ k := by ring
    _ ≤ volume.real (Ioo (α - 1 / (2 * (N : ℝ))) α \ E) * (c * (N : ℝ)) ^ k :=
      mul_le_mul_of_nonneg_right hremain (by positivity)
    _ ≤ _ := moment_lower_remaining hN hc hE ha hb hno hzero hF

#print axioms moment_lower_remaining
#print axioms moment_lower_of_half_hole
#print axioms moment_lower_outside
#print axioms transfer_from_left
#print axioms left_interval_subset_compl
#print axioms finite_primeSet_forces_missing_measure

end Erdos972OneSidedPrimePairHole
