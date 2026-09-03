import Submission.OneSidedPrimePairHole

/-!
The one-sided moment obstruction for an actual finite weighted prime-pair count.
No fourth-moment upper estimate is asserted here.
-/
namespace Erdos972NarrowPrimePairMoment

open Finset Set MeasureTheory Filter
open scoped Topology
open Erdos972Topology Erdos972OneSidedPrimePairHole

noncomputable def narrowBox (p q : ℕ) (β : ℝ) : ℝ :=
  (Set.Ioo ((q : ℝ) / p) (((q : ℝ) + 1 / 2) / p)).indicator
    (fun _ => Real.log p * Real.log q) β

noncomputable def narrowPairs (A B N : ℕ) (β : ℝ) : ℝ := by
  classical
  exact ∑ p ∈ (Finset.Ioc B N).filter Nat.Prime,
    ∑ q ∈ (Finset.Ioc 0 (A * p)).filter Nat.Prime, narrowBox p q β

noncomputable def narrowMass (A B N : ℕ) : ℝ := by
  classical
  exact ∑ p ∈ (Finset.Ioc B N).filter Nat.Prime,
    ∑ q ∈ (Finset.Ioc 0 (A * p)).filter Nat.Prime, Real.log p * Real.log q

lemma narrowBox_nonneg (p q : ℕ) (β : ℝ) : 0 ≤ narrowBox p q β :=
  Set.indicator_nonneg (fun _ _ =>
    mul_nonneg (Real.log_natCast_nonneg p) (Real.log_natCast_nonneg q)) β

lemma narrowBox_le (p q : ℕ) (β : ℝ) :
    narrowBox p q β ≤ Real.log p * Real.log q := by
  unfold narrowBox Set.indicator
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (Real.log_natCast_nonneg p) (Real.log_natCast_nonneg q)

lemma narrowPairs_nonneg (A B N : ℕ) (β : ℝ) : 0 ≤ narrowPairs A B N β := by
  exact sum_nonneg fun p _ => sum_nonneg fun q _ => narrowBox_nonneg p q β

lemma narrowPairs_le_mass (A B N : ℕ) (β : ℝ) :
    narrowPairs A B N β ≤ narrowMass A B N := by
  exact sum_le_sum fun p _ => sum_le_sum fun q _ => narrowBox_le p q β

lemma narrowMass_nonneg (A B N : ℕ) : 0 ≤ narrowMass A B N :=
  (narrowPairs_nonneg A B N 0).trans (narrowPairs_le_mass A B N 0)

lemma measurable_narrowPairs (A B N : ℕ) : Measurable (narrowPairs A B N) := by
  classical
  unfold narrowPairs narrowBox
  fun_prop (disch := exact measurableSet_Ioo)

lemma integrable_narrowBox (p q : ℕ) : Integrable (narrowBox p q) := by
  exact (integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)).integrable_indicator
    measurableSet_Ioo

lemma integrable_narrowPairs (A B N : ℕ) : Integrable (narrowPairs A B N) := by
  classical
  exact integrable_finset_sum _ fun p _ =>
    integrable_finset_sum _ fun q _ => integrable_narrowBox p q

lemma narrowPairs_eq_zero_of_not_mem {A B N : ℕ} {β : ℝ}
    (hβ : β ∉ narrowTail B N) : narrowPairs A B N β = 0 := by
  classical
  apply sum_eq_zero
  intro p hp
  obtain ⟨hpI, hpp⟩ := mem_filter.mp hp
  obtain ⟨hBp, hpN⟩ := Finset.mem_Ioc.mp hpI
  apply sum_eq_zero
  intro q hq
  obtain ⟨_, hqp⟩ := mem_filter.mp hq
  apply Set.indicator_of_notMem
  intro hbox
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hpp.pos
  exact hβ ⟨p, q, hBp, hpN, hpp, hqp,
    (div_lt_iff₀ hpR).mp hbox.1, (lt_div_iff₀ hpR).mp hbox.2⟩

/-- All the moments used below really are integrable on bounded slope
intervals, even after deleting an arbitrary set. -/
lemma integrableOn_narrowPairs_moment (A B N k : ℕ) (a b c : ℝ) (E : Set ℝ) :
    IntegrableOn (fun β => |narrowPairs A B N β - c * N| ^ k) (Set.Ioo a b \ E) := by
  have hs : volume (Set.Ioo a b \ E) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (show volume (Set.Ioo a b) ≠ ⊤ by
      rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    exact measure_mono diff_subset
  have hm : Measurable (fun β => |narrowPairs A B N β - c * N| ^ k) :=
    ((measurable_narrowPairs A B N).sub measurable_const).abs.pow_const _
  have hi : IntegrableOn (fun _β : ℝ => (narrowMass A B N + |c * N|) ^ k)
      (Set.Ioo a b \ E) := integrableOn_const hs
  apply hi.mono' hm.aestronglyMeasurable
  apply Eventually.of_forall
  intro β
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ |narrowPairs A B N β - c * N| ^ k)]
  apply pow_le_pow_left₀ (abs_nonneg _)
  calc
    _ ≤ |narrowPairs A B N β| + |c * N| := abs_sub _ _
    _ = narrowPairs A B N β + |c * N| := by rw [abs_of_nonneg (narrowPairs_nonneg A B N β)]
    _ ≤ _ := by linarith [narrowPairs_le_mass A B N β]

/-- The actual centered fourth moment of the genuine prime-pair count. -/
noncomputable def fourthMoment (A B N : ℕ) (a b : ℝ) (E : Set ℝ) : ℝ :=
  ∫ β in Set.Ioo a b \ E, |narrowPairs A B N β - (N : ℝ) / 2| ^ 4

/-- Finiteness, together with retention of half of the one-sided interval,
forces an `N^3/64` lower bound for the actual fourth moment. -/
lemma fourthMoment_lower_of_half_hole {α a b : ℝ} {A B N : ℕ} {E : Set ℝ}
    (hN : 0 < N) (hE : MeasurableSet E)
    (ha : a ≤ α - 1 / (2 * (N : ℝ))) (hb : α ≤ b)
    (hno : ∀ p ∈ primeSet α, p ≤ B)
    (hloss : volume.real (Set.Ioo (α - 1 / (2 * (N : ℝ))) α ∩ E) ≤ 1 / (4 * (N : ℝ))) :
    (N : ℝ)^3 / 64 ≤ fourthMoment A B N a b E := by
  have hm := moment_lower_of_half_hole (c := (1 / 2 : ℝ)) (k := 4) hN (by norm_num)
    hE ha hb hno hloss (fun _ h => narrowPairs_eq_zero_of_not_mem (A := A) h)
    (integrableOn_narrowPairs_moment A B N 4 a b (1 / 2) E)
  have he : (1 / 2 : ℝ) * N = (N : ℝ) / 2 := by ring
  rw [he] at hm
  have hr : ((N : ℝ) / 2)^4 / (4 * (N : ℝ)) = (N : ℝ)^3 / 64 := by
    have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
    field_simp
    ring
  simpa only [hr, fourthMoment] using hm

/-- A single bound on the finitely many input primes works at all large N,
uniformly for every measurable excluded set satisfying the local loss bound. -/
theorem finite_primeSet_forces_fourth_moment {α a b : ℝ} (A : ℕ)
    (ha : a < α) (hb : α < b) (hfin : (primeSet α).Finite) :
    ∃ B : ℕ, ∀ᶠ N : ℕ in atTop, 0 < N ∧
      ∀ E : Set ℝ, MeasurableSet E →
        volume.real (Set.Ioo (α - 1 / (2 * (N : ℝ))) α ∩ E) ≤ 1 / (4 * (N : ℝ)) →
        (N : ℝ)^3 / 64 ≤ fourthMoment A B N a b E := by
  obtain ⟨B, hB⟩ := hfin.bddAbove
  refine ⟨B, ?_⟩
  have he : ∀ᶠ N : ℕ in atTop, (1 / 2 : ℝ) / N < α - a :=
    (tendsto_order.mp (tendsto_const_div_atTop_nhds_zero_nat (1 / 2 : ℝ))).2
      (α - a) (sub_pos.mpr ha)
  filter_upwards [he, eventually_ge_atTop (1 : ℕ)] with N hsmall hN
  refine ⟨hN, fun E hE hloss => fourthMoment_lower_of_half_hole hN hE ?_ hb.le hB hloss⟩
  rw [div_div] at hsmall
  linarith

/-- The lower-tail fourth moment only measures shortages below `N/16`.
It does not require a sharp asymptotic centered at `N/2`. -/
noncomputable def deficitMoment (A B N : ℕ) (a b : ℝ) (E : Set ℝ) : ℝ :=
  ∫ β in Set.Ioo a b \ E, (max ((N : ℝ) / 16 - narrowPairs A B N β) 0) ^ 4

lemma capped_deviation_eq (x t : ℝ) : |min x t - t| = max (t - x) 0 := by
  by_cases h : x ≤ t
  · rw [min_eq_left h, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h),
      max_eq_left (sub_nonneg.mpr h)]
  · have ht : t ≤ x := (lt_of_not_ge h).le
    rw [min_eq_right ht, sub_self, abs_zero, max_eq_right (sub_nonpos.mpr ht)]

lemma integrableOn_narrowPairs_deficit (A B N : ℕ) (a b : ℝ) (E : Set ℝ) :
    IntegrableOn (fun β => (max ((N : ℝ) / 16 - narrowPairs A B N β) 0) ^ 4)
      (Set.Ioo a b \ E) := by
  have hs : volume (Set.Ioo a b \ E) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (show volume (Set.Ioo a b) ≠ ⊤ by
      rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    exact measure_mono diff_subset
  have hm : Measurable (fun β => (max ((N : ℝ) / 16 - narrowPairs A B N β) 0) ^ 4) :=
    ((measurable_const.sub (measurable_narrowPairs A B N)).max measurable_const).pow_const _
  have hi : IntegrableOn (fun _β : ℝ => ((N : ℝ) / 16) ^ 4) (Set.Ioo a b \ E) :=
    integrableOn_const hs
  apply hi.mono' hm.aestronglyMeasurable
  apply Eventually.of_forall
  intro β
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
    0 ≤ (max ((N : ℝ) / 16 - narrowPairs A B N β) 0) ^ 4)]
  apply pow_le_pow_left₀ (le_max_right _ _)
  apply max_le
  · linarith [narrowPairs_nonneg A B N β]
  · positivity

/-- A genuine-prime lower-tail obstruction, with all integrability and
support facts discharged. No upper estimate for this moment is assumed. -/
lemma deficitMoment_lower_of_half_hole {α a b : ℝ} {A B N : ℕ} {E : Set ℝ}
    (hN : 0 < N) (hE : MeasurableSet E)
    (ha : a ≤ α - 1 / (2 * (N : ℝ))) (hb : α ≤ b)
    (hno : ∀ p ∈ primeSet α, p ≤ B)
    (hloss : volume.real (Set.Ioo (α - 1 / (2 * (N : ℝ))) α ∩ E) ≤ 1 / (4 * (N : ℝ))) :
    (N : ℝ)^3 / 262144 ≤ deficitMoment A B N a b E := by
  let F : ℝ → ℝ := fun β => min (narrowPairs A B N β) ((N : ℝ) / 16)
  have he : (1 / 16 : ℝ) * N = (N : ℝ) / 16 := by ring
  have hzero : ∀ β ∉ narrowTail B N, F β = 0 := by
    intro β hβ
    dsimp [F]
    rw [narrowPairs_eq_zero_of_not_mem hβ, min_eq_left (by positivity)]
  have hint : IntegrableOn (fun β => |F β - (1 / 16 : ℝ) * N| ^ 4) (Set.Ioo a b \ E) := by
    simpa only [F, he, capped_deviation_eq] using integrableOn_narrowPairs_deficit A B N a b E
  have hm := moment_lower_of_half_hole (c := (1 / 16 : ℝ)) (k := 4) hN (by norm_num)
    hE ha hb hno hloss hzero hint
  rw [he] at hm
  have hr : ((N : ℝ) / 16)^4 / (4 * (N : ℝ)) = (N : ℝ)^3 / 262144 := by
    have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
    field_simp
    ring
  simpa only [hr, F, capped_deviation_eq, deficitMoment] using hm

/-- The fixed input threshold supplied by finiteness also gives the
one-sided moment obstruction at every large cutoff, for all admissible E. -/
theorem finite_primeSet_forces_deficit_moment {α a b : ℝ} (A : ℕ)
    (ha : a < α) (hb : α < b) (hfin : (primeSet α).Finite) :
    ∃ B : ℕ, ∀ᶠ N : ℕ in atTop, 0 < N ∧
      ∀ E : Set ℝ, MeasurableSet E →
        volume.real (Set.Ioo (α - 1 / (2 * (N : ℝ))) α ∩ E) ≤ 1 / (4 * (N : ℝ)) →
        (N : ℝ)^3 / 262144 ≤ deficitMoment A B N a b E := by
  obtain ⟨B, hB⟩ := hfin.bddAbove
  refine ⟨B, ?_⟩
  have he : ∀ᶠ N : ℕ in atTop, (1 / 2 : ℝ) / N < α - a :=
    (tendsto_order.mp (tendsto_const_div_atTop_nhds_zero_nat (1 / 2 : ℝ))).2
      (α - a) (sub_pos.mpr ha)
  filter_upwards [he, eventually_ge_atTop (1 : ℕ)] with N hsmall hN
  refine ⟨hN, fun E hE hloss => deficitMoment_lower_of_half_hole hN hE ?_ hb.le hB hloss⟩
  rw [div_div] at hsmall
  linarith

/-- The excluded rational neighborhoods cannot simply be omitted: the
integer slope two alone forces a cubic lower-tail moment on `(1,3)`. -/
lemma global_deficit_cubic_lower (A : ℕ) {N : ℕ} (hN : 0 < N) :
    (N : ℝ)^3 / 262144 ≤ deficitMoment A 0 N 1 3 ∅ := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hno : ∀ p ∈ primeSet (2 : ℝ), p ≤ 0 := by
    intro p hp
    obtain ⟨hpp, hq⟩ := hp
    change (⌊((2 : ℕ) : ℝ) * (p : ℝ)⌋₊).Prime at hq
    rw [← Nat.cast_mul, Nat.floor_natCast] at hq
    exact (Nat.not_prime_mul (by decide : (2 : ℕ) ≠ 1) hpp.ne_one hq).elim
  apply deficitMoment_lower_of_half_hole (α := 2) hN MeasurableSet.empty ?_
    (by norm_num) hno (by simp)
  have hr : 1 / (2 * (N : ℝ)) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by linarith)
  linarith

#print axioms global_deficit_cubic_lower
#print axioms integrableOn_narrowPairs_deficit
#print axioms deficitMoment_lower_of_half_hole
#print axioms finite_primeSet_forces_deficit_moment
#print axioms narrowPairs_eq_zero_of_not_mem
#print axioms integrableOn_narrowPairs_moment
#print axioms fourthMoment_lower_of_half_hole
#print axioms finite_primeSet_forces_fourth_moment

end Erdos972NarrowPrimePairMoment
