import Submission.PopulationSensitiveRowVariance
import Submission.ConditionalSurvivorBennett
import Submission.SoftEndpointReduction

/-! Exact insertion and nonlinear Laplace bounds using the actual old core
population. Neither row independence within the core nor an unproved
critical-scale concentration hypothesis is used. -/
namespace Erdos970.GapAverages
open Finset Real Erdos970.Resampling Erdos970.CoverFibers

lemma phaseSurvivors_extend_eq_avoidClass (P : Finset ℕ) (p : ℕ) (hp : p ∉ P)
    (m : ℕ) (r : Phase P) (a : Fin p) :
    phaseSurvivors (insert p P) m (extendPhase P p r a) =
      avoidClass (phaseSurvivors P m r) p a := by
  classical
  ext x
  simp only [phaseSurvivors, avoidClass, mem_filter]
  constructor
  · rintro ⟨hxm, hx⟩
    refine ⟨⟨hxm, ?_⟩, ?_⟩
    · intro q
      simpa only [extendPhase_old P p hp r a q] using
        hx ⟨q.val, mem_insert_of_mem q.property⟩
    · simpa only [extendPhase_new] using hx ⟨p, mem_insert_self p P⟩
  · rintro ⟨⟨hxm, hxo⟩, hxn⟩
    refine ⟨hxm, ?_⟩
    intro q
    by_cases hq : q.val = p
    · have he : q = ⟨p, mem_insert_self p P⟩ := Subtype.ext hq
      cases he
      simpa only [extendPhase_new] using hxn
    · have hqP : q.val ∈ P := (mem_insert.mp q.property).resolve_left hq
      have he : q = ⟨(⟨q.val,hqP⟩ : P).val, mem_insert_of_mem hqP⟩ := rfl
      rw [he, extendPhase_old P p hp r a ⟨q.val,hqP⟩]
      exact hxo ⟨q.val,hqP⟩

/-- Deletion of the new row is exact, including boundary and rounding effects. -/
theorem intervalCount_extend_eq_sub_row (P : Finset ℕ) (p : ℕ) (hp : p ∉ P)
    (m : ℕ) (r : Phase P) (a : Fin p) :
    intervalCount (insert p P) m (extendPhase P p r a) =
      intervalCount P m r - rowCount P m p a r := by
  rw [← phaseSurvivors_card, phaseSurvivors_extend_eq_avoidClass P p hp m r a]
  change remainingCount (phaseSurvivors P m r) p a = _
  rw [remainingCount_eq, phaseSurvivors_card, ← rowCount_eq_classHits]

/-- The Laplace transform over the new prime is conditional on the entire old
phase. This identity does not average away the dependence of its rows. -/
theorem countLaplace_insert_exact (P : Finset ℕ) (p : ℕ) (hp : p ∉ P)
    (m : ℕ) (t : ℝ) :
    countLaplace (insert p P) t m =
      phaseMean P (fun r => residueMean p (fun a =>
        exp (-t * (intervalCount P m r - rowCount P m p a r)))) := by
  unfold countLaplace
  rw [phaseMean_insert P p hp]
  simp_rw [intervalCount_extend_eq_sub_row P p hp m]
  rfl

lemma exp_chord_of_cap (t B x : ℝ) (hB : 0 < B) (hx : 0 ≤ x) (hxB : x ≤ B) :
    exp (t*x) ≤ 1 + (exp (t*B)-1)/B*x := by
  have hx1 : x/B ≤ 1 := (div_le_one hB).mpr hxB
  have hh := convexOn_exp.2 (show (0 : ℝ) ∈ Set.univ from trivial)
    (show t*B ∈ Set.univ from trivial) (show 0 ≤ 1-x/B by linarith)
    (div_nonneg hx hB.le) (show 1-x/B+x/B=1 by ring)
  simp only [smul_eq_mul, exp_zero, mul_zero, zero_add, mul_one] at hh
  convert hh using 1 <;> field_simp <;> ring

/-- An unconditional nonlinear one-step bound from a uniform row cap. -/
theorem row_deletion_laplace_le_cap (P : Finset ℕ) (m p : ℕ) (hp : 0 < p)
    (r : Phase P) (B t : ℝ) (hB : 0 < B)
    (hcap : ∀ a : Fin p, rowCount P m p a r ≤ B) :
    residueMean p (fun a => exp (-t * (intervalCount P m r - rowCount P m p a r))) ≤
      exp (-t * intervalCount P m r) *
        (1 + ((exp (t*B)-1)/(B*p))*intervalCount P m r) := by
  have hh := residueMean_mono p (fun a =>
    exp_chord_of_cap t B (rowCount P m p a r) hB
      (rowCount_nonneg' P m p a r) (hcap a))
  rw [residueMean_add, residueMean_const p hp, residueMean_mul,
    rowCount_mean P m p hp r] at hh
  have he (a : Fin p) : exp (-t * (intervalCount P m r - rowCount P m p a r)) =
      exp (-t * intervalCount P m r) * exp (t * rowCount P m p a r) := by
    rw [← exp_add]
    congr 1
    ring
  simp_rw [he]
  rw [residueMean_mul]
  convert mul_le_mul_of_nonneg_left hh (exp_pos _).le using 1 <;> ring

/-- Transport in the Laplace parameter. Positivity of the transported
parameter is not asserted, and must be checked before iterating any decay
claim. This is not a uniform lower-tail theorem. -/
theorem countLaplace_insert_le_transport (P : Finset ℕ) (p : ℕ) (hp : p ∉ P)
    (hp0 : 0 < p) (m : ℕ) (B t : ℝ) (hB : 0 < B)
    (hcap : ∀ (r : Phase P) (a : Fin p), rowCount P m p a r ≤ B) :
    countLaplace (insert p P) t m ≤
      countLaplace P (t-(exp (t*B)-1)/(B*p)) m := by
  rw [countLaplace_insert_exact P p hp m t]
  apply phaseMean_mono
  intro r
  apply (row_deletion_laplace_le_cap P m p hp0 r B t hB (hcap r)).trans
  have hh := mul_le_mul_of_nonneg_left
    (add_one_le_exp (((exp (t*B)-1)/(B*p))*intervalCount P m r)) (exp_pos (-t*intervalCount P m r)).le
  rw [← exp_add] at hh
  convert hh using 1 <;> ring

/-- Bennett's centered form keeps the negative quadratic population term.
The expectation over old phases has not been replaced by an exponential of
its unweighted mean variance. -/
theorem row_deletion_laplace_le_population_quadratic (P : Finset ℕ)
    (m p : ℕ) (hp : 0 < p) (r : Phase P) (B t : ℝ) (ht : 0 ≤ t)
    (hcap : ∀ a : Fin p, rowCount P m p a r ≤ B) :
    residueMean p (fun a => exp (-t * (intervalCount P m r - rowCount P m p a r))) ≤
      exp (-t*(1-1/(p : ℝ))*intervalCount P m r +
        bennettFactor t B * (B*(intervalCount P m r / p) -
          (intervalCount P m r / p)^2)) := by
  let N := intervalCount P m r
  have hN : 0 ≤ N := by
    dsimp only [N]
    rw [← phaseSurvivors_card]
    positivity
  have hmean : residueMean p (fun a => rowCount P m p a r - N/p) = 0 := by
    rw [residueMean_sub, rowCount_mean P m p hp r, residueMean_const p hp]
    exact sub_self _
  have hu (a : Fin p) : rowCount P m p a r - N/p ≤ B :=
    (sub_le_self _ (div_nonneg hN (Nat.cast_nonneg _))).trans (hcap a)
  have hh := residueMean_exp_bennett p hp
    (fun a => rowCount P m p a r - N/p) t B ht hmean hu
  have he (a : Fin p) : exp (-t*(N-rowCount P m p a r)) =
      exp (-t*(1-1/(p : ℝ))*N) * exp (t*(rowCount P m p a r-N/p)) := by
    rw [← exp_add]
    congr 1
    ring
  change residueMean p (fun a => exp (-t*(N-rowCount P m p a r))) ≤ _
  simp_rw [he]
  rw [residueMean_mul]
  have hb := rowConditionalVariance_le_cap_count P m p hp r B hcap
  have hh' := hh.trans (exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left hb (bennettFactor_nonneg t B)))
  have hmul := mul_le_mul_of_nonneg_left hh' (exp_pos (-t*(1-1/(p : ℝ))*N)).le
  rwa [← exp_add] at hmul

/-- The quadratic bound is averaged with its full nonlinear dependence on the
old population; it is not a closed estimate solely in terms of the mean. -/
theorem countLaplace_insert_le_population_quadratic (P : Finset ℕ)
    (p : ℕ) (hp : p ∉ P) (hp0 : 0 < p) (m : ℕ) (B t : ℝ) (ht : 0 ≤ t)
    (hcap : ∀ (r : Phase P) (a : Fin p), rowCount P m p a r ≤ B) :
    countLaplace (insert p P) t m ≤
      phaseMean P (fun r => exp (-t*(1-1/(p : ℝ))*intervalCount P m r +
        bennettFactor t B * (B*(intervalCount P m r / p) -
          (intervalCount P m r / p)^2))) := by
  rw [countLaplace_insert_exact P p hp m t]
  exact phaseMean_mono P (fun r =>
    row_deletion_laplace_le_population_quadratic P m p hp0 r B t ht (hcap r))

#print axioms countLaplace_insert_exact
#print axioms countLaplace_insert_le_transport
#print axioms row_deletion_laplace_le_population_quadratic
#print axioms countLaplace_insert_le_population_quadratic
end Erdos970.GapAverages
