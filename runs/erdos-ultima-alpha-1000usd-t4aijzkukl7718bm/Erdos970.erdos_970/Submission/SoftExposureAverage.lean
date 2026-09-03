import Submission.SoftExposureTree
import Submission.RowConditionalVariance

/-! Averaging the soft exposure tree over independent prime coordinates.
Conditional survivor populations are allowed to be arbitrary finite sets. -/
namespace Erdos970.SoftExposure
open Finset Real GapAverages Resampling CoverFibers

lemma phaseResidues_extend_old (P : Finset ℕ) (p : ℕ) (hp : p ∉ P)
    (r : Phase P) (a : Fin p) (q : ℕ) (hq : q ∈ P) :
    phaseResidues (insert p P) (extendPhase P p r a) q = phaseResidues P r q := by
  rw [phaseResidues_mem (insert p P) _ ⟨q, mem_insert_of_mem hq⟩,
    extendPhase_old P p hp r a ⟨q, hq⟩, phaseResidues_mem P r ⟨q, hq⟩]

lemma phaseResidues_extend_new (P : Finset ℕ) (p : ℕ) (r : Phase P) (a : Fin p) :
    phaseResidues (insert p P) (extendPhase P p r a) p = a.val := by
  rw [phaseResidues_mem (insert p P) _ ⟨p, mem_insert_self _ _⟩, extendPhase_new]

lemma avoid_extend (U P : Finset ℕ) (p : ℕ) (r : Phase P) (a : Fin p) :
    avoid U p (phaseResidues (insert p P) (extendPhase P p r a)) = avoidClass U p a := by
  simp only [avoid, avoidClass, phaseResidues_extend_new, Nat.ModEq, Nat.mod_eq_of_lt a.isLt]

lemma hitFraction_extend (U P : Finset ℕ) (p : ℕ) (r : Phase P) (a : Fin p) :
    hitFraction U p (phaseResidues (insert p P) (extendPhase P p r a)) = classHits U p a / U.card := by
  simp only [hitFraction, classHits_card, phaseResidues_extend_new, Nat.ModEq, Nat.mod_eq_of_lt a.isLt]

lemma hitFraction_average_le (U : Finset ℕ) (p : ℕ) (hp : 0 < p) :
    residueMean p (fun a => classHits U p a / U.card) ≤ (p : ℝ)⁻¹ := by
  rw [residueMean_div, classHits_mean U p hp]
  by_cases hU : U.card = 0
  · simp [hU]
  · have hUR : (U.card : ℝ) ≠ 0 := by exact_mod_cast hU
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
    apply le_of_eq
    field_simp

/-- One prime is tested against a uniformly selected old position. Even if
its successful deletion changes the population arbitrarily, a uniform bound
on the continuation costs at most 1/p after averaging that coordinate. -/
lemma step_mean_le (j : ℕ) (U P : Finset ℕ) (p : ℕ) (hp : p ∉ P)
    (hpp : 0 < p)
    (hcont : ∀ S : Finset ℕ,
      phaseMean P (fun r => tree j S P (phaseResidues P r)) ≤ budget j P) :
    phaseMean (insert p P) (fun r =>
      hitFraction U p (phaseResidues (insert p P) r) *
        tree j (avoid U p (phaseResidues (insert p P) r)) P (phaseResidues (insert p P) r)) ≤
      (p : ℝ)⁻¹ * budget j P := by
  rw [phaseMean_insert P p hp]
  change phaseMean P (fun r => residueMean p (fun a => _)) ≤ _
  rw [phaseMean_residueMean_comm]
  have he (r : Phase P) (a : Fin p) :
      hitFraction U p (phaseResidues (insert p P) (extendPhase P p r a)) *
        tree j (avoid U p (phaseResidues (insert p P) (extendPhase P p r a))) P
          (phaseResidues (insert p P) (extendPhase P p r a)) =
      (classHits U p a / U.card) * tree j (avoidClass U p a) P (phaseResidues P r) := by
    rw [hitFraction_extend, avoid_extend, tree_congr j _ P _ _
      (phaseResidues_extend_old P p hp r a)]
  simp_rw [he, phaseMean_mul]
  calc
    _ ≤ residueMean p (fun a => (classHits U p a / U.card) * budget j P) := by
      apply residueMean_mono
      intro a
      exact mul_le_mul_of_nonneg_left (hcont _) (div_nonneg (classHits_nonneg _ _ _) (Nat.cast_nonneg _))
    _ = residueMean p (fun a => classHits U p a / U.card) * budget j P := by
      have he' : (fun a : Fin p => classHits U p a / U.card * budget j P) =
          (fun a => budget j P * (classHits U p a / U.card)) := by funext a; ring
      rw [he', residueMean_mul, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hitFraction_average_le U p hpp) (budget_nonneg j P)

/-- Exact coordinate independence is used only for the residue draws, not for
positions or conditional survivor sets. -/
theorem tree_mean_le_budget (j : ℕ) (U P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    phaseMean P (fun r => tree j U P (phaseResidues P r)) ≤ budget j P := by
  induction j generalizing U P with
  | zero => simpa only [tree, budget] using (phaseMean_const P hP 1).le
  | succ j ih =>
    simp only [tree, budget]
    rw [phaseMean_sum]
    apply sum_le_sum
    intro p hp
    have hh := step_mean_le j U (P.erase p) p (notMem_erase _ _) (hP p hp).pos
      (fun S => ih S (P.erase p) (fun q hq => hP q (mem_of_mem_erase hq)))
    generalize hQ : P.erase p = Q at hh ⊢
    have he : insert p Q = P := by rw [← hQ, insert_erase hp]
    rw [he] at hh
    exact hh

lemma survivors_phase (U P : Finset ℕ) (r : Phase P) :
    survivors U P (phaseResidues P r) = populationSurvivors U P r := by
  ext x
  simp only [survivors, populationSurvivors, mem_filter]
  apply and_congr_right
  intro _
  constructor
  · intro hh p hp
    apply hh p.val p.property
    simpa only [Nat.ModEq, phaseResidues_mem, Nat.mod_eq_of_lt (r p).isLt] using hp
  · intro hh p hp he
    have he' : x % p = (r ⟨p, hp⟩).val := by
      simpa only [Nat.ModEq, phaseResidues_mem P r ⟨p, hp⟩,
        Nat.mod_eq_of_lt (r ⟨p, hp⟩).isLt] using he
    exact hh ⟨p, hp⟩ he'

/-- A fractional low-count version of the ordered-exposure probability bound.
The partial-population lower bound is the only additional deterministic input. -/
theorem lowCountFraction_mul_le_budget (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (m j : ℕ) (A b : ℝ) (hA : 0 < A) (hb : 0 ≤ b) (hbA : b ≤ A)
    (hpartial : ∀ r : Phase P, PartialLower j (range m) P (phaseResidues P r) A) :
    (1 - b / A) ^ j * lowCountFraction P m b ≤ budget j P := by
  have hpoint (r : Phase P) :
      (1 - b / A) ^ j * (if intervalCount P m r ≤ b then 1 else 0) ≤
        tree j (range m) P (phaseResidues P r) := by
    split_ifs with hr
    · rw [mul_one]
      apply tree_lower j (range m) P (phaseResidues P r) A b hA hb hbA (hpartial r)
      rw [survivors_phase, populationSurvivors_card]
      exact hr
    · simpa only [mul_zero] using tree_nonneg j (range m) P (phaseResidues P r)
  have hh := phaseMean_mono P hpoint
  rw [phaseMean_mul] at hh
  exact hh.trans (tree_mean_le_budget j (range m) P hP)

#print axioms tree_mean_le_budget
#print axioms lowCountFraction_mul_le_budget
end Erdos970.SoftExposure
