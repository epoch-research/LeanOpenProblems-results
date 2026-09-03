import Submission.GibbsOscillationTransport

/-! Product entropy with hereditary conditional row-oscillation caps.
The arithmetic cap hypothesis is explicit; raw row sizes are not used. -/
namespace Erdos970.FiniteGibbs
open Finset Real GapAverages Resampling CoverFibers
set_option maxHeartbeats 2000000

/-- All conditional core populations are included, but not arbitrary subsets
of the population. This distinction permits zero bounds for balanced rows. -/
def PopulationOscillationBound (P S : Finset ℕ) (B : ℕ → ℝ) : Prop :=
  ∀ Q ⊆ P, ∀ p ∈ P, p ∉ Q → ∀ r : Phase Q, ∀ a b : Fin p,
    |classHits (populationSurvivors S Q r) p a-
      classHits (populationSurvivors S Q r) p b| ≤ B p

lemma populationOscillationBound_avoid (P S : Finset ℕ) (p : ℕ) (hp : p ∉ P)
    (B : ℕ → ℝ) (h : PopulationOscillationBound (insert p P) S B) (a : Fin p) :
    PopulationOscillationBound P (avoidClass S p a) B := by
  classical
  intro Q hQ q hq hqQ r b c
  have hpQ : p ∉ Q := fun hp' => hp (hQ hp')
  have hqp : q ≠ p := fun he => hp (he ▸ hq)
  have hnot : q ∉ insert p Q := by simp only [mem_insert,not_or]; exact ⟨hqp,hqQ⟩
  have hh := h (insert p Q) (insert_subset_insert p hQ) q (mem_insert_of_mem hq) hnot
    (extendPhase Q p r a) b c
  rw [populationSurvivors_insert_avoid S Q p hpQ,← populationSurvivors_avoid_comm] at hh
  exact hh

lemma residue_entropy_oscillation (S : Finset ℕ) (p : ℕ) (hp : 0 < p) (t B : ℝ)
    (ht : 0 ≤ t) (hB : 0 ≤ B) (hosc : ∀ a b : Fin p, |classHits S p a-classHits S p b| ≤ B) :
    entropy (fun a => exp (-t*remainingCount S p a)) ≤
      t^2*((1+exp (t*B))*B/p)*mean (fun a => exp (-t*remainingCount S p a)*remainingCount S p a) := by
  letI : Nonempty (Fin p) := ⟨⟨0,hp⟩⟩
  have he := entropy_exp_le_resampling (remainingCount S p) t
  have hr := mul_le_mul_of_nonneg_left (gibbs_resampling_oscillation S p hp t B ht hB hosc)
    (sq_nonneg t)
  simp_rw [mean_fin_eq_residueMean] at he ⊢
  exact he.trans (by convert hr using 1; ring)

/-- Tensorization pays only conditional row oscillation, but requires the
stated cap in every relevant core phase. -/
theorem population_entropy_oscillation (P S : Finset ℕ) (hP : ∀ p ∈ P, 0 < p)
    (B : ℕ → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hB : ∀ p ∈ P, 0 ≤ B p)
    (hosc : PopulationOscillationBound P S B) :
    entropy (fun r : Phase P => exp (-t*count S P r)) ≤
      t^2*entropyCapBudget P B t*mean (fun r => exp (-t*count S P r)*count S P r) := by
  classical
  induction P using Finset.induction_on generalizing S with
  | empty =>
    letI : Nonempty (Phase ∅) := phase_nonempty ∅ (by simp)
    simp only [count_empty,entropy,mean_const,sub_self,entropyCapBudget,sum_empty,mul_zero,zero_mul,le_refl]
  | @insert p P hp ih =>
    have hp0 := hP p (mem_insert_self p P)
    have hPo : ∀ q ∈ P, 0 < q := fun q hq => hP q (mem_insert_of_mem hq)
    have hBo : ∀ q ∈ P, 0 ≤ B q := fun q hq => hB q (mem_insert_of_mem hq)
    letI : Nonempty (Phase P) := phase_nonempty P hPo
    letI : Nonempty (Fin p) := ⟨⟨0,hp0⟩⟩
    let f := fun (r : Phase P) (a : Fin p) => exp (-t*count S (insert p P) (extendPhase P p r a))
    let N := fun (r : Phase P) (a : Fin p) => count S (insert p P) (extendPhase P p r a)
    let c := (1+exp (t*B p))*B p/p
    let D := entropyCapBudget P B t
    have hnew (r : Phase P) : entropy (f r) ≤ t^2*c*mean (fun a => f r a*N r a) := by
      have hc := hosc P (subset_insert p P) p (mem_insert_self p P) hp r
      have hh := residue_entropy_oscillation (populationSurvivors S P r) p hp0 t (B p) ht
        (hB p (mem_insert_self p P)) hc
      simpa only [f,N,c,count_insert_remaining S P p hp] using hh
    have hold (a : Fin p) : entropy (fun r => f r a) ≤ t^2*D*mean (fun r => f r a*N r a) := by
      have hc := populationOscillationBound_avoid P S p hp B hosc a
      have hh := ih (avoidClass S p a) hPo hBo hc
      simpa only [f,N,D,count_insert_avoid S P p hp] using hh
    have htwo := entropy_two_coordinate f (fun r a => exp_pos _)
    have hn := mean_mono hnew
    have ho := mean_mono hold
    rw [mean_mul] at hn ho
    rw [mean_comm (fun (a : Fin p) (r : Phase P) => f r a*N r a)] at ho
    have hfin := htwo.trans (add_le_add hn ho)
    rw [entropy_insert P p hp]
    have hb : entropyCapBudget (insert p P) B t = c+D := by
      simp only [entropyCapBudget,sum_insert hp,c,D]
    rw [hb,mean_insert P p hp]
    convert hfin using 1
    dsimp only [f,N]
    ring

/-- Integrated consequence of the oscillation estimate. -/
theorem population_laplace_oscillation (P S : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (B : ℕ → ℝ) (T : ℝ) (hT : 0 < T)
    (hB : ∀ p ∈ P, 0 ≤ B p) (hosc : PopulationOscillationBound P S B) :
    laplace (count S P) T ≤
      exp (-((S.card : ℝ)*density P*T/(1+entropyCapBudget P B T*T))) := by
  letI : Nonempty (Phase P) := phase_nonempty P (fun p hp => (hP p hp).pos)
  rw [← mean_count P S hP]
  apply finite_herbst_bound _ _ T (entropyCapBudget_nonneg P B T hB) hT
  intro t ht
  have hh := population_entropy_oscillation P S (fun p hp => (hP p hp).pos) B t ht.1.le hB hosc
  apply hh.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (entropyCapBudget_mono P B hB ht.2) (sq_nonneg t))
    (mean_nonneg (fun r => mul_nonneg (exp_pos _).le (by unfold count; positivity)))

/-- Positivity of every phase from the actual phase-space cost and the
explicit conditional oscillation hypothesis. -/
theorem population_survivor_of_oscillation_budget
    (P S : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (B : ℕ → ℝ) (T : ℝ) (hT : 0 < T)
    (hB : ∀ p ∈ P, 0 ≤ B p) (hosc : PopulationOscillationBound P S B)
    (hcost : log (Fintype.card (Phase P) : ℝ) <
      (S.card : ℝ)*density P*T/(1+entropyCapBudget P B T*T)) :
    ∀ r : Phase P, (populationSurvivors S P r).Nonempty := by
  letI : Nonempty (Phase P) := phase_nonempty P (fun p hp => (hP p hp).pos)
  intro r
  by_contra hn
  have hz : count S P r = 0 := by
    simp only [count,Finset.not_nonempty_iff_eq_empty.mp hn,card_empty,Nat.cast_zero]
  have hl := reciprocal_card_le_laplace_of_zero (count S P) T r hz
  have hu := population_laplace_oscillation P S hP B T hT hB hosc
  have hc : (0 : ℝ) < Fintype.card (Phase P) := by exact_mod_cast Fintype.card_pos
  have he : exp (-((S.card : ℝ)*density P*T/(1+entropyCapBudget P B T*T))) <
      1/(Fintype.card (Phase P) : ℝ) := by
    rw [one_div,← exp_log (inv_pos.mpr hc),log_inv]
    exact exp_lt_exp.mpr (neg_lt_neg hcost)
  exact (hl.trans hu).not_gt he

/-- The refinement genuinely removes the raw-cap obstruction on balanced
rows, including a population that can be arbitrarily large. -/
lemma residue_entropy_eq_zero_of_balanced (S : Finset ℕ) (p : ℕ) (hp : 0 < p)
    (t : ℝ) (ht : 0 ≤ t)
    (hbal : ∀ a b : Fin p, classHits S p a = classHits S p b) :
    entropy (fun a : Fin p => exp (-t*remainingCount S p a)) = 0 := by
  letI : Nonempty (Fin p) := ⟨⟨0,hp⟩⟩
  have hh := residue_entropy_oscillation S p hp t 0 ht (by norm_num)
    (fun a b => by rw [hbal a b,sub_self,abs_zero])
  have hl := entropy_nonneg (fun a : Fin p => exp (-t*remainingCount S p a)) (fun _ => exp_pos _)
  simp only [mul_zero,zero_div,zero_mul] at hh
  exact le_antisymm hh hl

#print axioms population_entropy_oscillation
#print axioms population_laplace_oscillation
#print axioms population_survivor_of_oscillation_budget
#print axioms residue_entropy_eq_zero_of_balanced
end Erdos970.FiniteGibbs
