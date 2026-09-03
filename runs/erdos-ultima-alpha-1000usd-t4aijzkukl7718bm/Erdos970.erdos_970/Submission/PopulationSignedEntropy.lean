import Submission.FiniteGibbsDirichlet
import Submission.FiniteHerbstBound

/-! Tensorization with the actual signed Gibbs row cost, rather than uniform
row-size or oscillation caps. The resulting arithmetic cost estimate remains
an explicit hypothesis in the Laplace bound. -/
namespace Erdos970.FiniteGibbs
open Finset Real GapAverages Resampling CoverFibers
set_option maxHeartbeats 2000000

noncomputable def signedResidueCost (S : Finset ℕ) (p : ℕ) (t : ℝ) : ℝ :=
  t*mean (fun a : Fin p => exp (-t*remainingCount S p a)*centeredHits S p a)

lemma mean_remainingCount (S : Finset ℕ) (p : ℕ) (hp : 0 < p) :
    mean (remainingCount S p) = (S.card : ℝ)-(S.card : ℝ)/p := by
  letI : Nonempty (Fin p) := ⟨⟨0,hp⟩⟩
  change mean (fun a : Fin p => remainingCount S p a) = _
  simp only [remainingCount_eq,mean_sub,mean_const,mean_fin_eq_residueMean,
    classHits_mean S p hp]

/-- The sign of each centred row contribution is retained until the Gibbs
average. No bound on a conditional row difference is assumed. -/
theorem residue_entropy_le_signed (S : Finset ℕ) (p : ℕ) (hp : 0 < p) (t : ℝ) :
    entropy (fun a : Fin p => exp (-t*remainingCount S p a)) ≤ signedResidueCost S p t := by
  letI : Nonempty (Fin p) := ⟨⟨0,hp⟩⟩
  have hh := entropy_exp_le_signed (remainingCount S p) t
  rw [mean_remainingCount S p hp] at hh
  have he (a : Fin p) :
      (S.card : ℝ)-(S.card : ℝ)/p-remainingCount S p a = centeredHits S p a := by
    rw [remainingCount_eq,centeredHits]
    ring
  simpa only [he,signedResidueCost] using hh

lemma signedResidueCost_nonneg (S : Finset ℕ) (p : ℕ) (hp : 0 < p) (t : ℝ) :
    0 ≤ signedResidueCost S p t := by
  letI : Nonempty (Fin p) := ⟨⟨0,hp⟩⟩
  exact (entropy_nonneg (fun a : Fin p => exp (-t*remainingCount S p a))
    (fun _ => exp_pos _)).trans (residue_entropy_le_signed S p hp t)

/-- Balanced rows have zero signed cost, independently of their size. -/
lemma signedResidueCost_eq_zero_of_balanced (S : Finset ℕ) (p : ℕ) (hp : 0 < p)
    (t : ℝ) (hbal : ∀ a b : Fin p, classHits S p a = classHits S p b) :
    signedResidueCost S p t = 0 := by
  letI : Nonempty (Fin p) := ⟨⟨0,hp⟩⟩
  have hc (a : Fin p) : classHits S p a = (S.card : ℝ)/p := by
    have hh : mean (classHits S p) = classHits S p a := by
      change mean (fun b => classHits S p b) = _
      simp_rw [hbal _ a]
      exact mean_const _
    rw [mean_fin_eq_residueMean,classHits_mean S p hp] at hh
    exact hh.symm
  simp only [signedResidueCost,centeredHits,hc,sub_self,mul_zero,mean_const]

/-- Specialization of the sharper half-resampling bound to an actual row cap.
The exponential transport factor is still present. -/
theorem residue_entropy_half_cap (S : Finset ℕ) (p : ℕ) (hp : 0 < p)
    (t B : ℝ) (ht : 0 ≤ t) (hB : 0 ≤ B)
    (hcap : ∀ a : Fin p, classHits S p a ≤ B) :
    entropy (fun a : Fin p => exp (-t*remainingCount S p a)) ≤
      t^2/2*((1+exp (t*B))*B/p)*
        mean (fun a => exp (-t*remainingCount S p a)*remainingCount S p a) := by
  letI : Nonempty (Fin p) := ⟨⟨0,hp⟩⟩
  have he := entropy_exp_le_half_resampling (remainingCount S p) t
  have hr := mul_le_mul_of_nonneg_left
    (gibbs_resampling_second_moment S p hp t B ht hB hcap)
    (show 0 ≤ t^2/2 by positivity)
  simp_rw [mean_fin_eq_residueMean] at he ⊢
  exact he.trans (by convert hr using 1; ring)

/-- Every term is evaluated on the genuine population surviving the other
fixed coordinates. The recursion is finite and contains no worst-case caps. -/
noncomputable def signedPopulationCost : List ℕ → Finset ℕ → ℝ → ℝ
  | [], _, _ => 0
  | p::ps, S, t =>
    mean (fun r : Phase ps.toFinset => signedResidueCost (populationSurvivors S ps.toFinset r) p t) +
      mean (fun a : Fin p => signedPopulationCost ps (avoidClass S p a) t)

lemma signedPopulationCost_nonneg (ps : List ℕ) (hp : ∀ p ∈ ps, 0 < p)
    (S : Finset ℕ) (t : ℝ) : 0 ≤ signedPopulationCost ps S t := by
  induction ps generalizing S with
  | nil => exact le_rfl
  | cons p ps ih =>
    exact add_nonneg
      (mean_nonneg (fun r => signedResidueCost_nonneg _ p (hp p (by simp)) t))
      (mean_nonneg (fun a => ih (fun q hq => hp q (by simp [hq])) _))

/-- Full finite-product entropy with signed, phase-dependent row costs.
This tensorization is valid at every real tilt. -/
theorem population_entropy_le_signed (ps : List ℕ) (hnd : ps.Nodup)
    (hp : ∀ p ∈ ps, 0 < p) (S : Finset ℕ) (t : ℝ) :
    entropy (fun r : Phase ps.toFinset => exp (-t*count S ps.toFinset r)) ≤
      signedPopulationCost ps S t := by
  induction ps generalizing S with
  | nil =>
    letI : Nonempty (Phase ∅) := phase_nonempty ∅ (by simp)
    simp only [List.toFinset_nil,count_empty,entropy,mean_const,sub_self,signedPopulationCost,le_refl]
  | cons p ps ih =>
    obtain ⟨hnot,hnd'⟩ := List.nodup_cons.mp hnd
    have hp0 := hp p (by simp)
    have hps : ∀ q ∈ ps, 0 < q := fun q hq => hp q (by simp [hq])
    have hpP : p ∉ ps.toFinset := by simpa using hnot
    letI : Nonempty (Phase ps.toFinset) := phase_nonempty _ (by simpa using hps)
    letI : Nonempty (Fin p) := ⟨⟨0,hp0⟩⟩
    let f := fun (r : Phase ps.toFinset) (a : Fin p) =>
      exp (-t*count S (insert p ps.toFinset) (extendPhase ps.toFinset p r a))
    have hn (r : Phase ps.toFinset) :
        entropy (f r) ≤ signedResidueCost (populationSurvivors S ps.toFinset r) p t := by
      simpa only [f,count_insert_remaining S ps.toFinset p hpP] using
        residue_entropy_le_signed (populationSurvivors S ps.toFinset r) p hp0 t
    have ho (a : Fin p) :
        entropy (fun r => f r a) ≤ signedPopulationCost ps (avoidClass S p a) t := by
      simpa only [f,count_insert_avoid S ps.toFinset p hpP] using
        ih hnd' hps (avoidClass S p a)
    have hh := (entropy_two_coordinate f (fun _ _ => exp_pos _)).trans
      (add_le_add (mean_mono hn) (mean_mono ho))
    rw [List.toFinset_cons,entropy_insert ps.toFinset p hpP]
    exact hh

/-- A sufficient arithmetic estimate for the signed cost. Unlike a bound by
uniform conditional oscillations, this is an estimate of the Gibbs-weighted
cost itself; it is NOT asserted unconditionally. -/
theorem population_laplace_of_signed_cost (ps : List ℕ) (hnd : ps.Nodup)
    (hp : ∀ p ∈ ps, p.Prime) (S : Finset ℕ) (A T : ℝ) (hA : 0 ≤ A) (hT : 0 < T)
    (hcost : ∀ t ∈ Set.Ioc (0 : ℝ) T,
      signedPopulationCost ps S t ≤ t^2*A*laplaceMoment (count S ps.toFinset) t) :
    laplace (count S ps.toFinset) T ≤
      exp (-((S.card : ℝ)*density ps.toFinset*T/(1+A*T))) := by
  have hp0 : ∀ p ∈ ps, 0 < p := fun p h => (hp p h).pos
  letI : Nonempty (Phase ps.toFinset) := phase_nonempty _ (by simpa using hp0)
  rw [← mean_count ps.toFinset S (by simpa using hp)]
  apply finite_herbst_bound _ A T hA hT
  intro t ht
  exact (population_entropy_le_signed ps hnd hp0 S t).trans (hcost t ht)

/-- An explicit survivor certificate from the signed cost, retaining the
full phase-space logarithm. Its arithmetic cost premise remains unproved
at a uniform quadratic scale. -/
theorem population_survivor_of_signed_cost (ps : List ℕ) (hnd : ps.Nodup)
    (hp : ∀ p ∈ ps, p.Prime) (S : Finset ℕ) (A T : ℝ) (hA : 0 ≤ A) (hT : 0 < T)
    (hcost : ∀ t ∈ Set.Ioc (0 : ℝ) T,
      signedPopulationCost ps S t ≤ t^2*A*laplaceMoment (count S ps.toFinset) t)
    (hphase : log (Fintype.card (Phase ps.toFinset) : ℝ) <
      (S.card : ℝ)*density ps.toFinset*T/(1+A*T)) :
    ∀ r : Phase ps.toFinset, (populationSurvivors S ps.toFinset r).Nonempty := by
  have hp0 : ∀ p ∈ ps, 0 < p := fun p h => (hp p h).pos
  letI : Nonempty (Phase ps.toFinset) := phase_nonempty _ (by simpa using hp0)
  have hent : ∀ t ∈ Set.Ioc (0 : ℝ) T,
      entropy (fun r => exp (-t*count S ps.toFinset r)) ≤
        t^2*A*laplaceMoment (count S ps.toFinset) t :=
    fun t ht => (population_entropy_le_signed ps hnd hp0 S t).trans (hcost t ht)
  have hn := nonzero_of_finite_herbst (count S ps.toFinset) A T hA hT hent
    (by simpa only [mean_count ps.toFinset S (by simpa using hp)] using hphase)
  intro r
  by_contra he
  apply hn r
  simp only [count,Finset.not_nonempty_iff_eq_empty.mp he,card_empty,Nat.cast_zero]

#print axioms residue_entropy_le_signed
#print axioms residue_entropy_half_cap
#print axioms signedPopulationCost_nonneg
#print axioms population_entropy_le_signed
#print axioms population_laplace_of_signed_cost
#print axioms population_survivor_of_signed_cost
end Erdos970.FiniteGibbs
