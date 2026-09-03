import Submission.PopulationSignedEntropy

/-! Exact private-position form of the signed Gibbs entropy cost.
The surviving-count term is subtracted, not discarded. The final stability
condition is explicit and is not asserted at quadratic interval length. -/
namespace Erdos970.FiniteGibbs
open Finset Real GapAverages Resampling CoverFibers
set_option maxHeartbeats 2000000

/-- The hits in the omitted-coordinate population are exactly the positions
private to the newly chosen row after that row is inserted. -/
lemma signedResidueCost_private (S : Finset ℕ) (p : ℕ) (t : ℝ) :
    signedResidueCost S p t = t*(
      mean (fun a : Fin p => exp (-t*remainingCount S p a)*(1-1/(p : ℝ))*classHits S p a) -
      (1/(p : ℝ))*mean (fun a : Fin p => exp (-t*remainingCount S p a)*remainingCount S p a)) := by
  unfold signedResidueCost
  congr 1
  rw [← mean_mul,← mean_sub]
  congr 1
  funext a
  rw [centeredHits,remainingCount_eq]
  ring

/-- Gibbs-weighted mass of private positions, with weight 1-1/p for the
unique hitting coordinate. The recursion averages every other coordinate. -/
noncomputable def privateGibbsMass : List ℕ → Finset ℕ → ℝ → ℝ
  | [], _, _ => 0
  | p::ps, S, t =>
    mean (fun r : Phase ps.toFinset =>
      let U := populationSurvivors S ps.toFinset r
      mean (fun a : Fin p => exp (-t*remainingCount U p a)*(1-1/(p : ℝ))*classHits U p a)) +
      mean (fun a : Fin p => privateGibbsMass ps (avoidClass S p a) t)

lemma laplaceMoment_insert_remaining (S P : Finset ℕ) (p : ℕ) (hp : p ∉ P) (t : ℝ) :
    laplaceMoment (count S (insert p P)) t =
      mean (fun r : Phase P => mean (fun a : Fin p =>
        exp (-t*remainingCount (populationSurvivors S P r) p a)*
          remainingCount (populationSurvivors S P r) p a)) := by
  unfold laplaceMoment
  rw [mean_insert P p hp]
  simp only [count_insert_remaining S P p hp]

lemma laplaceMoment_insert_avoid (S P : Finset ℕ) (p : ℕ) (hp : p ∉ P) (t : ℝ) :
    laplaceMoment (count S (insert p P)) t =
      mean (fun a : Fin p => laplaceMoment (count (avoidClass S p a) P) t) := by
  unfold laplaceMoment
  rw [mean_insert P p hp,mean_comm]
  simp only [count_insert_avoid S P p hp]

/-- Exact global signed cost. A phase that is completely covered can still
have positive private mass, so this identity does not bound the cost by the
current survivor count alone. -/
theorem signedPopulationCost_eq_private (ps : List ℕ) (hnd : ps.Nodup)
    (S : Finset ℕ) (t : ℝ) :
    signedPopulationCost ps S t = t*(privateGibbsMass ps S t -
      (∑ p ∈ ps.toFinset, 1/(p : ℝ))*laplaceMoment (count S ps.toFinset) t) := by
  induction ps generalizing S with
  | nil => simp [signedPopulationCost,privateGibbsMass]
  | cons p ps ih =>
    obtain ⟨hnot,hnd'⟩ := List.nodup_cons.mp hnd
    have hp : p ∉ ps.toFinset := by simpa using hnot
    simp only [signedPopulationCost,privateGibbsMass,List.toFinset_cons,sum_insert hp]
    simp_rw [signedResidueCost_private,ih hnd']
    simp only [mean_mul,mean_sub]
    rw [← laplaceMoment_insert_remaining S ps.toFinset p hp t,
      ← laplaceMoment_insert_avoid S ps.toFinset p hp t]
    have he : laplaceMoment (count S (p::ps).toFinset) t =
        laplaceMoment (count S (insert p ps.toFinset)) t := by rw [List.toFinset_cons]
    rw [he]
    ring

lemma privateGibbsMass_nonneg (ps : List ℕ) (hp : ∀ p ∈ ps, 0 < p)
    (S : Finset ℕ) (t : ℝ) : 0 ≤ privateGibbsMass ps S t := by
  induction ps generalizing S with
  | nil => exact le_rfl
  | cons p ps ih =>
    have hp0 := hp p (by simp)
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp0
    have hf : 0 ≤ 1-1/(p : ℝ) := sub_nonneg.mpr
      ((div_le_one (by exact_mod_cast hp0)).mpr hp1)
    apply add_nonneg
    · exact mean_nonneg (fun r => mean_nonneg (fun a =>
        mul_nonneg (mul_nonneg (exp_pos _).le hf) (classHits_nonneg _ _ _)))
    · exact mean_nonneg (fun a => ih (fun q hq => hp q (by simp [hq])) _)

/-- Positivity of the signed cost gives a lower bound for private mass at
positive tilt, not the upper bound needed to prove a survivor theorem. -/
theorem privateGibbsMass_ge_survivor_balance (ps : List ℕ) (hnd : ps.Nodup)
    (hp : ∀ p ∈ ps, 0 < p) (S : Finset ℕ) (t : ℝ) (ht : 0 < t) :
    (∑ p ∈ ps.toFinset, 1/(p : ℝ))*laplaceMoment (count S ps.toFinset) t ≤
      privateGibbsMass ps S t := by
  have hh := signedPopulationCost_nonneg ps hp S t
  rw [signedPopulationCost_eq_private ps hnd] at hh
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left ht).mp hh)

/-- The needed private/survivor stability estimate is stated as a hypothesis.
It retains both sides of the exact signed balance. -/
theorem population_survivor_of_private_stability (ps : List ℕ) (hnd : ps.Nodup)
    (hp : ∀ p ∈ ps, p.Prime) (S : Finset ℕ) (A T : ℝ) (hA : 0 ≤ A) (hT : 0 < T)
    (hstab : ∀ t ∈ Set.Ioc (0 : ℝ) T,
      privateGibbsMass ps S t ≤
        ((∑ p ∈ ps.toFinset, 1/(p : ℝ))+A*t)*laplaceMoment (count S ps.toFinset) t)
    (hphase : log (Fintype.card (Phase ps.toFinset) : ℝ) <
      (S.card : ℝ)*density ps.toFinset*T/(1+A*T)) :
    ∀ r : Phase ps.toFinset, (populationSurvivors S ps.toFinset r).Nonempty := by
  apply population_survivor_of_signed_cost ps hnd hp S A T hA hT _ hphase
  intro t ht
  rw [signedPopulationCost_eq_private ps hnd]
  have hh := mul_le_mul_of_nonneg_left (hstab t ht) ht.1.le
  nlinarith only [hh]

#print axioms signedPopulationCost_eq_private
#print axioms privateGibbsMass_nonneg
#print axioms privateGibbsMass_ge_survivor_balance
#print axioms population_survivor_of_private_stability
end Erdos970.FiniteGibbs
