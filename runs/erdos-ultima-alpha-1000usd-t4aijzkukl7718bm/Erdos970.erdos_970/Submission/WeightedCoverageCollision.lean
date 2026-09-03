import Submission.OneHitCollisionRemainder

/-! An exact nonlinear covariance recursion for finite residue-class covers.
The positive correction retains the probabilities of completing each
remaining population. No small uniform bound for that correction is asserted. -/
namespace Erdos970.OneHitLogConcavity
open Finset GapAverages CoverFibers Resampling
set_option maxHeartbeats 2000000

lemma populationCoveredFraction_antitone_population (P S T : Finset ℕ) (hST : S ⊆ T) :
    populationCoveredFraction T P ≤ populationCoveredFraction S P := by
  unfold populationCoveredFraction
  apply phaseMean_mono
  intro r
  split_ifs with hT hS hS
  · norm_num
  · exact (hS (fun x hx => hT x (hST hx))).elim
  · norm_num
  · norm_num

lemma populationCoveredFraction_empty_moduli (S : Finset ℕ) :
    populationCoveredFraction S ∅ = if S = ∅ then 1 else 0 := by
  simp [populationCoveredFraction,phaseMean,eq_empty_iff_forall_notMem]

lemma populationCoveredFraction_insert_avoid (P S : Finset ℕ) (p : ℕ) (hp : p ∉ P) :
    populationCoveredFraction S (insert p P) =
      residueMean p (fun a => populationCoveredFraction (avoidClass S p a) P) := by
  unfold populationCoveredFraction
  rw [phaseMean_insert P p hp]
  simp_rw [insert_cover_filter_iff S P p hp]
  rw [phaseMean_div,phaseMean_sum]
  rfl

lemma avoidClass_union (S T : Finset ℕ) (p : ℕ) (a : Fin p) :
    avoidClass (S ∪ T) p a = avoidClass S p a ∪ avoidClass T p a := filter_union _ _ _

lemma residueMean_product_increment_identity (p : ℕ) (hp : 0 < p)
    (f g : Fin p → ℝ) (f₀ g₀ : ℝ) :
    residueMean p (fun a => f a*g a) = residueMean p f*residueMean p g +
      residueMean p (fun a => (f a-f₀)*(g a-g₀)) -
        (residueMean p f-f₀)*(residueMean p g-g₀) := by
  have he (a : Fin p) : (f a-f₀)*(g a-g₀) =
      f a*g a-g₀*f a-f₀*g a+f₀*g₀ := by ring
  simp_rw [he]
  rw [residueMean_add,residueMean_sub,residueMean_sub,
    residueMean_mul,residueMean_mul,residueMean_const p hp]
  ring

/-- Gain in remaining coverage probability from deleting one selected row.
It is not replaced by a bare indicator that the row meets the population. -/
noncomputable def completionIncrement (P S : Finset ℕ) (p : ℕ) (a : Fin p) : ℝ :=
  populationCoveredFraction (avoidClass S p a) P-populationCoveredFraction S P

lemma completionIncrement_nonneg (P S : Finset ℕ) (p : ℕ) (a : Fin p) :
    0 ≤ completionIncrement P S p a :=
  sub_nonneg.mpr (populationCoveredFraction_antitone_population P _ S (filter_subset _ _))

lemma completionIncrement_mean (P S : Finset ℕ) (p : ℕ) (hp : p ∉ P) (hp0 : 0 < p) :
    residueMean p (completionIncrement P S p) =
      populationCoveredFraction S (insert p P)-populationCoveredFraction S P := by
  unfold completionIncrement
  rw [residueMean_sub,residueMean_const p hp0,populationCoveredFraction_insert_avoid P S p hp]

/-- Weighted shared-residue contribution of one insertion. Both factors are
actual completion-probability increments of the remaining sieve. -/
noncomputable def completionCollision (P S T : Finset ℕ) (p : ℕ) : ℝ :=
  residueMean p (fun a => completionIncrement P S p a*completionIncrement P T p a)

lemma completionCollision_nonneg (P S T : Finset ℕ) (p : ℕ) :
    0 ≤ completionCollision P S T p :=
  residueMean_nonneg p (fun a => mul_nonneg (completionIncrement_nonneg P S p a)
    (completionIncrement_nonneg P T p a))

noncomputable def coverageCovariance (P S T : Finset ℕ) : ℝ :=
  populationCoveredFraction (S ∪ T) P-
    populationCoveredFraction S P*populationCoveredFraction T P

/-- Exact covariance identity, including the negative product of average
completion increments. It allows repeated hits in both populations. -/
theorem coverageCovariance_insert (P S T : Finset ℕ) (p : ℕ)
    (hp : p ∉ P) (hp0 : 0 < p) :
    coverageCovariance (insert p P) S T =
      residueMean p (fun a => coverageCovariance P (avoidClass S p a) (avoidClass T p a)) +
      completionCollision P S T p -
      (populationCoveredFraction S (insert p P)-populationCoveredFraction S P)*
        (populationCoveredFraction T (insert p P)-populationCoveredFraction T P) := by
  have he := residueMean_product_increment_identity p hp0
    (fun a => populationCoveredFraction (avoidClass S p a) P)
    (fun a => populationCoveredFraction (avoidClass T p a) P)
    (populationCoveredFraction S P) (populationCoveredFraction T P)
  unfold coverageCovariance
  simp only [← avoidClass_union]
  rw [residueMean_sub]
  simp only [populationCoveredFraction_insert_avoid P _ p hp]
  unfold completionCollision completionIncrement
  linarith only [he]

/-- A positive recursive majorant for covariance. Every child retains its
actual remaining population, and every source retains completion weights. -/
noncomputable def weightedCollisionCost : List ℕ → Finset ℕ → Finset ℕ → ℝ
  | [], _, _ => 0
  | p::ps, S, T =>
      residueMean p (fun a => weightedCollisionCost ps (avoidClass S p a) (avoidClass T p a)) +
        completionCollision ps.toFinset S T p

lemma weightedCollisionCost_nonneg (ps : List ℕ) (S T : Finset ℕ) :
    0 ≤ weightedCollisionCost ps S T := by
  induction ps generalizing S T with
  | nil => exact le_rfl
  | cons p ps ih =>
    exact add_nonneg (residueMean_nonneg p (fun a => ih _ _))
      (completionCollision_nonneg ps.toFinset S T p)

/-- A full finite-prime comparison; there is no one-hit assumption. The
weighted cost still requires an estimate before giving useful decay. -/
theorem coverageCovariance_le_weightedCollisionCost (ps : List ℕ) (hnd : ps.Nodup)
    (hp : ∀ p ∈ ps, 0 < p) (S T : Finset ℕ) :
    coverageCovariance ps.toFinset S T ≤ weightedCollisionCost ps S T := by
  induction ps generalizing S T with
  | nil =>
    simp only [List.toFinset_nil,weightedCollisionCost,coverageCovariance,
      populationCoveredFraction_empty_moduli,union_eq_empty]
    split_ifs <;> norm_num <;> tauto
  | cons p ps ih =>
    obtain ⟨hnot,hnd'⟩ := List.nodup_cons.mp hnd
    have hp0 := hp p (by simp)
    have hps : ∀ q ∈ ps, 0 < q := fun q hq => hp q (by simp [hq])
    have hpP : p ∉ ps.toFinset := by simpa using hnot
    rw [List.toFinset_cons,coverageCovariance_insert ps.toFinset S T p hpP hp0,weightedCollisionCost]
    have hchild := residueMean_mono p (fun a => ih hnd' hps (avoidClass S p a) (avoidClass T p a))
    have hS : 0 ≤ populationCoveredFraction S (insert p ps.toFinset)-populationCoveredFraction S ps.toFinset := by
      rw [← completionIncrement_mean _ _ _ hpP hp0]
      exact residueMean_nonneg p (completionIncrement_nonneg _ _ _)
    have hT : 0 ≤ populationCoveredFraction T (insert p ps.toFinset)-populationCoveredFraction T ps.toFinset := by
      rw [← completionIncrement_mean _ _ _ hpP hp0]
      exact residueMean_nonneg p (completionIncrement_nonneg _ _ _)
    linarith only [hchild,mul_nonneg hS hT]

/-- Unconditional finite coverage comparison with its weighted correction. -/
theorem population_cover_le_product_add_weightedCollisionCost
    (ps : List ℕ) (hnd : ps.Nodup) (hp : ∀ p ∈ ps, 0 < p) (S T : Finset ℕ) :
    populationCoveredFraction (S ∪ T) ps.toFinset ≤
      populationCoveredFraction S ps.toFinset*populationCoveredFraction T ps.toFinset+
        weightedCollisionCost ps S T := by
  have hh := coverageCovariance_le_weightedCollisionCost ps hnd hp S T
  unfold coverageCovariance at hh
  linarith only [hh]

/-- Cross separation only compares the two populations. Repeated residues
within either one are allowed. This is weaker than injectivity on their union. -/
def CrossSeparated (P S T : Finset ℕ) : Prop :=
  ∀ p ∈ P, ∀ x ∈ S, ∀ y ∈ T, x % p ≠ y % p

lemma completionCollision_zero_of_separated (P S T : Finset ℕ) (p : ℕ)
    (hsep : ∀ x ∈ S, ∀ y ∈ T, x % p ≠ y % p) :
    completionCollision P S T p = 0 := by
  classical
  have he (a : Fin p) : completionIncrement P S p a*completionIncrement P T p a = 0 := by
    by_cases hS : ∀ x ∈ S, x % p ≠ a.val
    · have ha : avoidClass S p a=S := filter_eq_self.mpr hS
      simp only [completionIncrement,ha,sub_self,zero_mul]
    · obtain ⟨x,hx,hxa⟩ := by simpa only [not_forall,Classical.not_imp,not_not,exists_prop] using hS
      have hT : ∀ y ∈ T, y % p ≠ a.val := by
        intro y hy hya
        exact hsep x hx y hy (hxa.trans hya.symm)
      have ha : avoidClass T p a=T := filter_eq_self.mpr hT
      simp only [completionIncrement,ha,sub_self,mul_zero]
  unfold completionCollision residueMean
  simp only [he,sum_const_zero,zero_div]

lemma weightedCollisionCost_zero_of_crossSeparated (ps : List ℕ) (S T : Finset ℕ)
    (hsep : CrossSeparated ps.toFinset S T) : weightedCollisionCost ps S T=0 := by
  induction ps generalizing S T with
  | nil => rfl
  | cons p ps ih =>
    have hchild (a : Fin p) : CrossSeparated ps.toFinset (avoidClass S p a) (avoidClass T p a) := by
      intro q hq x hx y hy
      exact hsep q (by simp only [List.toFinset_cons]; exact mem_insert_of_mem hq)
        x (mem_filter.mp hx).1 y (mem_filter.mp hy).1
    have hsrc : completionCollision ps.toFinset S T p=0 :=
      completionCollision_zero_of_separated _ _ _ _ (hsep p (by simp))
    simp only [weightedCollisionCost,hsrc,add_zero,ih _ _ (hchild _),residueMean,sum_const_zero,zero_div]

/-- Negative dependence with cross-residue separation, without a one-hit
restriction inside either population. This remains a restricted theorem. -/
theorem population_cover_le_product_of_crossSeparated (P S T : Finset ℕ)
    (hp : ∀ p ∈ P, 0 < p) (hsep : CrossSeparated P S T) :
    populationCoveredFraction (S ∪ T) P ≤ populationCoveredFraction S P*populationCoveredFraction T P := by
  have hh := population_cover_le_product_add_weightedCollisionCost P.toList P.nodup_toList
    (fun p hp' => hp p (by simpa using hp')) S T
  have he := weightedCollisionCost_zero_of_crossSeparated P.toList S T (by simpa using hsep)
  simpa [he] using hh

#print axioms coverageCovariance_insert
#print axioms population_cover_le_product_add_weightedCollisionCost
#print axioms population_cover_le_product_of_crossSeparated
end Erdos970.OneHitLogConcavity
