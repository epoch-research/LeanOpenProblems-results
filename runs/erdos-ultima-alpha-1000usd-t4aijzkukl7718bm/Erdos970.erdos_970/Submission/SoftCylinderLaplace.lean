import Submission.PhaseUnionBennett
import Submission.SoftEndpointReduction

/-! Weighted neighborhoods of a covering residue vector give product lower
bounds on the actual Laplace transform. These are unconditional finite
inequalities, not the Laplace upper bound needed to settle Erdős 970. -/
namespace Erdos970.GapAverages
open Finset Real Resampling
set_option maxHeartbeats 1500000

/-- The exact product weight of independently retaining a distinguished residue
or paying its exposed-population cap when that residue is changed. -/
noncomputable def softCylinderWeight (P : Finset ℕ) (B : P → ℝ) (t : ℝ) : ℝ :=
  ∏ p : P, (1 + ((p.val : ℝ)-1)*exp (-t*B p))/(p.val : ℝ)

/-- Every new survivor must have lost at least one of its old covering rows.
The row populations here are those of the actual fixed population S. -/
theorem population_count_le_changed_hits (S P : Finset ℕ) (r s : Phase P)
    (hcover : ∀ x ∈ S, ∃ p : P, x % p.val = (r p).val) :
    ((populationSurvivors S P s).card : ℝ) ≤
      ∑ p : P, if s p = r p then 0 else classHits S p.val (r p) := by
  classical
  rw [populationSurvivors_card]
  have hpoint (x : ℕ) (hx : x ∈ S) : point P x s ≤
      ∑ p : P, if s p = r p then 0 else
        if x % p.val = (r p).val then (1 : ℝ) else 0 := by
    by_cases hs : ∀ p : P, x % p.val ≠ (s p).val
    · obtain ⟨p,hp⟩ := hcover x hx
      have hne : s p ≠ r p := by
        intro he
        exact hs p (he ▸ hp)
      rw [CoverFibers.point_eq_avoidance_indicator,if_pos hs]
      have hh := single_le_sum (s := (univ : Finset P))
        (f := fun p => if s p = r p then 0 else
          if x % p.val = (r p).val then (1 : ℝ) else 0)
        (fun p _ => by dsimp only; split_ifs <;> norm_num) (mem_univ p)
      simpa only [hne,if_false,hp,if_true] using hh
    · rw [CoverFibers.point_eq_avoidance_indicator,if_neg hs]
      exact sum_nonneg (fun p _ => by split_ifs <;> norm_num)
  have hh := sum_le_sum hpoint
  rw [sum_comm] at hh
  apply hh.trans_eq
  apply sum_congr rfl
  intro p hp
  by_cases he : s p = r p
  · simp [he]
  · simp only [he,if_false,classHits]

theorem population_count_le_changed_caps (S P : Finset ℕ) (r s : Phase P)
    (hcover : ∀ x ∈ S, ∃ p : P, x % p.val = (r p).val)
    (B : P → ℝ) (hB : ∀ p, classHits S p.val (r p) ≤ B p) :
    ((populationSurvivors S P s).card : ℝ) ≤
      ∑ p : P, if s p = r p then 0 else B p := by
  apply (population_count_le_changed_hits S P r s hcover).trans
  apply sum_le_sum
  intro p hp
  split_ifs
  · exact le_rfl
  · exact hB p

lemma phaseMean_exp_changed_caps (P : Finset ℕ) (r : Phase P)
    (B : P → ℝ) (t : ℝ) :
    phaseMean P (fun s => exp (-t * ∑ p : P, if s p = r p then 0 else B p)) =
      softCylinderWeight P B t := by
  classical
  have he (s : Phase P) : exp (-t * ∑ p : P, if s p = r p then 0 else B p) =
      ∏ p : P, exp (-t * (if s p = r p then 0 else B p)) := by
    rw [mul_sum,exp_sum]
  simp_rw [he]
  rw [phaseMean_prod P (fun p a => exp (-t * (if a = r p then 0 else B p)))]
  unfold softCylinderWeight
  apply prod_congr rfl
  intro p hp
  congr 1
  have he' (a : Fin p.val) : exp (-t * (if a = r p then 0 else B p)) =
      exp (-t*B p) + if a = r p then 1-exp (-t*B p) else 0 := by
    by_cases ha : a = r p <;> simp [ha]
  simp_rw [he']
  rw [sum_add_distrib]
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,sum_ite_eq',mem_univ,
    if_true]
  ring

/-- A covered population forces a whole product neighborhood to contribute to
its Laplace transform. This is stronger than retaining only one residue vector. -/
theorem softCylinderWeight_le_population_laplace (S P : Finset ℕ)
    (r : Phase P) (hcover : ∀ x ∈ S, ∃ p : P, x % p.val = (r p).val)
    (B : P → ℝ) (hB : ∀ p, classHits S p.val (r p) ≤ B p)
    (t : ℝ) (ht : 0 ≤ t) :
    softCylinderWeight P B t ≤
      phaseMean P (fun s => exp (-t*((populationSurvivors S P s).card : ℝ))) := by
  rw [← phaseMean_exp_changed_caps P r B t]
  apply phaseMean_mono
  intro s
  apply exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left
    (population_count_le_changed_caps S P r s hcover B hB) (neg_nonpos.mpr ht)

/-- Interval specialization with explicit, universally valid row caps. -/
theorem softCylinderWeight_le_countLaplace_of_cover (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (m : ℕ) (r : Phase P)
    (hr : intervalCount P m r = 0) (t : ℝ) (ht : 0 ≤ t) :
    softCylinderWeight P (fun p => (m : ℝ)/p.val+1) t ≤ countLaplace P t m := by
  have hcover : ∀ x ∈ range m, ∃ p : P, x % p.val = (r p).val :=
    fun x hx => cover_of_count_zero P m r hr x (mem_range.mp hx)
  have hB (p : P) : classHits (range m) p.val (r p) ≤ (m : ℝ)/p.val+1 := by
    unfold classHits
    rw [← residueHits_cast]
    exact residueHits_le_real m p.val (hP p.val p.property).pos (r p)
  have hh := softCylinderWeight_le_population_laplace (range m) P r hcover _ hB t ht
  simpa only [populationSurvivors_card,intervalCount,countLaplace] using hh

/-- A single soft coordinate costs no more than either its full logarithmic
phase cost or its exposed-population cost. -/
lemma exp_min_le_soft_coordinate (p B t : ℝ) (hp : 1 ≤ p)
    (hB : 0 ≤ B) (ht : 0 ≤ t) :
    exp (-min (log p) (t*B)) ≤ (1+(p-1)*exp (-t*B))/p := by
  have hp0 : 0 < p := by linarith only [hp]
  have he : exp (-t*B) ≤ 1 := by
    apply exp_le_one_iff.mpr
    nlinarith only [mul_nonneg ht hB]
  have hphase : 1/p ≤ (1+(p-1)*exp (-t*B))/p := by
    apply div_le_div_of_nonneg_right _ hp0.le
    have hh := mul_nonneg (sub_nonneg.mpr hp) (exp_pos (-t*B)).le
    linarith only [hh]
  have hcost : exp (-t*B) ≤ (1+(p-1)*exp (-t*B))/p := by
    apply (le_div_iff₀ hp0).mpr
    nlinarith only [he]
  rcases le_total (log p) (t*B) with h | h
  · rw [min_eq_left h,exp_neg,exp_log hp0]
    simpa only [one_div] using hphase
  · simpa only [min_eq_right h,neg_mul] using hcost

/-- Soft neighborhood entropy is bounded by the sum of the coordinatewise
minimum costs. No full phase-space logarithm is discarded for free. -/
theorem exp_softCost_le_softCylinderWeight (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (B : P → ℝ) (hB : ∀ p, 0 ≤ B p)
    (t : ℝ) (ht : 0 ≤ t) :
    exp (-(∑ p : P, min (log (p.val : ℝ)) (t*B p))) ≤ softCylinderWeight P B t := by
  rw [← sum_neg_distrib,exp_sum]
  unfold softCylinderWeight
  apply prod_le_prod
  · intro p hp
    exact (exp_pos _).le
  · intro p hp
    exact exp_min_le_soft_coordinate p.val (B p) t
      (by exact_mod_cast (hP p.val p.property).one_le) (hB p) ht

/-- The soft coordinate is at most the sum of its two hard choices. -/
lemma soft_coordinate_le_two_exp_min (p B t : ℝ) (hp : 1 ≤ p) :
    (1+(p-1)*exp (-t*B))/p ≤ 2*exp (-min (log p) (t*B)) := by
  have hp0 : 0 < p := by linarith only [hp]
  have hphase : 1/p ≤ exp (-min (log p) (t*B)) := by
    have hh := exp_le_exp.mpr (neg_le_neg (min_le_left (log p) (t*B)))
    rw [exp_neg,exp_log hp0] at hh
    simpa only [one_div] using hh
  have hcost : exp (-t*B) ≤ exp (-min (log p) (t*B)) := by
    simpa only [neg_mul] using
      exp_le_exp.mpr (neg_le_neg (min_le_right (log p) (t*B)))
  have hsum : (1+(p-1)*exp (-t*B))/p ≤ 1/p+exp (-t*B) := by
    apply (div_le_iff₀ hp0).mpr
    have he : (1/p+exp (-t*B))*p = 1+p*exp (-t*B) := by
      field_simp
    rw [he]
    nlinarith only [(exp_pos (-t*B)).le]
  linarith only [hsum,hphase,hcost]

/-- The product soft bound is within a factor 2^|P| of its best coordinatewise
hard choice. This is only a comparison of the two finite bounds. -/
theorem softCylinderWeight_le_two_pow_exp_softCost (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (B : P → ℝ) (t : ℝ) :
    softCylinderWeight P B t ≤ (2 : ℝ)^P.card *
      exp (-(∑ p : P, min (log (p.val : ℝ)) (t*B p))) := by
  have hh : softCylinderWeight P B t ≤
      ∏ p : P, 2*exp (-min (log (p.val : ℝ)) (t*B p)) := by
    unfold softCylinderWeight
    apply prod_le_prod
    · intro p hp
      have h1 : (1 : ℝ) ≤ p.val := by exact_mod_cast (hP p.val p.property).one_le
      apply div_nonneg _ (Nat.cast_nonneg _)
      have hh := mul_nonneg (sub_nonneg.mpr h1) (exp_pos (-t*B p)).le
      linarith only [hh]
    · intro p hp
      exact soft_coordinate_le_two_exp_min p.val (B p) t
        (by exact_mod_cast (hP p.val p.property).one_le)
  apply hh.trans_eq
  rw [prod_mul_distrib,prod_const,card_univ,Fintype.card_coe,← exp_sum,sum_neg_distrib]

/-- A genuine positive-parameter Laplace upper bound follows from a low-count
bound, with both terms retained. A zero-count bound alone does not suffice. -/
theorem countLaplace_le_lowCountFraction_add_exp (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (m : ℕ) (b t : ℝ) (ht : 0 ≤ t) :
    countLaplace P t m ≤ lowCountFraction P m b + exp (-t*b) := by
  have hh := phaseMean_mono P (f := fun r => exp (-t*intervalCount P m r))
    (g := fun r => (if intervalCount P m r ≤ b then 1 else 0) + exp (-t*b))
    (fun r => by
      dsimp only
      by_cases hr : intervalCount P m r ≤ b
      · rw [if_pos hr]
        have hn : 0 ≤ intervalCount P m r := by
          change 0 ≤ ∑ x ∈ range m, point P x r
          rw [← populationSurvivors_card]
          positivity
        have he : exp (-t*intervalCount P m r) ≤ 1 := by
          apply exp_le_one_iff.mpr
          nlinarith only [mul_nonneg ht hn]
        linarith only [he,(exp_pos (-t*b)).le]
      · rw [if_neg hr,zero_add]
        apply exp_le_exp.mpr
        exact mul_le_mul_of_nonpos_left (le_of_not_ge hr) (neg_nonpos.mpr ht))
  simpa only [phaseMean_add,phaseMean_const P hP,lowCountFraction,countLaplace] using hh

/-- A strict upper bound below the weighted neighborhood excludes a cover.
The strict Laplace upper bound is an explicit hypothesis, not established here. -/
theorem survivor_of_softCylinderLaplace (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (m : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (hupper : countLaplace P t m <
      softCylinderWeight P (fun p => (m : ℝ)/p.val+1) t)
    (r : ℕ → ℕ) : ∃ x < m, ∀ p ∈ P, ¬x ≡ r p [MOD p] := by
  classical
  by_contra hbad
  push_neg at hbad
  let s : Phase P := fun p => ⟨r p.val % p.val,
    Nat.mod_lt _ (hP p.val p.property).pos⟩
  have hs : intervalCount P m s = 0 := by
    apply count_zero_of_cover
    intro x hx
    obtain ⟨p,hp,hxp⟩ := hbad x hx
    exact ⟨⟨p,hp⟩,hxp⟩
  exact hupper.not_ge (softCylinderWeight_le_countLaplace_of_cover P hP m s hs t ht)

/-- Keeping one core phase but varying every tail coordinate gives the product
of the core cylinder mass and the tail soft weight. The caps are for the
actual core-filtered population, not the unfiltered interval. -/
theorem core_softCylinderWeight_le_countLaplace (Q R : Finset ℕ)
    (hdis : Disjoint Q R) (hQ : ∀ q ∈ Q, q.Prime) (m : ℕ)
    (r : Phase Q) (s : Phase R)
    (hcover : ∀ x ∈ populationSurvivors (range m) Q r,
      ∃ p : R, x % p.val = (s p).val)
    (B : R → ℝ)
    (hB : ∀ p, classHits (populationSurvivors (range m) Q r) p.val (s p) ≤ B p)
    (t : ℝ) (ht : 0 ≤ t) :
    softCylinderWeight R B t * (∏ q ∈ Q, (q : ℝ)⁻¹) ≤ countLaplace (Q ∪ R) t m := by
  classical
  unfold countLaplace
  rw [phaseMean_union Q R hdis]
  have he (r' : Phase Q) (s' : Phase R) :
      intervalCount (Q ∪ R) m (joinPhase Q R r' s') =
      ((populationSurvivors (populationSurvivors (range m) Q r') R s').card : ℝ) := by
    rw [← populationSurvivors_union _ _ _ hdis,populationSurvivors_card]
    rfl
  simp_rw [he]
  apply phaseMean_lower_of_cylinder Q Q (Subset.refl _) hQ r
  · intro r'
    unfold phaseMean
    positivity
  · intro r' hr'
    have heq : r' = r := funext (fun p => hr' p p.property)
    subst r'
    exact softCylinderWeight_le_population_laplace _ R s hcover B hB t ht

#print axioms softCylinderWeight_le_population_laplace
#print axioms softCylinderWeight_le_countLaplace_of_cover
#print axioms exp_softCost_le_softCylinderWeight
#print axioms softCylinderWeight_le_two_pow_exp_softCost
#print axioms countLaplace_le_lowCountFraction_add_exp
#print axioms survivor_of_softCylinderLaplace
#print axioms core_softCylinderWeight_le_countLaplace
end Erdos970.GapAverages
