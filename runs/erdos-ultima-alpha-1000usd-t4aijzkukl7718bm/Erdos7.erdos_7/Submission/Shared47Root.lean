import Submission.Shared47RootRows
import Submission.Shared47Real
import Submission.TernaryTwoGeometricLaw
import Submission.TernaryTwoBlockCompression

/-! Exact finite-depth root certificate for the ternary-two shared-prefix
comparison. This alone is not an arithmetic covering obstruction. -/
namespace Erdos7Shared47Root
open scoped BigOperators
open Erdos7Shared47Rows Erdos7Shared47Metadata Erdos7Shared47Real
open Erdos7TernaryTwoSharedPrefix Erdos7TernaryTwoSharedComparison
open Erdos7TernaryTwoGeometricLaw
set_option maxHeartbeats 3000000

lemma root_good : Good stage7.F := stage7_metadata.2.2.2.2.1

lemma geo_bound (E : ℕ) (n : ℚ) (hn : 1≤n) :
    geometricSum E (evalR stage7.F) n ≤ (mixture 5 1 (1/5) stage7.F n : ℝ) := by
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn
  have hh := geometricSum_le_budget E 24 (evalR stage7.F)
    (evalR_monotone stage7.F root_good) 24 (slope stage7.F) n
    (slope_nonneg stage7.F root_good) (evalR_tail stage7.F root_good)
    (by linarith) (by norm_num; linarith)
  rw [← mixture_cast]
  simpa only [Rat.cast_ofNat,Rat.cast_one,Rat.cast_div] using hh

lemma geo_aggregate (E : ℕ) :
    (∑ n : Fin 3,(starWeight n : ℝ)/5*geometricSum E (evalR stage7.F) (n.val+1)) ≤ (geoRoot:ℝ) := by
  have h1 := geo_bound E 1 (by norm_num)
  have h2 := geo_bound E 2 (by norm_num)
  have h3 := geo_bound E 3 (by norm_num)
  norm_num only [Rat.cast_one,Rat.cast_ofNat] at h1 h2 h3
  norm_num [starWeight,Fin.sum_univ_succ]
  unfold geoRoot
  push_cast
  linarith

lemma corner_cost (E : ℕ) (c : Fin 10) :
    1-(∑ z,refWeight c (geometricWeight E) z)+
      (∑ z,refWeight c (geometricWeight E) z*evalR stage7.F (refCount (geometricLength E) z)) ≤
      ((if c.val<5 then shortRoot else longRoot : ℚ):ℝ) := by
  rw [reference_eval,reference_mass]
  have hg := geo_aggregate E
  norm_num [starWeight,Fin.sum_univ_succ] at hg
  have h1 := evalR_cast stage7.F (1:ℚ)
  have h2 := evalR_cast stage7.F (2:ℚ)
  have h3 := evalR_cast stage7.F (3:ℚ)
  norm_num only [Rat.cast_one,Rat.cast_ofNat] at h1 h2 h3
  by_cases hc : c.val<5
  · simp only [if_pos hc,lowNum]
    norm_num [Fin.sum_univ_succ,starWeight]
    rw [h1,h2,h3]
    unfold shortRoot
    push_cast
    linarith
  · simp only [if_neg hc,lowNum]
    norm_num [Fin.sum_univ_succ,starWeight]
    rw [h1,h2,h3]
    unfold longRoot
    push_cast
    linarith

lemma shortRoot_le_limit : shortRoot≤(999/1000:ℚ) := by rw [shortRoot_exact]; norm_num
lemma longRoot_le_limit : longRoot≤(999/1000:ℚ) := by rw [longRoot_exact]; norm_num

lemma corner_cost_le (E : ℕ) (c : Fin 10) :
    1-(∑ z,refWeight c (geometricWeight E) z)+
      (∑ z,refWeight c (geometricWeight E) z*evalR stage7.F (refCount (geometricLength E) z)) ≤
      (999:ℝ)/1000 := by
  apply (corner_cost E c).trans
  split_ifs
  · have hh : (shortRoot:ℝ)≤((999/1000:ℚ):ℝ) := Rat.cast_le.mpr shortRoot_le_limit
    norm_num at hh
    exact hh
  · have hh : (longRoot:ℝ)≤((999/1000:ℚ):ℝ) := Rat.cast_le.mpr longRoot_le_limit
    norm_num at hh
    exact hh

lemma mixed_cost_le (E : ℕ) (w : Fin 10 → ℝ) (hw : ∀ c,0≤w c) (hm : (∑ c,w c)=1) :
    1-(∑ z,Erdos7TernaryTwoMixedComparison.refWeight w (geometricWeight E) z)+
      (∑ z,Erdos7TernaryTwoMixedComparison.refWeight w (geometricWeight E) z *
        evalR stage7.F (refCount (geometricLength E) z)) ≤ (999:ℝ)/1000 := by
  have hmass : (∑ z,Erdos7TernaryTwoMixedComparison.refWeight w (geometricWeight E) z)=
      ∑ c,w c*(∑ z,refWeight c (geometricWeight E) z) := by
    unfold Erdos7TernaryTwoMixedComparison.refWeight
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum]
  have heval : (∑ z,Erdos7TernaryTwoMixedComparison.refWeight w (geometricWeight E) z *
      evalR stage7.F (refCount (geometricLength E) z))=
      ∑ c,w c*(∑ z,refWeight c (geometricWeight E) z *
        evalR stage7.F (refCount (geometricLength E) z)) := by
    unfold Erdos7TernaryTwoMixedComparison.refWeight
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [mul_assoc,← Finset.mul_sum]
  rw [hmass,heval]
  have hh := Finset.sum_le_sum (fun c (_ : c∈Finset.univ) =>
    mul_le_mul_of_nonneg_left (corner_cost_le E c) (hw c))
  simp only [mul_add,mul_sub,mul_one,Finset.sum_add_distrib,Finset.sum_sub_distrib,hm] at hh
  simpa only [← Finset.sum_mul,hm,one_mul] using hh

/-- A uniform exact margin remains for every finite geometric depth and
every positive convex mixture of current profiles. -/
lemma mixed_gap (E : ℕ) (w : Fin 10 → ℝ) (hw : ∀ c,0≤w c) (hm : (∑ c,w c)=1) :
    (∑ z,Erdos7TernaryTwoMixedComparison.refWeight w (geometricWeight E) z *
      evalR stage7.F (refCount (geometricLength E) z)) ≤
      (∑ z,Erdos7TernaryTwoMixedComparison.refWeight w (geometricWeight E) z)-1/1000 := by
  have hh := mixed_cost_le E w hw hm
  linarith

/-- The certified root excludes any family budget meeting the actual group
marginal and slice-profile hypotheses. The arithmetic extraction is separate. -/
theorem block_not_budget {A α : Type} [Fintype A] [Nonempty α]
    (w : Fin 10 → ℝ) (hw : ∀ c,0≤w c) (hm : (∑ c,w c)=1)
    (E : ℕ) (ν : Fin 5 → A → ℝ) (hν : ∀ x y,0≤ν x y)
    (hmass : ∀ x,(∑ y,ν x y)=Erdos7TernaryTwoBlockCompression.retention w x/5)
    (K : α → ℕ → Fin 5 → ℝ) (s : α → ℕ → Fin 5 → A → ℝ)
    (hK : ∀ a j,j<E+1 → ∀ x,0≤K a (j+1) x)
    (hs : ∀ a j,j<E+1 → ∀ x y,0≤s a j x y)
    (hsK : ∀ a j,j<E+1 → ∀ x y,s a j x y≤K a (j+1) x)
    (hmarg : ∀ a j,j<E+1 → ∀ x,(∑ y,ν x y*s a j x y)≤
      (1/5)*Erdos7TernaryTwoBlockCompression.tail E j*K a (j+1) x)
    (hprofile : ∀ a j,j<E+2 → ∃ g : Fin 5 → ℝ,
      g∈convexHull ℝ (Set.range Erdos7TernaryTwoCoherentMixture.corner) ∧ ∀ x,K a j x≤g x) :
    ¬ Erdos7BackwardFamilyBudget.HasBudget (fun z : Fin 5 × A => ν z.1 z.2)
      (fun a z => K a 0 z.1+∑ j∈Finset.range (E+1),s a j z.1 z.2)
      (evalR stage7.F) 1 (3*((E:ℝ)+2)) := by
  apply Erdos7TernaryTwoMixedComparison.not_budget_of_common_reference
    (fun z : Fin 5 × A => ν z.1 z.2)
    (fun a z => K a 0 z.1+∑ j∈Finset.range (E+1),s a j z.1 z.2)
    (evalR stage7.F) 1 (3*((E:ℝ)+2))
    (Erdos7TernaryTwoMixedComparison.refWeight w (geometricWeight E))
    (Erdos7TernaryTwoMixedComparison.ref_nonneg w _ hw (geometric_nonneg E))
    (fun z => (refCount (geometricLength E) z : ℝ))
  · intro z
    constructor
    · exact_mod_cast (reference_count_bounds E z).1
    · exact_mod_cast (reference_count_bounds E z).2
  · intro a φ hφ hmφ
    simpa only [Fintype.sum_prod_type] using
      Erdos7TernaryTwoBlockCompression.block_comparison w hw hm E ν hν hmass
        (K a) (s a) (hK a) (hs a) (hsK a) (hmarg a) (hprofile a) φ hφ hmφ
  · have hh := mixed_gap E w hw hm
    rw [Erdos7TernaryTwoBlockCompression.reference_mass_eq w hm E ν hmass] at hh
    rw [Fintype.sum_prod_type]
    linarith

#print axioms mixed_gap
#print axioms block_not_budget

#print axioms geo_aggregate
#print axioms corner_cost_le
end Erdos7Shared47Root
