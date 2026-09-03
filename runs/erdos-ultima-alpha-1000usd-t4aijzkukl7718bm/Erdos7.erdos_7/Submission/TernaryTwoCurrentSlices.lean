import Submission.RectangleFamilies
import Submission.TernaryTwoFamilySlices
import Submission.TernaryTwoCurrentPadding

/-! Actual current slices and feasible full-profile padding at the first5
step. No arithmetic completion or irredundance is required. -/
namespace Erdos7TernaryTwoCurrentSlices
open scoped BigOperators
open Erdos7CompleteFamilyModel Erdos7TernaryTwoFamilySlices
open Erdos7TernaryTwoCoherentMixture Erdos7TernaryTwoCurrentPadding
set_option maxHeartbeats 3000000
set_option autoImplicit false
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable
variable (E : Fin 14 → ℕ)

noncomputable def zeroFamily : Family E (exponent E) 2 := sliceFamily E 2 (fun _ => 0)

lemma current_labels (a : Fin (E 1)) :
    (zeroFamily E).labels.filter (fun k => exponent E k 1=a.val+1)=
      (currentFamily E 1 (by omega) a).labels := by
  ext k
  simp only [Finset.mem_filter,zeroFamily,sliceFamily_labels,currentFamily_labels]
  constructor
  · rintro ⟨hrest,h1⟩
    refine ⟨h1,fun j hj => ?_⟩
    exact congrArg Fin.val (hrest j hj)
  · rintro ⟨h1,hrest⟩
    refine ⟨fun j hj => Fin.ext (hrest j hj),h1⟩

variable (A : Fin 14 → Type) [∀ i,Fintype (A i)] [∀ i,Nonempty (A i)] [∀ i,DecidableEq (A i)]
variable (X : Pattern E → ∀ i,Finset (A i)) (ξ : Fin 5 → ∀ i,A i)

lemma current_slice (a : Fin (E 1)) (x : Fin 5) :
    slice A X ξ (zeroFamily E) (a.val+1) x=count A X (currentFamily E 1 (by omega) a) (ξ x) := by
  unfold Erdos7TernaryTwoFamilySlices.slice count
  rw [current_labels]
  rfl

theorem current_corners (hE : E 0=2)
    (hbranch : ∀ k,exponent E k 0=1 → ∃ q : Fin 2,∀ x,
      indicator A 1 (exponent E k) (X k) (ξ x)≤(if branch x=q then (1:ℝ) else 0))
    (hpoint : ∀ k,exponent E k 0=2 → ∃ y : Fin 5,∀ x,
      indicator A 1 (exponent E k) (X k) (ξ x)≤(if x=y then (1:ℝ) else 0)) :
    ∃ c : Fin (E 1) → Fin 10,∀ a x,
      count A X (currentFamily E 1 (by omega) a) (ξ x)≤corner (c a) x := by
  have hh (a : Fin (E 1)) := slice_single_corner A X ξ (zeroFamily E) (exponent_bound E)
    hE (by rfl) hbranch hpoint (a.val+1) (by omega)
  choose c hc using hh
  refine ⟨c,fun a x => ?_⟩
  rw [← current_slice]
  exact hc a x

noncomputable def weight (R : ℕ) (a : Fin R) : ℝ := 4/(5:ℝ)^(a.val+1)
lemma weight_nonneg (R : ℕ) (a : Fin R) : 0≤weight R a := by unfold weight; positivity
lemma weight_mass_exact (R : ℕ) : (∑ a,weight R a)=1-1/(5:ℝ)^R := by
  induction R with
  | zero => simp [weight]
  | succ R ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [weight,Fin.val_castSucc,Fin.val_last] at *
    rw [ih,pow_succ]
    field_simp
    ring
lemma weight_mass (R : ℕ) : (∑ a,weight R a)≤1 := by
  rw [weight_mass_exact]
  have hh : (0:ℝ)≤1/(5:ℝ)^R := by positivity
  linarith

/-- Actual current congruences admit an avoiding cap1 kernel whose retained
mass is an exact convex mixture of full ternary profiles. -/
theorem exists_current_kernel (hE : E 0=2)
    (hbranch : ∀ k,exponent E k 0=1 → ∃ q : Fin 2,∀ x,
      indicator A 1 (exponent E k) (X k) (ξ x)≤(if branch x=q then (1:ℝ) else 0))
    (hpoint : ∀ k,exponent E k 0=2 → ∃ y : Fin 5,∀ x,
      indicator A 1 (exponent E k) (X k) (ξ x)≤(if x=y then (1:ℝ) else 0))
    (ρ : A 1 → ℝ) (hρ : ∀ y,0≤ρ y) (hρmass : (∑ y,ρ y)=1)
    (hd : ∀ k,exponent E k 1≠0 →
      (∑ y,if y∈X k 1 then ρ y else 0)≤1/(5:ℝ)^(exponent E k 1)) :
    ∃ (c : Fin (E 1) → Fin 10) (ν : Fin 5 → A 1 → ℝ),
      (∀ x y,0≤ν x y) ∧ (∀ x y,ν x y≤ρ y/5) ∧
      (∀ x y,currentBad A E X 1 (by omega) (ξ x) y → ν x y=0) ∧
      (∀ x,(∑ y,ν x y)=(1-paddedCount (weight (E 1)) 0 c x/4)/5) := by
  obtain ⟨c,hc⟩ := current_corners E A X ξ hE hbranch hpoint
  have hbad (x : Fin 5) :
      (∑ y,if currentBad A E X 1 (by omega) (ξ x) y then ρ y else 0)≤
      (∑ a,weight (E 1) a*(Erdos7TernaryTwoSharedPrefix.count (c a) x : ℝ))/4 := by
    have hh := currentBad_density A E X 1 (by omega) (ξ x) ρ hρ
      (fun j => 1/(5:ℝ)^(j+1)) (fun k hk => by
        simpa only [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk)] using hd k hk)
    apply hh.trans
    calc
      _ ≤ ∑ a : Fin (E 1),(1/(5:ℝ)^(a.val+1))*corner (c a) x :=
        Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hc a x) (by positivity))
      _ = _ := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro a _
        unfold weight corner
        ring
  obtain ⟨ν,hν,hcap,hzero,hmass⟩ := exists_padded_kernel (weight (E 1))
    (weight_nonneg (E 1)) (weight_mass (E 1)) 0 c ρ hρ hρmass
    (fun x y => currentBad A E X 1 (by omega) (ξ x) y) hbad
  exact ⟨c,ν,hν,hcap,hzero,hmass⟩

#print axioms exists_current_kernel
end Erdos7TernaryTwoCurrentSlices
