import Submission.GaussianSmoothedCosetCounts
import Submission.GaussianPolynomialBoxCounts

/-! Smoothed counts for polynomial congruences. The weight is the normalized
number of ways to express a point as a difference of points of two boxes.
Every point has weight at most one. The congruence error is bounded by 64
per root class when the ideal index is at most R^2. -/
namespace Erdos952Investigation.GaussianSmoothedPolynomialCounts
open GaussianIdealRepresentatives GaussianIdealBoxCounts GaussianPolynomialBoxCounts
open GaussianSmoothedCosetCounts
open scoped BigOperators Classical
set_option maxHeartbeats 0
noncomputable section

local instance (a : GaussianInt) (R : ℕ) : Fintype (Box a R) := Fintype.ofFinite _

def pairPredicateCount (p : GaussianInt → Prop) (a b : GaussianInt) (R : ℕ) : ℕ :=
  Nat.card {uv : Box a R × Box b R // p (uv.1.val-uv.2.val)}

def smoothedCount (p : GaussianInt → Prop) (a b : GaussianInt) (R : ℕ) : ℝ :=
  (pairPredicateCount p a b R : ℝ)/(R : ℝ)^2

lemma pairPredicateCount_sum (p : GaussianInt → Prop) (a b : GaussianInt) (R : ℕ) :
    (pairPredicateCount p a b R : ℝ) =
      ∑ uv : Box a R × Box b R, if p (uv.1.val-uv.2.val) then 1 else 0 := by
  rw [pairPredicateCount,Nat.card_eq_fintype_card,Fintype.card_subtype,Finset.sum_boole]

lemma smoothedCount_sum (p : GaussianInt → Prop) (a b : GaussianInt) (R : ℕ) :
    smoothedCount p a b R =
      (∑ uv : Box a R × Box b R, if p (uv.1.val-uv.2.val) then 1 else 0)/(R : ℝ)^2 := by
  rw [smoothedCount,pairPredicateCount_sum]

lemma smoothedCount_congr (p q : GaussianInt → Prop) (h : ∀ z, p z ↔ q z)
    (a b : GaussianInt) (R : ℕ) : smoothedCount p a b R = smoothedCount q a b R := by
  have hpq : p = q := funext (fun z => propext (h z))
  rw [hpq]

lemma pairResidueCount_eq_sum (g : GaussianInt)
    (S : Finset (GaussianInt ⧸ multiples g)) (a b : GaussianInt) (R : ℕ) :
    pairPredicateCount (fun z => Submodule.Quotient.mk z ∈ S) a b R =
      ∑ c ∈ S, pairCount g c a b R := by
  let e := Equiv.sigmaSubtypeFiberEquivSubtype
    (fun uv : Box a R × Box b R => (Submodule.Quotient.mk (uv.1.val-uv.2.val) : GaussianInt ⧸ multiples g))
    (p := fun uv => Submodule.Quotient.mk (uv.1.val-uv.2.val) ∈ S)
    (q := fun c => c ∈ S) (fun _ => Iff.rfl)
  rw [pairPredicateCount,Nat.card_congr e.symm,Nat.card_sigma]
  exact Finset.sum_coe_sort S (fun c => pairCount g c a b R)

lemma smoothedResidueCount_eq_sum (g : GaussianInt)
    (S : Finset (GaussianInt ⧸ multiples g)) (a b : GaussianInt) (R : ℕ) :
    smoothedCount (fun z => Submodule.Quotient.mk z ∈ S) a b R =
      ∑ c ∈ S, smoothedCosetCount g c a b R := by
  rw [smoothedCount,pairResidueCount_eq_sum,Nat.cast_sum,Finset.sum_div]
  rfl

theorem smoothed_residue_error (g : GaussianInt) (hg : g ≠ 0)
    (S : Finset (GaussianInt ⧸ multiples g)) (a b : GaussianInt) (R : ℕ)
    (hR : 0 < R) (hmR : g.norm.natAbs ≤ R^2) :
    |smoothedCount (fun z => Submodule.Quotient.mk z ∈ S) a b R-
      (S.card : ℝ)*(R : ℝ)^2/(g.norm.natAbs : ℝ)| ≤ 64*(S.card : ℝ) := by
  rw [smoothedResidueCount_eq_sum]
  have he : (∑ c ∈ S, smoothedCosetCount g c a b R)-
      (S.card : ℝ)*(R : ℝ)^2/(g.norm.natAbs : ℝ) =
      ∑ c ∈ S, (smoothedCosetCount g c a b R-(R : ℝ)^2/(g.norm.natAbs : ℝ)) := by
    rw [Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul]
    ring
  rw [he]
  calc
    _ ≤ ∑ c ∈ S, |smoothedCosetCount g c a b R-(R : ℝ)^2/(g.norm.natAbs : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _c ∈ S, (64 : ℝ) := Finset.sum_le_sum
      (fun c _ => smoothed_coset_error g hg c a b R hR hmR)
    _ = _ := by simp [mul_comm]

def smoothedEvalCount (g : GaussianInt) (P : Polynomial GaussianInt)
    (a b : GaussianInt) (R : ℕ) : ℝ := smoothedCount (fun z => g ∣ P.eval z) a b R

/-- Smoothed polynomial congruence counting, including the full number of
root classes in the error. -/
theorem smoothed_eval_error (g : GaussianInt) (hg : g ≠ 0)
    (P : Polynomial GaussianInt) (a b : GaussianInt) (R : ℕ)
    (hR : 0 < R) (hmR : g.norm.natAbs ≤ R^2) :
    |smoothedEvalCount g P a b R-
      (rootCount g hg P : ℝ)*(R : ℝ)^2/(g.norm.natAbs : ℝ)| ≤
        64*(rootCount g hg P : ℝ) := by
  have he := smoothedCount_congr (fun z => g ∣ P.eval z)
    (fun z => Submodule.Quotient.mk z ∈ rootClasses g hg P)
    (fun z => (mem_rootClasses g hg P z).symm) a b R
  rw [smoothedEvalCount,he]
  exact smoothed_residue_error g hg (rootClasses g hg P) a b R hR hmR

/-- The triangular weight of a single point is at most one. Consequently
a finite exceptional set contributes no more than its cardinality. -/
theorem smoothed_finset_le (E : Finset GaussianInt) (a b : GaussianInt) (R : ℕ)
    (hR : 0 < R) : smoothedCount (fun z => z ∈ E) a b R ≤ E.card := by
  let f : {uv : Box a R × Box b R // uv.1.val-uv.2.val ∈ E} → E × Box b R :=
    fun uv => (⟨uv.val.1.val-uv.val.2.val,uv.property⟩,uv.val.2)
  have hf : Function.Injective f := by
    intro u v he
    have hv : u.val.2 = v.val.2 := congrArg (fun x : E × Box b R => x.2) he
    have hd : u.val.1.val-u.val.2.val = v.val.1.val-v.val.2.val :=
      congrArg (fun x : E × Box b R => x.1.val) he
    rw [hv] at hd
    exact Subtype.ext (Prod.ext (Subtype.ext (sub_left_injective hd)) hv)
  have hh := Nat.card_le_card_of_injective f hf
  have hE : Nat.card E = E.card := by simp
  rw [Nat.card_prod,box_card,hE] at hh
  have hcast : (pairPredicateCount (fun z => z ∈ E) a b R : ℝ) ≤
      (E.card : ℝ)*(R : ℝ)^2 := by exact_mod_cast hh
  have hRp : 0 < (R : ℝ)^2 := sq_pos_of_pos (by exact_mod_cast hR)
  exact (div_le_iff₀ hRp).mpr hcast

lemma smoothed_count_le_add (p q r : GaussianInt → Prop) (a b : GaussianInt) (R : ℕ)
    (h : ∀ z, p z → q z ∨ r z) :
    smoothedCount p a b R ≤ smoothedCount q a b R+smoothedCount r a b R := by
  simp only [smoothedCount_sum,← add_div,← Finset.sum_add_distrib]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  apply Finset.sum_le_sum
  intro uv _
  by_cases hp : p (uv.1.val-uv.2.val)
  · rcases h _ hp with hq | hr
    · simp only [if_pos hp,if_pos hq]
      split_ifs <;> norm_num
    · simp only [if_pos hp,if_pos hr]
      split_ifs <;> norm_num
  · rw [if_neg hp]
    split_ifs <;> norm_num

#print axioms smoothed_eval_error
#print axioms smoothed_finset_le
#print axioms smoothed_count_le_add
end
end Erdos952Investigation.GaussianSmoothedPolynomialCounts
