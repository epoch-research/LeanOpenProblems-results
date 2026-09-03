import Submission.GaussianPolynomialBoxCounts

/-! A Gaussian polynomial Lambda-squared upper bound with the full
root-count-weighted lattice error. The theorem is valid for arbitrary finite
weights normalized at one. It does not assert that weights producing a
sublinear prime-path count exist. -/
namespace Erdos952Investigation.GaussianWeightedSieve
open GaussianIdealBoxCounts GaussianPolynomialBoxCounts
open scoped BigOperators Classical
set_option maxHeartbeats 0
noncomputable section

local instance : GCDMonoid GaussianInt := EuclideanDomain.gcdMonoid GaussianInt
local instance (a : GaussianInt) (R : ℕ) : Fintype (Box a R) := Fintype.ofFinite _

lemma count_box_sum (p : GaussianInt → Prop) (a : GaussianInt) (R : ℕ) :
    (Nat.card {t : GaussianInt // InBox a R t ∧ p t} : ℝ) =
      ∑ t : Box a R, if p t.val then 1 else 0 := by
  rw [← Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (InBox a R) p)]
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype,Finset.sum_boole]

lemma evalCount_sum (g : GaussianInt) (P : Polynomial GaussianInt)
    (a : GaussianInt) (R : ℕ) :
    (evalCount g P a R : ℝ) = ∑ t : Box a R, if g ∣ P.eval t.val then 1 else 0 :=
  count_box_sum _ a R

/-- A deliberately general sifted condition: no modulus in D except the
chosen unit 1 divides the polynomial value. Later applications must verify
that their prime translates satisfy this condition. -/
def Sifted (D : Finset GaussianInt) (P : Polynomial GaussianInt) (t : GaussianInt) : Prop :=
  ∀ d ∈ D, d ≠ 1 → ¬ d ∣ P.eval t

def siftedCount (D : Finset GaussianInt) (P : Polynomial GaussianInt)
    (a : GaussianInt) (R : ℕ) : ℕ :=
  Nat.card {t : GaussianInt // InBox a R t ∧ Sifted D P t}

lemma weights_eq_one (D : Finset GaussianInt) (hD : 1 ∈ D)
    (w : GaussianInt → ℝ) (hw : w 1 = 1) (P : Polynomial GaussianInt)
    (t : GaussianInt) (ht : Sifted D P t) :
    (∑ d ∈ D, if d ∣ P.eval t then w d else 0) = 1 := by
  rw [Finset.sum_eq_single 1]
  · simp [hw]
  · intro d hd hne
    simp [ht d hd hne]
  · exact fun h => False.elim (h hD)

/-- The unapproximated Lambda-squared inequality, before estimating any
congruence count. It requires no squarefreeness or multiplicativity assumption. -/
theorem lambda_sq_sieve (D : Finset GaussianInt) (hD : 1 ∈ D)
    (w : GaussianInt → ℝ) (hw : w 1 = 1) (P : Polynomial GaussianInt)
    (a : GaussianInt) (R : ℕ) :
    (siftedCount D P a R : ℝ) ≤
      ∑ d ∈ D, ∑ e ∈ D, w d*w e*(evalCount (lcm d e) P a R : ℝ) := by
  have hpoint (d e t : GaussianInt) :
      (if d ∣ P.eval t then w d else 0)*(if e ∣ P.eval t then w e else 0) =
      w d*w e*(if lcm d e ∣ P.eval t then 1 else 0) := by
    by_cases hd : d ∣ P.eval t <;> by_cases he : e ∣ P.eval t <;>
      simp [hd,he,lcm_dvd_iff]
  calc
    (siftedCount D P a R : ℝ) =
        ∑ t : Box a R, if Sifted D P t.val then 1 else 0 := count_box_sum _ a R
    _ ≤ ∑ t : Box a R, (∑ d ∈ D, if d ∣ P.eval t.val then w d else 0)^2 := by
      apply Finset.sum_le_sum
      intro t _
      by_cases ht : Sifted D P t.val
      · rw [if_pos ht,weights_eq_one D hD w hw P t.val ht]
        norm_num
      · rw [if_neg ht]
        exact sq_nonneg _
    _ = ∑ t : Box a R, ∑ d ∈ D, ∑ e ∈ D,
        w d*w e*(if lcm d e ∣ P.eval t.val then 1 else 0) := by
      simp_rw [pow_two,Finset.sum_mul_sum,hpoint]
    _ = ∑ d ∈ D, ∑ e ∈ D, ∑ t : Box a R,
        w d*w e*(if lcm d e ∣ P.eval t.val then 1 else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.sum_comm]
    _ = _ := by simp_rw [← Finset.mul_sum,← evalCount_sum]

/-- Root count extended by zero at the zero modulus. All discrepancy
applications below still explicitly require a nonzero modulus. -/
def rho (P : Polynomial GaussianInt) (g : GaussianInt) : ℕ :=
  if hg : g ≠ 0 then rootCount g hg P else 0

lemma rho_of_ne_zero (P : Polynomial GaussianInt) (g : GaussianInt) (hg : g ≠ 0) :
    rho P g = rootCount g hg P := by simp [rho,hg]

/-- Units have zero counting error, not the generic O(R) boundary estimate. -/
def remainderBound (P : Polynomial GaussianInt) (g : GaussianInt) (R : ℕ) : ℝ :=
  if IsUnit g then 0 else (rho P g : ℝ)*(4*(R : ℝ)/Real.sqrt (g.norm.natAbs : ℝ)+4)

lemma eval_count_error (P : Polynomial GaussianInt) (g : GaussianInt)
    (hg : g ≠ 0) (a : GaussianInt) (R : ℕ) :
    |(evalCount g P a R : ℝ)-(rho P g : ℝ)*(R : ℝ)^2/(g.norm.natAbs : ℝ)| ≤
      remainderBound P g R := by
  by_cases hu : IsUnit g
  · have hn : g.norm = 1 :=
      (Zsqrtd.norm_eq_one_iff' (by norm_num : (-1 : ℤ) ≤ 0) g).mpr hu
    simp [rho_of_ne_zero P g hg,rootCount_of_isUnit g hg P hu,
      evalCount_of_isUnit g P hu a R,hn,remainderBound,hu]
  · rw [remainderBound,if_neg hu,rho_of_ne_zero P g hg]
    exact eval_count_sqrt_error g hg P a R

def mainSum (D : Finset GaussianInt) (w : GaussianInt → ℝ)
    (P : Polynomial GaussianInt) : ℝ :=
  ∑ d ∈ D, ∑ e ∈ D, w d*w e*(rho P (lcm d e) : ℝ)/((lcm d e).norm.natAbs : ℝ)

def errorSum (D : Finset GaussianInt) (w : GaussianInt → ℝ)
    (P : Polynomial GaussianInt) (R : ℕ) : ℝ :=
  ∑ d ∈ D, ∑ e ∈ D, |w d*w e| *remainderBound P (lcm d e) R

/-- An explicit Gaussian Lambda-squared sieve bound. Both terms retain all
weight and root-count dependence. No bound uniform in polynomial degree is
silently substituted for this expression. -/
theorem sifted_count_le_main_error (D : Finset GaussianInt)
    (hD1 : 1 ∈ D) (hD0 : ∀ d ∈ D, d ≠ 0)
    (w : GaussianInt → ℝ) (hw : w 1 = 1) (P : Polynomial GaussianInt)
    (a : GaussianInt) (R : ℕ) :
    (siftedCount D P a R : ℝ) ≤ (R : ℝ)^2*mainSum D w P+errorSum D w P R := by
  have hp (d : GaussianInt) (hd : d ∈ D) (e : GaussianInt) (he : e ∈ D) :
      w d*w e*(evalCount (lcm d e) P a R : ℝ) ≤
      (R : ℝ)^2*(w d*w e*(rho P (lcm d e) : ℝ)/((lcm d e).norm.natAbs : ℝ))+
        |w d*w e| *remainderBound P (lcm d e) R := by
    have hg : lcm d e ≠ 0 := by
      rw [Ne, lcm_eq_zero_iff]
      exact not_or.mpr ⟨hD0 d hd,hD0 e he⟩
    have hh := eval_count_error P (lcm d e) hg a R
    have ha := le_abs_self (w d*w e*((evalCount (lcm d e) P a R : ℝ)-
      (rho P (lcm d e) : ℝ)*(R : ℝ)^2/((lcm d e).norm.natAbs : ℝ)))
    rw [abs_mul] at ha
    have hm := mul_le_mul_of_nonneg_left hh (abs_nonneg (w d*w e))
    have h := ha.trans hm
    calc
      _ = (R : ℝ)^2*(w d*w e*(rho P (lcm d e) : ℝ)/((lcm d e).norm.natAbs : ℝ))+
          w d*w e*((evalCount (lcm d e) P a R : ℝ)-
            (rho P (lcm d e) : ℝ)*(R : ℝ)^2/((lcm d e).norm.natAbs : ℝ)) := by ring
      _ ≤ _ := add_le_add le_rfl h
  apply (lambda_sq_sieve D hD1 w hw P a R).trans
  calc
    _ ≤ ∑ d ∈ D, ∑ e ∈ D,
        ((R : ℝ)^2*(w d*w e*(rho P (lcm d e) : ℝ)/((lcm d e).norm.natAbs : ℝ))+
          |w d*w e| *remainderBound P (lcm d e) R) :=
      Finset.sum_le_sum (fun d hd => Finset.sum_le_sum (fun e he => hp d hd e he))
    _ = _ := by simp only [mainSum,errorSum,Finset.sum_add_distrib,Finset.mul_sum]

#print axioms lambda_sq_sieve
#print axioms eval_count_error
#print axioms sifted_count_le_main_error
end
end Erdos952Investigation.GaussianWeightedSieve
