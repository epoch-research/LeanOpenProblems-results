import FormalConjecturesUtil
import Submission.ConditionalThetaWeighted

/-! An explicitly conditional density-gap reduction. The predicate DensityGap
is not proved here. If supplied, it yields the weighted estimate and a direct
whole-host square bound, without regularization. This does not settle Erdős 713. -/
open Finset SimpleGraph
namespace Erdos713ThetaDensityGapReduction
open Erdos713ThetaGram Erdos713ThetaCross Erdos713ThetaSplit Erdos713GlobalLight
open Erdos713GlobalTheta Erdos713ConditionalThetaWeighted
set_option maxHeartbeats 2000000

/-- The proposed local row/light-pair bound. This is an unproved hypothesis. -/
def DensityGap (C : ℕ) : Prop :=
  ∀ (A B : Type) [Fintype A] [Fintype B] (R : A → B → Prop),
    ¬ HasTheta R → (Nat.card B)^2 ≤ C*(Nat.card A+lightCount R)

lemma weighted_of_quadratic_gap {E m k t D C K : ℝ}
    (hm : 0 ≤ m) (hk : 0 ≤ k) (ht : 0 ≤ t) (hD : 0 ≤ D)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hE : E ≤ D*k) (hcap : D ≤ K*k)
    (hgap : k^2 ≤ C*(m+t)) :
    E ≤ (2*K*C+Real.sqrt (2*C))*(m+D*Real.sqrt t) := by
  have hs : 0 ≤ Real.sqrt (2*C) := Real.sqrt_nonneg _
  have hcoef : 0 ≤ 2*K*C+Real.sqrt (2*C) := by positivity
  have hleft : 2*K*C ≤ 2*K*C+Real.sqrt (2*C) := le_add_of_nonneg_right hs
  have hright : Real.sqrt (2*C) ≤ 2*K*C+Real.sqrt (2*C) :=
    le_add_of_nonneg_left (by positivity)
  by_cases hsmall : k^2 ≤ 2*C*m
  · calc
      E ≤ D*k := hE
      _ ≤ (K*k)*k := mul_le_mul_of_nonneg_right hcap hk
      _ = K*k^2 := by ring
      _ ≤ K*(2*C*m) := mul_le_mul_of_nonneg_left hsmall hK
      _ = (2*K*C)*m := by ring
      _ ≤ (2*K*C+Real.sqrt (2*C))*m := mul_le_mul_of_nonneg_right hleft hm
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) hcoef
  · have hkt : k^2 ≤ 2*C*t := by linarith
    have hroot : k ≤ Real.sqrt (2*C)*Real.sqrt t := by
      have hsq : (Real.sqrt (2*C)*Real.sqrt t)^2 = 2*C*t := by
        rw [mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt ht]
      have hnon : 0 ≤ Real.sqrt (2*C)*Real.sqrt t := by positivity
      nlinarith only [hkt,hsq,hnon,hk]
    calc
      E ≤ D*k := hE
      _ ≤ D*(Real.sqrt (2*C)*Real.sqrt t) := mul_le_mul_of_nonneg_left hroot hD
      _ = Real.sqrt (2*C)*(D*Real.sqrt t) := by ring
      _ ≤ (2*K*C+Real.sqrt (2*C))*(D*Real.sqrt t) :=
        mul_le_mul_of_nonneg_right hright (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hm) hcoef

/-- A density-gap constant supplies the formerly separate capped weighted
hypothesis, with an explicit constant for each nonnegative cap ratio K. -/
theorem cappedWeighted_of_densityGap {C : ℕ} (h : DensityGap C) {K : ℝ} (hK : 0 ≤ K) :
    CappedWeighted K (2*K*C+Real.sqrt (2*C)) := by
  intro A B instA instB R D hf hD hcap
  classical
  have he : Nat.card {p : A × B // R p.1 p.2} ≤ D*Nat.card B := by
    rw [edge_card_eq_cols]
    calc
      _ ≤ ∑ _b : B, D := sum_le_sum (fun b _ => hD b)
      _ = _ := by simp [Nat.card_eq_fintype_card,Nat.mul_comm]
  apply weighted_of_quadratic_gap (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) hK (by exact_mod_cast he) hcap
  exact_mod_cast h A B R hf

/-- The same local density constant can instead be summed over all links.
The original number of rows, not a pruned host order, occurs on the right. -/
theorem sum_row_squares {C : ℕ} (h : DensityGap C) {A B : Type}
    [Fintype A] [Fintype B] (R : A → B → Prop)
    (hf : ∀ a, ¬ HasTheta (link R a)) :
    (∑ a : A, (Nat.card {b // R a b})^2) ≤
      C*((Fintype.card A)^2+3*(Fintype.card B)^2) := by
  classical
  have hlocal (a : A) : (Nat.card {b // R a b})^2 ≤
      C*(Fintype.card A+(lightPairs R 3 a).card) := by
    have hb := h {x : A // x ≠ a} {b : B // R a b} (link R a) (hf a)
    rw [link_lightCount] at hb
    have hm : Nat.card {x : A // x ≠ a} ≤ Fintype.card A := by
      simpa only [Nat.card_eq_fintype_card] using
        Fintype.card_le_of_injective (fun x : {x : A // x ≠ a} => x.val) Subtype.val_injective
    exact hb.trans (Nat.mul_le_mul_left C (Nat.add_le_add_right hm _))
  have hs := sum_le_sum (s := (univ : Finset A)) (fun a _ => hlocal a)
  have ht := Nat.mul_le_mul_left C (sum_lightPairs_le R 3)
  simp only [mul_add,sum_add_distrib,sum_const,card_univ,Nat.nsmul_eq_mul,← mul_sum] at hs
  nlinarith only [hs,ht]

/-- A direct conditional incidence bound: no minimum degree, degree cap,
maximum-degree hypothesis, or regularization is used. -/
theorem incidence_square {C : ℕ} (h : DensityGap C) {A B : Type}
    [Fintype A] [Fintype B] (R : A → B → Prop)
    (hf : ∀ a, ¬ HasTheta (link R a)) :
    (Nat.card {p : A × B // R p.1 p.2})^2 ≤
      C*((Fintype.card A)^3+3*Fintype.card A*(Fintype.card B)^2) := by
  classical
  rw [edge_card_eq_rows]
  have hc := sq_sum_le_card_mul_sum_sq (s := (univ : Finset A))
    (f := fun a => Nat.card {b // R a b})
  rw [card_univ] at hc
  have hu := Nat.mul_le_mul_left (Fintype.card A) (sum_row_squares h R hf)
  nlinarith only [hc,hu]

/-- In balanced hosts this is the square of an O(n^(3/2)) edge estimate,
still conditional on the unproved local DensityGap assertion. -/
theorem balanced_pattern_free {C : ℕ} (h : DensityGap C) (n : ℕ)
    (R : Fin n → Fin n → Prop) (hf : pattern.Free (Erdos713C6.bipGraph R)) :
    (Nat.card {p : Fin n × Fin n // R p.1 p.2})^2 ≤ 4*C*n^3 := by
  have hb := incidence_square h R (no_theta_links hf)
  simp only [Fintype.card_fin] at hb
  nlinarith only [hb]

#print axioms cappedWeighted_of_densityGap
#print axioms sum_row_squares
#print axioms balanced_pattern_free
end Erdos713ThetaDensityGapReduction
