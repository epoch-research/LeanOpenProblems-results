import Submission.QuadraticRotationApproxExplore
import Submission.RotationFloorPerturbationExplore

/-! A uniform logarithmic discrepancy bound for finite rotation orbits whose
slope approximates sqrt(2) to the square of the requested horizon. -/
namespace Erdos66ShortRotationLogBound
open Erdos66QuadraticRotationApprox Erdos66RotationFloorPerturbation
open scoped Classical
set_option maxHeartbeats 2200000

lemma exists_good_rotation_block (α : ℝ) (Q N : ℕ) (hN : 0 < N) (hNQ : N ≤ Q)
    (hnear : (Q : ℝ)^2*|α-Real.sqrt 2| ≤ 1) :
    ∃ d : ℕ, 0 < d ∧ d ≤ N ∧ N+1 ≤ 5*d ∧
      ∀ x θ : ℝ, |rotationSum α x θ d-(d : ℝ)*θ| ≤ 5 := by
  obtain ⟨r,hdN,hcomp,_,happrox⟩ := exists_comparable_approx N hN
  refine ⟨r.den,r.pos,hdN,hcomp,?_⟩
  have htriangle := abs_sub_le α (Real.sqrt 2) (r : ℝ)
  have hdQ : (r.den : ℝ) ≤ Q := by exact_mod_cast hdN.trans hNQ
  have hd0 : (0 : ℝ) ≤ r.den := Nat.cast_nonneg _
  have hpow : (r.den : ℝ)^2 ≤ (Q : ℝ)^2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hpow (abs_nonneg (α-Real.sqrt 2))
  have hm' := mul_le_mul_of_nonneg_left htriangle (sq_nonneg (r.den : ℝ))
  have he : (r.den : ℝ)^2*|α-(r : ℝ)| ≤ 2 := by nlinarith only [hm,hm',hnear,happrox]
  intro x θ
  convert block_error_of_approximation r α x θ 2 he using 1
  norm_num

/-- The phase is fixed before x, theta and the initial segment length.
The estimate holds uniformly over all starting phases and window widths. -/
theorem rotation_log_bound (α : ℝ) (Q : ℕ)
    (hnear : (Q : ℝ)^2*|α-Real.sqrt 2| ≤ 1) (N : ℕ) (hNQ : N ≤ Q) (x θ : ℝ) :
    |rotationSum α x θ N-(N : ℝ)*θ| ≤ 25*Real.log ((N : ℝ)+1) := by
  have main : ∀ N : ℕ, N ≤ Q → ∀ x θ : ℝ,
      |rotationSum α x θ N-(N : ℝ)*θ| ≤ 25*Real.log ((N : ℝ)+1) := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro hNQ x θ
      by_cases hN : N=0
      · subst N
        simp [rotationSum_zero]
      · have hNp : 0 < N := Nat.pos_of_ne_zero hN
        obtain ⟨d,hd,hdN,hcomp,hblock⟩ := exists_good_rotation_block α Q N hNp hNQ hnear
        let R := N-d
        have hRN : R < N := Nat.sub_lt hNp hd
        have hRQ : R ≤ Q := (Nat.sub_le N d).trans hNQ
        have hih := ih R hRN hRQ (x+(d : ℝ)*α) θ
        have hgood := hblock x θ
        have hdecomp : d+R=N := Nat.add_sub_of_le hdN
        have hsum := rotationSum_add α x θ d R
        rw [hdecomp] at hsum
        have hcast : (N : ℝ)=(d : ℝ)+R := by exact_mod_cast hdecomp.symm
        have herr : rotationSum α x θ N-(N : ℝ)*θ =
            (rotationSum α x θ d-(d : ℝ)*θ) +
              (rotationSum α (x+(d : ℝ)*α) θ R-(R : ℝ)*θ) := by
          rw [hsum,hcast]
          ring
        have hRpos : (0 : ℝ) < (R : ℝ)+1 := by positivity
        have hNpos : (0 : ℝ) < (N : ℝ)+1 := by positivity
        have hscale : (R : ℝ)+1 ≤ (4/5 : ℝ)*((N : ℝ)+1) := by
          have hcomp' : (N : ℝ)+1 ≤ 5*(d : ℝ) := by exact_mod_cast hcomp
          rw [hcast] at hcomp' ⊢
          linarith
        have hlog := Real.log_le_log hRpos hscale
        rw [Real.log_mul (by norm_num : (4/5 : ℝ) ≠ 0) hNpos.ne'] at hlog
        have hsmall := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4/5)
        have hbudget : 5+25*Real.log ((R : ℝ)+1) ≤ 25*Real.log ((N : ℝ)+1) := by
          linarith
        rw [herr]
        exact (abs_add_le _ _).trans ((add_le_add hgood hih).trans hbudget)
  exact main N hNQ x θ

end Erdos66ShortRotationLogBound
