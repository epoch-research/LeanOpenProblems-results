import Submission.LocalPolynomialPhaseExtension

/-! Exact top differences under dilation, and removal of a small top Newton
coefficient. These identities support induction for higher-degree partitions. -/
namespace Erdos3HigherDifferenceDilation
open Finset Erdos3HigherPhaseDifferences Erdos3LocalPolynomialPhaseExtension
  Erdos3HigherPhaseRepresentation Erdos3LocalQuadraticProgressions
open scoped BigOperators Classical
set_option maxHeartbeats 2000000

/-- Dilating the variable by d multiplies a constant kth difference by d^k.
The new base point is arbitrary and does not affect the top coefficient. -/
theorem diffIter_dilate_top {G : Type*} [AddCommGroup G]
    (k : ℕ) (f : ℕ → G) (z : G) (hf : diffIter k f = fun _ ↦ z) (a d : ℕ) :
    diffIter k (fun n ↦ f (a+n*d)) = fun _ ↦ (d^k) • z := by
  induction k generalizing f z with
  | zero =>
    funext n
    have hh := congr_fun hf (a+n*d)
    simpa only [diffIter,Function.iterate_zero,id_eq,pow_zero,one_nsmul] using hh
  | succ k ih =>
    let g : ℕ → G := fun n ↦ f (n+d)-f n
    have hg : diffIter k g = fun _ ↦ d • z := by
      have hh := shifted_difference_top f z k hf (i := d) (j := 0) (Nat.zero_le d)
      simpa only [Nat.sub_zero,Nat.add_zero] using hh
    have he : fwdDiff (1 : ℕ) (fun n ↦ f (a+n*d)) = fun n ↦ g (a+n*d) := by
      funext n
      simp only [fwdDiff,g]
      congr 2
      ring
    rw [diffIter,Function.iterate_succ_apply,he]
    have hh := ih g (d • z) hg
    change diffIter k (fun n ↦ g (a+n*d)) = _
    rw [hh]
    funext n
    rw [smul_smul,pow_succ]

lemma diffIter_choose_top {G : Type*} [AddCommGroup G] (z : G) (k : ℕ) :
    diffIter k (fun n : ℕ ↦ n.choose k • z) = fun _ ↦ z := by
  let φ : ℤ →+ G := zmultiplesHom G z
  have he : (fun n : ℕ ↦ n.choose k • z) = fun n : ℕ ↦ φ (n.choose k : ℤ) := by
    funext n
    exact (natCast_zsmul _ _).symm
  have hc : diffIter k (fun n : ℕ ↦ (n.choose k : ℤ)) = fun _ ↦ (1 : ℤ) := by
    simpa only [Nat.add_zero,Nat.choose_zero_right,Nat.cast_one] using fwdDiff_iter_choose 0 k
  rw [he,diffIter_map,hc]
  funext n
  exact one_zsmul z

/-- Removing the kth Newton term lowers the degree by one. -/
lemma subtract_top_difference_zero {G : Type*} [AddCommGroup G]
    (k : ℕ) (f : ℕ → G) (z : G) (hf : diffIter k f = fun _ ↦ z) :
    diffIter k (fun n ↦ f n-n.choose k • z) = 0 := by
  change diffIter k (f-(fun n ↦ n.choose k • z)) = 0
  rw [diffIter_sub,diffIter_choose_top,hf]
  exact sub_self _

/-- A small top circle coefficient produces a uniformly small error on the
whole coarse interval after removal of its Newton term. -/
lemma subtract_top_phase_error (f : ℕ → Additive Circle) (z : Additive Circle)
    (k M : ℕ) {η : ℝ} (hη : ‖phase z-1‖ ≤ η) (n : ℕ) (hn : n ≤ M) :
    ‖phase (f n)-phase (f n-n.choose k • z)‖ ≤ (M : ℝ)^k*η := by
  have hη0 : 0 ≤ η := (norm_nonneg _).trans hη
  have hchoose : (n.choose k : ℝ) ≤ (M : ℝ)^k := by
    exact_mod_cast (Nat.choose_le_pow n k).trans (Nat.pow_le_pow_left hn k)
  rw [phase_sub_norm,sub_sub_cancel,phase_nsmul]
  exact (unit_power_oscillation (phase z) (phase_norm z) (n.choose k)).trans
    (mul_le_mul hchoose hη (norm_nonneg _) (pow_nonneg (Nat.cast_nonneg M) k))

#print axioms diffIter_dilate_top
#print axioms subtract_top_phase_error
end Erdos3HigherDifferenceDilation
