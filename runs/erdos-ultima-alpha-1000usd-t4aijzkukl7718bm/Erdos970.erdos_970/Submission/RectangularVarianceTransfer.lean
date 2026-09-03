import Submission.RowConditionalVariance

/-! A deterministic use of row variance. A uniform lower count in a long
rectangle, together with a UNIFORM (not phase-averaged) row-variance bound,
forces a lower count in its shorter rows. The uniform variance premise is
explicit and is not proved in this file. -/
namespace Erdos970.GapAverages
open Finset Erdos970.Resampling

lemma row_deviation_square_le (P : Finset ℕ) (m p : ℕ) (hp : 0 < p)
    (r : Phase P) (a : Fin p) :
    (rowCount P m p a r - intervalCount P m r / p) ^ 2 ≤
      (p : ℝ) * rowConditionalVariance P m p r := by
  have hh := single_le_sum (s := (univ : Finset (Fin p)))
    (f := fun a => (rowCount P m p a r - intervalCount P m r / p) ^ 2)
    (fun a _ => sq_nonneg _) (mem_univ a)
  unfold rowConditionalVariance residueMean
  rw [mul_div_cancel₀ _ (by exact_mod_cast hp.ne')]
  exact hh

lemma row_gt_of_mean_variance (P : Finset ℕ) (m p : ℕ) (hp : 0 < p)
    (r : Phase P) (a : Fin p) (A b V : ℝ)
    (hA : A ≤ intervalCount P m r / p) (hb : b ≤ A)
    (hV : rowConditionalVariance P m p r ≤ V)
    (hgap : (p : ℝ) * V < (A - b) ^ 2) :
    b < rowCount P m p a r := by
  by_contra hbad
  have hr : rowCount P m p a r ≤ b := le_of_not_gt hbad
  have hdev := row_deviation_square_le P m p hp r a
  have hm := mul_le_mul_of_nonneg_left hV (Nat.cast_nonneg p)
  have hs : (A - b) ^ 2 ≤ (rowCount P m p a r - intervalCount P m r / p) ^ 2 := by
    have hh := pow_le_pow_left₀ (sub_nonneg.mpr hb)
      (show A - b ≤ intervalCount P m r / p - rowCount P m p a r by linarith only [hA, hr]) 2
    nlinarith only [hh]
  exact hgap.not_ge (hs.trans (hdev.trans hm))

lemma row_zero_affine_rectangle (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime)
    (n p : ℕ) (hp : 0 < p) (hc : ∀ q ∈ P, p.Coprime q) (r : Phase P) :
    rowCount P (p * n) p ⟨0, hp⟩ (affinePhaseEquiv P hP 0 p hc r) = intervalCount P n r := by
  rw [rowCount_eq_progression P (p * n) p hp]
  have hlen : IntervalRescaling.progressionLength (p * n) p 0 hp = n := by
    rw [progressionLength_eq_residueHits (p * n) p hp ⟨0, hp⟩,
      residueHits_eq (p * n) p hp ⟨0, hp⟩, Nat.mul_div_cancel_left n hp, Nat.mul_mod_right]
    simp only [Fin.val_mk, lt_self_iff_false, if_false, add_zero]
  rw [hlen]
  exact progressionCount_affine P hP 0 p n hc r

/-- A long-interval count estimate and a uniform row-variance estimate imply
an everywhere short-interval count estimate. No row independence is used. -/
theorem count_lower_of_rectangular_variance (P : Finset ℕ)
    (hP : ∀ q ∈ P, q.Prime) (n p : ℕ) (hp : 0 < p)
    (hc : ∀ q ∈ P, p.Coprime q) (A b V : ℝ) (hb : b ≤ A)
    (hcount : ∀ r : Phase P, (p : ℝ) * A ≤ intervalCount P (p * n) r)
    (hvar : ∀ r : Phase P, rowConditionalVariance P (p * n) p r ≤ V)
    (hgap : (p : ℝ) * V < (A - b) ^ 2) :
    ∀ r : Phase P, b < intervalCount P n r := by
  intro r
  let s := affinePhaseEquiv P hP 0 p hc r
  have hA : A ≤ intervalCount P (p * n) s / p := by
    apply (le_div_iff₀ (show (0 : ℝ) < p by exact_mod_cast hp)).mpr
    simpa only [mul_comm] using hcount s
  have hh := row_gt_of_mean_variance P (p * n) p hp s ⟨0, hp⟩ A b V
    hA hb (hvar s) hgap
  simpa only [s, row_zero_affine_rectangle P hP n p hp hc] using hh

#print axioms row_deviation_square_le
#print axioms count_lower_of_rectangular_variance
end Erdos970.GapAverages
