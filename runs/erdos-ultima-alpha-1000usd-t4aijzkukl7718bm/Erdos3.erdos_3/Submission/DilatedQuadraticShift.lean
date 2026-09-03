import Submission.HigherPhaseDifferences

/-! Large quadratic phase means control a bounded positive multiple of every
sufficiently short dilate. This supplies many near-integer linear orbit points,
not merely a single good short shift. -/
namespace Erdos3DilatedQuadraticShift
open Finset Erdos3HigherPhaseDifferences Erdos3QuadraticRecurrenceExtraction
  Erdos3QuadraticRecurrenceAverages Erdos3FiniteFourier
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 3000000

lemma dilated_short_shift_correlation (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ = 1)
    {N H t : ℕ} (hN : 0 < N) (hH : 0 < H) {δ : ℝ} (hδ : 0 < δ)
    (hmean : δ ≤ ‖intervalMean N f‖)
    (hshift : 2*(H : ℝ)*(t : ℝ)/(N : ℝ) ≤ δ/2)
    (hdiag : 1/(H : ℝ) ≤ δ^2/8) :
    ∃ i j : Fin H, j.val < i.val ∧ δ^2/16 <
      ‖𝔼 n : Fin N, f (n.val+i.val*t)*conj (f (n.val+j.val*t))‖ := by
  letI : NeZero N := ⟨by omega⟩
  letI : NeZero H := ⟨by omega⟩
  let a : ℂ := 𝔼 h : Fin H, intervalMean N (fun n ↦ f (n+h.val*t))
  have hd : ‖a-intervalMean N f‖ ≤ 2*(H : ℝ)*(t : ℝ)/(N : ℝ) := by
    dsimp only [a]
    rw [← Fintype.expect_const (ι := Fin H) (intervalMean N f), ← expect_sub_distrib]
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply expect_le univ_nonempty
    intro h _
    apply (interval_shift_bound f (fun n ↦ (hf n).le) N (h.val*t)).trans
    push_cast
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    have hh : (h.val : ℝ) ≤ H := by exact_mod_cast h.isLt.le
    nlinarith only [mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg t)]
  have ha : δ/2 ≤ ‖a‖ := by
    have ht : ‖intervalMean N f‖ ≤ ‖a‖+‖a-intervalMean N f‖ := by
      calc
        _ = ‖a-(a-intervalMean N f)‖ := by congr 1; ring
        _ ≤ _ := norm_sub_le _ _
    linarith only [hmean, hshift, hd, ht]
  have henergy : δ^2/4 ≤ 𝔼 n : Fin N, ‖𝔼 h : Fin H, f (n.val+h.val*t)‖^2 := by
    have he : a = 𝔼 n : Fin N, 𝔼 h : Fin H, f (n.val+h.val*t) := expect_comm _ _ _
    calc
      _ = (δ/2)^2 := by ring
      _ ≤ ‖a‖^2 := pow_le_pow_left₀ (by positivity) ha 2
      _ ≤ _ := by rw [he]; exact norm_mean_sq_le _
  have hex : ∃ i j : Fin H, i ≠ j ∧ δ^2/16 <
      ‖𝔼 n : Fin N, f (n.val+i.val*t)*conj (f (n.val+j.val*t))‖ := by
    by_contra hn
    push_neg at hn
    have hu := (pair_energy_bounds (fun (n : Fin N) (h : Fin H) ↦ f (n.val+h.val*t))
      (fun n h ↦ hf _) (by positivity : 0 ≤ δ^2/16) hn).2
    rw [Fintype.card_fin] at hu
    have hpos : 0 < δ^2 := sq_pos_of_pos hδ
    linarith only [hu,hdiag,henergy,hpos]
  obtain ⟨i,j,hij,hcorr⟩ := hex
  rcases lt_trichotomy j.val i.val with h|h|h
  · exact ⟨i,j,h,hcorr⟩
  · exact (hij (Fin.ext h.symm)).elim
  · refine ⟨j,i,h,?_⟩
    rw [norm_pair_swap]
    exact hcorr

/-- For every short dilate t, one of its first H multiples has a small chord
error for the quadratic leading phase. -/
theorem quadratic_dilate_inverse (f : ℕ → Additive Circle) (z : Additive Circle)
    (hf : diffIter 2 f = fun _ ↦ z) {N H t : ℕ} {δ : ℝ}
    (hN : 0 < N) (hH : 0 < H) (hδ : 0 < δ)
    (hmean : δ ≤ ‖intervalMean N (fun n ↦ phase (f n))‖)
    (hshift : 2*(H : ℝ)*(t : ℝ)/(N : ℝ) ≤ δ/2)
    (hdiag : 1/(H : ℝ) ≤ δ^2/8) :
    ∃ d : ℕ, 0 < d ∧ d < H ∧ ‖(phase z)^(d*t)-1‖ ≤ 32/(δ^2*(N : ℝ)) := by
  obtain ⟨i,j,hji,hcorr⟩ := dilated_short_shift_correlation (fun n ↦ phase (f n))
    (fun n ↦ phase_norm _) hN hH hδ hmean hshift hdiag
  let g : ℕ → Additive Circle := fun n ↦ f (n+i.val*t)-f (n+j.val*t)
  have hg : diffIter 1 g = fun _ ↦ ((i.val-j.val)*t) • z := by
    have hh := shifted_difference_top f z 1 hf (Nat.mul_le_mul_right t hji.le)
    simpa only [Nat.sub_mul] using hh
  have hm : ‖𝔼 n : Fin N, phase (f (n.val+i.val*t))*conj (phase (f (n.val+j.val*t)))‖ =
      ‖𝔼 n : Fin N, ((phase z)^((i.val-j.val)*t))^n.val‖ := by
    have he : (𝔼 n : Fin N, phase (g n.val)) =
        𝔼 n : Fin N, phase (g 0)*((phase z)^((i.val-j.val)*t))^n.val := by
      apply expect_congr rfl
      intro n _
      rw [first_difference_phase g _ hg, phase_nsmul]
    simp_rw [← phase_sub]
    change ‖𝔼 n : Fin N, phase (g n.val)‖ = _
    rw [he, ← mul_expect, norm_mul, phase_norm, one_mul]
  rw [hm] at hcorr
  have hgeo := geometric_mean_norm ((phase z)^((i.val-j.val)*t))
    (by rw [norm_pow,phase_norm,one_pow]) N
  have hmul := (mul_le_mul_of_nonneg_right hcorr.le
    (norm_nonneg ((phase z)^((i.val-j.val)*t)-1))).trans hgeo
  refine ⟨i.val-j.val,by omega,by omega,?_⟩
  have hδ2 : 0 < δ^2/16 := by positivity
  calc
    _ ≤ (2/(N : ℝ))/(δ^2/16) := (le_div_iff₀ hδ2).mpr (by linarith only [hmul])
    _ = _ := by ring

#print axioms quadratic_dilate_inverse
end Erdos3DilatedQuadraticShift
