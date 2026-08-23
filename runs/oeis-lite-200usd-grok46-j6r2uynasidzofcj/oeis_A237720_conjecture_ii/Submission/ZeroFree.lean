import FormalConjectures.Util.ProblemImports
import Submission.Zeta341

/-!
Borel–Carathéodory and the bound on `-ζ'/ζ` for `re s > 1`.
-/

open Complex Real Metric Set
open ArithmeticFunction hiding log

noncomputable section

/-! ## Borel–Carathéodory -/

lemma exp_f_norm_le_one_of_re_nonpos {f : ℂ → ℂ} {R : ℝ}
    (hRe : ∀ z ∈ ball 0 R, (f z).re ≤ 0) :
    ∀ w ∈ ball 0 R, ‖Complex.exp (f w)‖ ≤ 1 := by
  intro w hw
  rw [Complex.norm_exp]
  exact Real.exp_le_one_iff.mpr (hRe w hw)

lemma borel_caratheodory_zero {f : ℂ → ℂ} {R r : ℝ}
    (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R)
    (hf : DifferentiableOn ℂ f (ball 0 R))
    (hf0 : f 0 = 0)
    (hRe : ∀ z ∈ ball 0 R, (f z).re ≤ 0) :
    ∀ z ∈ closedBall 0 r, f z = 0 := by
  intro z hz
  have hzball : z ∈ ball 0 R :=
    mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hz) hrR)
  have hexp_le := exp_f_norm_le_one_of_re_nonpos hRe
  have hmax : IsMaxOn (fun w => ‖Complex.exp (f w)‖) (ball 0 R) 0 := by
    intro w hw
    have h0 : ‖Complex.exp (f 0)‖ = 1 := by simp [hf0]
    exact (hexp_le w hw).trans (le_of_eq h0.symm)
  have hdiff_exp : DifferentiableOn ℂ (fun w => Complex.exp (f w)) (ball 0 R) :=
    Complex.differentiable_exp.comp_differentiableOn hf
  have heq :=
    eq_const_of_exists_max (f := fun w => Complex.exp (f w)) hdiff_exp
      (mem_ball_self hR) hmax
  have hexp1 : ∀ w ∈ ball 0 R, Complex.exp (f w) = 1 := by
    intro w hw
    have := heq hw
    simpa [hf0] using this
  have hderiv0 : (ball 0 R).EqOn (deriv f) 0 := by
    intro w hw
    have hfw : DifferentiableAt ℂ f w := hf.differentiableAt (isOpen_ball.mem_nhds hw)
    have hexpw : HasDerivAt (fun u => Complex.exp (f u)) 0 w := by
      refine (hasDerivAt_const w (1 : ℂ)).congr_of_eventuallyEq ?_
      exact Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hw) fun u hu => hexp1 u hu
    have hchain : HasDerivAt (fun u => Complex.exp (f u))
        (Complex.exp (f w) * deriv f w) w :=
      (Complex.hasDerivAt_exp (f w)).comp w hfw.hasDerivAt
    have : Complex.exp (f w) * deriv f w = 0 := HasDerivAt.unique hchain hexpw
    simpa [hexp1 w hw] using this
  have hfz : f z = f 0 :=
    isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) R).isPreconnected
      hf hderiv0 hzball (mem_ball_self hR)
  simpa [hf0] using hfz

lemma two_M_sub_ne_zero {f : ℂ → ℂ} {R M : ℝ} {w : ℂ}
    (hM : 0 < M) (hw : w ∈ ball 0 R)
    (hRe : ∀ z ∈ ball 0 R, (f z).re ≤ M) :
    (2 * M : ℂ) - f w ≠ 0 := by
  intro h0
  have hre0 : ((2 * M : ℂ) - f w).re = 0 := by simp [h0]
  have : 2 * M - (f w).re = 0 := by
    simpa [sub_re] using hre0
  have heq : (f w).re = 2 * M := by linarith
  have hle : (f w).re ≤ M := hRe w hw
  linarith

lemma norm_le_of_re_le_M {z : ℂ} {M : ℝ} (hM : 0 < M) (hre : z.re ≤ M) :
    ‖z‖ ≤ ‖(2 * M : ℂ) - z‖ := by
  have hz : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hw : ‖(2 * M : ℂ) - z‖ ^ 2 = (2 * M - z.re) ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [sub_re, sub_im]
    ring
  have hsq : ‖z‖ ^ 2 ≤ ‖(2 * M : ℂ) - z‖ ^ 2 := by
    rw [hz, hw]
    nlinarith [hM.le, hre]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

lemma schwarz_at_zero {g : ℂ → ℂ} {R : ℝ} {z : ℂ}
    (hR : 0 < R) (hg : DifferentiableOn ℂ g (ball 0 R))
    (hg0 : g 0 = 0)
    (hgnorm : ∀ w ∈ ball 0 R, ‖g w‖ ≤ 1)
    (hz : z ∈ ball 0 R) :
    ‖g z‖ ≤ ‖z‖ / R := by
  have hmaps : MapsTo g (ball 0 R) (closedBall (g 0) 1) := by
    intro w hw
    simpa [hg0, mem_closedBall, dist_zero_right] using hgnorm w hw
  have hdist := dist_le_div_mul_dist_of_mapsTo_ball (R₁ := R) (R₂ := 1)
    (c := (0 : ℂ)) (z := z) hg hmaps hz
  simpa [hg0, dist_eq_norm, dist_zero_right, div_eq_inv_mul] using hdist

/-- If `f` is holomorphic on the open disk of radius `R`, `f 0 = 0` and
`re (f z) ≤ M` on that disk, then `‖f z‖ ≤ 2 * M * r / (R - r)` whenever
`‖z‖ ≤ r < R`. -/
lemma borel_caratheodory {f : ℂ → ℂ} {R r M : ℝ}
    (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R) (hM : 0 ≤ M)
    (hf : DifferentiableOn ℂ f (ball 0 R))
    (hf0 : f 0 = 0)
    (hRe : ∀ z ∈ ball 0 R, (f z).re ≤ M) :
    ∀ z ∈ closedBall 0 r, ‖f z‖ ≤ 2 * M * r / (R - r) := by
  intro z hz
  have hzR : ‖z‖ < R := lt_of_le_of_lt (mem_closedBall_zero_iff.mp hz) hrR
  have hzball : z ∈ ball 0 R := mem_ball_zero_iff.mpr hzR
  rcases eq_or_lt_of_le hM with hM0 | hMpos
  · subst hM0
    have := borel_caratheodory_zero hR hr hrR hf hf0 hRe z hz
    simp [this]
  · let g : ℂ → ℂ := fun w => f w / ((2 * M : ℂ) - f w)
    have hden_ne : ∀ w ∈ ball 0 R, (2 * M : ℂ) - f w ≠ 0 :=
      fun w hw => two_M_sub_ne_zero hMpos hw hRe
    have hg0 : g 0 = 0 := by simp [g, hf0]
    have hgnorm : ∀ w ∈ ball 0 R, ‖g w‖ ≤ 1 := by
      intro w hw
      have hle := norm_le_of_re_le_M hMpos (hRe w hw)
      have hne := hden_ne w hw
      simp only [g, norm_div]
      exact (div_le_one (norm_pos_iff.mpr hne)).mpr hle
    have hg : DifferentiableOn ℂ g (ball 0 R) := by
      intro w hw
      exact ((hf.differentiableAt (isOpen_ball.mem_nhds hw)).div
        ((differentiableAt_const _).sub
          (hf.differentiableAt (isOpen_ball.mem_nhds hw)))
        (hden_ne w hw)).differentiableWithinAt
    have hf_of_g : ∀ w ∈ ball 0 R, f w = (2 * M : ℂ) * g w / (1 + g w) := by
      intro w hw
      have hne := hden_ne w hw
      have h1eq : (1 : ℂ) + f w / ((2 * M : ℂ) - f w) =
          (2 * M : ℂ) / ((2 * M : ℂ) - f w) := by
        field
      simp only [g]
      rw [h1eq]
      field
      have hMne : (M : ℂ) ≠ 0 := ofReal_ne_zero.mpr hMpos.ne'
      simp [hMne]
    by_cases hz0 : z = 0
    · subst hz0
      simp [hf0]
      apply div_nonneg
      · nlinarith [hMpos.le, hr]
      · linarith
    · have hgz : ‖g z‖ ≤ ‖z‖ / R :=
        schwarz_at_zero hR hg hg0 hgnorm hzball
      have hgz_lt : ‖g z‖ < 1 :=
        lt_of_le_of_lt hgz ((div_lt_one hR).mpr hzR)
      have hfz := hf_of_g z hzball
      have hMabs : ‖(2 * M : ℂ)‖ = 2 * M := by
        have hnn : 0 ≤ (2 * M : ℝ) := by nlinarith [hMpos.le]
        simpa using Complex.norm_of_nonneg hnn
      have h1g_ge : 1 - ‖g z‖ ≤ ‖(1 : ℂ) + g z‖ := by
        have htri : (1 : ℝ) ≤ ‖(1 : ℂ) + g z‖ + ‖g z‖ := by
          have := norm_add_le ((1 : ℂ) + g z) (-g z)
          simpa [add_neg_cancel_right, norm_neg] using this
        linarith
      have hpos : 0 < 1 - ‖g z‖ := sub_pos.mpr hgz_lt
      have hbound : ‖f z‖ ≤ 2 * M * ‖g z‖ / (1 - ‖g z‖) := by
        rw [hfz, norm_div, norm_mul, hMabs]
        refine (div_le_div_of_nonneg_left
          (mul_nonneg (by nlinarith [hMpos.le]) (norm_nonneg _))
          hpos h1g_ge).trans_eq ?_
        ring
      have hgzr : ‖g z‖ ≤ r / R :=
        hgz.trans (div_le_div_of_nonneg_right (mem_closedBall_zero_iff.mp hz) hR.le)
      have hfrac : ‖g z‖ / (1 - ‖g z‖) ≤ (r / R) / (1 - r / R) := by
        have hden_pos : 0 < 1 - r / R := by
          rw [sub_pos, div_lt_one hR]; exact hrR
        have h2 : 0 < 1 - ‖g z‖ := sub_pos.mpr hgz_lt
        refine (div_le_div_iff₀ h2 hden_pos).mpr ?_
        nlinarith [norm_nonneg (g z)]
      have hsimp : (r / R) / (1 - r / R) = r / (R - r) := by field
      calc
        ‖f z‖ ≤ 2 * M * ‖g z‖ / (1 - ‖g z‖) := hbound
        _ = 2 * M * (‖g z‖ / (1 - ‖g z‖)) := by ring
        _ ≤ 2 * M * ((r / R) / (1 - r / R)) :=
          mul_le_mul_of_nonneg_left hfrac (by nlinarith [hMpos.le])
        _ = 2 * M * (r / (R - r)) := by rw [hsimp]
        _ = 2 * M * r / (R - r) := by ring

/-- `|L Λ (σ + it)| ≤ 80 / (σ - 1)` for `1 < σ ≤ 2`. -/
lemma LSeries_vonMangoldt_abs_bound {σ t : ℝ} (hσ : 1 < σ) (hσ2 : σ ≤ 2) :
    ‖LSeries (fun n => (vonMangoldt n : ℂ)) (σ + I * t)‖ ≤ 80 / (σ - 1) := by
  have hs : 1 < (σ + I * t : ℂ).re := by simp [hσ]
  have hre := LSeries_vonMangoldt_real_bound hσ hσ2
  have hsum1 : LSeriesSummable (fun n => (vonMangoldt n : ℂ)) (σ + I * t) :=
    LSeriesSummable_vonMangoldt hs
  have hsum0 : 1 < (σ : ℂ).re := by simp [hσ]
  have hterm : ∀ n,
      ‖LSeries.term (fun k => (vonMangoldt k : ℂ)) (σ + I * t) n‖ ≤
        (LSeries.term (fun k => (vonMangoldt k : ℂ)) (σ : ℂ) n).re := by
    intro n
    rw [re_term_vonMangoldt]
    by_cases hn : n = 0
    · subst hn; simp [LSeries.term_zero]
    · have hpos : 0 < n := Nat.pos_of_ne_zero hn
      rw [LSeries.term_def₀ (by exact_mod_cast vonMangoldt_zero'), if_neg hn]
      have hnorm : ‖(vonMangoldt n : ℂ) * (n : ℂ) ^ (-(σ + I * t))‖ =
          vonMangoldt n * (n : ℝ) ^ (-σ) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
        have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
        rw [norm_cpow_of_ne_zero hn0]
        simp [neg_re, add_re, mul_re, I_re, I_im]
      rw [hnorm]
      simp
  have hle : ‖LSeries (fun n => (vonMangoldt n : ℂ)) (σ + I * t)‖ ≤
      (LSeries (fun n => (vonMangoldt n : ℂ)) (σ : ℂ)).re := by
    refine (norm_tsum_le_tsum_norm hsum1.norm).trans ?_
    have : ∑' n, ‖LSeries.term (fun k => (vonMangoldt k : ℂ)) (σ + I * t) n‖ ≤
        ∑' n, (LSeries.term (fun k => (vonMangoldt k : ℂ)) (σ : ℂ) n).re :=
      Summable.tsum_le_tsum hterm hsum1.norm (summable_re_term_vonMangoldt hsum0)
    exact this.trans (le_of_eq (re_LSeries_vonMangoldt hsum0).symm)
  have hpos : 0 ≤ (LSeries (fun n => (vonMangoldt n : ℂ)) (σ : ℂ)).re := by
    rw [re_LSeries_eq_sum_vonMangoldt hσ]
    exact tsum_nonneg fun n => by
      split_ifs
      · exact le_rfl
      · exact mul_nonneg vonMangoldt_nonneg
          (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  linarith

end
