import Submission.ExactDilationBias

/-! A fixed finite alphabet can retain biased natural skew correlations while
being exactly invariant under every fixed multiplier eventually. This does
not establish the max-under-multiplication condition of prime-factor labels. -/
namespace Erdos371.ExactMultiplierChirpObstruction
open Finset Filter
open scoped Topology

lemma finite_unitBall_quantizer (η : ℝ) (hη : 0 < η) :
    ∃ Q : ℕ, ∃ v : Fin Q → ℂ, ∃ q : ℂ → Fin Q,
      (∀ a, ‖v a‖ ≤ 1) ∧ ∀ z : ℂ, ‖z‖ ≤ 1 → ‖v (q z)-z‖ < η := by
  classical
  obtain ⟨S,hS,hSf,hcover⟩ := Metric.finite_approx_of_totallyBounded
    (isCompact_closedBall (0 : ℂ) 1).totallyBounded η hη
  have hex (z : ℂ) (hz : ‖z‖ ≤ 1) : ∃ a : S, ‖a.val-z‖ < η := by
    have hm := hcover (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz)
    obtain ⟨a,ha,hm⟩ := Set.mem_iUnion₂.mp hm
    exact ⟨⟨a,ha⟩,by simpa only [Metric.mem_ball,dist_eq_norm,norm_sub_rev] using hm⟩
  obtain ⟨a₀,ha₀⟩ := hex 0 (by norm_num)
  letI : Fintype S := hSf.fintype
  let e := Fintype.equivFin S
  let qS : ℂ → S := fun z => if hz : ‖z‖ ≤ 1 then Classical.choose (hex z hz) else a₀
  refine ⟨Fintype.card S,fun a => (e.symm a).val,fun z => e (qS z),?_,?_⟩
  · intro a
    simpa only [Metric.mem_closedBall,dist_zero_right] using hS (e.symm a).property
  · intro z hz
    simp only [e.symm_apply_apply]
    dsimp [qS]
    rw [dif_pos hz]
    exact Classical.choose_spec (hex z hz)

lemma imaginaryBias_uniform_error (f g : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1)
    (η : ℝ) (happrox : ∀ n, ‖f n-g n‖ ≤ η) (N : ℕ) (hN : 0 < N) :
    |imaginaryBias f N-imaginaryBias g N| ≤ 2*η := by
  unfold imaginaryBias
  rw [← sub_div,abs_div,abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N),← sum_sub_distrib]
  apply (div_le_iff₀ (by exact_mod_cast hN)).mpr
  calc
    _ ≤ ∑ n ∈ Icc 1 N, |(f (n+1)*(starRingEnd ℂ) (f n)).im-
        (g (n+1)*(starRingEnd ℂ) (g n)).im| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Icc 1 N, 2*η := by
      apply sum_le_sum
      intro n _
      have he := imaginary_correlation_error f g hf hg n
      linarith [happrox n,happrox (n+1)]
    _ = _ := by simp [mul_comm]

noncomputable def phaseSkew {Q : ℕ} (v : Fin Q → ℂ) (a b : Fin Q) : ℝ :=
  (v b*(starRingEnd ℂ) (v a)).im

lemma phaseSkew_swap {Q : ℕ} (v : Fin Q → ℂ) (a b : Fin Q) :
    phaseSkew v b a = -phaseSkew v a b := by
  have he : v a*(starRingEnd ℂ) (v b) = (starRingEnd ℂ) (v b*(starRingEnd ℂ) (v a)) := by
    simp only [map_mul,starRingEnd_self_apply,mul_comm]
  unfold phaseSkew
  rw [he,Complex.conj_im]

lemma phaseSkew_abs_le {Q : ℕ} (v : Fin Q → ℂ) (hv : ∀ a, ‖v a‖ ≤ 1) (a b : Fin Q) :
    |phaseSkew v a b| ≤ 1 := by
  apply (Complex.abs_im_le_norm _).trans
  rw [norm_mul,Complex.norm_conj]
  exact (mul_le_mul (hv b) (hv a) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

/-- Exact fixed-multiplier invariance, a fixed finite alphabet, and bounded
antisymmetry do NOT imply natural-average skew cancellation. In particular,
the arithmetic max identity or growing-range stability cannot be discarded. -/
theorem exists_finite_exact_dilation_stable_skew_bias :
    ∃ Q : ℕ, ∃ N : ℕ → ℕ, ∃ L : ℕ → ℕ → Fin Q, ∃ C : Fin Q → Fin Q → ℝ,
      Tendsto N atTop atTop ∧
      (∀ a b, C b a = -C a b) ∧ (∀ a b, |C a b| ≤ 1) ∧
      (∀ j k, 0 < k → k ≤ j → ∀ n, L j (k*n) = L j n) ∧
      ∀ j, (1/240 : ℝ) ≤ (∑ n ∈ Icc 1 (N j), C (L j n) (L j (n+1)))/(N j) := by
  obtain ⟨N,F,hN,hF,hstable,hbias⟩ := exists_exact_dilation_stable_biased_family
  obtain ⟨Q,v,q,hv,hq⟩ := finite_unitBall_quantizer (1/10000) (by norm_num)
  refine ⟨Q,N,fun j n => q (F j n),phaseSkew v,hN,phaseSkew_swap v,phaseSkew_abs_le v hv,?_,?_⟩
  · intro j k hk hkj n
    dsimp only
    rw [hstable j k hk hkj n]
  · intro j
    have hNj : 0 < N j := by
      by_contra h
      have hz : N j = 0 := by omega
      have hb := hbias j
      norm_num [imaginaryBias,hz] at hb
    let G := fun n => v (q (F j n))
    have herr := imaginaryBias_uniform_error G (F j) (fun n => hv _) (hF j) (1/10000)
      (fun n => (hq (F j n) (hF j n)).le) (N j) hNj
    change (1/240 : ℝ) ≤ imaginaryBias G (N j)
    have hlo := (abs_le.mp herr).1
    linarith [hbias j]

#print axioms exists_finite_exact_dilation_stable_skew_bias
end Erdos371.ExactMultiplierChirpObstruction
