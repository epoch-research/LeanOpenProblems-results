import Submission.WidePrimeProducts

/-!
# Power savings for primitive conductors in logarithmically wide intervals

The lower and upper cutoffs are independent.  The conditions below ensure
that the three terms of the Vaughan mean are genuinely power-saving.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators
namespace Erdos821
open AnalyticSieve
set_option maxHeartbeats 2000000

lemma real_two_pow_div_le (u v w : ℕ) (h : u ≤ v+w) :
    (2 : ℝ)^u/(2 : ℝ)^v ≤ (2 : ℝ)^w := by
  apply (div_le_iff₀ (by positivity)).mpr
  rw [← pow_add]
  exact pow_le_pow_right₀ (by norm_num) (by omega)

lemma wide_conductor_scale_ratios (a b t m : ℕ)
    (ha : 1 ≤ a) (ht : 1 ≤ t)
    (h1 : 4*b+1 ≤ t+2*a) (h2 : 64*b+1 ≤ 64*a+3*t) :
    let Q := progressionScaleN (b*m)
    let N := progressionScaleN (t*m)
    let L : ℝ := progressionScaleN (a*m)
    let B : ℕ := 2^(3*(t*m))
    let F : ℝ := (2 : ℝ)^((64*t-1)*m)
    (Q : ℝ)^2*Real.sqrt N/L ≤ F ∧ (Q : ℝ)*N/B/L ≤ F ∧ (N : ℝ)/L ≤ F := by
  dsimp only
  rw [sqrt_progressionScaleN]
  simp only [progressionScaleN, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, ← pow_add]
  have h1' : 128*b+32*t ≤ 64*a+(64*t-1) := by omega
  have h2' : 64*b+64*t ≤ 3*t+64*a+(64*t-1) := by omega
  have h3' : 64*t ≤ 64*a+(64*t-1) := by omega
  refine ⟨?_,?_,?_⟩
  · apply real_two_pow_div_le
    nlinarith only [Nat.mul_le_mul_right m h1']
  · rw [div_div, ← pow_add]
    apply real_two_pow_div_le
    nlinarith only [Nat.mul_le_mul_right m h2']
  · apply real_two_pow_div_le
    nlinarith only [Nat.mul_le_mul_right m h3']

def wideMeanConstant (t : ℕ) : ℕ := 4000000000000*(t+1)^5

/-- The primitive mean for any finite pool inside the given interval. -/
theorem wide_primitive_mean_bound (P : Finset ℕ) (a b t m : ℕ)
    (ha : 1 ≤ a) (ht : 1 ≤ t) (hhalf : 2*b ≤ t)
    (h1 : 4*b+1 ≤ t+2*a) (h2 : 64*b+1 ≤ 64*a+3*t)
    (hP : ∀ d ∈ P, 2 ≤ d ∧ progressionScaleN (a*m) ≤ d ∧ d ≤ progressionScaleN (b*m)) :
    primitivePoolMean P (progressionScaleN (t*m)) ≤
      (wideMeanConstant t : ℝ)*((m : ℝ)+1)^5*(2 : ℝ)^((64*t-1)*m) := by
  let Q := progressionScaleN (b*m)
  let N := progressionScaleN (t*m)
  let U := progressionScaleU (t*m)
  let L : ℝ := progressionScaleN (a*m)
  let B : ℕ := 2^(3*(t*m))
  let z : ℝ := ((t*m : ℕ) : ℝ)+1
  let F : ℝ := (2 : ℝ)^((64*t-1)*m)
  have hz : 1 ≤ z := by dsimp [z]; linarith [Nat.cast_nonneg (α := ℝ) (t*m)]
  have hL : 0 < L := by dsimp [L, progressionScaleN]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hB : 1 ≤ B := Nat.one_le_of_lt (by dsimp [B]; positivity)
  have hBU : B^2 = U := by dsimp [B,U,progressionScaleU]; rw [← pow_mul]; congr 1; ring
  have hmean := primitivePoolMean_le_unbalanced P (progressionScaleN (a*m)) Q U U N B
    (by unfold progressionScaleN; positivity) (by dsimp [Q,progressionScaleN]; positivity) hP hB
    (by rw [hBU]; omega) (by rw [hBU])
  have hrat := wide_conductor_scale_ratios a b t m ha ht h1 h2
  change (Q : ℝ)^2*Real.sqrt N/L ≤ F ∧ (Q : ℝ)*N/B/L ≤ F ∧ (N : ℝ)/L ≤ F at hrat
  have hQhalf : Q ≤ progressionScaleQ (t*m) 0 := by
    simp only [Q, progressionScaleN, progressionScaleQ, Nat.mul_zero, Nat.sub_zero]
    apply Nat.pow_le_pow_right (by decide)
    nlinarith only [Nat.mul_le_mul_right m hhalf]
  have hshort : vaughanShortMajorant U U N Q ≤ 6400*z^2*Real.sqrt N := by
    apply (vaughanShortMajorant_mono_modulus U U N hQhalf).trans
    dsimp only [U,N,z]
    rw [sqrt_progressionScaleN]
    exact progression_scales_short_bound (t*m) 0
  have hshortDiv : (Q : ℝ)^2*vaughanShortMajorant U U N Q/L ≤ 6400*z^2*F := by
    calc
      _ ≤ (Q : ℝ)^2*(6400*z^2*Real.sqrt N)/L := by gcongr
      _ = 6400*z^2*((Q : ℝ)^2*Real.sqrt N/L) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hrat.1 (by positivity)
  have hIIDiv : unbalancedTypeIIMajorant N Q B/L ≤ 3000000000000*z^5*F := by
    calc
      _ ≤ (1000000000000*z^5*((Q : ℝ)^2*Real.sqrt N+(Q : ℝ)*N/B+N))/L :=
        div_le_div_of_nonneg_right (unbalanced_majorant_scale_log_bound (t*m) Q B) hL.le
      _ = 1000000000000*z^5*((Q : ℝ)^2*Real.sqrt N/L+(Q : ℝ)*N/B/L+(N : ℝ)/L) := by ring
      _ ≤ 1000000000000*z^5*(F+F+F) :=
        mul_le_mul_of_nonneg_left (_root_.add_le_add (_root_.add_le_add hrat.1 hrat.2.1) hrat.2.2) (by positivity)
      _ = _ := by ring
  have hraw : primitivePoolMean P N ≤ 4000000000000*z^5*F := by
    change primitivePoolMean P N ≤ ((Q : ℝ)^2*vaughanShortMajorant U U N Q+unbalancedTypeIIMajorant N Q B)/L at hmean
    rw [add_div] at hmean
    have hz25 := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hz (by decide : 2 ≤ 5)) hF
    have hn : 0 ≤ z^5*F := by positivity
    nlinarith only [hmean,hshortDiv,hIIDiv,hz25,hn]
  apply hraw.trans
  have hzUp : z ≤ ((t : ℝ)+1)*((m : ℝ)+1) := by
    dsimp [z]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) t, Nat.cast_nonneg (α := ℝ) m]
  calc
    _ ≤ 4000000000000*(((t : ℝ)+1)*((m : ℝ)+1))^5*F := by gcongr
    _ = _ := by
      simp only [wideMeanConstant, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
        Nat.cast_add, Nat.cast_one, mul_pow, F]
      ring

end Erdos821
