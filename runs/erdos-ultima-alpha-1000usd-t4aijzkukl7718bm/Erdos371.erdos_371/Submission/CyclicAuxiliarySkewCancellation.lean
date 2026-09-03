import Submission.FiniteRingSkewFourier
import Submission.FiniteEndpointTransfer

/-! Uniform cancellation after averaging auxiliary positive integer multiples
of a gap. This applies to every finite-label cyclic process, without a prime
exponential-sum estimate. The averaging over auxiliary gaps must be retained. -/
namespace Erdos371.SkewKernel
open Finset
variable {F A : Type*} [CommRing F] [Fintype F] [DecidableEq F]
  [Fintype A] [DecidableEq A]

lemma weighted_skewCorrelation_le (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (f g : F → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ x, ‖g x‖ ≤ 1)
    (h : F) (H : ℕ) (w : ℕ → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hw : ∀ z : ℂ, ‖z‖ ≤ 1 → |(shiftPolynomial H w z).im| ≤ ε) :
    ‖∑ k ∈ range H, (w k : ℂ)*(shiftCorrelation f g ((k : F)*h)-
      shiftCorrelation g f ((k : F)*h))‖ ≤ 2*ε := by
  have hcard : 0 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have henergy (v : F → ℂ) (hv : ∀ x, ‖v x‖ ≤ 1) :
      0 ≤ (∑ x, ‖v x‖^2)/(Fintype.card F : ℝ) ∧
        (∑ x, ‖v x‖^2)/(Fintype.card F : ℝ) ≤ 1 := by
    refine ⟨by positivity, (div_le_one hcard).mpr ?_⟩
    calc
      _ ≤ ∑ _ : F, (1 : ℝ) := sum_le_sum fun x _ => by
        nlinarith [hv x, norm_nonneg (v x)]
      _ = _ := by simp
  have hs := weighted_skewCorrelation_sq_le ψ hψ f g h H w ε hε hw
  have hef := henergy f hf
  have heg := henergy g hg
  have hprod := mul_le_mul hef.2 heg.2 heg.1 zero_le_one
  have hm := mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ 4*ε^2)
  nlinarith [norm_nonneg (∑ k ∈ range H, (w k : ℂ)*(shiftCorrelation f g ((k : F)*h)-
      shiftCorrelation g f ((k : F)*h)))]

noncomputable def labelIndicator (L : F → A) (a : A) (x : F) : ℂ := if L x = a then 1 else 0

omit [CommRing F] [Fintype F] [Fintype A] [DecidableEq F] in
lemma labelIndicator_norm_le (L : F → A) (a : A) (x : F) : ‖labelIndicator L a x‖ ≤ 1 := by
  unfold labelIndicator
  split_ifs <;> norm_num

noncomputable def labelPairMean (L : F → A) (C : A → A → ℝ) (h : F) : ℂ :=
  (∑ x, (C (L x) (L (x+h)) : ℂ))/(Fintype.card F : ℂ)

omit [DecidableEq F] in
lemma labelPairMean_expansion (L : F → A) (C : A → A → ℝ) (h : F) :
    labelPairMean L C h = ∑ a, ∑ b, (C a b : ℂ)*
      shiftCorrelation (labelIndicator L a) (labelIndicator L b) h := by
  unfold labelPairMean shiftCorrelation
  simp only [← mul_div_assoc, ← sum_div, mul_sum]
  congr 1
  simp_rw [sum_comm (s := (univ : Finset A)) (t := (univ : Finset F))]
  simp [labelIndicator]

omit [DecidableEq F] in
lemma labelPairMean_skew_expansion (L : F → A) (C : A → A → ℝ)
    (hC : ∀ a b, C b a = -C a b) (h : F) (H : ℕ) (w : ℕ → ℝ) :
    2*(∑ k ∈ range H, (w k : ℂ)*labelPairMean L C ((k : F)*h)) =
      ∑ a, ∑ b, (C a b : ℂ)*(∑ k ∈ range H, (w k : ℂ)*
        (shiftCorrelation (labelIndicator L a) (labelIndicator L b) ((k : F)*h)-
          shiftCorrelation (labelIndicator L b) (labelIndicator L a) ((k : F)*h))) := by
  simp_rw [mul_sub, sum_sub_distrib, mul_sub, sum_sub_distrib]
  have he : (∑ a, ∑ b, (C a b : ℂ)*(∑ k ∈ range H, (w k : ℂ)*
      shiftCorrelation (labelIndicator L a) (labelIndicator L b) ((k : F)*h))) =
        ∑ k ∈ range H, (w k : ℂ)*labelPairMean L C ((k : F)*h) := by
    simp_rw [labelPairMean_expansion, mul_sum]
    simp_rw [sum_comm (s := (univ : Finset A)) (t := range H)]
    apply sum_congr rfl
    intro k _
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro b _
    ring
  have hs : (∑ a, ∑ b, (C a b : ℂ)*(∑ k ∈ range H, (w k : ℂ)*
      shiftCorrelation (labelIndicator L b) (labelIndicator L a) ((k : F)*h))) =
      -(∑ a, ∑ b, (C a b : ℂ)*(∑ k ∈ range H, (w k : ℂ)*
        shiftCorrelation (labelIndicator L a) (labelIndicator L b) ((k : F)*h))) := by
    rw [sum_comm, ← sum_neg_distrib]
    apply sum_congr rfl
    intro a _
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro b _
    rw [hC, Complex.ofReal_neg, neg_mul]
  rw [hs,he]
  ring

/-- The same auxiliary kernel works for every cyclic label sequence and every
choice of the base gap, including prime gaps. -/
theorem weighted_labelPairMean_le (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (L : F → A) (C : A → A → ℝ) (hC : ∀ a b, C b a = -C a b)
    (hCb : ∀ a b, |C a b| ≤ 1) (h : F) (H : ℕ) (w : ℕ → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hw : ∀ z : ℂ, ‖z‖ ≤ 1 → |(shiftPolynomial H w z).im| ≤ ε) :
    ‖∑ k ∈ range H, (w k : ℂ)*labelPairMean L C ((k : F)*h)‖ ≤
      ε*(Fintype.card A : ℝ)^2 := by
  have he := labelPairMean_skew_expansion L C hC h H w
  have hn := congrArg norm he
  rw [norm_mul] at hn
  norm_num only [Complex.norm_ofNat] at hn
  have hb : ‖∑ a, ∑ b, (C a b : ℂ)*(∑ k ∈ range H, (w k : ℂ)*
      (shiftCorrelation (labelIndicator L a) (labelIndicator L b) ((k : F)*h)-
        shiftCorrelation (labelIndicator L b) (labelIndicator L a) ((k : F)*h)))‖ ≤
      2*ε*(Fintype.card A : ℝ)^2 := by
    calc
      _ ≤ ∑ a, ‖∑ b, (C a b : ℂ)*(∑ k ∈ range H, (w k : ℂ)*
          (shiftCorrelation (labelIndicator L a) (labelIndicator L b) ((k : F)*h)-
            shiftCorrelation (labelIndicator L b) (labelIndicator L a) ((k : F)*h)))‖ := norm_sum_le _ _
      _ ≤ ∑ _a : A, ∑ _b : A, 2*ε := by
        apply sum_le_sum
        intro a _
        apply (norm_sum_le _ _).trans
        apply sum_le_sum
        intro b _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have hs := weighted_skewCorrelation_le ψ hψ (labelIndicator L a) (labelIndicator L b)
          (labelIndicator_norm_le L a) (labelIndicator_norm_le L b) h H w ε hε hw
        exact (mul_le_mul (hCb a b) hs (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
      _ = _ := by simp; ring
  rw [← hn] at hb
  linarith

/-- Finite positive auxiliary shifts suffice for uniform skew cancellation on
all cycles. This does not remove the auxiliary shifts in arithmetic dilation. -/
theorem exists_cyclic_auxiliary_skew_kernel (A : Type*) [Fintype A] (ε : ℝ) (hε : 0 < ε) :
    ∃ H : ℕ, ∃ w : ℕ → ℝ,
      (∀ k, 0 ≤ w k) ∧ w 0 = 0 ∧ (∀ k, H ≤ k → w k = 0) ∧
      (∑ k ∈ range H, w k) = 1 ∧
      ∀ (N : ℕ) [NeZero N], ∀ (L : ZMod N → A) (C : A → A → ℝ),
        (∀ a b, C b a = -C a b) → (∀ a b, |C a b| ≤ 1) → ∀ p : ZMod N,
        |∑ k ∈ range H, w k * FiniteInformation.mean (FiniteInformation.uniformLaw (ZMod N))
          (fun x => C (L x) (L (x+(k : ZMod N)*p)))| < ε := by
  classical
  let δ := ε/((Fintype.card A : ℝ)^2+1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨H,w,hw0,hwz,hwH,hws,hw⟩ := exists_positive_shift_kernel δ hδ
  refine ⟨H,w,hw0,hwz,hwH,hws,?_⟩
  intro N _ L C hC hCb p
  have hb := weighted_labelPairMean_le (ZMod.stdAddChar (N := N)) (ZMod.isPrimitive_stdAddChar N)
    L C hC hCb p H w δ hδ.le (fun z hz => (hw z hz).le)
  have he : (∑ k ∈ range H, (w k : ℂ)*labelPairMean L C ((k : ZMod N)*p)) =
      (∑ k ∈ range H, w k * FiniteInformation.mean (FiniteInformation.uniformLaw (ZMod N))
        (fun x => C (L x) (L (x+(k : ZMod N)*p)))) := by
    unfold labelPairMean FiniteInformation.mean
    simp only [FiniteInformation.uniformLaw, ZMod.card]
    push_cast
    simp only [← div_eq_inv_mul, ← sum_div]
  rw [he, Complex.norm_real, Real.norm_eq_abs] at hb
  apply hb.trans_lt
  have heδ : δ*((Fintype.card A : ℝ)^2+1) = ε := by dsimp [δ]; field_simp
  nlinarith

#print axioms exists_cyclic_auxiliary_skew_kernel
end Erdos371.SkewKernel
