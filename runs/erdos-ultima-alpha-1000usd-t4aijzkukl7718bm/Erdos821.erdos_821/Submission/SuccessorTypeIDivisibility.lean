import Submission.SuccessorTypeIIGram
import Submission.CofactorCharacterCancellation

/-!
# Output divisibility discrepancies and Vaughan Type I terms

The discrepancy is taken over actual output multiples. Partial summation
handles the logarithmic term, while the other Type I term uses the true
Vaughan coefficient bound. These finite estimates do not bound the separate
Type II Gram correlations.
-/
open Nat Finset ArithmeticFunction
open scoped Classical BigOperators ArithmeticFunction.zeta ArithmeticFunction.Moebius
namespace Erdos821.AnalyticSieve.SuccessorVaughan
set_option maxHeartbeats 3000000

noncomputable def divisibleOutputPrefix (W : ℕ → ℝ) (d T : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 T with d ∣ n, W n

lemma divisibleOutputPrefix_eq_multiples (W : ℕ → ℝ) (d T : ℕ) (hd : 0 < d) :
    divisibleOutputPrefix W d T = ∑ s ∈ Icc 1 (T/d), W (d*s) := by
  simpa only [divisibleOutputPrefix, Nat.zero_div, zero_add] using
    sum_multiples_natural_interval W 0 T d hd

noncomputable def outputPrefixSelector (W : ℕ → ℝ) (d N : ℕ) : ℕ :=
  Classical.choose (exists_max_image (range (N+1))
    (fun T => |divisibleOutputPrefix W d T|) ⟨0,by simp⟩)

lemma outputPrefixSelector_spec (W : ℕ → ℝ) (d N : ℕ) :
    outputPrefixSelector W d N ≤ N ∧ ∀ T ≤ N,
      |divisibleOutputPrefix W d T| ≤
        |divisibleOutputPrefix W d (outputPrefixSelector W d N)| := by
  have h := Classical.choose_spec (exists_max_image (range (N+1))
    (fun T => |divisibleOutputPrefix W d T|) ⟨0,by simp⟩)
  exact ⟨by unfold outputPrefixSelector; exact Nat.le_of_lt_succ (mem_range.mp h.1),
    fun T hT => h.2 T (mem_range.mpr (by omega))⟩

noncomputable def outputMaxPrefix (W : ℕ → ℝ) (d N : ℕ) : ℝ :=
  |divisibleOutputPrefix W d (outputPrefixSelector W d N)|

lemma outputMaxPrefix_nonneg (W : ℕ → ℝ) (d N : ℕ) :
    0 ≤ outputMaxPrefix W d N := abs_nonneg _

lemma divisibleOutputPrefix_le_max (W : ℕ → ℝ) (d N T : ℕ) (hT : T ≤ N) :
    |divisibleOutputPrefix W d T| ≤ outputMaxPrefix W d N :=
  (outputPrefixSelector_spec W d N).2 T hT

lemma multiples_prefix_le_max (W : ℕ → ℝ) (d N L : ℕ) (hd : 0 < d)
    (hL : L ≤ N/d) :
    |∑ s ∈ Icc 1 L, W (d*s)| ≤ outputMaxPrefix W d N := by
  have hdL : d*L ≤ N := by
    simpa only [mul_comm] using (Nat.le_div_iff_mul_le hd).mp hL
  have h := divisibleOutputPrefix_le_max W d N (d*L) hdL
  rw [divisibleOutputPrefix_eq_multiples W d (d*L) hd,
    Nat.mul_div_cancel_left L hd] at h
  exact h

lemma abs_monotone_weighted_sum_le (f g : ℕ → ℝ)
    (hf : Monotone f) (hf0 : ∀ n, 0 ≤ f n) (B : ℝ) (hB : 0 ≤ B) (N : ℕ)
    (hg : ∀ L ≤ N, |∑ i ∈ range L, g i| ≤ B) :
    |∑ i ∈ range N, f i*g i| ≤ 2*B*f (N-1) := by
  change |∑ i ∈ range N, f i • g i| ≤ _
  rw [sum_range_by_parts]
  simp only [smul_eq_mul]
  calc
    _ ≤ |f (N-1)*(∑ i ∈ range N, g i)|+
        |∑ i ∈ range (N-1), (f (i+1)-f i)*(∑ j ∈ range (i+1), g j)| := abs_sub _ _
    _ ≤ f (N-1)*B+∑ i ∈ range (N-1), (f (i+1)-f i)*B := by
      apply _root_.add_le_add
      · rw [abs_mul,abs_of_nonneg (hf0 _)]
        exact mul_le_mul_of_nonneg_left (hg N le_rfl) (hf0 _)
      · apply (abs_sum_le_sum_abs _ _).trans
        apply sum_le_sum
        intro i hi
        have hdiff : 0 ≤ f (i+1)-f i := sub_nonneg.mpr (hf (by omega))
        rw [abs_mul,abs_of_nonneg hdiff]
        exact mul_le_mul_of_nonneg_left (hg (i+1) (by have := mem_range.mp hi; omega)) hdiff
    _ = f (N-1)*B+(f (N-1)-f 0)*B := by rw [← sum_mul,sum_range_sub]
    _ ≤ _ := by nlinarith only [mul_nonneg (hf0 0) hB]

lemma log_multiples_sum_le_max (W : ℕ → ℝ) (d N : ℕ) (hd : 0 < d) :
    |∑ s ∈ Icc 1 (N/d), Real.log s*W (d*s)| ≤
      2*outputMaxPrefix W d N*Real.log N := by
  have hf : Monotone (fun i : ℕ => Real.log (i+1 : ℕ)) := by
    intro i j hij
    exact log_nat_mono (by omega)
  have h := abs_monotone_weighted_sum_le (fun i => Real.log (i+1 : ℕ))
    (fun i => W (d*(i+1))) hf (fun _ => Real.log_natCast_nonneg _)
    (outputMaxPrefix W d N) (outputMaxPrefix_nonneg W d N) (N/d) (by
      intro L hL
      simpa only [sum_Icc_one_eq_sum_range] using multiples_prefix_le_max W d N L hd hL)
  have he : Real.log (N/d-1+1 : ℕ)=Real.log (N/d : ℕ) := by
    by_cases hz : N/d=0
    · simp [hz]
    · rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hz)]
  dsimp only at h
  rw [he] at h
  rw [sum_Icc_one_eq_sum_range]
  exact h.trans (mul_le_mul_of_nonneg_left (log_nat_mono (Nat.div_le_self N d))
    (mul_nonneg (by norm_num) (outputMaxPrefix_nonneg W d N)))

lemma hyperbolicSum_quotient (f g : ArithmeticFunction ℝ) (W : ℕ → ℝ) (N : ℕ) :
    hyperbolicSum f g W N =
      ∑ d ∈ Icc 1 N, f d*(∑ s ∈ Icc 1 (N/d), g s*W (d*s)) := by
  unfold hyperbolicSum
  apply sum_congr rfl
  intro d hd
  have hd0 : 0 < d := (mem_Icc.mp hd).1
  have he : (Icc 1 N).filter (fun s => d*s ≤ N) = Icc 1 (N/d) := by
    ext s
    simp only [mem_filter,mem_Icc,← Nat.le_div_iff_mul_le hd0,mul_comm d s]
    have hh := Nat.div_le_self N d
    omega
  rw [← sum_filter,he,mul_sum]
  exact sum_congr rfl (fun s _ => by ring)

lemma hyperbolicSum_supported_le (f g : ArithmeticFunction ℝ) (W : ℕ → ℝ)
    (N D : ℕ) (C : ℝ) (E : ℕ → ℝ) (hC : 0 ≤ C) (hE : ∀ d, 0 ≤ E d)
    (hf : ∀ d ∈ Icc 1 N, |f d| ≤ C) (hD : ∀ d, D < d → f d=0)
    (hinner : ∀ d ∈ Icc 1 N, |∑ s ∈ Icc 1 (N/d), g s*W (d*s)| ≤ E d) :
    |hyperbolicSum f g W N| ≤ C*∑ d ∈ Icc 1 D, E d := by
  rw [hyperbolicSum_quotient]
  calc
    _ ≤ ∑ d ∈ Icc 1 N, if d ≤ D then C*E d else 0 := by
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro d hd
      by_cases h : d ≤ D
      · rw [if_pos h,abs_mul]
        exact mul_le_mul (hf d hd) (hinner d hd) (abs_nonneg _) hC
      · simp only [if_neg h,hD d (Nat.lt_of_not_ge h),zero_mul,abs_zero,le_refl]
    _ = ∑ d ∈ (Icc 1 N).filter (fun d => d ≤ D), C*E d := (sum_filter _ _).symm
    _ ≤ ∑ d ∈ Icc 1 D, C*E d := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro d hd
        obtain ⟨hd,hdD⟩ := mem_filter.mp hd
        exact mem_Icc.mpr ⟨(mem_Icc.mp hd).1,hdD⟩
      · intro d hd hnot
        exact mul_nonneg hC (hE d)
    _ = _ := (mul_sum _ _ _).symm

noncomputable def outputDivisorError (W : ℕ → ℝ) (Q N : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 Q, outputMaxPrefix W d N

lemma outputDivisorError_nonneg (W : ℕ → ℝ) (Q N : ℕ) :
    0 ≤ outputDivisorError W Q N := sum_nonneg (fun d _ => outputMaxPrefix_nonneg W d N)

lemma outputDivisorError_mono (W : ℕ → ℝ) (Q R N : ℕ) (hQR : Q ≤ R) :
    outputDivisorError W Q N ≤ outputDivisorError W R N :=
  sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl hQR)
    (fun d _ _ => outputMaxPrefix_nonneg W d N)

lemma successor_mu_log_le_divisor_error (W : ℕ → ℝ) (N V : ℕ) :
    |hyperbolicSum (shortPart (μ : ArithmeticFunction ℝ) V) log W N| ≤
      2*Real.log N*outputDivisorError W V N := by
  have h := hyperbolicSum_supported_le (shortPart (μ : ArithmeticFunction ℝ) V) log W
    N V 1 (fun d => 2*outputMaxPrefix W d N*Real.log N) (by norm_num)
    (fun d => mul_nonneg (mul_nonneg (by norm_num) (outputMaxPrefix_nonneg W d N))
      (Real.log_natCast_nonneg N))
    (fun d _ => abs_shortPart_moebius_le_one V d)
    (fun d hd => by simp only [shortPart_apply,if_neg (not_le.mpr hd)]) (by
      intro d hd
      simpa only [log_apply] using log_multiples_sum_le_max W d N (mem_Icc.mp hd).1)
  apply h.trans_eq
  simp only [one_mul,outputDivisorError,mul_sum]
  exact sum_congr rfl (fun d _ => by ring)

lemma successor_typeI_zeta_le_divisor_error (W : ℕ → ℝ) (N U V : ℕ) :
    |hyperbolicSum (vaughanTypeI U V) (ζ : ArithmeticFunction ℝ) W N| ≤
      Real.log N*outputDivisorError W (U*V) N := by
  apply hyperbolicSum_supported_le (vaughanTypeI U V) (ζ : ArithmeticFunction ℝ)
    W N (U*V) (Real.log N) (fun d => outputMaxPrefix W d N)
    (Real.log_natCast_nonneg N) (outputMaxPrefix_nonneg W · N)
    (fun d hd => (abs_vaughanTypeI_le U V d).trans (log_nat_mono (mem_Icc.mp hd).2))
    (fun d hd => vaughanTypeI_eq_zero hd)
  intro d hd
  have he : (∑ s ∈ Icc 1 (N/d), (ζ : ArithmeticFunction ℝ) s*W (d*s)) =
      ∑ s ∈ Icc 1 (N/d), W (d*s) := by
    apply sum_congr rfl
    intro s hs
    have hs0 : s ≠ 0 := by have := (mem_Icc.mp hs).1; omega
    simp only [natCoe_apply,zeta_apply_ne hs0,Nat.cast_one,one_mul]
  rw [he]
  exact multiples_prefix_le_max W d N (N/d) (mem_Icc.mp hd).1 le_rfl

/-- The two Type I convolution terms need only actual output-divisibility
prefix discrepancies. In particular no character bound for an unrelated
input weight is substituted here. -/
theorem successorTypeIError_le_divisor_error (w v : ℕ → ℝ)
    (N U V : ℕ) (hU : 1 ≤ U) :
    successorTypeIError w v N U V ≤
      |weightedSum (shortPart vonMangoldt U) (fun n => w n-v n) N|+
      3*Real.log N*outputDivisorError (fun n => w n-v n) (U*V) N := by
  have h₁ := successor_mu_log_le_divisor_error (fun n => w n-v n) N V
  have h₂ := successor_typeI_zeta_le_divisor_error (fun n => w n-v n) N U V
  have hmono := outputDivisorError_mono (fun n => w n-v n) V (U*V) N
    (Nat.le_mul_of_pos_left V (by omega))
  have hh := mul_le_mul_of_nonneg_left hmono
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Real.log_natCast_nonneg N))
  unfold successorTypeIError
  linarith only [h₁,h₂,hh]

lemma weighted_short_sum_le (W : ℕ → ℝ) (N U : ℕ) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ n ∈ Icc 1 N, |W n| ≤ B) :
    |weightedSum (shortPart vonMangoldt U) W N| ≤ (U : ℝ)*B*Real.log N := by
  have hlog := Real.log_natCast_nonneg N
  have hcard : ((Icc 1 N).filter (fun n => n ≤ U)).card ≤ U := by
    apply (card_le_card (show (Icc 1 N).filter (fun n => n ≤ U) ⊆ Icc 1 U from fun n hn =>
      mem_Icc.mpr ⟨(mem_Icc.mp (mem_filter.mp hn).1).1,(mem_filter.mp hn).2⟩)).trans_eq
    simp
  unfold weightedSum
  calc
    _ ≤ ∑ n ∈ Icc 1 N, if n ≤ U then Real.log N*B else 0 := by
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro n hn
      by_cases hnU : n ≤ U
      · rw [if_pos hnU,abs_mul,abs_of_nonneg (shortPart_vonMangoldt_nonneg U n)]
        exact mul_le_mul ((shortPart_vonMangoldt_le U n).trans
          (vonMangoldt_le_log.trans (log_nat_mono (mem_Icc.mp hn).2)))
          (hB n hn) (abs_nonneg _) hlog
      · simp only [if_neg hnU,shortPart_apply,zero_mul,abs_zero,le_refl]
    _ = (((Icc 1 N).filter (fun n => n ≤ U)).card : ℝ)*(Real.log N*B) := by
      rw [← sum_filter,sum_const,nsmul_eq_mul]
    _ ≤ (U : ℝ)*(Real.log N*B) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (mul_nonneg hlog hB0)
    _ = _ := by ring

/-- A completely finite bound for the short term and both Type I terms. -/
theorem successorTypeIError_le_bounded_divisor_error (w v : ℕ → ℝ)
    (N U V : ℕ) (hU : 1 ≤ U) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ n ∈ Icc 1 N, |w n-v n| ≤ B) :
    successorTypeIError w v N U V ≤ (U : ℝ)*B*Real.log N+
      3*Real.log N*outputDivisorError (fun n => w n-v n) (U*V) N := by
  exact (successorTypeIError_le_divisor_error w v N U V hU).trans
    (add_le_add (weighted_short_sum_le (fun n => w n-v n) N U B hB0 hB) le_rfl)

/-- Exact output-divisibility counts for a finite successor rectangle.
Both the prefix cutoff and the successor congruence remain visible. -/
lemma rectangle_divisible_output_prefix (P A B : Finset ℕ) (d T : ℕ) :
    divisibleOutputPrefix (rectangleOutputWeight P A B) d T =
      (((P ×ˢ (A ×ˢ B)).filter (fun z =>
        z.1*z.2.1*z.2.2+1 ≤ T ∧ d ∣ z.1*z.2.1*z.2.2+1)).card : ℝ) := by
  unfold divisibleOutputPrefix rectangleOutputWeight
  rw [← Nat.cast_sum,sum_card_fiberwise_eq_card_filter]
  congr 1
  congr 1
  ext z
  have hpos : 1 ≤ z.1*z.2.1*z.2.2+1 := Nat.succ_pos _
  simp only [mem_filter,mem_Icc,hpos,true_and]

/-- A finite prime criterion with the Type I hypotheses stated entirely
as output divisibility discrepancies. The separate Gram hypothesis remains
necessary in this theorem. -/
theorem prime_output_card_gt_of_divisibility_gram (w v : ℕ → ℝ)
    (N U V : ℕ) (hN : 1 ≤ N) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (B C D K E : ℝ) (hB0 : 0 ≤ B) (hC0 : 0 ≤ C) (hE : 0 ≤ E)
    (hw : ∀ n ∈ Icc 1 N, 0 ≤ w n) (hB : ∀ n ∈ Icc 1 N, w n ≤ B)
    (hC : ∀ n ∈ Icc 1 N, |w n-v n| ≤ C)
    (Hdiv : outputDivisorError (fun n => w n-v n) (U*V) N ≤ D)
    (Hgram : ((typeIILevels N U V).card : ℝ)^3*
      (∑ j ∈ typeIILevels N U V, successorTypeIIBlockFourthMajorant w v N U V j) ≤ E^4)
    (Hmain : B*Real.log N*K+2*B*Real.sqrt N*Real.log N+
      (U : ℝ)*C*Real.log N+3*Real.log N*D+E < weightedSum vonMangoldt v N) :
    K < ((positivePrimeOutputs w N).card : ℝ) := by
  apply prime_output_card_gt_of_gram w v N U V hN hV B K E hB0 hE hw hB Hgram
  have ht := successorTypeIError_le_bounded_divisor_error w v N U V hU C hC0 hC
  have hd := mul_le_mul_of_nonneg_left Hdiv
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (Real.log_natCast_nonneg N))
  linarith only [ht,hd,Hmain]

end Erdos821.AnalyticSieve.SuccessorVaughan
