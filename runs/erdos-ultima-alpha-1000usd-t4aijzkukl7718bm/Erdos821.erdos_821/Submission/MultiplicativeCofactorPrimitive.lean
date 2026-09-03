import Submission.MultiplicativeCofactorMaximal
import Submission.CofactorProductPrimitiveMean

/-!
# Primitive conductor means with a retained multiplier pool

The large-sieve scale uses the full product D*B*N. This estimates the
primitive part only; an all-modulus successor sieve is still separate.
-/
open Nat Finset ArithmeticFunction
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 4000000

noncomputable def primitivePoolCofactorMean (f : ArithmeticFunction ℝ) (S P : Finset ℕ) (B N : ℕ) : ℝ :=
  ∑ d ∈ S, (∑ ψ ∈ Erdos821.primitiveCharacters d,
    ‖∑ c ∈ P, ψ (c : ZMod d)‖*cofactorMaxPrefix ψ B*
      ‖twistedArithmeticSum ψ f N‖)/(d.totient : ℝ)

lemma primitivePoolCofactorMean_nonneg (f : ArithmeticFunction ℝ) (S P : Finset ℕ) (B N : ℕ) :
    0 ≤ primitivePoolCofactorMean f S P B N := by
  exact sum_nonneg (fun d _ => div_nonneg (sum_nonneg (fun ψ _ =>
    mul_nonneg (mul_nonneg (norm_nonneg _) (cofactorMaxPrefix_nonneg ψ B)) (norm_nonneg _)))
      (Nat.cast_nonneg _))

noncomputable def poolCofactorLogLoss (D B : ℕ) : ℝ :=
  (2+Real.log ((B : ℝ)+2))*(1+Real.log (D*B : ℕ))^2

lemma poolCofactorLogLoss_nonneg (D B : ℕ) : 0 ≤ poolCofactorLogLoss D B := by
  have hh := Real.log_nonneg (show (1 : ℝ) ≤ (B : ℝ)+2 by linarith [Nat.cast_nonneg (α := ℝ) B])
  unfold poolCofactorLogLoss
  positivity

lemma maximalPairCofactorKernel_eq (Q D B N : ℕ) :
    maximalPairCofactorKernel Q D B N = poolCofactorLogLoss D B*cofactorBilinearKernel Q (D*B) N := by
  unfold maximalPairCofactorKernel pairCofactorKernel poolCofactorLogLoss
  ring

theorem primitivePoolCofactorMean_le_kernel (f : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (hΛ : ∀ n, f n ≤ vonMangoldt n) (S P : Finset ℕ) (L Q D B N : ℕ)
    (hPool : P ⊆ Icc 1 D) (hL : 0 < L) (hQ : 0 < Q) (hP : ∀ d ∈ S, L ≤ d ∧ d ≤ Q) :
    primitivePoolCofactorMean f S P B N ≤ maximalPairCofactorKernel Q D B N/(L : ℝ) := by
  let M : Finset ℕ+ := S.attach.image (fun d => ⟨d.val, hL.trans_le (hP d.val d.property).1⟩)
  have hmem {d : ℕ+} : d ∈ M ↔ (d : ℕ) ∈ S := by
    constructor
    · intro hd
      obtain ⟨e,he,heq⟩ := mem_image.mp hd
      have hv := congrArg (fun x : ℕ+ => (x : ℕ)) heq
      change e.val = (d : ℕ) at hv
      exact hv ▸ e.property
    · intro hd
      exact mem_image.mpr ⟨⟨d,hd⟩,mem_attach _ _,Subtype.ext rfl⟩
  have hsum (F : ℕ → ℝ) : (∑ d ∈ M, F d) = ∑ d ∈ S, F d := by
    apply sum_bij (fun (d : ℕ+) _ => (d : ℕ))
    · intro d hd
      exact hmem.mp hd
    · intro d hd e he h
      exact PNat.coe_injective h
    · intro d hd
      exact ⟨⟨d,hL.trans_le (hP d hd).1⟩,hmem.mpr hd,rfl⟩
    · intros
      rfl
  have hh := primitive_maxPrefix_pool_bilinear_bound f hf hΛ M Q hQ
    (fun d hd => (hP d (hmem.mp hd)).2)
    (fun d => Erdos821.primitiveCharacters (d : ℕ))
    (fun _ _ _ hc => (mem_filter.mp hc).2) P D B N hPool
  rw [hsum (fun d => (d : ℝ)/(d.totient : ℝ)*∑ ψ ∈ Erdos821.primitiveCharacters d,
    ‖∑ c ∈ P, ψ (c : ZMod d)‖*cofactorMaxPrefix ψ B*‖twistedArithmeticSum ψ f N‖)] at hh
  apply (le_div_iff₀ (by exact_mod_cast hL : (0 : ℝ) < L)).mpr
  rw [mul_comm,primitivePoolCofactorMean,mul_sum]
  apply (sum_le_sum (fun d hd => ?_)).trans hh
  have hdL : (L : ℝ) ≤ d := by exact_mod_cast (hP d hd).1
  have hc := mul_le_mul_of_nonneg_right hdL
    (div_nonneg (sum_nonneg (s := Erdos821.primitiveCharacters d) (fun ψ _ => mul_nonneg (mul_nonneg (norm_nonneg (∑ c ∈ P, ψ (c : ZMod d))) (cofactorMaxPrefix_nonneg ψ B)) (norm_nonneg (twistedArithmeticSum ψ f N))))
      (Nat.cast_nonneg d.totient))
  convert hc using 1; ring

lemma primitivePoolCofactorMean_dyadic_block (f : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (hΛ : ∀ n, f n ≤ vonMangoldt n) (P : Finset ℕ) (D j B N : ℕ)
    (hP : P ⊆ Icc 1 D) (hDB : 1 ≤ D*B) (hN : 1 ≤ N) :
    primitivePoolCofactorMean f (Ioc (2^j) (2^(j+1))) P B N ≤
      poolCofactorLogLoss D B*(36*(2+Real.log (((D*B : ℕ) : ℝ)+2))*Real.log N*
        cofactorBilinearShape (2^(j+1)) (2^j) (D*B) N) := by
  have hh := primitivePoolCofactorMean_le_kernel f hf hΛ (Ioc (2^j) (2^(j+1))) P
    (2^j) (2^(j+1)) D B N hP (by positivity) (by positivity)
    (fun d hd => ⟨(mem_Ioc.mp hd).1.le,(mem_Ioc.mp hd).2⟩)
  apply hh.trans
  rw [maximalPairCofactorKernel_eq,mul_div_assoc,
    show 2^(j+1)=2*2^j by ring]
  exact mul_le_mul_of_nonneg_left
    (cofactorBilinearKernel_double_bound (2^j) (D*B) N (by positivity) hDB hN)
    (poolCofactorLogLoss_nonneg D B)

lemma primitivePoolCofactorMean_dyadic_interval (f : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (hΛ : ∀ n, f n ≤ vonMangoldt n) (P : Finset ℕ) (D a r B N : ℕ)
    (hP : P ⊆ Icc 1 D) (hDB : 1 ≤ D*B) (hN : 1 ≤ N) :
    primitivePoolCofactorMean f (Ioc (2^a) (2^(a+r))) P B N ≤
      poolCofactorLogLoss D B*((r : ℝ)*36*(2+Real.log (((D*B : ℕ) : ℝ)+2))*Real.log N*
        cofactorBilinearShape (2^(a+r)) (2^a) (D*B) N) := by
  have hC : 0 ≤ poolCofactorLogLoss D B*36*(2+Real.log (((D*B : ℕ) : ℝ)+2))*Real.log N := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ ((D*B : ℕ) : ℝ)+2 by
      linarith [Nat.cast_nonneg (α := ℝ) (D*B)])
    have := Real.log_natCast_nonneg N
    have := poolCofactorLogLoss_nonneg D B
    positivity
  induction r with
  | zero => simp [primitivePoolCofactorMean]
  | succ r ih =>
    have h1 : 2^a ≤ (2 : ℕ)^(a+r) := Nat.pow_le_pow_right (by decide) (by omega)
    have h2 : 2^(a+r) ≤ (2 : ℕ)^(a+(r+1)) := Nat.pow_le_pow_right (by decide) (by omega)
    have he : primitivePoolCofactorMean f (Ioc (2^a) (2^(a+(r+1)))) P B N =
        primitivePoolCofactorMean f (Ioc (2^a) (2^(a+r))) P B N+
        primitivePoolCofactorMean f (Ioc (2^(a+r)) (2^(a+(r+1)))) P B N := by
      unfold primitivePoolCofactorMean
      rw [← Ioc_union_Ioc_eq_Ioc h1 h2,sum_union (Ioc_disjoint_Ioc_of_le le_rfl)]
    rw [he]
    have hlo : primitivePoolCofactorMean f (Ioc (2^a) (2^(a+r))) P B N ≤
        poolCofactorLogLoss D B*((r : ℝ)*36*(2+Real.log (((D*B : ℕ) : ℝ)+2))*Real.log N*
          cofactorBilinearShape (2^(a+(r+1))) (2^a) (D*B) N) := by
      apply ih.trans
      have hb := mul_le_mul_of_nonneg_left
        (cofactorBilinearShape_mono (2^(a+r)) (2^(a+(r+1))) (2^a) (2^a)
          (D*B) N h2 le_rfl (by positivity))
        (mul_nonneg (Nat.cast_nonneg (α := ℝ) r) hC)
      convert hb using 1 <;> ring
    have hblock := primitivePoolCofactorMean_dyadic_block f hf hΛ P D (a+r) B N hP hDB hN
    have hhi : primitivePoolCofactorMean f (Ioc (2^(a+r)) (2^(a+(r+1)))) P B N ≤
        poolCofactorLogLoss D B*(36*(2+Real.log (((D*B : ℕ) : ℝ)+2))*Real.log N*
          cofactorBilinearShape (2^(a+(r+1))) (2^a) (D*B) N) := by
      rw [show a+(r+1)=a+r+1 by omega]
      apply hblock.trans
      have hb := mul_le_mul_of_nonneg_left
        (cofactorBilinearShape_mono (2^(a+r+1)) (2^(a+r+1)) (2^(a+r)) (2^a) (D*B) N
          le_rfl h1 (by positivity)) hC
      convert hb using 1 <;> ring
    have hh := _root_.add_le_add hlo hhi
    convert hh using 1; push_cast; ring

/-- A power saving at the half level of the full product D*B*N, for the
primitive conductor range. The explicit additional loss is logarithmic. -/
theorem cofactorScale_pool_primitive_saving (f : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (hΛ : ∀ n, f n ≤ vonMangoldt n) (P : Finset ℕ) (D a b l v t m B X : ℕ)
    (hP : P ⊆ Icc 1 D) (ha : 1 ≤ a) (hab : a ≤ b) (hl : 1 ≤ l) (ht : 1 ≤ t)
    (hlevel : 2*b+1 ≤ l+t)
    (hB : cofactorScale l m ≤ D*B) (hBup : D*B ≤ cofactorScale v m)
    (hX : X ≤ cofactorScale t m) :
    ((2 : ℝ)^m)^2*primitivePoolCofactorMean f (Ioc (cofactorScale a m) (cofactorScale b m)) P B X ≤
      poolCofactorLogLoss D B*cofactorProductMeanConstant b v t*((m : ℝ)+1)^3*
        ((D*B : ℕ) : ℝ)*(cofactorScale t m : ℝ) := by
  by_cases hX0 : X = 0
  · subst X
    simp only [primitivePoolCofactorMean,twistedArithmeticSum,show Icc (1 : ℕ) 0 = ∅ by decide,
      sum_empty,norm_zero,mul_zero,zero_div,sum_const_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (poolCofactorLogLoss_nonneg D B)
      (cofactorProductMeanConstant_nonneg b v t)) (by positivity)) (Nat.cast_nonneg _))
        (Nat.cast_nonneg _)
  have hX1 : 1 ≤ X := by omega
  have hB1 : 1 ≤ D*B := (cofactorScale_pos l m).trans_le hB
  let r := 256*(b-a)*m
  have hexp : 256*a*m+r=256*b*m := by
    have hh := congrArg (fun z : ℕ => 256*z*m) (Nat.add_sub_of_le hab)
    dsimp [r]
    nlinarith only [hh]
  have hh := primitivePoolCofactorMean_dyadic_interval f hf hΛ P D (256*a*m) r B X hP hB1 hX1
  rw [hexp,← cofactorScale_eq a m,← cofactorScale_eq b m] at hh
  have hr : (r : ℝ) ≤ (256*(b : ℝ))*((m : ℝ)+1) := by
    have hnat : r ≤ 256*b*m := Nat.mul_le_mul_right m (Nat.mul_le_mul_left _ (Nat.sub_le b a))
    have hc : (r : ℝ) ≤ 256*(b : ℝ)*m := by exact_mod_cast hnat
    nlinarith only [hc,Nat.cast_nonneg (α := ℝ) b]
  have hlog := cofactorScale_log_add_two_le v m (D*B) hBup
  have hlogX : Real.log X ≤ 256*(t : ℝ)*((m : ℝ)+1) :=
    (log_nat_mono hX).trans (cofactorScale_log_le t m)
  have hshape := cofactorBilinearShape_mono_right (cofactorScale b m) (cofactorScale a m)
    (D*B) X (cofactorScale t m) hX
  have hnonneg : 0 ≤ 2+Real.log (((D*B : ℕ) : ℝ)+2) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ ((D*B : ℕ) : ℝ)+2 by
      linarith [Nat.cast_nonneg (α := ℝ) (D*B)])
    linarith
  have hraw : primitivePoolCofactorMean f (Ioc (cofactorScale a m) (cofactorScale b m)) P B X ≤
      poolCofactorLogLoss D B*
        ((36*(256*(b : ℝ))*(256*(v : ℝ)+4)*(256*(t : ℝ)))*((m : ℝ)+1)^3*
          cofactorBilinearShape (cofactorScale b m) (cofactorScale a m) (D*B) (cofactorScale t m)) := by
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (poolCofactorLogLoss_nonneg D B)
    have hc := mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right hr (by norm_num : (0 : ℝ) ≤ 36))
      hlog hnonneg (by positivity)) hlogX (Real.log_natCast_nonneg _) (by positivity)
    have hc' := mul_le_mul hc hshape (cofactorBilinearShape_nonneg _ _ _ _) (by positivity)
    convert hc' using 1; ring
  have hscaled := mul_le_mul_of_nonneg_left hraw (sq_nonneg ((2 : ℝ)^m))
  have hsave := mul_le_mul_of_nonneg_left
    (cofactorScale_bilinear_shape_saving a b l t m (D*B) ha hl ht hlevel hB)
    (mul_nonneg (poolCofactorLogLoss_nonneg D B)
      (show 0 ≤ (36*(256*(b : ℝ))*(256*(v : ℝ)+4)*(256*(t : ℝ)))*((m : ℝ)+1)^3 by positivity))
  apply hscaled.trans
  unfold cofactorProductMeanConstant
  convert hsave using 1 <;> ring

end Erdos821.AnalyticSieve
