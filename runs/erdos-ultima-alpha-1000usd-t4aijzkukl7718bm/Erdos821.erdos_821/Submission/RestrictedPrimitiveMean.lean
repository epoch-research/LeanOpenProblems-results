import Submission.RestrictedCofactorWeights
import Submission.CofactorProductPrimitiveMean

/-!
# Restricted-weight primitive means at the product half level

The pointwise bound on f controls its coefficient energy. No cancellation
of the restricted prime-weighted character sums is assumed individually.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 4000000

lemma restrictedMass_le_log (f : ArithmeticFunction ℝ)
    (hΛ : ∀ n, f n ≤ vonMangoldt n) (N : ℕ) :
    restrictedMass f N ≤ (N : ℝ)*Real.log N := by
  calc
    _ ≤ ∑ _n ∈ Icc 1 N, Real.log N := by
      apply sum_le_sum
      intro n hn
      exact (hΛ n).trans ((vonMangoldt_le_log (n := n)).trans (log_nat_mono (mem_Icc.mp hn).2))
    _ = _ := by simp

lemma restrictedBilinearKernel_le (f : ArithmeticFunction ℝ)
    (hΛ : ∀ n, f n ≤ vonMangoldt n) (Q B N : ℕ) :
    restrictedBilinearKernel f Q B N ≤ cofactorBilinearKernel Q B N := by
  have hlog : 0 ≤ 2+Real.log ((B : ℝ)+2) := by
    have := Real.log_nonneg (show 1 ≤ (B : ℝ)+2 by linarith [Nat.cast_nonneg (α := ℝ) B])
    linarith
  unfold restrictedBilinearKernel cofactorBilinearKernel
  apply mul_le_mul_of_nonneg_left _ hlog
  apply Real.sqrt_le_sqrt
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hh := mul_le_mul_of_nonneg_left (restrictedMass_le_log f hΛ N) (Real.log_natCast_nonneg N)
  convert hh using 1; ring

noncomputable def restrictedPrimitiveMean (f : ArithmeticFunction ℝ) (P : Finset ℕ) (B N : ℕ) : ℝ :=
  ∑ c ∈ P, (∑ ψ ∈ Erdos821.primitiveCharacters c,
    cofactorMaxPrefix ψ B*‖twistedArithmeticSum ψ f N‖)/(c.totient : ℝ)

lemma restrictedPrimitiveMean_nonneg (f : ArithmeticFunction ℝ) (P : Finset ℕ) (B N : ℕ) :
    0 ≤ restrictedPrimitiveMean f P B N := by
  exact sum_nonneg (fun c _ => div_nonneg (sum_nonneg
    (fun ψ _ => mul_nonneg (cofactorMaxPrefix_nonneg ψ B) (norm_nonneg _))) (Nat.cast_nonneg _))

theorem restrictedPrimitiveMean_le_kernel (f : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (hΛ : ∀ n, f n ≤ vonMangoldt n) (P : Finset ℕ) (L Q B N : ℕ)
    (hL : 0 < L) (hQ : 0 < Q) (hP : ∀ d ∈ P, L ≤ d ∧ d ≤ Q) :
    restrictedPrimitiveMean f P B N ≤ cofactorBilinearKernel Q B N/(L : ℝ) := by
  let M : Finset ℕ+ := P.attach.image (fun d => ⟨d.val, hL.trans_le (hP d.val d.property).1⟩)
  have hmem {d : ℕ+} : d ∈ M ↔ (d : ℕ) ∈ P := by
    constructor
    · intro hd
      obtain ⟨e,he,heq⟩ := mem_image.mp hd
      have hv := congrArg (fun x : ℕ+ => (x : ℕ)) heq
      change e.val = (d : ℕ) at hv
      exact hv ▸ e.property
    · intro hd
      exact mem_image.mpr ⟨⟨d,hd⟩,mem_attach _ _,Subtype.ext rfl⟩
  have hsum (F : ℕ → ℝ) : (∑ d ∈ M, F d) = ∑ d ∈ P, F d := by
    apply sum_bij (fun (d : ℕ+) _ => (d : ℕ))
    · intro d hd
      exact hmem.mp hd
    · intro d hd e he h
      exact PNat.coe_injective h
    · intro d hd
      exact ⟨⟨d,hL.trans_le (hP d hd).1⟩,hmem.mpr hd,rfl⟩
    · intros
      rfl
  have hh := (restricted_primitive_maxPrefix_bilinear_bound f hf hΛ M Q hQ
    (fun d hd => (hP d (hmem.mp hd)).2)
    (fun d => Erdos821.primitiveCharacters (d : ℕ))
    (fun _ _ _ hc => (mem_filter.mp hc).2) B N).trans (restrictedBilinearKernel_le f hΛ Q B N)
  rw [hsum (fun d => (d : ℝ)/(d.totient : ℝ)*∑ ψ ∈ Erdos821.primitiveCharacters d,
    cofactorMaxPrefix ψ B*‖twistedArithmeticSum ψ f N‖)] at hh
  apply (le_div_iff₀ (by exact_mod_cast hL : (0 : ℝ) < L)).mpr
  rw [mul_comm,restrictedPrimitiveMean,mul_sum]
  apply (sum_le_sum (fun d hd => ?_)).trans hh
  have hdL : (L : ℝ) ≤ d := by exact_mod_cast (hP d hd).1
  have hc := mul_le_mul_of_nonneg_right hdL
    (div_nonneg (sum_nonneg (s := Erdos821.primitiveCharacters d) (fun ψ _ => mul_nonneg (cofactorMaxPrefix_nonneg ψ B) (norm_nonneg (twistedArithmeticSum ψ f N))))
      (Nat.cast_nonneg d.totient))
  convert hc using 1; ring


lemma restrictedPrimitiveMean_dyadic_block (f : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (hΛ : ∀ n, f n ≤ vonMangoldt n) (j B N : ℕ) (hB : 1 ≤ B) (hN : 1 ≤ N) :
    restrictedPrimitiveMean f (Ioc (2^j) (2^(j+1))) B N ≤
      36*(2+Real.log ((B : ℝ)+2))*Real.log N*cofactorBilinearShape (2^(j+1)) (2^j) B N := by
  have hh := restrictedPrimitiveMean_le_kernel f hf hΛ (Ioc (2^j) (2^(j+1))) (2^j) (2^(j+1)) B N
    (by positivity) (by positivity) (fun d hd => ⟨(mem_Ioc.mp hd).1.le,(mem_Ioc.mp hd).2⟩)
  apply hh.trans
  rw [show 2^(j+1)=2*2^j by ring]
  exact cofactorBilinearKernel_double_bound (2^j) B N (by positivity) hB hN

/-- Each dyadic conductor block pays a logarithmic, not a power-size, loss. -/
theorem restrictedPrimitiveMean_dyadic_interval (f : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (hΛ : ∀ n, f n ≤ vonMangoldt n) (a r B N : ℕ) (hB : 1 ≤ B) (hN : 1 ≤ N) :
    restrictedPrimitiveMean f (Ioc (2^a) (2^(a+r))) B N ≤
      (r : ℝ)*36*(2+Real.log ((B : ℝ)+2))*Real.log N*cofactorBilinearShape (2^(a+r)) (2^a) B N := by
  have hC : 0 ≤ 36*(2+Real.log ((B : ℝ)+2))*Real.log N := by
    have := Real.log_nonneg (show 1 ≤ (B : ℝ)+2 by linarith [Nat.cast_nonneg (α := ℝ) B])
    have := Real.log_natCast_nonneg N
    positivity
  induction r with
  | zero => simp [restrictedPrimitiveMean]
  | succ r ih =>
    have h1 : 2^a ≤ (2 : ℕ)^(a+r) := Nat.pow_le_pow_right (by decide) (by omega)
    have h2 : 2^(a+r) ≤ (2 : ℕ)^(a+(r+1)) := Nat.pow_le_pow_right (by decide) (by omega)
    have he : restrictedPrimitiveMean f (Ioc (2^a) (2^(a+(r+1)))) B N =
        restrictedPrimitiveMean f (Ioc (2^a) (2^(a+r))) B N+
        restrictedPrimitiveMean f (Ioc (2^(a+r)) (2^(a+(r+1)))) B N := by
      unfold restrictedPrimitiveMean
      rw [← Ioc_union_Ioc_eq_Ioc h1 h2,sum_union (Ioc_disjoint_Ioc_of_le le_rfl)]
    rw [he]
    have hlo := ih.trans (mul_le_mul_of_nonneg_left
      (cofactorBilinearShape_mono _ _ _ _ B N h2 le_rfl (by positivity)) (by
        convert mul_nonneg (Nat.cast_nonneg (α := ℝ) r) hC using 1; ring))
    have hblock := restrictedPrimitiveMean_dyadic_block f hf hΛ (a+r) B N hB hN
    have hhi := hblock.trans (mul_le_mul_of_nonneg_left
      (cofactorBilinearShape_mono (2^(a+r+1)) (2^(a+(r+1))) (2^(a+r)) (2^a) B N (le_of_eq (congrArg (fun e : ℕ => (2 : ℕ)^e) (by omega))) h1 (by positivity)) hC)
    have hh := _root_.add_le_add hlo hhi
    convert hh using 1; push_cast; ring

lemma restricted_cofactorScale_primitive_saving (f : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (hΛ : ∀ n, f n ≤ vonMangoldt n) (a b l v t m B X : ℕ)
    (ha : 1 ≤ a) (hab : a ≤ b) (hl : 1 ≤ l) (ht : 1 ≤ t)
    (hlevel : 2*b+1 ≤ l+t)
    (hB : cofactorScale l m ≤ B) (hBup : B ≤ cofactorScale v m) (hX : X ≤ cofactorScale t m) :
    ((2 : ℝ)^m)^2*restrictedPrimitiveMean f (Ioc (cofactorScale a m) (cofactorScale b m)) B X ≤
      cofactorProductMeanConstant b v t*((m : ℝ)+1)^3*(B : ℝ)*(cofactorScale t m : ℝ) := by
  by_cases hX0 : X = 0
  · subst X
    simp only [restrictedPrimitiveMean,twistedArithmeticSum,show Icc (1 : ℕ) 0 = ∅ by decide,
      sum_empty,norm_zero,mul_zero,zero_div,sum_const_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (cofactorProductMeanConstant_nonneg b v t)
      (by positivity)) (Nat.cast_nonneg B)) (Nat.cast_nonneg _)
  have hX1 : 1 ≤ X := by omega
  have hB1 : 1 ≤ B := (cofactorScale_pos l m).trans_le hB
  let r := 256*(b-a)*m
  have hexp : 256*a*m+r=256*b*m := by
    have hh := congrArg (fun z : ℕ => 256*z*m) (Nat.add_sub_of_le hab)
    dsimp [r]
    nlinarith only [hh]
  have hh := restrictedPrimitiveMean_dyadic_interval f hf hΛ (256*a*m) r B X hB1 hX1
  rw [hexp,← cofactorScale_eq a m,← cofactorScale_eq b m] at hh
  have hr : (r : ℝ) ≤ (256*(b : ℝ))*((m : ℝ)+1) := by
    have hnat : r ≤ 256*b*m := Nat.mul_le_mul_right m (Nat.mul_le_mul_left _ (Nat.sub_le b a))
    have hc : (r : ℝ) ≤ 256*(b : ℝ)*m := by exact_mod_cast hnat
    nlinarith only [hc,Nat.cast_nonneg (α := ℝ) b]
  have hlog := cofactorScale_log_add_two_le v m B hBup
  have hlogX : Real.log X ≤ 256*(t : ℝ)*((m : ℝ)+1) :=
    (log_nat_mono hX).trans (cofactorScale_log_le t m)
  have hshape := cofactorBilinearShape_mono_right (cofactorScale b m) (cofactorScale a m) B X (cofactorScale t m) hX
  have hnonneg : 0 ≤ 2+Real.log ((B : ℝ)+2) := by
    have := Real.log_nonneg (show 1 ≤ (B : ℝ)+2 by linarith [Nat.cast_nonneg (α := ℝ) B])
    linarith
  have hraw : restrictedPrimitiveMean f (Ioc (cofactorScale a m) (cofactorScale b m)) B X ≤
      (36*(256*(b : ℝ))*(256*(v : ℝ)+4)*(256*(t : ℝ)))*((m : ℝ)+1)^3*
        cofactorBilinearShape (cofactorScale b m) (cofactorScale a m) B (cofactorScale t m) := by
    apply hh.trans
    have hc := mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right hr (by norm_num : (0 : ℝ) ≤ 36))
      hlog hnonneg (by positivity)) hlogX (Real.log_natCast_nonneg _) (by positivity)
    have hc' := mul_le_mul hc hshape (cofactorBilinearShape_nonneg _ _ _ _) (by positivity)
    convert hc' using 1; ring
  have hscaled := mul_le_mul_of_nonneg_left hraw (sq_nonneg ((2 : ℝ)^m))
  have hsave := mul_le_mul_of_nonneg_left
    (cofactorScale_bilinear_shape_saving a b l t m B ha hl ht hlevel hB)
    (show 0 ≤ (36*(256*(b : ℝ))*(256*(v : ℝ)+4)*(256*(t : ℝ)))*((m : ℝ)+1)^3 by positivity)
  apply hscaled.trans
  unfold cofactorProductMeanConstant
  convert hsave using 1 <;> ring


end Erdos821.AnalyticSieve
