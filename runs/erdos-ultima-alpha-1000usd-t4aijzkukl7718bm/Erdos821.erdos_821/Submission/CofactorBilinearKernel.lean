import Submission.CofactorBilinearLargeSieve

/-!
# Explicit unbalanced bounds for the cofactor bilinear kernel
-/
open Nat Finset ArithmeticFunction
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 3000000

lemma cofactorBilinearKernel_factor_bound (Q B N : ℕ) (hB : 1 ≤ B) (hN : 1 ≤ N) :
    cofactorBilinearKernel Q B N ≤
      (2+Real.log ((B : ℝ)+2))*Real.log N*
        (2*(Q : ℝ)+6*Real.sqrt B)*(2*(Q : ℝ)+6*Real.sqrt N)*Real.sqrt B*Real.sqrt N := by
  let K : ℕ → ℝ := fun X => 2*(Q : ℝ)^2+4*(2*Real.pi*X+1)
  have hK (X : ℕ) : 0 ≤ K X := by dsimp [K]; positivity
  have he : cofactorBilinearKernel Q B N =
      (2+Real.log ((B : ℝ)+2))*Real.log N*
        Real.sqrt (K B)*Real.sqrt (K N)*Real.sqrt B*Real.sqrt N := by
    unfold cofactorBilinearKernel
    change (2+Real.log ((B : ℝ)+2))*Real.sqrt (K B*K N*(B : ℝ)*((N : ℝ)*(Real.log N)^2)) = _
    rw [Real.sqrt_mul (mul_nonneg (mul_nonneg (hK B) (hK N)) (Nat.cast_nonneg B)),
      Real.sqrt_mul (mul_nonneg (hK B) (hK N)),Real.sqrt_mul (hK B),
      Real.sqrt_mul (Nat.cast_nonneg (α := ℝ) N),Real.sqrt_sq_eq_abs,
      abs_of_nonneg (Real.log_natCast_nonneg N)]
    ring
  rw [he]
  have hlog : 0 ≤ 2+Real.log ((B : ℝ)+2) := by
    have := Real.log_nonneg (show 1 ≤ (B : ℝ)+2 by linarith [Nat.cast_nonneg (α := ℝ) B])
    linarith
  have hkB := large_sieve_kernel_sqrt_le Q B hB
  have hkN := large_sieve_kernel_sqrt_le Q N hN
  change Real.sqrt (K B) ≤ _ at hkB
  change Real.sqrt (K N) ≤ _ at hkN
  gcongr

noncomputable def cofactorBilinearShape (Q R B N : ℕ) : ℝ :=
  (Q : ℝ)*Real.sqrt B*Real.sqrt N+(B : ℝ)*Real.sqrt N+(N : ℝ)*Real.sqrt B+
    (B : ℝ)*N/(R : ℝ)

lemma cofactorBilinearShape_nonneg (Q R B N : ℕ) : 0 ≤ cofactorBilinearShape Q R B N := by
  unfold cofactorBilinearShape
  positivity

lemma cofactorBilinearKernel_double_bound (D B N : ℕ) (hD : 0 < D) (hB : 1 ≤ B) (hN : 1 ≤ N) :
    cofactorBilinearKernel (2*D) B N/(D : ℝ) ≤
      36*(2+Real.log ((B : ℝ)+2))*Real.log N*cofactorBilinearShape (2*D) D B N := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hlogB : 0 ≤ 2+Real.log ((B : ℝ)+2) := by
    have := Real.log_nonneg (show 1 ≤ (B : ℝ)+2 by linarith [Nat.cast_nonneg (α := ℝ) B])
    linarith
  have hsB := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) B)
  have hsN := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N)
  have hpoly :
      (2*((2*D : ℕ) : ℝ)+6*Real.sqrt B)*(2*((2*D : ℕ) : ℝ)+6*Real.sqrt N)*Real.sqrt B*Real.sqrt N ≤
        36*cofactorBilinearShape (2*D) D B N*(D : ℝ) := by
    unfold cofactorBilinearShape
    push_cast
    have he : (↑B*↑N/(D : ℝ))*(D : ℝ) = (B : ℝ)*N := by field_simp
    have ha : 0 ≤ (D : ℝ)^2*Real.sqrt B*Real.sqrt N := by positivity
    have hb : 0 ≤ (D : ℝ)*(B : ℝ)*Real.sqrt N := by positivity
    have hn : 0 ≤ (D : ℝ)*(N : ℝ)*Real.sqrt B := by positivity
    calc
      _ = 16*(D : ℝ)^2*Real.sqrt B*Real.sqrt N+24*(D : ℝ)*(B : ℝ)*Real.sqrt N+
          24*(D : ℝ)*(N : ℝ)*Real.sqrt B+36*(B : ℝ)*N := by
        rw [← hsB,← hsN]
        simp only [Real.sqrt_sq_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
        ring
      _ ≤ _ := by nlinarith only [he,ha,hb,hn]
  apply (div_le_iff₀ hDR).mpr
  apply (cofactorBilinearKernel_factor_bound (2*D) B N hB hN).trans
  have hh := mul_le_mul_of_nonneg_left hpoly (mul_nonneg hlogB (Real.log_natCast_nonneg N))
  convert hh using 1 <;> ring

lemma cofactorBilinearShape_mono (Q Q' R R' B N : ℕ)
    (hQQ : Q ≤ Q') (hRR : R' ≤ R) (hR : 0 < R') :
    cofactorBilinearShape Q R B N ≤ cofactorBilinearShape Q' R' B N := by
  unfold cofactorBilinearShape
  have hq : (Q : ℝ) ≤ Q' := by exact_mod_cast hQQ
  have hr : (R' : ℝ) ≤ R := by exact_mod_cast hRR
  apply _root_.add_le_add
  · gcongr
  · exact div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hR) hr

lemma primitiveCofactorBilinearMean_dyadic_block (j B N : ℕ) (hB : 1 ≤ B) (hN : 1 ≤ N) :
    primitiveCofactorBilinearMean (Ioc (2^j) (2^(j+1))) B N ≤
      36*(2+Real.log ((B : ℝ)+2))*Real.log N*cofactorBilinearShape (2^(j+1)) (2^j) B N := by
  have hh := primitiveCofactorBilinearMean_le_kernel (Ioc (2^j) (2^(j+1))) (2^j) (2^(j+1)) B N
    (by positivity) (by positivity) (fun d hd => ⟨(mem_Ioc.mp hd).1.le,(mem_Ioc.mp hd).2⟩)
  apply hh.trans
  rw [show 2^(j+1)=2*2^j by ring]
  exact cofactorBilinearKernel_double_bound (2^j) B N (by positivity) hB hN

/-- Each dyadic conductor block pays a logarithmic, not a power-size, loss. -/
theorem primitiveCofactorBilinearMean_dyadic_interval (a r B N : ℕ) (hB : 1 ≤ B) (hN : 1 ≤ N) :
    primitiveCofactorBilinearMean (Ioc (2^a) (2^(a+r))) B N ≤
      (r : ℝ)*36*(2+Real.log ((B : ℝ)+2))*Real.log N*cofactorBilinearShape (2^(a+r)) (2^a) B N := by
  have hC : 0 ≤ 36*(2+Real.log ((B : ℝ)+2))*Real.log N := by
    have := Real.log_nonneg (show 1 ≤ (B : ℝ)+2 by linarith [Nat.cast_nonneg (α := ℝ) B])
    have := Real.log_natCast_nonneg N
    positivity
  induction r with
  | zero => simp [primitiveCofactorBilinearMean]
  | succ r ih =>
    have h1 : 2^a ≤ (2 : ℕ)^(a+r) := Nat.pow_le_pow_right (by decide) (by omega)
    have h2 : 2^(a+r) ≤ (2 : ℕ)^(a+(r+1)) := Nat.pow_le_pow_right (by decide) (by omega)
    have he : primitiveCofactorBilinearMean (Ioc (2^a) (2^(a+(r+1)))) B N =
        primitiveCofactorBilinearMean (Ioc (2^a) (2^(a+r))) B N+
        primitiveCofactorBilinearMean (Ioc (2^(a+r)) (2^(a+(r+1)))) B N := by
      unfold primitiveCofactorBilinearMean
      rw [← Ioc_union_Ioc_eq_Ioc h1 h2,sum_union (Ioc_disjoint_Ioc_of_le le_rfl)]
    rw [he]
    have hlo := ih.trans (mul_le_mul_of_nonneg_left
      (cofactorBilinearShape_mono _ _ _ _ B N h2 le_rfl (by positivity)) (by
        convert mul_nonneg (Nat.cast_nonneg (α := ℝ) r) hC using 1; ring))
    have hblock := primitiveCofactorBilinearMean_dyadic_block (a+r) B N hB hN
    have hhi := hblock.trans (mul_le_mul_of_nonneg_left
      (cofactorBilinearShape_mono (2^(a+r+1)) (2^(a+(r+1))) (2^(a+r)) (2^a) B N (le_of_eq (congrArg (fun e : ℕ => (2 : ℕ)^e) (by omega))) h1 (by positivity)) hC)
    have hh := _root_.add_le_add hlo hhi
    convert hh using 1; push_cast; ring

end Erdos821.AnalyticSieve
