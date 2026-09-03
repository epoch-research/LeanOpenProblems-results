import Submission.MultiplicativeCofactorEnergy

/-!
# A maximal cofactor mean retaining multiplier-pool cancellation

Fourier completion applies to the short cofactor before multiplication.
Its phase-weighted product coefficients retain the divisor-square energy
bound. This is a primitive-character estimate, not yet an all-modulus
prime-successor sieve.
-/
open Nat Finset ArithmeticFunction
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 5000000

lemma cofactor_prefix_fourier (B T : ℕ) (hT : T ≤ B)
    {q : ℕ} (χ : DirichletCharacter ℂ q) :
    (∑ a ∈ Icc 1 T, χ (a : ZMod q)) =
      ∑ r : ZMod (B+2), normalizedFourier (intervalIndicator (T+1)) r *
        (∑ a ∈ Icc 1 B, (ZMod.stdAddChar (r*(a : ZMod (B+2))) : ℂ)*χ (a : ZMod q)) := by
  letI : NeZero (B+2) := ⟨by omega⟩
  calc
    _ = ∑ a ∈ Icc 1 B, intervalIndicator (T+1) (a : ZMod (B+2))*χ (a : ZMod q) := by
      rw [← cofactorPrefix_filter B T hT,sum_filter]
      apply sum_congr rfl
      intro a ha
      have haB := (mem_Icc.mp ha).2
      simp only [intervalIndicator,ZMod.val_natCast_of_lt (by omega : a < B+2),
        Nat.lt_succ_iff,ite_mul,one_mul,zero_mul]
    _ = ∑ a ∈ Icc 1 B, ∑ r : ZMod (B+2),
        (normalizedFourier (intervalIndicator (T+1)) r *
          (ZMod.stdAddChar (r*(a : ZMod (B+2))) : ℂ))*χ (a : ZMod q) := by
      apply sum_congr rfl
      intro a ha
      rw [normalizedFourier_inversion (intervalIndicator (T+1)) (a : ZMod (B+2)),sum_mul]
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro r hr
      rw [mul_sum]
      exact sum_congr rfl (fun a ha => by ring)

lemma pool_prefix_weight_fourier (f : ArithmeticFunction ℝ) (P : Finset ℕ) (B T N : ℕ) (hT : T ≤ B)
    {q : ℕ} (χ : DirichletCharacter ℂ q) :
    (∑ c ∈ P, χ (c : ZMod q))*(∑ a ∈ Icc 1 T, χ (a : ZMod q))*
        twistedArithmeticSum χ f N =
      ∑ r : ZMod (B+2), normalizedFourier (intervalIndicator (T+1)) r *
        ((∑ c ∈ P, χ (c : ZMod q))*
          (∑ a ∈ Icc 1 B, (ZMod.stdAddChar (r*(a : ZMod (B+2))) : ℂ)*χ (a : ZMod q))*
          twistedArithmeticSum χ f N) := by
  rw [cofactor_prefix_fourier B T hT χ]
  rw [mul_sum,sum_mul]
  exact sum_congr rfl (fun r hr => by ring)

noncomputable def maximalPairCofactorKernel (Q D B N : ℕ) : ℝ :=
  (2+Real.log ((B : ℝ)+2))*pairCofactorKernel Q D B N

lemma maximalPairCofactorKernel_nonneg (Q D B N : ℕ) :
    0 ≤ maximalPairCofactorKernel Q D B N := by
  unfold maximalPairCofactorKernel
  have hh := Real.log_nonneg (show (1 : ℝ) ≤ (B : ℝ)+2 by linarith [Nat.cast_nonneg (α := ℝ) B])
  exact mul_nonneg (by linarith) (pairCofactorKernel_nonneg _ _ _ _)

/-- The prefix may depend on both modulus and character. The multiplier
pool is retained inside the character sum, not replaced by its cardinality. -/
theorem adaptive_pairCofactor_bilinear_bound (f : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (hΛ : ∀ n, f n ≤ vonMangoldt n)
    (M : Finset ℕ+) (Q : ℕ) (hQ : 0 < Q) (hM : ∀ q ∈ M, (q : ℕ) ≤ Q)
    (C : ∀ q : ℕ+, Finset (DirichletCharacter ℂ (q : ℕ)))
    (hC : ∀ q ∈ M, ∀ χ ∈ C q, χ.IsPrimitive)
    (P : Finset ℕ) (D B N : ℕ) (hP : P ⊆ Icc 1 D)
    (T : (q : ℕ+) → DirichletCharacter ℂ (q : ℕ) → ℕ)
    (hT : ∀ q ∈ M, ∀ χ ∈ C q, T q χ ≤ B) :
    (∑ q ∈ M, ((q : ℕ) : ℝ)/(q : ℕ).totient*∑ χ ∈ C q,
      ‖∑ c ∈ P, χ (c : ZMod (q : ℕ))‖*
      ‖∑ a ∈ Icc 1 (T q χ), χ (a : ZMod (q : ℕ))‖*
      ‖twistedArithmeticSum χ f N‖) ≤ maximalPairCofactorKernel Q D B N := by
  letI : NeZero (B+2) := ⟨by omega⟩
  have hh := weighted_norm_variable_combination_le (M.sigma C) (univ : Finset (ZMod (B+2)))
    (fun z => ((z.1 : ℕ) : ℝ)/(z.1 : ℕ).totient)
    (fun z r => normalizedFourier (intervalIndicator (T z.1 z.2+1)) r)
    (fun r z => (∑ c ∈ P, z.2 (c : ZMod (z.1 : ℕ)))*
      (∑ a ∈ Icc 1 B, (ZMod.stdAddChar (r*(a : ZMod (B+2))) : ℂ)*z.2 (a : ZMod (z.1 : ℕ)))*
        twistedArithmeticSum z.2 f N)
    (fun r => fourierEnvelope (-r)) (fun z hz => by positivity)
    (fun r hr => fourierEnvelope_nonneg _)
    (fun z hz r hr => norm_interval_fourier_le_envelope _ (by
      have ht := hT z.1 (mem_sigma.mp hz).1 z.2 (mem_sigma.mp hz).2
      omega) r)
    (pairCofactorKernel Q D B N) (by
      intro r hr
      have hf := primitive_pairCofactor_bilinear_bound f hf hΛ M Q hQ hM C hC P (Icc 1 B)
        (fun a => (ZMod.stdAddChar (r*(a : ZMod (B+2))) : ℂ)) D B N hP Subset.rfl
        (fun a ha => le_of_eq (Circle.norm_coe _))
      simpa only [sum_sigma,norm_mul,← mul_sum] using hf)
  have he : (∑ z ∈ M.sigma C, ((z.1 : ℕ) : ℝ)/(z.1 : ℕ).totient*
      ‖∑ r : ZMod (B+2), normalizedFourier (intervalIndicator (T z.1 z.2+1)) r *
        ((∑ c ∈ P, z.2 (c : ZMod (z.1 : ℕ)))*
          (∑ a ∈ Icc 1 B, (ZMod.stdAddChar (r*(a : ZMod (B+2))) : ℂ)*z.2 (a : ZMod (z.1 : ℕ)))*
          twistedArithmeticSum z.2 f N)‖) =
      ∑ q ∈ M, ((q : ℕ) : ℝ)/(q : ℕ).totient*∑ χ ∈ C q,
        ‖∑ c ∈ P, χ (c : ZMod (q : ℕ))‖*
        ‖∑ a ∈ Icc 1 (T q χ), χ (a : ZMod (q : ℕ))‖*
        ‖twistedArithmeticSum χ f N‖ := by
    rw [sum_sigma]
    apply sum_congr rfl
    intro q hq
    rw [mul_sum]
    apply sum_congr rfl
    intro χ hχ
    rw [← pool_prefix_weight_fourier f P B (T q χ) N (hT q hq χ hχ) χ,norm_mul,norm_mul]
  rw [he] at hh
  apply hh.trans
  unfold maximalPairCofactorKernel
  have henv := sum_neg_fourierEnvelope_le (W := B+2) (by omega)
  simpa only [Nat.cast_add,Nat.cast_ofNat] using
    mul_le_mul_of_nonneg_right henv (pairCofactorKernel_nonneg Q D B N)

/-- A maximal primitive mean for a finite multiplier pool and a cofactor
prefix. No lower-density hypothesis on the multiplier pool is imposed. -/
theorem primitive_maxPrefix_pool_bilinear_bound (f : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (hΛ : ∀ n, f n ≤ vonMangoldt n)
    (M : Finset ℕ+) (Q : ℕ) (hQ : 0 < Q) (hM : ∀ q ∈ M, (q : ℕ) ≤ Q)
    (C : ∀ q : ℕ+, Finset (DirichletCharacter ℂ (q : ℕ)))
    (hC : ∀ q ∈ M, ∀ χ ∈ C q, χ.IsPrimitive)
    (P : Finset ℕ) (D B N : ℕ) (hP : P ⊆ Icc 1 D) :
    (∑ q ∈ M, ((q : ℕ) : ℝ)/(q : ℕ).totient*∑ χ ∈ C q,
      ‖∑ c ∈ P, χ (c : ZMod (q : ℕ))‖*cofactorMaxPrefix χ B*
        ‖twistedArithmeticSum χ f N‖) ≤ maximalPairCofactorKernel Q D B N :=
  adaptive_pairCofactor_bilinear_bound f hf hΛ M Q hQ hM C hC P D B N hP
    (fun _ χ => cofactorPrefixSelector χ B)
    (fun _ _ χ _ => (cofactorPrefixSelector_spec χ B).1)

end Erdos821.AnalyticSieve
