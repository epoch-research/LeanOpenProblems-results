import Submission.CofactorMaxPrefix
import Submission.AdaptivePrefixLargeSieve

/-!
# A bilinear primitive mean retaining maximal cofactor prefixes
-/
open Nat Finset ArithmeticFunction
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 3000000

lemma cofactorPrefix_filter (B T : ℕ) (hT : T ≤ B) :
    (Icc 1 B).filter (fun n => n ≤ T) = Icc 1 T := by
  ext n
  simp only [mem_filter,mem_Icc]
  omega

lemma mangoldt_coefficient_energy (N : ℕ) :
    (∑ n ∈ Icc 1 N, ‖(vonMangoldt n : ℂ)‖^2) ≤ (N : ℝ)*(Real.log N)^2 := by
  simp only [Complex.norm_real,Real.norm_eq_abs,sq_abs]
  calc
    _ ≤ ∑ _n ∈ Icc 1 N, (Real.log N)^2 := by
      apply sum_le_sum
      intro n hn
      have h := (vonMangoldt_le_log (n := n)).trans (log_nat_mono (mem_Icc.mp hn).2)
      nlinarith [vonMangoldt_nonneg (n := n),Real.log_natCast_nonneg N]
    _ = _ := by simp

noncomputable def cofactorBilinearKernel (Q B N : ℕ) : ℝ :=
  (2+Real.log ((B : ℝ)+2))*Real.sqrt
    ((2*(Q : ℝ)^2+4*(2*Real.pi*B+1))*(2*(Q : ℝ)^2+4*(2*Real.pi*N+1))*
      (B : ℝ)*((N : ℝ)*(Real.log N)^2))

lemma cofactorBilinearKernel_nonneg (Q B N : ℕ) : 0 ≤ cofactorBilinearKernel Q B N := by
  have hlog : 0 ≤ Real.log ((B : ℝ)+2) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) B])
  unfold cofactorBilinearKernel
  positivity

theorem primitive_maxPrefix_bilinear_bound
    (M : Finset ℕ+) (Q : ℕ) (hQ : 0 < Q) (hM : ∀ q ∈ M, (q : ℕ) ≤ Q)
    (C : ∀ q : ℕ+, Finset (DirichletCharacter ℂ (q : ℕ)))
    (hC : ∀ q ∈ M, ∀ χ ∈ C q, χ.IsPrimitive) (B N : ℕ) :
    (∑ q ∈ M, ((q : ℕ) : ℝ)/(q : ℕ).totient*∑ χ ∈ C q,
      cofactorMaxPrefix χ B*‖twistedArithmeticSum χ vonMangoldt N‖) ≤
        cofactorBilinearKernel Q B N := by
  have hh := adaptive_prefix_bilinear_large_sieve_nat M Q hQ hM C hC
    (Icc 1 B) (Icc 1 N) (fun _ => 1) (fun n => (vonMangoldt n : ℂ)) B N
    (fun n hn => (mem_Icc.mp hn).2) (fun n hn => (mem_Icc.mp hn).2)
    (fun _ χ => cofactorPrefixSelector χ B)
    (fun _ _ χ _ => (cofactorPrefixSelector_spec χ B).1)
  simp only [cofactorPrefix_filter B _ (cofactorPrefixSelector_spec _ B).1,
    one_mul,norm_one,one_pow,sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel,
    mul_one] at hh
  change (∑ q ∈ M, ((q : ℕ) : ℝ)/(q : ℕ).totient*∑ χ ∈ C q,
    cofactorMaxPrefix χ B*‖twistedArithmeticSum χ vonMangoldt N‖) ≤ _ at hh
  apply hh.trans
  unfold cofactorBilinearKernel
  apply mul_le_mul_of_nonneg_left _ (by
    have hlog : 0 ≤ Real.log ((B : ℝ)+2) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) B])
    linarith)
  apply Real.sqrt_le_sqrt
  exact mul_le_mul_of_nonneg_left (mangoldt_coefficient_energy N) (by positivity)

noncomputable def primitiveCofactorBilinearMean (P : Finset ℕ) (B N : ℕ) : ℝ :=
  ∑ c ∈ P, (∑ ψ ∈ Erdos821.primitiveCharacters c,
    cofactorMaxPrefix ψ B*‖twistedArithmeticSum ψ vonMangoldt N‖)/(c.totient : ℝ)

lemma primitiveCofactorBilinearMean_nonneg (P : Finset ℕ) (B N : ℕ) :
    0 ≤ primitiveCofactorBilinearMean P B N := by
  exact sum_nonneg (fun c _ => div_nonneg (sum_nonneg
    (fun ψ _ => mul_nonneg (cofactorMaxPrefix_nonneg ψ B) (norm_nonneg _))) (Nat.cast_nonneg _))

theorem primitiveCofactorBilinearMean_le_kernel (P : Finset ℕ) (L Q B N : ℕ)
    (hL : 0 < L) (hQ : 0 < Q) (hP : ∀ d ∈ P, L ≤ d ∧ d ≤ Q) :
    primitiveCofactorBilinearMean P B N ≤ cofactorBilinearKernel Q B N/(L : ℝ) := by
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
  have hh := primitive_maxPrefix_bilinear_bound M Q hQ
    (fun d hd => (hP d (hmem.mp hd)).2)
    (fun d => Erdos821.primitiveCharacters (d : ℕ))
    (fun _ _ _ hc => (mem_filter.mp hc).2) B N
  rw [hsum (fun d => (d : ℝ)/(d.totient : ℝ)*∑ ψ ∈ Erdos821.primitiveCharacters d,
    cofactorMaxPrefix ψ B*‖twistedArithmeticSum ψ vonMangoldt N‖)] at hh
  apply (le_div_iff₀ (by exact_mod_cast hL : (0 : ℝ) < L)).mpr
  rw [mul_comm,primitiveCofactorBilinearMean,mul_sum]
  apply (sum_le_sum (fun d hd => ?_)).trans hh
  have hdL : (L : ℝ) ≤ d := by exact_mod_cast (hP d hd).1
  have hc := mul_le_mul_of_nonneg_right hdL
    (div_nonneg (sum_nonneg (s := Erdos821.primitiveCharacters d) (fun ψ _ => mul_nonneg (cofactorMaxPrefix_nonneg ψ B) (norm_nonneg (twistedArithmeticSum ψ vonMangoldt N))))
      (Nat.cast_nonneg d.totient))
  convert hc using 1; ring

end Erdos821.AnalyticSieve
