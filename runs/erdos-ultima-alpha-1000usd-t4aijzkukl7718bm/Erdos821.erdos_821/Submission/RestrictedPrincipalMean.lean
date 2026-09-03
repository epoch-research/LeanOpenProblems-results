import Submission.RestrictedCofactorWeights
import Submission.UniformCofactorNaturalMean

/-! The all-modulus principal-density error retains the restricted mass. -/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 4000000

lemma restricted_principal_mean_of_local_weight (f : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (hΛ : ∀ n, f n ≤ vonMangoldt n) (Q A B N : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (H : ∀ d ∈ Icc 1 Q, (3 : ℝ)^d.primeFactors.card/(d.totient : ℝ) ≤ K/(d : ℝ)) :
    (∑ d ∈ Icc 1 Q, |restrictedCofactorPrincipal f d A B N-((B-A : ℕ) : ℝ)*restrictedMass f N/(d : ℝ)|) ≤
      K*(harmonic Q : ℝ)*(restrictedMass f N+((B-A : ℕ) : ℝ)*(Nat.log 2 N : ℝ)*Real.log Q) := by
  have hpoint (d : ℕ) (hd : d ∈ Icc 1 Q) :
      |restrictedCofactorPrincipal f d A B N-((B-A : ℕ) : ℝ)*restrictedMass f N/(d : ℝ)| ≤
        (K/(d : ℝ))*(restrictedMass f N+((B-A : ℕ) : ℝ)*(Nat.log 2 N : ℝ)*Real.log Q) := by
    have hdR : (0 : ℝ)<d := by exact_mod_cast (mem_Icc.mp hd).1
    have h1 : 1/(d.totient : ℝ) ≤ K/(d : ℝ) :=
      (div_le_div_of_nonneg_right (one_le_pow₀ (by norm_num : (1 : ℝ)≤3)) (Nat.cast_nonneg _)).trans (H d hd)
    have hlog : characterLiftError d N ≤ (Nat.log 2 N : ℝ)*Real.log Q :=
      mul_le_mul_of_nonneg_left (Real.log_le_log hdR (by exact_mod_cast (mem_Icc.mp hd).2)) (Nat.cast_nonneg _)
    have hsmall := mul_le_mul_of_nonneg_right (H d hd) (restrictedMass_nonneg f hf N)
    have hlarge := mul_le_mul_of_nonneg_left
      (mul_le_mul h1 hlog (characterLiftError_nonneg d N) (div_nonneg hK hdR.le)) (Nat.cast_nonneg (B-A))
    apply (restricted_principal_density_lift_error f hf hΛ d A B N (mem_Icc.mp hd).1).trans
    convert _root_.add_le_add hsmall hlarge using 1 <;> ring
  apply (sum_le_sum hpoint).trans_eq
  rw [← sum_mul]
  have he : (∑ d ∈ Icc 1 Q, K/(d : ℝ)) = K*(harmonic Q : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    rw [mul_sum]
    exact sum_congr rfl (fun d _ => by ring)
  rw [he]

/-- Uniform over all positive moduli, including those with small conductors. -/
theorem exists_restricted_principal_mean_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ArithmeticFunction ℝ,
      (∀ n, 0 ≤ f n) → (∀ n, f n ≤ vonMangoldt n) → ∀ Q A B N : ℕ,
      (∑ d ∈ Icc 1 Q, |restrictedCofactorPrincipal f d A B N-((B-A : ℕ) : ℝ)*restrictedMass f N/(d : ℝ)|) ≤
        C*(Q : ℝ)^ε*(harmonic Q : ℝ)*(restrictedMass f N+((B-A : ℕ) : ℝ)*(Nat.log 2 N : ℝ)*Real.log Q) := by
  obtain ⟨C,hC,HC⟩ := exists_uniform_local_factor_div_totient 3 ε (by norm_num) hε
  refine ⟨C,hC,?_⟩
  intro f hf hΛ Q A B N
  exact restricted_principal_mean_of_local_weight f hf hΛ Q A B N (C*(Q : ℝ)^ε) (by positivity)
    (fun d hd => HC Q d (mem_Icc.mp hd).1 (mem_Icc.mp hd).2)


lemma exists_restricted_principal_power_saving_cutoff (b t l : ℕ) (hb : 1 ≤ b) (ht : 1 ≤ t) (hl : 1 ≤ l) :
    ∃ K : ℝ, 0 < K ∧ ∀ f : ArithmeticFunction ℝ,
      (∀ n, 0 ≤ f n) → (∀ n, f n ≤ vonMangoldt n) → ∀ m A B X : ℕ, X ≤ cofactorScale t m → cofactorScale l m ≤ B-A →
      (∑ d ∈ Icc 1 (cofactorScale b m), |restrictedCofactorPrincipal f d A B X-
        ((B-A : ℕ) : ℝ)*restrictedMass f X/(d : ℝ)|) ≤
          K*((m : ℝ)+1)^6/(2 : ℝ)^m*((B-A : ℕ) : ℝ)*(cofactorScale t m : ℝ) := by
  let ε : ℝ := 1/(256*(b : ℝ))
  obtain ⟨C,hC,HC⟩ := exists_restricted_principal_mean_bound ε (by dsimp [ε]; positivity)
  let D : ℝ := (256*(b : ℝ)+1)*(6+(256*(t : ℝ))*(256*(b : ℝ)))
  refine ⟨C*D,mul_pos hC (by dsimp [D]; positivity),?_⟩
  intro f hf hΛ m A B X hXN hAB
  let E := ∑ d ∈ Icc 1 (cofactorScale b m), |restrictedCofactorPrincipal f d A B X-
    ((B-A : ℕ) : ℝ)*restrictedMass f X/(d : ℝ)|
  let L : ℝ := (B-A : ℕ)
  let N : ℝ := cofactorScale t m
  let Z : ℝ := (2 : ℝ)^m
  let H : ℝ := harmonic (cofactorScale b m)
  let J : ℝ := Nat.log 2 (cofactorScale t m)
  let Q : ℝ := Real.log (cofactorScale b m)
  have hL : 0 ≤ L := Nat.cast_nonneg _
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hZ : 0 < Z := by dsimp [Z]; positivity
  have hH : 0 ≤ H := harmonic_natCast_nonneg _
  have hJ : 0 ≤ J := Nat.cast_nonneg _
  have hQ : 0 ≤ Q := Real.log_natCast_nonneg _
  have hmain0 := HC f hf hΛ (cofactorScale b m) A B X
  have hlogX : (Nat.log 2 X : ℝ) ≤ Nat.log 2 (cofactorScale t m) := by
    exact_mod_cast Nat.log_mono_right hXN
  have hmain : E ≤ C*(cofactorScale b m : ℝ)^ε*H*(restrictedMass f X+L*J*Q) := by
    apply hmain0.trans
    gcongr
  rw [show ε=1/(256*(b : ℝ)) from rfl,cofactorScale_rpow b m hb] at hmain
  change E ≤ C*Z*H*(restrictedMass f X+L*J*Q) at hmain
  have hZL : Z^2 ≤ L := by
    have hh := cofactorScale_lift_saving 0 l m hl
    have he : (cofactorScale 0 m : ℝ)=1 := by simp [cofactorScale,progressionScaleN]
    rw [he,mul_one] at hh
    exact hh.trans (by dsimp [L]; exact_mod_cast hAB)
  have hZN : Z^2 ≤ N := by
    have hh := cofactorScale_lift_saving 0 t m ht
    simpa [cofactorScale,progressionScaleN,Z,N] using hh
  have hS : Z^2*restrictedMass f X ≤ 6*L*N := by
    have hh := mul_le_mul hZL (((restrictedMass_le_mangoldt f hΛ X).trans (Erdos821.mangoldtSum_le_six_mul X)).trans (by exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hXN) (by norm_num)))
      (restrictedMass_nonneg f hf _) hL
    convert hh using 1; dsimp [N]; ring
  have hI := mul_le_mul_of_nonneg_right hZN (mul_nonneg (mul_nonneg hL hJ) hQ)
  have hsum := mul_le_mul_of_nonneg_left (_root_.add_le_add hS hI) (mul_nonneg hC.le hH)
  have hEZ := mul_le_mul_of_nonneg_left hmain hZ.le
  have hnormalized : Z*E ≤ C*L*N*(H*(6+J*Q)) := by
    nlinarith only [hEZ,hsum]
  have hpoly := mul_le_mul_of_nonneg_left (cofactor_principal_log_polynomial b t m)
    (show 0 ≤ C*L*N by positivity)
  have hscaled : Z*E ≤ C*L*N*D*((m : ℝ)+1)^6 := by
    have hh := hnormalized.trans hpoly
    convert hh using 1; dsimp [D]; ring
  change E ≤ C*D*((m : ℝ)+1)^6/Z*L*N
  apply (mul_le_mul_iff_right₀ hZ).mp
  apply hscaled.trans_eq
  field_simp



end Erdos821.AnalyticSieve
