import Submission.PrimeBlockMomentComparison
import Submission.SharpPrimeBlockVariance

/-!
Exponential and even-moment bounds for the independent Bernoulli prime model.
Arithmetic moments still require the comparison error to be controlled.
-/
namespace Erdos1206.PrimeBlockModelMoments
open Finset PrimeBlockVariance PrimeBlockMomentComparison FiniteThinnedSieve
open SharpPrimeBlockVariance
open scoped Classical

lemma model_mono (P : Finset ℕ) (hP : ∀ p∈P,p.Prime)
    (F G : Finset ℕ → ℝ) (hFG : ∀ J ⊆ P,F J ≤ G J) : model P F ≤ model P G := by
  apply sum_le_sum
  intro J hJ
  apply mul_le_mul_of_nonneg_left (hFG J (mem_powerset.mp hJ))
  apply weight_nonneg P _ _ (mem_powerset.mp hJ)
  intro p hp
  refine ⟨by positivity,?_⟩
  exact (div_le_one (by exact_mod_cast (hP p hp).pos)).mpr
    (by exact_mod_cast (hP p hp).one_lt.le)

lemma model_score_eq (P : Finset ℕ) (w : ℕ → ℝ) (J : Finset ℕ) :
    modelScore P w J=(∑ p∈P,w p*mask J p)-mean P w := by
  simp only [modelScore,modelCentered,mean,mul_sub,←sum_sub_distrib]
  apply sum_congr rfl
  intros
  ring

lemma model_exponential_exact (P : Finset ℕ) (w : ℕ → ℝ) (t : ℝ) :
    model P (fun J => Real.exp (t*modelScore P w J))=
      Real.exp (-(t*mean P w))*∏ p∈P,(1+(Real.exp (t*w p)-1)/p) := by
  have he (J : Finset ℕ) : Real.exp (t*modelScore P w J)=
      Real.exp (-(t*mean P w))*∏ p∈P,(if p∈J then Real.exp (t*w p) else 1) := by
    rw [model_score_eq,mul_sub,Real.exp_sub,div_eq_mul_inv,←Real.exp_neg,mul_comm]
    congr 1
    rw [mul_sum,Real.exp_sum]
    apply prod_congr rfl
    intro p hp
    by_cases hj : p∈J <;> simp [mask,hj]
  simp_rw [he]
  rw [model_const_mul]
  change Real.exp (-(t*mean P w))*(∑ J∈P.powerset,
    weight P (fun p => 1/(p:ℝ)) J*(∏ p∈P,if p∈J then Real.exp (t*w p) else 1))=_
  rw [FiniteSelbergWeights.expectation_product]
  congr 1
  apply prod_congr rfl
  intros
  ring

/-- The independent model has the expected quadratic cumulant for signed
weights bounded by one. The parameter t can have either sign. -/
theorem model_exponential_le (P : Finset ℕ) (hP : ∀ p∈P,p.Prime)
    (w : ℕ → ℝ) (hw : ∀ p∈P,|w p| ≤ 1) {t : ℝ} (ht : |t| ≤ 1) :
    model P (fun J => Real.exp (t*modelScore P w J)) ≤
      Real.exp (t^2*mass P w) := by
  rw [model_exponential_exact]
  have hprod : (∏ p∈P,(1+(Real.exp (t*w p)-1)/p)) ≤
      Real.exp (∑ p∈P,(Real.exp (t*w p)-1)/p) := by
    rw [Real.exp_sum]
    apply prod_le_prod
    · intro p hp
      have hpR : (1:ℝ) < p := by exact_mod_cast (hP p hp).one_lt
      have he := Real.exp_pos (t*w p)
      have heq : (1+(Real.exp (t*w p)-1)/(p:ℝ))=(p+Real.exp (t*w p)-1)/p := by
        field_simp; ring
      rw [heq]
      exact div_nonneg (by linarith) (Nat.cast_nonneg p)
    · intro p hp
      simpa only [add_comm] using Real.add_one_le_exp ((Real.exp (t*w p)-1)/p)
  apply (mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le).trans
  rw [←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have he : -(t*mean P w)+(∑ p∈P,(Real.exp (t*w p)-1)/p)=
      ∑ p∈P,(Real.exp (t*w p)-1-t*w p)/p := by
    simp only [mean,mul_sum,←sum_neg_distrib,←sum_add_distrib]
    apply sum_congr rfl
    intros
    ring
  rw [he,mass,mul_sum]
  apply sum_le_sum
  intro p hp
  have htw : |t*w p| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul ht (hw p hp) (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hb := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le htw)).2
  have hh := div_le_div_of_nonneg_right hb (Nat.cast_nonneg p)
  convert hh using 1; ring

lemma even_power_le_exponentials (x : ℝ) (k : ℕ) :
    x^(2*k) ≤ (Nat.factorial (2*k):ℝ)*(Real.exp x+Real.exp (-x)) := by
  have hh := Real.pow_div_factorial_le_exp |x| (abs_nonneg x) (2*k)
  have hfac : (0:ℝ) < Nat.factorial (2*k) := by exact_mod_cast Nat.factorial_pos (2*k)
  have hpow : |x|^(2*k)=x^(2*k) := by rw [pow_mul,pow_mul,sq_abs]
  rw [hpow] at hh
  have hbound : Real.exp |x| ≤ Real.exp x+Real.exp (-x) := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]; linarith [Real.exp_pos (-x)]
    · rw [abs_of_nonpos hx]; linarith [Real.exp_pos x]
  have hm := (div_le_iff₀ hfac).mp (hh.trans hbound)
  simpa only [mul_comm] using hm

/-- A parameterized even-moment estimate. Choosing t as a function of k and
mass gives the usual subexponential/Bernstein moment scale. -/
theorem model_even_moment (P : Finset ℕ) (hP : ∀ p∈P,p.Prime)
    (w : ℕ → ℝ) (hw : ∀ p∈P,|w p| ≤ 1) (k : ℕ) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t ≤ 1) :
    t^(2*k)*model P (fun J => (modelScore P w J)^(2*k)) ≤
      2*(Nat.factorial (2*k):ℝ)*Real.exp (t^2*mass P w) := by
  have hh := model_mono P hP
    (fun J => (t*modelScore P w J)^(2*k))
    (fun J => (Nat.factorial (2*k):ℝ)*
      (Real.exp (t*modelScore P w J)+Real.exp (-(t*modelScore P w J))))
    (fun J _ => even_power_le_exponentials (t*modelScore P w J) k)
  simp_rw [mul_pow,←neg_mul] at hh
  rw [model_const_mul,model_const_mul,model_add] at hh
  have hp := model_exponential_le P hP w hw
    (show |t| ≤ 1 by rwa [abs_of_pos ht0])
  have hn := model_exponential_le P hP w hw
    (show |-t| ≤ 1 by rwa [abs_neg,abs_of_pos ht0])
  rw [neg_sq] at hn
  have hfac : 0 ≤ (Nat.factorial (2*k):ℝ) := Nat.cast_nonneg _
  have hb := mul_le_mul_of_nonneg_left (add_le_add hp hn) hfac
  have hbe : (Nat.factorial (2*k):ℝ)*
      (Real.exp (t^2*mass P w)+Real.exp (t^2*mass P w))=
      2*(Nat.factorial (2*k):ℝ)*Real.exp (t^2*mass P w) := by ring
  exact hh.trans (hb.trans_eq hbe)

/-- Optimizing the model parameter gives a uniform Bernstein-scale moment
bound, with no reference to the number or magnitudes of the primes. -/
theorem model_even_moment_optimized (P : Finset ℕ) (hP : ∀ p∈P,p.Prime)
    (w : ℕ → ℝ) (hw : ∀ p∈P,|w p| ≤ 1) {k : ℕ} (hk : 0 < k) :
    model P (fun J => (modelScore P w J)^(2*k)) ≤
      2*(12*(k:ℝ)*(mass P w+k))^k := by
  let M := mass P w
  have hM : 0 ≤ M := mass_nonneg P w
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hden : 0 < M+k := by positivity
  let t := Real.sqrt ((k:ℝ)/(M+k))
  have ht0 : 0 < t := Real.sqrt_pos.mpr (div_pos hkR hden)
  have ht1 : t ≤ 1 := Real.sqrt_le_one.mpr ((div_le_one hden).mpr (by linarith))
  have ht2 : t^2=(k:ℝ)/(M+k) := Real.sq_sqrt (div_nonneg hkR.le hden.le)
  have htM : t^2*M ≤ k := by
    rw [ht2,div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hExp : Real.exp (t^2*M) ≤ (3:ℝ)^k := by
    calc
      _ ≤ Real.exp ((k:ℝ)*1) := Real.exp_le_exp.mpr (by simpa using htM)
      _ = (Real.exp 1)^k := Real.exp_nat_mul 1 k
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le k
  have hfact : (Nat.factorial (2*k):ℝ) ≤ (2*(k:ℝ))^(2*k) := by
    exact_mod_cast Nat.factorial_le_pow (2*k)
  have hm := model_even_moment P hP w hw k ht0 ht1
  change t^(2*k)*model P (fun J => modelScore P w J^(2*k)) ≤
    2*(Nat.factorial (2*k):ℝ)*Real.exp (t^2*M) at hm
  have hupper : t^(2*k)*model P (fun J => modelScore P w J^(2*k)) ≤
      2*(12*(k:ℝ)^2)^k := by
    apply hm.trans
    calc
      _ ≤ 2*(2*(k:ℝ))^(2*k)*(3:ℝ)^k := by gcongr
      _ = _ := by rw [pow_mul,mul_assoc,←mul_pow]; congr 1; ring
  have hscale : t^2*(12*(k:ℝ)*(M+k))=12*(k:ℝ)^2 := by
    rw [ht2]
    field_simp
  have hscalePow : t^(2*k)*(2*(12*(k:ℝ)*(M+k))^k)=2*(12*(k:ℝ)^2)^k := by
    rw [pow_mul,mul_left_comm,←mul_pow,hscale]
  apply (mul_le_mul_iff_right₀ (pow_pos ht0 (2*k))).mp
  rw [hscalePow]
  exact hupper

/-- The arithmetic estimate keeps its polynomial comparison error explicit. -/
theorem arithmetic_even_moment (P : Finset ℕ) (hP : ∀ p∈P,p.Prime)
    (w : ℕ → ℝ) (hw : ∀ p∈P,|w p| ≤ 1) {k : ℕ} (hk : 0 < k) (N : ℕ) :
    (∑ n∈Icc 1 N,(primeSum P w n-mean P w)^(2*k)) ≤
      2*(N:ℝ)*(12*(k:ℝ)*(mass P w+k))^k+(2*∑ p∈P,|w p|)^(2*k) := by
  have hd := (abs_le.mp (score_moment_discrepancy P hP w (2*k) N)).2
  have hm := mul_le_mul_of_nonneg_left (model_even_moment_optimized P hP w hw hk)
    (Nat.cast_nonneg N)
  linarith


#print axioms model_exponential_le
#print axioms model_even_moment
#print axioms model_even_moment_optimized
#print axioms arithmetic_even_moment
end Erdos1206.PrimeBlockModelMoments
