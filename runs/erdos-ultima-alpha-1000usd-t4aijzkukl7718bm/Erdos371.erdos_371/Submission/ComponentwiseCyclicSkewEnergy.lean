import Submission.ComponentwiseMixturePrimeTransfer
import Submission.AbelCyclicPrimeSkew

/-! A finite componentwise skew bound by odd-shift indicator energies.
The bound is uniform in the number and lengths of the cycles. -/
namespace Erdos371.FiniteInformation
open Finset AbelPrimes
set_option autoImplicit false

variable {A : Type*} [Fintype A] [DecidableEq A]

noncomputable def cyclicOddIndicatorAverage (N : ℕ) [NeZero N]
    (L : ZMod N → A) (P : Finset ℕ) (b : A) (x : ZMod N) : ℝ :=
  (∑ p ∈ P, ((if L (x+(p : ZMod N))=b then (1 : ℝ) else 0)-
    (if L (x-(p : ZMod N))=b then 1 else 0)))/(P.card : ℝ)

noncomputable def cyclicOddIndicatorEnergy (N : ℕ) [NeZero N]
    (L : ZMod N → A) (P : Finset ℕ) (b : A) : ℝ :=
  mean (uniformLaw (ZMod N)) (fun x => (cyclicOddIndicatorAverage N L P b x)^2)

noncomputable def cyclicPrimeSkewAverage (N : ℕ) [NeZero N]
    (L : ZMod N → A) (P : Finset ℕ) (C : A → A → ℝ) : ℝ :=
  (∑ p ∈ P, cyclicSkew L C (p : ZMod N))/(P.card : ℝ)

lemma mean_uniform_eq_cyclicSkew (N : ℕ) [NeZero N]
    (L : ZMod N → A) (C : A → A → ℝ) (p : ZMod N) :
    mean (uniformLaw (ZMod N)) (fun x => C (L x) (L (x+p))) = cyclicSkew L C p := by
  simp only [mean,uniformLaw,ZMod.card,cyclicSkew,← mul_sum,div_eq_mul_inv]
  ring

lemma cyclic_pair_indicator_expansion (N : ℕ) [NeZero N]
    (L : ZMod N → A) (C : A → A → ℝ) (p : ZMod N) :
    (∑ b, mean (uniformLaw (ZMod N)) (fun x => C (L x) b*
      ((if L (x+p)=b then (1 : ℝ) else 0)-(if L (x-p)=b then 1 else 0)))) =
        cyclicSkew L C p-cyclicSkew L C (-p) := by
  rw [← mean_finset_sum]
  have hpoint (x : ZMod N) :
      (∑ b, C (L x) b*((if L (x+p)=b then (1 : ℝ) else 0)-
        (if L (x-p)=b then 1 else 0))) = C (L x) (L (x+p))-C (L x) (L (x-p)) := by
    simp only [mul_sub,sum_sub_distrib,mul_ite,mul_one,mul_zero]
    simp only [eq_comm,sum_ite_eq',mem_univ,if_true]
  simp_rw [hpoint]
  rw [mean_sub,mean_uniform_eq_cyclicSkew]
  simp only [sub_eq_add_neg,mean_uniform_eq_cyclicSkew]

lemma cyclicPrimeSkewAverage_indicator_expansion (N : ℕ) [NeZero N]
    (L : ZMod N → A) (P : Finset ℕ) (C : A → A → ℝ)
    (hC : ∀ a b, C b a = -C a b) :
    2*cyclicPrimeSkewAverage N L P C = ∑ b, mean (uniformLaw (ZMod N))
      (fun x => C (L x) b*cyclicOddIndicatorAverage N L P b x) := by
  simp only [cyclicOddIndicatorAverage,← mul_div_assoc,mul_sum,mean_div,mean_finset_sum,← sum_div]
  rw [sum_comm]
  simp_rw [cyclic_pair_indicator_expansion,cyclicSkew_odd L C hC,sub_neg_eq_add]
  simp only [sum_add_distrib,cyclicPrimeSkewAverage]
  ring

lemma abs_le_positive_add_square_div (x η : ℝ) (hη : 0 < η) :
    |x| ≤ η+x^2/η := by
  have hh : |x| * η ≤ η^2+x^2 := by nlinarith [sq_nonneg (|x|-η),sq_abs x]
  have hd := (le_div_iff₀ hη).mpr hh
  convert hd using 1
  field_simp

lemma cyclicPrimeSkewAverage_energy_bound (N : ℕ) [NeZero N]
    (L : ZMod N → A) (P : Finset ℕ) (C : A → A → ℝ)
    (hC : ∀ a b, C b a = -C a b) (hCb : ∀ a b, |C a b| ≤ 1)
    (η : ℝ) (hη : 0 < η) :
    2*|cyclicPrimeSkewAverage N L P C| ≤
      Fintype.card A*η+(∑ b, cyclicOddIndicatorEnergy N L P b)/η := by
  have he := congrArg abs (cyclicPrimeSkewAverage_indicator_expansion N L P C hC)
  rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<2)] at he
  rw [he]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ b, mean (uniformLaw (ZMod N)) (fun x =>
        η+(cyclicOddIndicatorAverage N L P b x)^2/η) := by
      apply sum_le_sum
      intro b _
      apply (abs_mean_le_mean_abs _ _).trans
      apply mean_mono
      intro x
      rw [abs_mul]
      calc
        _ ≤ |cyclicOddIndicatorAverage N L P b x| := by
          have h := mul_le_mul_of_nonneg_right (hCb (L x) b)
            (abs_nonneg (cyclicOddIndicatorAverage N L P b x))
          simpa only [one_mul] using h
        _ ≤ _ := abs_le_positive_add_square_div _ η hη
    _ = _ := by
      simp only [mean_add,mean_const,mean_div,cyclicOddIndicatorEnergy,
        sum_add_distrib,sum_const,card_univ,nsmul_eq_mul,sum_div]

/-- The observables may differ across components. Only their skew symmetry
and common unit bound are used. -/
theorem componentwise_cyclicPrimeSkewAverage_energy_bound
    {ι : Type*} [Fintype ι] (N : ι → ℕ) [∀ i, NeZero (N i)]
    (ρ : Law ι) (L : ∀ i, ZMod (N i) → A) (P : Finset ℕ)
    (C : ι → A → A → ℝ) (hC : ∀ i a b, C i b a = -C i a b)
    (hCb : ∀ i a b, |C i a b| ≤ 1) (η : ℝ) (hη : 0 < η) :
    2*mean ρ (fun i => |cyclicPrimeSkewAverage (N i) (L i) P (C i)|) ≤
      Fintype.card A*η+
        mean ρ (fun i => ∑ b, cyclicOddIndicatorEnergy (N i) (L i) P b)/η := by
  have h := mean_mono ρ _ _ (fun i =>
    cyclicPrimeSkewAverage_energy_bound (N i) (L i) P (C i) (hC i) (hCb i) η hη)
  simpa only [mean_const_mul,mean_add,mean_const,mean_div] using h

#print axioms componentwise_cyclicPrimeSkewAverage_energy_bound
end Erdos371.FiniteInformation
