import FormalConjecturesUtil

/-! Nonnegative Fourier densities from positive Toeplitz kernels. These
finite approximants will provide the spectral representation by compactness. -/
namespace Erdos371.DilationSpectrum
open Finset MeasureTheory Complex
open scoped Topology ENNReal ComplexConjugate
set_option autoImplicit false

/-- Positivity on all finite natural-indexed quadratic forms. -/
def ToeplitzPositive (c : ℤ → ℂ) : Prop :=
  ∀ H : ℕ, ∀ a : ℕ → ℂ,
    0 ≤ (∑ i ∈ range H, ∑ j ∈ range H, conj (a i)*a j*c ((i : ℤ)-j)).re

noncomputable def toeplitzKernel (c : ℤ → ℂ) (H : ℕ) (x : UnitAddCircle) : ℂ :=
  ∑ i ∈ range H, ∑ j ∈ range H, c ((i : ℤ)-j)*fourier ((j : ℤ)-i) x

lemma continuous_toeplitzKernel (c : ℤ → ℂ) (H : ℕ) : Continuous (toeplitzKernel c H) := by
  unfold toeplitzKernel
  exact continuous_finset_sum _ (fun i _ => continuous_finset_sum _ (fun j _ =>
    continuous_const.mul (fourier ((j : ℤ)-i)).continuous))

lemma integral_fourier_haar (k : ℤ) :
    (∫ x : UnitAddCircle, fourier k x ∂AddCircle.haarAddCircle) = if k = 0 then 1 else 0 := by
  have hh := (orthonormal_iff_ite.mp (orthonormal_fourier (T := 1))) 0 k
  rw [ContinuousMap.inner_toLp] at hh
  simpa only [fourier_zero,map_one,mul_one,eq_comm] using hh

lemma toeplitzKernel_conj (c : ℤ → ℂ) (hc : ∀ k, c (-k) = conj (c k)) (H : ℕ) (x : UnitAddCircle) :
    conj (toeplitzKernel c H x) = toeplitzKernel c H x := by
  unfold toeplitzKernel
  simp only [map_sum,map_mul,← hc,← fourier_neg]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  simp only [neg_sub]

lemma toeplitzKernel_real (c : ℤ → ℂ) (hc : ∀ k, c (-k) = conj (c k)) (H : ℕ) (x : UnitAddCircle) :
    ((toeplitzKernel c H x).re : ℂ) = toeplitzKernel c H x := by
  have hh := congrArg Complex.im (toeplitzKernel_conj c hc H x)
  simp only [conj_im] at hh
  apply Complex.ext
  · rfl
  · simp only [ofReal_im]
    linarith

lemma toeplitzKernel_nonneg (c : ℤ → ℂ) (hc : ToeplitzPositive c) (H : ℕ) (x : UnitAddCircle) :
    0 ≤ (toeplitzKernel c H x).re := by
  have hh := hc H (fun i => fourier i x)
  convert hh using 1
  unfold toeplitzKernel
  congr 1
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  rw [← fourier_neg,show (j : ℤ)-i= - (i : ℤ)+j by omega,fourier_add]
  ring

lemma integral_toeplitzKernel_mul_fourier (c : ℤ → ℂ) (H : ℕ) (k : ℤ) :
    (∫ x : UnitAddCircle, toeplitzKernel c H x*fourier k x ∂AddCircle.haarAddCircle) =
      ∑ i ∈ range H, ∑ j ∈ range H, if (i : ℤ)-j=k then c k else 0 := by
  have hi (i j : ℕ) : Integrable (fun x : UnitAddCircle => c ((i : ℤ)-j)*fourier ((j : ℤ)-i+k) x)
      AddCircle.haarAddCircle :=
    (continuous_const.mul (fourier ((j : ℤ)-i+k)).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he (x : UnitAddCircle) : toeplitzKernel c H x*fourier k x =
      ∑ i ∈ range H, ∑ j ∈ range H, c ((i : ℤ)-j)*fourier ((j : ℤ)-i+k) x := by
    simp only [toeplitzKernel,sum_mul,fourier_add,mul_assoc]
  simp_rw [he]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hi i j))]
  simp_rw [integral_finset_sum _ (fun j _ => hi _ j),integral_const_mul,integral_fourier_haar]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  by_cases hk : (i : ℤ)-j=k
  · simp [show (j : ℤ)-i+k=0 by omega,hk]
  · simp [show (j : ℤ)-i+k≠0 by omega,hk]

lemma toeplitz_index_sum_nat (c : ℤ → ℂ) (H k : ℕ) :
    (∑ i ∈ range H, ∑ j ∈ range H, if (i : ℤ)-j=k then c k else 0) = (H-k : ℕ)*c k := by
  classical
  rw [sum_comm]
  have hinner (j : ℕ) (hj : j ∈ range H) :
      (∑ i ∈ range H, if (i : ℤ)-j=k then c k else 0) = if j+k<H then c k else 0 := by
    have he (i : ℕ) : (i : ℤ)-j=k ↔ i=j+k := by omega
    simp_rw [he]
    simp only [sum_ite_eq',mem_range]
  rw [sum_congr rfl hinner]
  have he : (range H).filter (fun j => j+k<H) = range (H-k) := by
    ext j
    simp only [mem_filter,mem_range]
    omega
  rw [← sum_filter,he,sum_const,card_range,nsmul_eq_mul]

lemma toeplitz_index_sum (c : ℤ → ℂ) (H : ℕ) (k : ℤ) :
    (∑ i ∈ range H, ∑ j ∈ range H, if (i : ℤ)-j=k then c k else 0) =
      (H-k.natAbs : ℕ)*c k := by
  rcases le_total 0 k with hk | hk
  · lift k to ℕ using hk with n hn
    simpa using toeplitz_index_sum_nat c H n
  · obtain ⟨n,rfl⟩ : ∃ n : ℕ, k = -(n : ℤ) := by
      exact ⟨(-k).toNat,by rw [Int.toNat_of_nonneg (by omega)]; omega⟩
    rw [sum_comm]
    have he (i j : ℕ) : (j : ℤ)-i= -(n : ℤ) ↔ (i : ℤ)-j=n := by omega
    simp_rw [he]
    simpa only [Int.natAbs_neg,Int.natAbs_natCast] using
      toeplitz_index_sum_nat (fun k => c (-k)) H n

noncomputable def toeplitzDensity (c : ℤ → ℂ) (H : ℕ) (x : UnitAddCircle) : ℝ :=
  (toeplitzKernel c H x).re/H

lemma continuous_toeplitzDensity (c : ℤ → ℂ) (H : ℕ) : Continuous (toeplitzDensity c H) :=
  (Complex.continuous_re.comp (continuous_toeplitzKernel c H)).div_const _

lemma toeplitzDensity_nonneg (c : ℤ → ℂ) (hc : ToeplitzPositive c) (H : ℕ) (x : UnitAddCircle) :
    0 ≤ toeplitzDensity c H x := div_nonneg (toeplitzKernel_nonneg c hc H x) (Nat.cast_nonneg H)

lemma integral_toeplitzDensity_mul_fourier (c : ℤ → ℂ) (hc : ∀ k, c (-k)=conj (c k))
    (H : ℕ) (k : ℤ) :
    (∫ x : UnitAddCircle, (toeplitzDensity c H x : ℂ)*fourier k x ∂AddCircle.haarAddCircle) =
      ((H-k.natAbs : ℕ) : ℂ)/H*c k := by
  have he (x : UnitAddCircle) : (toeplitzDensity c H x : ℂ)*fourier k x =
      (toeplitzKernel c H x*fourier k x)/(H : ℂ) := by
    simp only [toeplitzDensity,ofReal_div,ofReal_natCast,toeplitzKernel_real c hc]
    ring
  simp_rw [he]
  rw [integral_div,integral_toeplitzKernel_mul_fourier,toeplitz_index_sum]
  ring

lemma integral_toeplitzDensity (c : ℤ → ℂ) (hc : ∀ k, c (-k)=conj (c k)) (H : ℕ) (hH : 0 < H) :
    (∫ x : UnitAddCircle, toeplitzDensity c H x ∂AddCircle.haarAddCircle) = (c 0).re := by
  have hh := integral_toeplitzDensity_mul_fourier c hc H 0
  have hHR : (H : ℂ) ≠ 0 := by exact_mod_cast hH.ne'
  simp only [fourier_zero,mul_one,Int.natAbs_zero,Nat.sub_zero,div_self hHR,one_mul] at hh
  have hreal : (∫ x : UnitAddCircle, (toeplitzDensity c H x : ℂ) ∂AddCircle.haarAddCircle) =
      Complex.ofReal (∫ x : UnitAddCircle, toeplitzDensity c H x ∂AddCircle.haarAddCircle) := integral_ofReal
  rw [hreal] at hh
  exact congrArg Complex.re hh

#print axioms integral_toeplitzDensity_mul_fourier
end Erdos371.DilationSpectrum
