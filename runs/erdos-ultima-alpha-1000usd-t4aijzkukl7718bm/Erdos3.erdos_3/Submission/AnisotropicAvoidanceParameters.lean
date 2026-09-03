import Submission.AnisotropicFejerKernel

/-! Polynomial-in-total-precision powers for anisotropic finite kernels.
Each coordinate cutoff is linear in inverse dyadic accuracy. -/
namespace Erdos3AnisotropicAvoidanceParameters
open Finset Erdos3AnisotropicFejerKernel
open scoped BigOperators Classical
set_option maxHeartbeats 3000000

variable {I : Type*} [Fintype I]

def precisionMass (t : I → ℕ) : ℕ := Fintype.card I + ∑ i, t i + 1

def kernelPower (t : I → ℕ) : ℕ := 16*(precisionMass t)^2

def frequencyMeanExponent (t : I → ℕ) : ℕ :=
  (∑ i, t i)+6*Fintype.card I+2*precisionMass t*Fintype.card I+2

lemma precisionMass_pos (t : I → ℕ) : 0 < precisionMass t := by unfold precisionMass; omega
lemma kernelPower_pos (t : I → ℕ) : 0 < kernelPower t := by
  exact Nat.mul_pos (by decide) (Nat.pow_pos (precisionMass_pos t))

lemma kernelPower_dyadic (t : I → ℕ) : kernelPower t ≤ 2^(4+2*precisionMass t) := by
  have hh : precisionMass t ≤ 2^(precisionMass t) := Nat.lt_two_pow_self.le
  calc
    _ ≤ 16*(2^(precisionMass t))^2 := Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left hh 2)
    _ = _ := by rw [show 16=2^4 by norm_num,← pow_mul,← pow_add]; congr 1; omega

lemma cutoff_product (t : I → ℕ) : (∏ i, 2^(t i+2)) = 2^((∑ i, t i)+2*Fintype.card I) := by
  rw [prod_pow_eq_pow_sum]
  congr 1
  simp only [sum_add_distrib,sum_const,card_univ,nsmul_eq_mul,Nat.cast_id]
  omega

lemma kernel_volume_dyadic (t : I → ℕ) :
    4*(∏ i, kernelPower t*2^(t i+2)) ≤ 2^(frequencyMeanExponent t) := by
  rw [prod_mul_distrib,prod_const,card_univ,cutoff_product]
  calc
    _ ≤ 4*(2^(4+2*precisionMass t))^(Fintype.card I)*2^((∑ i,t i)+2*Fintype.card I) := by
      have hh := Nat.pow_le_pow_left (kernelPower_dyadic t) (Fintype.card I)
      simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right (2^((∑ i,t i)+2*Fintype.card I)) (Nat.mul_le_mul_left 4 hh)
    _ = _ := by
      rw [show 4=2^2 by norm_num,← pow_mul,← pow_add,← pow_add]
      congr 1
      unfold frequencyMeanExponent
      ring

lemma kernel_volume_budget (t : I → ℕ) :
    2*(∏ i, kernelPower t*2^(t i+2)) ≤ 4^(kernelPower t) := by
  have hs : frequencyMeanExponent t ≤ 2*kernelPower t := by
    let L := precisionMass t
    have hL : 0 < L := precisionMass_pos t
    have hm : Fintype.card I ≤ L := by dsimp only [L,precisionMass]; omega
    have ht : (∑ i,t i) ≤ L := by dsimp only [L,precisionMass]; omega
    have hml := Nat.mul_le_mul_left L hm
    have hsq : L ≤ L^2 := Nat.le_self_pow (by decide) L
    change (∑ i,t i)+6*Fintype.card I+2*L*Fintype.card I+2 ≤ 2*(16*L^2)
    nlinarith only [hml,hm,ht,hsq,hL]
  calc
    _ ≤ 4*(∏ i, kernelPower t*2^(t i+2)) := Nat.mul_le_mul_right _ (by decide)
    _ ≤ 2^(frequencyMeanExponent t) := kernel_volume_dyadic t
    _ ≤ 2^(2*kernelPower t) := Nat.pow_le_pow_right (by decide) hs
    _ = _ := pow_mul _ _ _

/-- Anisotropic avoidance with a polynomial-in-total-precision frequency
multiplier. In coordinate i the bound is 4*kernelPower(t)*2^(t_i). -/
theorem dyadic_anisotropic_avoidance [DecidableEq I]
    {X : Type*} [Fintype X] [Nonempty X]
    (t : I → ℕ) (v : X → I → ℂ) (hv : ∀ x i, ‖v x i‖ = 1)
    (havoid : ∀ x, ∃ i, (1/2 : ℝ)^(t i) ≤ ‖v x i-1‖) :
    ∃ h : I → ℤ, (∃ i, h i ≠ 0) ∧
      (∀ i, |h i| < (kernelPower t*2^(t i+2) : ℕ)) ∧
      (1/2 : ℝ)^(frequencyMeanExponent t) < ‖𝔼 x, ∏ i, (v x i)^(h i)‖ := by
  have hscale (i : I) : 4 ≤ ((2^(t i+2) : ℕ) : ℝ)*(1/2 : ℝ)^(t i) := by
    have he : ((2^(t i+2) : ℕ) : ℝ)*(1/2 : ℝ)^(t i) = 4 := by
      push_cast
      rw [pow_add,div_pow,one_pow]
      field_simp
      ring
    exact he.ge
  obtain ⟨h,hne,hb,hm⟩ := anisotropic_avoidance_frequency (kernelPower t) (kernelPower_pos t)
    (fun i ↦ 2^(t i+2)) (fun i ↦ Nat.two_pow_pos _) v hv (fun i ↦ (1/2 : ℝ)^(t i))
    (fun i ↦ pow_pos (by norm_num) _) hscale (kernel_volume_budget t) havoid
  refine ⟨h,hne,hb,lt_of_le_of_lt ?_ hm⟩
  rw [div_pow,one_pow]
  have hvol : 0 < ∏ i, kernelPower t*2^(t i+2) :=
    prod_pos (fun i _ ↦ Nat.mul_pos (kernelPower_pos t) (Nat.two_pow_pos _))
  apply one_div_le_one_div_of_le (mul_pos (by norm_num) (Nat.cast_pos.mpr hvol))
  exact_mod_cast kernel_volume_dyadic t

#print axioms dyadic_anisotropic_avoidance
end Erdos3AnisotropicAvoidanceParameters
