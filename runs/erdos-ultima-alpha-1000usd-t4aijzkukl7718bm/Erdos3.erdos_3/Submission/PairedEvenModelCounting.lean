import Submission.QuadraticModelCounting
import Submission.FourierMultilinearTransfer

/-! Positivity for all even-length paired models. These model inequalities
are not a structural theorem for arbitrary progression-free sets. -/
namespace Erdos3PairedEvenModelCounting
open Finset Erdos3FiniteSampling Erdos3FourierMultilinearTransfer
open scoped BigOperators Classical
set_option maxHeartbeats 4000000

variable {G : Type*} [AddCommGroup G] [Fintype G]
variable {Y : Type*} [Fintype Y]

noncomputable def mixedConvolution (f : G → ℝ) (g : Y → ℝ) (T : Y → G) (w : G) : ℝ :=
  𝔼 y : Y, f (w+T y)*g y

noncomputable def mixedBalancedCount (f : G → ℝ) (g : Y → ℝ) (T : Y → G) : ℝ :=
  𝔼 x : G, 𝔼 y : Y, 𝔼 z : Y, f x*g y*g z*f (x-T y+T z)

lemma mixedConvolution_mean (f : G → ℝ) (g : Y → ℝ) (T : Y → G) :
    (𝔼 w, mixedConvolution f g T w) = (𝔼 x, f x)*(𝔼 y, g y) := by
  unfold mixedConvolution
  rw [expect_comm]
  have hs (y : Y) : (𝔼 w : G, f (w+T y)*g y) = (𝔼 x, f x)*g y := by
    rw [← expect_mul]
    congr 1
    exact Fintype.expect_equiv (Equiv.addRight (T y)) _ f (fun _ ↦ rfl)
  simp only [hs,← mul_expect]

lemma mixedBalancedCount_eq_square (f : G → ℝ) (g : Y → ℝ) (T : Y → G) :
    mixedBalancedCount f g T = 𝔼 w, (mixedConvolution f g T w)^2 := by
  symm
  unfold mixedConvolution mixedBalancedCount
  simp only [pow_two,Fintype.expect_mul_expect]
  rw [expect_comm]
  have hs (y : Y) :
      (𝔼 w : G, 𝔼 z : Y, (f (w+T y)*g y)*(f (w+T z)*g z)) =
      𝔼 x : G, 𝔼 z : Y, f x*g y*g z*f (x-T y+T z) := by
    apply (Fintype.expect_equiv (Equiv.subRight (T y)) _ _ ?_).symm
    intro x
    apply expect_congr rfl
    intro z _
    simp only [Equiv.subRight_apply,sub_add_cancel]
    ring
  simp only [hs]
  rw [expect_comm]

theorem mixedBalancedCount_lower (f : G → ℝ) (g : Y → ℝ) (T : Y → G) :
    ((𝔼 x, f x)*(𝔼 y, g y))^2 ≤ mixedBalancedCount f g T := by
  have hvar : 0 ≤ 𝔼 w : G, (mixedConvolution f g T w-𝔼 u, mixedConvolution f g T u)^2 :=
    expect_nonneg (fun _ _ ↦ sq_nonneg _)
  rw [expect_center_sq,mixedConvolution_mean,← mixedBalancedCount_eq_square] at hvar
  linarith

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma expect_pi_product (f : G → ℝ) :
    (𝔼 v : I → G, ∏ i, f (v i)) = (𝔼 x : G, f x)^(Fintype.card I) := by
  calc
    _ = ∏ _i : I, 𝔼 x : G, f x := by
      simp only [Fintype.expect_eq_sum_div_card,Fintype.card_pi,← Fintype.prod_sum,
        Nat.cast_prod,prod_div_distrib]
    _ = _ := by rw [prod_const,card_univ]

/-- T records the contribution of all but one coordinate to one side of a
paired relation. It need not be linear for the energy argument. -/
noncomputable def pairedModelCount (f : G → ℝ) (T : (I → G) → G) : ℝ :=
  mixedBalancedCount f (fun v ↦ ∏ i, f (v i)) T

theorem pairedModelCount_lower (f : G → ℝ) (T : (I → G) → G) :
    (𝔼 x : G, f x)^(2*(Fintype.card I+1)) ≤ pairedModelCount f T := by
  have h := mixedBalancedCount_lower f (fun v : I → G ↦ ∏ i, f (v i)) T
  rw [expect_pi_product] at h
  convert h using 1
  rw [pow_mul,show (𝔼 x : G, f x)*(𝔼 x : G, f x)^Fintype.card I =
      (𝔼 x : G, f x)^(Fintype.card I+1) by rw [pow_succ]; ring]
  ring

/-- An even collection of values, with two halves paired by T. -/
def pairedValues (T : (I → G) → G) (p : G × (I → G) × (I → G)) :
    Option I ⊕ Option I → G
  | .inl none => p.1
  | .inl (some i) => p.2.1 i
  | .inr none => p.1-T p.2.1+T p.2.2
  | .inr (some i) => p.2.2 i

lemma pairedValues_prod (f : G → ℝ) (T : (I → G) → G)
    (p : G × (I → G) × (I → G)) :
    (∏ i : Option I ⊕ Option I, f (pairedValues T p i)) =
      f p.1*(∏ i, f (p.2.1 i))*(∏ i, f (p.2.2 i))*f (p.1-T p.2.1+T p.2.2) := by
  rw [Fintype.prod_sum_type,Fintype.prod_option,Fintype.prod_option]
  dsimp only [pairedValues]
  ring

lemma pairedModelCount_eq (f : G → ℝ) (T : (I → G) → G) :
    pairedModelCount f T =
      𝔼 p : G × (I → G) × (I → G), ∏ i : Option I ⊕ Option I, f (pairedValues T p i) := by
  simp only [pairedValues_prod]
  unfold pairedModelCount mixedBalancedCount
  rw [show (𝔼 p : G × (I → G) × (I → G),
      f p.1*(∏ i, f (p.2.1 i))*(∏ i, f (p.2.2 i))*f (p.1-T p.2.1+T p.2.2)) =
      𝔼 x : G, 𝔼 uv : (I → G) × (I → G),
      f x*(∏ i, f (uv.1 i))*(∏ i, f (uv.2 i))*f (x-T uv.1+T uv.2)
    from expect_product _ _ _]
  apply expect_congr rfl
  intro x _
  symm
  exact expect_product _ _ _

/-- All even-length paired-model lower bounds transfer under the explicit
multilinear character discrepancy hypothesis. -/
theorem paired_model_transfer_lower {X : Type*} [Fintype X]
    (f : G → ℝ) (T : (I → G) → G) (v : X → Option I ⊕ Option I → G)
    {ε : ℝ}
    (hdisc : ∀ χ : Option I ⊕ Option I → AddChar G ℂ,
      ‖(𝔼 x : X, ∏ i, χ i (v x i))-
        (𝔼 p : G × (I → G) × (I → G), ∏ i, χ i (pairedValues T p i))‖ ≤ ε) :
    (𝔼 y : G, f y)^(2*(Fintype.card I+1))-
      ε*fourierMass (fun y ↦ (f y : ℂ))^(2*(Fintype.card I+1)) ≤
      𝔼 x : X, ∏ i, f (v x i) := by
  have ht := multilinear_transfer_real (fun _ : Option I ⊕ Option I ↦ f) v (pairedValues T) hdisc
  rw [← pairedModelCount_eq] at ht
  have hcard : Fintype.card (Option I ⊕ Option I) = 2*(Fintype.card I+1) := by simp; omega
  simp only [prod_const,card_univ,hcard] at ht
  have hl := pairedModelCount_lower f T
  have he := (abs_le.mp ht).1
  linarith

#print axioms pairedModelCount_lower
#print axioms paired_model_transfer_lower
end Erdos3PairedEvenModelCounting
