import Submission.SimultaneousAvoidanceFrequency

/-! Finite anisotropic Fejér kernels. The power parameter is independent of
the dimension, allowing coordinate cutoffs linear in inverse accuracy. -/
namespace Erdos3AnisotropicFejerKernel
open Finset Erdos3TensorFejerKernel Erdos3FiniteFiberEnergy
  Erdos3SimultaneousAvoidanceFrequency Erdos3QuadraticRecurrenceAverages
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 3000000

lemma complex_expect_dpi_prod {I : Type*} [Fintype I] [DecidableEq I]
    {A : I → Type*} [∀ i, Fintype (A i)] (f : ∀ i, A i → ℂ) :
    (𝔼 a : ∀ i, A i, ∏ i, f i (a i)) = ∏ i, 𝔼 a, f i a := by
  simp only [Fintype.expect_eq_sum_div_card,Fintype.card_pi,← Fintype.prod_sum,
    Nat.cast_prod,prod_div_distrib]

noncomputable def anisotropicAtom {I : Type*} [Fintype I] (r : ℕ) (K : I → ℕ)
    (v : I → ℂ) (a : ∀ i, Fin r → Fin (K i)) : ℂ :=
  ∏ i, (v i)^(coordinateSum r (K i) (a i))

lemma anisotropicAtom_mean {I : Type*} [Fintype I] [DecidableEq I]
    (r : ℕ) (K : I → ℕ) (v : I → ℂ) :
    (𝔼 a, anisotropicAtom r K v a) = ∏ i, (𝔼 b : Fin (K i), (v i)^b.val)^r := by
  unfold anisotropicAtom
  calc
    _ = ∏ i, 𝔼 a : Fin r → Fin (K i), (v i)^(coordinateSum r (K i) a) := by
      convert complex_expect_dpi_prod (fun (i : I) (a : Fin r → Fin (K i)) ↦
        (v i)^(coordinateSum r (K i) a)) using 1
    _ = _ := by simp only [geometric_power_mean]

lemma anisotropicAtom_norm {I : Type*} [Fintype I]
    (r : ℕ) (K : I → ℕ) (v : I → ℂ) (hv : ∀ i, ‖v i‖ = 1)
    (a : ∀ i, Fin r → Fin (K i)) : ‖anisotropicAtom r K v a‖ = 1 := by
  simp only [anisotropicAtom,norm_prod,norm_pow,hv,one_pow,prod_const_one]

lemma anisotropic_kernel_small {I : Type*} [Fintype I] [DecidableEq I]
    (r : ℕ) (K : I → ℕ) (hK : ∀ i, 0 < K i)
    (v : I → ℂ) (hv : ∀ i, ‖v i‖ = 1) (ε : I → ℝ) (hε : ∀ i, 0 < ε i)
    (hscale : ∀ i, 4 ≤ (K i : ℝ)*ε i)
    (havoid : ∃ i, ε i ≤ ‖v i-1‖) :
    ‖𝔼 a, anisotropicAtom r K v a‖^2 ≤ (1/4 : ℝ)^r := by
  let g (i : I) := ‖𝔼 b : Fin (K i), (v i)^b.val‖
  have hg0 (i : I) : 0 ≤ g i := norm_nonneg _
  have hg1 (i : I) : g i ≤ 1 := geometric_mean_le_one (K i) (hK i) (v i) (hv i)
  obtain ⟨i,hi⟩ := havoid
  have hgeo := geometric_mean_norm (v i) (hv i) (K i)
  have hsmall : g i ≤ 1/2 := by
    have hh := (mul_le_mul_of_nonneg_left hi (hg0 i)).trans hgeo
    have hdiv : g i ≤ (2/(K i : ℝ))/ε i := (le_div_iff₀ (hε i)).mpr hh
    have hKi : (0 : ℝ) < K i := by exact_mod_cast hK i
    have he : (2/(K i : ℝ))/ε i = 2/((K i : ℝ)*ε i) := by ring
    rw [he] at hdiv
    apply hdiv.trans
    apply (div_le_iff₀ (mul_pos hKi (hε i))).mpr
    linarith only [hscale i]
  have hprod : (∏ j, (g j)^r) ≤ (g i)^r := by
    have hh : (∏ j ∈ univ.erase i, (g j)^r) ≤ 1 :=
      prod_le_one (fun j _ ↦ pow_nonneg (hg0 j) _) (fun j _ ↦ pow_le_one₀ (hg0 j) (hg1 j))
    calc
      _ = (∏ j ∈ univ.erase i, (g j)^r)*(g i)^r := (prod_erase_mul _ _ (mem_univ i)).symm
      _ ≤ 1*(g i)^r := mul_le_mul_of_nonneg_right hh (pow_nonneg (hg0 i) _)
      _ = _ := one_mul _
  have hnorm : ‖𝔼 a, anisotropicAtom r K v a‖ ≤ (g i)^r := by
    rw [anisotropicAtom_mean,norm_prod]
    simpa only [norm_pow] using hprod
  calc
    _ ≤ ((g i)^r)^2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ ((1/2 : ℝ)^r)^2 := pow_le_pow_left₀ (pow_nonneg (hg0 i) _)
      (pow_le_pow_left₀ (hg0 i) hsmall r) 2
    _ = _ := by rw [← pow_mul,Nat.mul_comm r 2,pow_mul]; norm_num

/-- A simultaneous avoidance certificate with anisotropic cutoffs. The volume
condition trades an independently chosen power r for cutoffs K_i≈1/epsilon_i. -/
theorem anisotropic_avoidance_frequency {I X : Type*}
    [Fintype I] [DecidableEq I] [Fintype X] [Nonempty X]
    (r : ℕ) (hr : 0 < r) (K : I → ℕ) (hK : ∀ i, 0 < K i)
    (v : X → I → ℂ) (hv : ∀ x i, ‖v x i‖ = 1)
    (ε : I → ℝ) (hε : ∀ i, 0 < ε i)
    (hscale : ∀ i, 4 ≤ (K i : ℝ)*ε i)
    (hvolume : 2*(∏ i, r*K i) ≤ 4^r)
    (havoid : ∀ x, ∃ i, ε i ≤ ‖v x i-1‖) :
    ∃ h : I → ℤ, (∃ i, h i ≠ 0) ∧ (∀ i, |h i| < (r*K i : ℕ)) ∧
      1/(4*((∏ i, r*K i : ℕ) : ℝ)) < ‖𝔼 x, ∏ i, (v x i)^(h i)‖ := by
  letI : NeZero r := ⟨by omega⟩
  letI (i : I) : NeZero (K i) := ⟨by have hh := hK i; omega⟩
  let A := ∀ i, Fin r → Fin (K i)
  let J := ∀ i, Fin (r*K i)
  let φ : A → J := fun a i ↦ ⟨coordinateSum r (K i) (a i),coordinateSum_lt hr _⟩
  let f : X → A → ℂ := fun x a ↦ anisotropicAtom r K (v x) a
  have hcard : Fintype.card J = ∏ i, r*K i := by simp only [J,Fintype.card_pi,Fintype.card_fin]
  have hf : ∀ x a, ‖f x a‖ = 1 := fun x a ↦ anisotropicAtom_norm r K (v x) (hv x) a
  have hsame : ∀ x a b, φ a = φ b → f x a = f x b := by
    intro x a b hab
    apply prod_congr rfl
    intro i _
    have hh := congrArg (fun c : J ↦ (c i).val) hab
    change coordinateSum r (K i) (a i) = coordinateSum r (K i) (b i) at hh
    rw [hh]
  have hupper : (𝔼 x, ‖𝔼 a, f x a‖^2) ≤ 1/(2*(Fintype.card J : ℝ)) := by
    apply expect_le univ_nonempty
    intro x _
    apply (anisotropic_kernel_small r K hK (v x) (hv x) ε hε hscale (havoid x)).trans
    rw [div_pow,one_pow]
    apply one_div_le_one_div_of_le (by positivity)
    rw [hcard]
    exact_mod_cast hvolume
  obtain ⟨a,b,hab,hmean⟩ := low_energy_off_fiber_correlation φ f hf hsame hupper
  let h : I → ℤ := fun i ↦ (coordinateSum r (K i) (a i) : ℤ)-(coordinateSum r (K i) (b i) : ℤ)
  have hne : ∃ i, h i ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hab
    funext i
    apply Fin.ext
    exact_mod_cast sub_eq_zero.mp (hn i)
  have hbound (i : I) : |h i| < (r*K i : ℕ) := by
    have ha := coordinateSum_lt hr (a i)
    have hb := coordinateSum_lt hr (b i)
    apply abs_lt.mpr
    dsimp only [h]
    constructor <;> omega
  have hpair (x : X) : f x a*conj (f x b) = ∏ i, (v x i)^(h i) := by
    dsimp only [f,anisotropicAtom]
    rw [map_prod,← prod_mul_distrib]
    apply prod_congr rfl
    intro i _
    exact unit_pair_zpow (v x i) (hv x i) _ _
  exact ⟨h,hne,hbound,by simpa only [hpair,hcard] using hmean⟩

#print axioms anisotropic_avoidance_frequency
end Erdos3AnisotropicFejerKernel
