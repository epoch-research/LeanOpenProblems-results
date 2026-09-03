import Submission.FiniteFiberEnergy

/-! Finite tensor Fejér kernels with sufficient powers to detect simultaneous
avoidance. All expansions are finite; no Fourier convergence is required. -/
namespace Erdos3TensorFejerKernel
open Finset Erdos3QuadraticRecurrenceAverages Erdos3FiniteFourier
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 3000000

lemma complex_expect_pi_prod {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
    (f : I → A → ℂ) :
    (𝔼 a : I → A, ∏ i, f i (a i)) = ∏ i, 𝔼 a, f i a := by
  simp only [Fintype.expect_eq_sum_div_card,Fintype.card_pi,← Fintype.prod_sum,
    Nat.cast_prod,prod_div_distrib]

def coordinateSum (m K : ℕ) (a : Fin m → Fin K) : ℕ := ∑ j, (a j).val

def kernelAtom (m K : ℕ) (v : Fin m → ℂ) (a : Fin m → Fin m → Fin K) : ℂ :=
  ∏ j, (v j)^(coordinateSum m K (a j))

lemma coordinateSum_lt {m K : ℕ} (hm : 0 < m) (a : Fin m → Fin K) :
    coordinateSum m K a < m*K := by
  letI : NeZero m := ⟨by omega⟩
  have hh := sum_lt_sum_of_nonempty (s := univ) univ_nonempty (fun j _ ↦ (a j).isLt)
  simpa only [coordinateSum,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] using hh

lemma geometric_power_mean (m K : ℕ) (v : ℂ) :
    (𝔼 a : Fin m → Fin K, v^(coordinateSum m K a)) = (𝔼 j : Fin K, v^j.val)^m := by
  simp only [coordinateSum,← prod_pow_eq_pow_sum]
  calc
    _ = ∏ _j : Fin m, 𝔼 a : Fin K, v^a.val := by
      convert complex_expect_pi_prod (fun (_j : Fin m) (a : Fin K) ↦ v^a.val) using 1
    _ = _ := by simp only [prod_const,card_univ,Fintype.card_fin]

lemma kernel_mean (m K : ℕ) (v : Fin m → ℂ) :
    (𝔼 a, kernelAtom m K v a) = ∏ j, (𝔼 b : Fin K, (v j)^b.val)^m := by
  unfold kernelAtom
  calc
    _ = ∏ j : Fin m, 𝔼 a : Fin m → Fin K, (v j)^(coordinateSum m K a) := by
      convert complex_expect_pi_prod (fun (j : Fin m) (a : Fin m → Fin K) ↦ (v j)^(coordinateSum m K a)) using 1
    _ = _ := by simp only [geometric_power_mean]

lemma kernelAtom_norm (m K : ℕ) (v : Fin m → ℂ) (hv : ∀ j, ‖v j‖ = 1)
    (a : Fin m → Fin m → Fin K) : ‖kernelAtom m K v a‖ = 1 := by
  simp only [kernelAtom,norm_prod,norm_pow,hv,one_pow,prod_const_one]

lemma geometric_mean_le_one (K : ℕ) (hK : 0 < K) (v : ℂ) (hv : ‖v‖ = 1) :
    ‖𝔼 b : Fin K, v^b.val‖ ≤ 1 := by
  letI : NeZero K := ⟨by omega⟩
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  apply expect_le univ_nonempty
  intro b _
  simp only [norm_pow,hv,one_pow,le_refl]

/-- A single coordinate outside the epsilon-neighborhood forces a small tensor
kernel, with enough decay relative to the whole m-dimensional fiber space. -/
theorem kernel_avoidance_bound {m K : ℕ} (hm : 0 < m) (hK : 0 < K)
    (v : Fin m → ℂ) (hv : ∀ j, ‖v j‖ = 1) {ε : ℝ} (hε : 0 < ε)
    (hscale : 8*(m : ℝ) ≤ (K : ℝ)*ε^2)
    (havoid : ∃ j, ε ≤ ‖v j-1‖) :
    ‖𝔼 a, kernelAtom m K v a‖^2 ≤ 1/(2*((m : ℝ)*(K : ℝ))^m) := by
  letI : NeZero m := ⟨by omega⟩
  letI : NeZero K := ⟨by omega⟩
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  let g (j : Fin m) := ‖𝔼 b : Fin K, (v j)^b.val‖
  have hg0 (j : Fin m) : 0 ≤ g j := norm_nonneg _
  have hg1 (j : Fin m) : g j ≤ 1 := geometric_mean_le_one K hK (v j) (hv j)
  obtain ⟨j,hj⟩ := havoid
  have hgeo := geometric_mean_norm (v j) (hv j) K
  have hsmall : g j ≤ 2/((K : ℝ)*ε) := by
    have hh := (mul_le_mul_of_nonneg_left hj (hg0 j)).trans hgeo
    calc
      _ ≤ (2/(K : ℝ))/ε := (le_div_iff₀ hε).mpr hh
      _ = _ := by ring
  have hprod : (∏ i, (g i)^m) ≤ (g j)^m := by
    have hh : (∏ i ∈ univ.erase j, (g i)^m) ≤ 1 :=
      prod_le_one (fun i _ ↦ pow_nonneg (hg0 i) _) (fun i _ ↦ pow_le_one₀ (hg0 i) (hg1 i))
    calc
      _ = (∏ i ∈ univ.erase j, (g i)^m)*(g j)^m := (prod_erase_mul _ _ (mem_univ j)).symm
      _ ≤ 1*(g j)^m := mul_le_mul_of_nonneg_right hh (pow_nonneg (hg0 j) _)
      _ = _ := one_mul _
  have hnorm : ‖𝔼 a, kernelAtom m K v a‖ ≤ (g j)^m := by
    rw [kernel_mean,norm_prod]
    simpa only [norm_pow] using hprod
  have hsquare : (2/((K : ℝ)*ε))^2 ≤ 1/(2*(m : ℝ)*(K : ℝ)) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*(m : ℝ)*(K : ℝ))).mpr
    have he : (2/((K : ℝ)*ε))^2*(2*(m : ℝ)*(K : ℝ)) =
        8*(m : ℝ)/((K : ℝ)*ε^2) := by field_simp; ring
    rw [he]
    exact (div_le_one (by positivity)).mpr hscale
  have htwo : (2 : ℝ) ≤ 2^m := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hm
  calc
    _ ≤ ((g j)^m)^2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = ((g j)^2)^m := by rw [← pow_mul,← pow_mul,Nat.mul_comm m 2]
    _ ≤ ((2/((K : ℝ)*ε))^2)^m := pow_le_pow_left₀ (sq_nonneg _) (pow_le_pow_left₀ (hg0 j) hsmall 2) m
    _ ≤ (1/(2*(m : ℝ)*(K : ℝ)))^m := pow_le_pow_left₀ (sq_nonneg _) hsquare m
    _ = 1/((2 : ℝ)^m*((m : ℝ)*(K : ℝ))^m) := by rw [div_pow,one_pow,mul_pow,mul_pow,mul_pow]; ring
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_right htwo (by positivity))

#print axioms kernel_avoidance_bound
end Erdos3TensorFejerKernel
