import Submission.BoundedFrequencyObservable

/-! Only Fourier tests with nonzero coefficients matter in multilinear model
transfer. Bounded-frequency observables therefore require bounded-frequency
character discrepancy, not uniformity of every character of the grid. -/
namespace Erdos3SparseFourierModelTransfer
open Finset Erdos3FourierMultilinearTransfer Erdos3FiniteFourier
  Erdos3QuadraticModelTransfer Erdos3QuadraticModelCounting
  Erdos3FiniteFrequencyCoordinates Erdos3BoundedFrequencyObservable
open scoped BigOperators Classical
set_option maxHeartbeats 6000000

variable {G J X Y : Type*} [AddCommGroup G] [Fintype G]
  [Fintype J] [Fintype X] [Fintype Y]

theorem sparse_multilinear_transfer (f : J → G → ℂ) (v : X → J → G) (w : Y → J → G)
    {ε : ℝ}
    (hdisc : ∀ χ : J → AddChar G ℂ, (∀ i, hat (f i) (χ i) ≠ 0) →
      ‖(𝔼 x : X, ∏ i, χ i (v x i))-(𝔼 y : Y, ∏ i, χ i (w y i))‖ ≤ ε) :
    ‖(𝔼 x : X, ∏ i, f i (v x i))-(𝔼 y : Y, ∏ i, f i (w y i))‖ ≤
      ε*∏ i, fourierMass (f i) := by
  rw [multilinear_expansion,multilinear_expansion,← sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    _ ≤ ∑ χ : J → AddChar G ℂ,
        ‖(∏ i, hat (f i) (χ i))*
          ((𝔼 x : X, ∏ i, χ i (v x i))-(𝔼 y : Y, ∏ i, χ i (w y i)))‖ := norm_sum_le _ _
    _ ≤ ∑ χ : J → AddChar G ℂ, (∏ i, ‖hat (f i) (χ i)‖)*ε := by
      apply sum_le_sum
      intro χ _
      by_cases hz : (∏ i, hat (f i) (χ i)) = 0
      · have hzn : (∏ i, ‖hat (f i) (χ i)‖) = 0 := by rw [← norm_prod,hz,norm_zero]
        simp only [hz,hzn,zero_mul,norm_zero,le_refl]
      · rw [norm_mul,norm_prod]
        apply mul_le_mul_of_nonneg_left (hdisc χ ?_) (prod_nonneg (fun _ _ ↦ norm_nonneg _))
        intro i hi
        exact hz (prod_eq_zero (mem_univ i) hi)
    _ = _ := by
      rw [← sum_mul,← Fintype.prod_sum (fun i (χ : AddChar G ℂ) ↦ ‖hat (f i) χ‖)]
      exact mul_comm _ _

lemma sparse_multilinear_transfer_real (f : J → G → ℝ) (v : X → J → G) (w : Y → J → G)
    {ε : ℝ}
    (hdisc : ∀ χ : J → AddChar G ℂ, (∀ i, hat (fun x ↦ (f i x : ℂ)) (χ i) ≠ 0) →
      ‖(𝔼 x : X, ∏ i, χ i (v x i))-(𝔼 y : Y, ∏ i, χ i (w y i))‖ ≤ ε) :
    |(𝔼 x : X, ∏ i, f i (v x i))-(𝔼 y : Y, ∏ i, f i (w y i))| ≤
      ε*∏ i, fourierMass (fun x ↦ (f i x : ℂ)) := by
  have h := sparse_multilinear_transfer (fun i x ↦ (f i x : ℂ)) v w hdisc
  simpa only [← Complex.ofReal_prod,← Complex.ofReal_expect,← Complex.ofReal_sub,
    Complex.norm_real,Real.norm_eq_abs] using h

/-- The transformed triple characters are tested only when the original four
Fourier coefficients are nonzero. -/
theorem sparse_quadratic_model_lower (f : G → ℝ) (a b c d : X → G)
    (hrel : ∀ x, d x = a x-3 • b x+3 • c x) {ε : ℝ}
    (hdisc : ∀ χ : Fin 4 → AddChar G ℂ,
      (∀ i, hat (fun x ↦ (f x : ℂ)) (χ i) ≠ 0) →
      ‖(𝔼 x : X, (χ 0*χ 3) (a x)*(χ 1/(χ 3)^3) (b x)*(χ 2*(χ 3)^3) (c x))-
        (𝔼 p : G × G × G, (χ 0*χ 3) p.1*(χ 1/(χ 3)^3) p.2.1*(χ 2*(χ 3)^3) p.2.2)‖ ≤ ε) :
    (𝔼 y : G, f y)^4-ε*fourierMass (fun y ↦ (f y : ℂ))^4 ≤
      𝔼 x : X, f (a x)*f (b x)*f (c x)*f (d x) := by
  let v : X → Fin 4 → G := fun x ↦ ![a x,b x,c x,d x]
  let w : G × G × G → Fin 4 → G := fun p ↦ ![p.1,p.2.1,p.2.2,p.1-3 • p.2.1+3 • p.2.2]
  have hd (χ : Fin 4 → AddChar G ℂ) (hχ : ∀ i, hat (fun x ↦ (f x : ℂ)) (χ i) ≠ 0) :
      ‖(𝔼 x : X, ∏ i, χ i (v x i))-(𝔼 p : G × G × G, ∏ i, χ i (w p i))‖ ≤ ε := by
    have hv (x : X) : (∏ i : Fin 4, χ i (v x i)) =
        (χ 0*χ 3) (a x)*(χ 1/(χ 3)^3) (b x)*(χ 2*(χ 3)^3) (c x) := by
      rw [Fin.prod_univ_four]
      change χ 0 (a x)*χ 1 (b x)*χ 2 (c x)*χ 3 (d x) = _
      rw [hrel]
      exact four_characters_relation χ _ _ _
    have hw (p : G × G × G) : (∏ i : Fin 4, χ i (w p i)) =
        (χ 0*χ 3) p.1*(χ 1/(χ 3)^3) p.2.1*(χ 2*(χ 3)^3) p.2.2 := by
      rw [Fin.prod_univ_four]
      exact four_characters_relation χ _ _ _
    simp only [hv,hw]
    exact hdisc χ hχ
  have h := sparse_multilinear_transfer_real (J := Fin 4) (fun _ ↦ f) v w hd
  have hw : (𝔼 p : G × G × G, ∏ i : Fin 4, f (w p i)) = quadraticModelCount f := by
    simp only [Fin.prod_univ_four,w,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,expect_triple]
    exact (quadraticModelCount_eq_balanced f).symm
  rw [hw] at h
  have h' : |(𝔼 x : X, f (a x)*f (b x)*f (c x)*f (d x))-quadraticModelCount f| ≤
      ε*fourierMass (fun y ↦ (f y : ℂ))^4 := by
    simpa only [Fin.prod_univ_four,v,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,prod_const,card_univ,Fintype.card_fin] using h
  have hl := quadraticModelCount_lower f
  linarith [(abs_le.mp h').1]

variable {I : Type*} [Fintype I] [DecidableEq I] {N : ℕ} [NeZero N]

lemma frequency_bound_mono {R T : ℕ} (hRT : R ≤ T) {χ : AddChar (I → ZMod N) ℂ}
    (hχ : HasFrequencyBound R χ) : HasFrequencyBound T χ := by
  obtain ⟨k,hk,rfl⟩ := hχ
  exact ⟨k,fun i ↦ (hk i).trans (by exact_mod_cast hRT),rfl⟩

theorem bounded_frequency_model_lower (R : ℕ) (f : (I → ZMod N) → ℝ)
    (hs : ∀ χ, ¬ HasFrequencyBound R χ → hat (fun y ↦ (f y : ℂ)) χ = 0)
    (a b c d : X → I → ZMod N)
    (hrel : ∀ x, d x = a x-3 • b x+3 • c x) {ε : ℝ}
    (hdisc : ∀ χ₀ χ₁ χ₂ : AddChar (I → ZMod N) ℂ,
      HasFrequencyBound (4*R) χ₀ → HasFrequencyBound (4*R) χ₁ → HasFrequencyBound (4*R) χ₂ →
      ‖(𝔼 x : X, χ₀ (a x)*χ₁ (b x)*χ₂ (c x))-
        (𝔼 p : (I → ZMod N) × (I → ZMod N) × (I → ZMod N), χ₀ p.1*χ₁ p.2.1*χ₂ p.2.2)‖ ≤ ε) :
    (𝔼 y : I → ZMod N, f y)^4-ε*fourierMass (fun y ↦ (f y : ℂ))^4 ≤
      𝔼 x : X, f (a x)*f (b x)*f (c x)*f (d x) := by
  apply sparse_quadratic_model_lower f a b c d hrel
  intro χ hχ
  have hf (i : Fin 4) : HasFrequencyBound R (χ i) := by
    by_contra hn
    exact hχ i (hs (χ i) hn)
  apply hdisc
  · exact frequency_bound_mono (by omega) ((hf 0).mul (hf 3))
  · exact frequency_bound_mono (by omega) ((hf 1).div ((hf 3).pow 3))
  · exact frequency_bound_mono (by omega) ((hf 2).mul ((hf 3).pow 3))

#print axioms sparse_multilinear_transfer
#print axioms bounded_frequency_model_lower
end Erdos3SparseFourierModelTransfer
