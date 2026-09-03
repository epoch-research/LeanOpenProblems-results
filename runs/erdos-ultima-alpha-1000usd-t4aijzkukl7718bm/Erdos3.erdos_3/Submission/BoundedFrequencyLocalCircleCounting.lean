import Submission.LocalFrequencyModel

/-! Actual local circle-factor counting using only bounded integer-frequency
combinations of the original phases. Spectral smoothing removes ambient grid
size from the Fourier-mass cost; rounding contributes only a vanishing error. -/
namespace Erdos3BoundedFrequencyLocalCircleCounting
open Finset Erdos3LocalFrequencyModel Erdos3BoundedFrequencyPhaseApproximation
  Erdos3FiniteFrequencyCoordinates Erdos3BoundedFrequencyObservable
  Erdos3LocalCircleFactorCounting Erdos3FiniteCircleGrid Erdos3StableMaskedUniformity
  Erdos3FiniteUniformity Erdos3CorrelationSifting Erdos3RelativeStableBohr Erdos3FiniteBohr
  Erdos3StableWindowCounting Erdos3LocalQuadraticInverse Erdos3FourierMultilinearTransfer
open scoped BigOperators Classical
set_option maxHeartbeats 8000000
variable {F I : Type*} [Field F] [Fintype F] [Fintype I] [DecidableEq I]
  {N K : ℕ} [NeZero N]

/-- Restricted rounded-character version, before transferring back to exact
integer combinations of the original locally quadratic phases. -/
theorem cutoff_local_circle_count (hKN : K+1 ≤ N) (B : Finset F) (hB : B.Nonempty)
    (hv : Function.Injective (fun j : Fin 4 ↦ (j.val : F)))
    (C : Finset (AddChar F ℂ)) {r : ℝ} (hr : 0 < r)
    {z : ℕ} (hz : 0 < z) (hstable : RelativeStable C z r)
    (hs : ∀ b c : B, ∀ j : Fin 4,
      (j.val : F)*((c : F)-b) ∈ bohr C (relativeWidth C z r))
    (Q : I → F → ℂ) (hQ : ∀ i x, ‖Q i x‖ = 1)
    (hpoly : ∀ i, IsLocallyQuadratic (bohr C r : Set F) (Q i))
    (H : (I → ℂ) → ℝ) (hH : ∀ v, 0 ≤ H v ∧ H v ≤ 1)
    {L : NNReal} (hLip : LipschitzWith L H) {θ σ : ℝ} (hθ : 0 ≤ θ) (hσ : 0 ≤ σ)
    (hscale : 2/(K+1 : ℝ) ≤ σ^2)
    (hU : ∀ χ : AddChar (I → ZMod N) ℂ, HasFrequencyBound (4*K) χ → χ ≠ 1 →
      uniformityPower 1 (mask (bohr C r) (fun x ↦ χ (roundedFactor Q x))) ≤ θ^4) :
    (𝔼 y : I → ZMod N, H (gridVector y))^4-
      (θ/(density (bohr C r)*density B)+3/(z : ℝ))*(K+1 : ℝ)^(4*Fintype.card I)-
      4/(z : ℝ)-6*(L : ℝ)*(Fintype.card I : ℝ)*σ-96*(L : ℝ)/(N : ℝ) ≤
      windowPatternAverage (bohr C r)
        (fun (p : B × B) (j : Fin 4) ↦ (j.val : F)*((p.2 : F)-p.1))
        (fun t ↦ H (fun i ↦ Q i t)) := by
  letI : Nonempty B := hB.to_subtype
  let q : F → I → ZMod N := roundedFactor Q
  let Φ : (I → ZMod N) → ℝ := cutoffObservable K H
  let s (p : B × B) (j : Fin 4) : F := (j.val : F)*((p.2 : F)-p.1)
  have hΦ (y : I → ZMod N) : 0 ≤ Φ y ∧ Φ y ≤ 1 := cutoffObservable_bounds K H hH y
  have hdef (p : B × B) (t : bohr C r)
      (hin : ∀ j : Fin 4, (t : F)+s p j ∈ bohr C r) :
      |Φ (q ((t : F)+s p 3))-
        Φ (q ((t : F)+s p 0)-3 • q ((t : F)+s p 1)+3 • q ((t : F)+s p 2))| ≤
      2*((L : ℝ)*(Fintype.card I : ℝ)*σ)+(L : ℝ)*(64/(N : ℝ)) := by
    let v (j : Fin 4) (i : I) := Q i ((t : F)+s p j)
    have hrel (i : I) : v 3 i = quadraticWord (v 0 i) (v 1 i) (v 2 i) := by
      have hh := local_quadratic_word (Q i) (hQ i) (hpoly i) (t : F) ((p.2 : F)-p.1)
        (fun j ↦ by simpa only [nsmul_eq_mul] using hin j)
      simpa only [v,s,Fin.val_zero,Fin.val_one,Fin.val_two,Nat.cast_zero,Nat.cast_one,
        Nat.cast_ofNat,zero_mul,add_zero,one_mul,nsmul_eq_mul] using hh
    exact cutoffObservable_quadratic_defect hKN H hLip hσ hscale v (fun j i ↦ hQ i _) hrel
  have hd : ∀ χ₀ χ₁ χ₂ : AddChar (I → ZMod N) ℂ,
      HasFrequencyBound (4*K) χ₀ → HasFrequencyBound (4*K) χ₁ → HasFrequencyBound (4*K) χ₂ →
      ‖(𝔼 p : B × B, 𝔼 t : bohr C r,
        χ₀ (q ((t : F)+s p 0))*χ₁ (q ((t : F)+s p 1))*χ₂ (q ((t : F)+s p 2)))-
        (𝔼 y : (I → ZMod N) × (I → ZMod N) × (I → ZMod N),
          χ₀ y.1*χ₁ y.2.1*χ₂ y.2.2)‖ ≤
        θ/(density (bohr C r)*density B)+3/(z : ℝ) := by
    intro χ₀ χ₁ χ₂ hχ₀ hχ₁ hχ₂
    have h := local_triple_discrepancy_frequency B hB (fun j : Fin 3 ↦ (j.val : F))
      (hv.comp (Fin.castSucc_injective 3)) (by simp) C hr hz hstable
      (fun b c j ↦ hs b c j.castSucc) (4*K) q hθ hU χ₀ χ₁ χ₂ hχ₀ hχ₁ hχ₂
    have he := expect_product (univ : Finset B) (univ : Finset B)
      (fun p : B × B ↦ 𝔼 t : bohr C r,
        χ₀ (q ((t : F)+s p 0))*χ₁ (q ((t : F)+s p 1))*χ₂ (q ((t : F)+s p 2)))
    simp only [univ_product_univ] at he
    rw [he]
    exact h
  have hε : 0 ≤ θ/(density (bohr C r)*density B)+3/(z : ℝ) :=
    add_nonneg (div_nonneg hθ (mul_nonneg (density_nonneg _) (density_nonneg _))) (by positivity)
  have hcount := local_frequency_model_lower_of_defect C hr hz hstable s
    (fun p j ↦ hs p.1 p.2 j) K q Φ hΦ (cutoffObservable_hat_support K H)
    (by positivity) hdef hε hd
  have herr := window_sup_counting_bound (bohr C r) ⟨0,bohr_zero C hr.le⟩ s
    (fun t ↦ Φ (q t)) (fun t ↦ H (fun i ↦ Q i t))
    (fun t ↦ hΦ (q t)) (fun t ↦ hH _)
    (fun t ↦ cutoffObservable_rounding_error hKN H hLip hσ hscale
      (fun i ↦ Q i t) (fun i ↦ hQ i t))
  have hm := mul_le_mul_of_nonneg_left (cutoffObservable_fourierMass hKN H hH) hε
  have hmean : (𝔼 y : I → ZMod N, Φ y) = 𝔼 y : I → ZMod N, H (gridVector y) :=
    cutoffObservable_mean K H
  rw [hmean] at hcount
  simp only [Fintype.card_fin,Nat.cast_ofNat] at herr
  have he : (2*((L : ℝ)*(Fintype.card I : ℝ)*σ)+(L : ℝ)*(64/(N : ℝ)))+
      4*((L : ℝ)*(Fintype.card I : ℝ)*σ+(L : ℝ)*(8/(N : ℝ))) =
      6*(L : ℝ)*(Fintype.card I : ℝ)*σ+96*(L : ℝ)/(N : ℝ) := by ring
  change _ ≤ windowPatternAverage (bohr C r) s (fun t ↦ H (fun i ↦ Q i t))
  change _ ≤ _ at hm
  linarith [(abs_le.mp herr).2]

/-- Distribution can be tested on exact locally quadratic integer combinations
of the original phases. Only nonzero vectors with |k_i| <=4K are required. -/
theorem local_circle_count_from_exact_phases (hKN : K+1 ≤ N) (B : Finset F) (hB : B.Nonempty)
    (hv : Function.Injective (fun j : Fin 4 ↦ (j.val : F)))
    (C : Finset (AddChar F ℂ)) {r : ℝ} (hr : 0 < r)
    {z : ℕ} (hz : 0 < z) (hstable : RelativeStable C z r)
    (hs : ∀ b c : B, ∀ j : Fin 4,
      (j.val : F)*((c : F)-b) ∈ bohr C (relativeWidth C z r))
    (Q : I → F → ℂ) (hQ : ∀ i x, ‖Q i x‖ = 1)
    (hpoly : ∀ i, IsLocallyQuadratic (bohr C r : Set F) (Q i))
    (H : (I → ℂ) → ℝ) (hH : ∀ v, 0 ≤ H v ∧ H v ≤ 1)
    {L : NNReal} (hLip : LipschitzWith L H) {θ σ : ℝ} (hθ : 0 ≤ θ) (hσ : 0 ≤ σ)
    (hscale : 2/(K+1 : ℝ) ≤ σ^2)
    (hround : 32*density (bohr C r)*(Fintype.card I : ℝ)*(4*K : ℕ)/(N : ℝ) ≤ θ^4/2)
    (hU : ∀ k : I → ℤ, (∀ i, |k i| ≤ (4*K : ℕ)) → (∃ i, k i ≠ 0) →
      uniformityPower 1 (mask (bohr C r) (fun x ↦ integerPhase k (fun i ↦ Q i x))) ≤ θ^4/2) :
    (𝔼 y : I → ZMod N, H (gridVector y))^4-
      (θ/(density (bohr C r)*density B)+3/(z : ℝ))*(K+1 : ℝ)^(4*Fintype.card I)-
      4/(z : ℝ)-6*(L : ℝ)*(Fintype.card I : ℝ)*σ-96*(L : ℝ)/(N : ℝ) ≤
      windowPatternAverage (bohr C r)
        (fun (p : B × B) (j : Fin 4) ↦ (j.val : F)*((p.2 : F)-p.1))
        (fun t ↦ H (fun i ↦ Q i t)) := by
  apply cutoff_local_circle_count hKN B hB hv C hr hz hstable hs Q hQ hpoly H hH hLip hθ hσ hscale
  intro χ hfreq hχ
  obtain ⟨k,hk,rfl⟩ := hfreq
  have hkne : ∃ i, k i ≠ 0 := by
    by_contra! hn
    apply hχ
    ext x
    simp only [integerCharacter_apply,hn,zpow_zero,prod_const_one,AddChar.one_apply]
  have hp := (abs_le.mp (rounded_integer_U2_error (N := N) (bohr C r) Q hQ k hk)).2
  have hu := hU k hk hkne
  change uniformityPower 1
    (mask (bohr C r) (fun x ↦ integerCharacter k (fun i ↦ roundPhase N (Q i x)))) ≤ _
  linarith

#print axioms cutoff_local_circle_count
#print axioms local_circle_count_from_exact_phases
end Erdos3BoundedFrequencyLocalCircleCounting
