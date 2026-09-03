import Submission.ApproximateLocalQuadraticCounting

/-! Counting for the actual circle-valued local factors, via finite grid
quantization with controlled observable defect. The sole distribution input
is the explicitly stated masked U2 bound for the rounded factor characters.
No such bound is inferred from local polynomiality alone. -/
namespace Erdos3LocalCircleFactorCounting
open Finset Erdos3ApproximateLocalQuadraticCounting Erdos3LocalQuadraticDistribution
  Erdos3FiniteCircleGrid Erdos3StableMaskedUniformity Erdos3FiniteUniformity
  Erdos3CorrelationSifting Erdos3RelativeStableBohr Erdos3FiniteBohr
  Erdos3StableWindowCounting Erdos3RobustTopDegreeCounting Erdos3LocalQuadraticInverse
open scoped BigOperators Classical
set_option maxHeartbeats 7000000

variable {G I D : Type*} [AddCommGroup G] [Fintype G] [Fintype I]
  [Fintype D] [Nonempty D]

lemma window_sup_counting_bound (W : Finset G) (hW : W.Nonempty) (s : D → I → G)
    (f g : G → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    {κ : ℝ} (herr : ∀ x, |f x-g x| ≤ κ) :
    |windowPatternAverage W s f-windowPatternAverage W s g| ≤ (Fintype.card I : ℝ)*κ := by
  letI : Nonempty W := hW.to_subtype
  unfold windowPatternAverage
  rw [← expect_sub_distrib]
  apply (Finset.abs_expect_le _ _).trans
  apply expect_le univ_nonempty
  intro d _
  rw [← expect_sub_distrib]
  apply (Finset.abs_expect_le _ _).trans
  apply expect_le univ_nonempty
  intro t _
  calc
    _ ≤ ∑ i : I, |f (t+s d i)-g (t+s d i)| := by
      apply abs_prod_sub_prod_le
      · intro i _; rw [abs_of_nonneg (hf _).1]; exact (hf _).2
      · intro i _; rw [abs_of_nonneg (hg _).1]; exact (hg _).2
    _ ≤ ∑ _i : I, κ := sum_le_sum (fun i _ ↦ herr _)
    _ = _ := by simp

variable {F : Type*} [Field F] [Fintype F] {N : ℕ} [NeZero N]

noncomputable def roundedFactor (Q : I → F → ℂ) (x : F) : I → ZMod N :=
  fun i ↦ roundPhase N (Q i x)

/-- Local circle-valued factors have an actual count lower bound under masked
character-U2 control. The extra grid loss is 96L/N, including the approximate
quadratic identity and the return to the original, unrounded observable. -/
theorem local_circle_count (B : Finset F) (hB : B.Nonempty)
    (hv : Function.Injective (fun j : Fin 4 ↦ (j.val : F)))
    (C : Finset (AddChar F ℂ)) {r : ℝ} (hr : 0 < r)
    {z : ℕ} (hz : 0 < z) (hstable : RelativeStable C z r)
    (hs : ∀ b c : B, ∀ j : Fin 4,
      (j.val : F)*((c : F)-b) ∈ bohr C (relativeWidth C z r))
    (Q : I → F → ℂ) (hQ : ∀ i x, ‖Q i x‖ = 1)
    (hpoly : ∀ i, IsLocallyQuadratic (bohr C r : Set F) (Q i))
    (H : (I → ℂ) → ℝ) (hH : ∀ v, 0 ≤ H v ∧ H v ≤ 1)
    {L : NNReal} (hLip : LipschitzWith L H) {η : ℝ} (hη : 0 ≤ η)
    (hU : ∀ χ : AddChar (I → ZMod N) ℂ, χ ≠ 1 →
      uniformityPower 1 (mask (bohr C r) (fun x ↦ χ (roundedFactor Q x))) ≤ η^4) :
    (𝔼 y : I → ZMod N, H (gridVector y))^4-
      (η/(density (bohr C r)*density B)+3/(z : ℝ))*(N : ℝ)^(2*Fintype.card I)-
      4/(z : ℝ)-96*(L : ℝ)/(N : ℝ) ≤
      windowPatternAverage (bohr C r)
        (fun (p : B × B) (j : Fin 4) ↦ (j.val : F)*((p.2 : F)-p.1))
        (fun t ↦ H (fun i ↦ Q i t)) := by
  letI : Nonempty B := hB.to_subtype
  let q : F → I → ZMod N := roundedFactor Q
  let Φ : (I → ZMod N) → ℝ := gridObservable H
  let s (p : B × B) (j : Fin 4) : F := (j.val : F)*((p.2 : F)-p.1)
  have hΦ (y : I → ZMod N) : 0 ≤ Φ y ∧ Φ y ≤ 1 := hH _
  have hdef (p : B × B) (t : bohr C r)
      (hin : ∀ j : Fin 4, (t : F)+s p j ∈ bohr C r) :
      |Φ (q ((t : F)+s p 3))-
        Φ (q ((t : F)+s p 0)-3 • q ((t : F)+s p 1)+3 • q ((t : F)+s p 2))| ≤
      (L : ℝ)*(64/(N : ℝ)) := by
    let v (j : Fin 4) (i : I) := Q i ((t : F)+s p j)
    have hrel (i : I) : v 3 i = quadraticWord (v 0 i) (v 1 i) (v 2 i) := by
      have hh := local_quadratic_word (Q i) (hQ i) (hpoly i) (t : F) ((p.2 : F)-p.1)
        (fun j ↦ by simpa only [nsmul_eq_mul] using hin j)
      simpa only [v,s,Fin.val_zero,Fin.val_one,Fin.val_two,Nat.cast_zero,Nat.cast_one,
        Nat.cast_ofNat,zero_mul,add_zero,one_mul,nsmul_eq_mul] using hh
    exact gridObservable_defect H hLip v (fun j i ↦ hQ i _) hrel
  have hd : ∀ χ₀ χ₁ χ₂ : AddChar (I → ZMod N) ℂ,
      ‖(𝔼 p : B × B, 𝔼 t : bohr C r,
        χ₀ (q ((t : F)+s p 0))*χ₁ (q ((t : F)+s p 1))*χ₂ (q ((t : F)+s p 2)))-
        (𝔼 y : (I → ZMod N) × (I → ZMod N) × (I → ZMod N),
          χ₀ y.1*χ₁ y.2.1*χ₂ y.2.2)‖ ≤
        η/(density (bohr C r)*density B)+3/(z : ℝ) := by
    intro χ₀ χ₁ χ₂
    have h := local_triple_discrepancy B hB (fun j : Fin 3 ↦ (j.val : F))
      (hv.comp (Fin.castSucc_injective 3)) (by simp) C hr hz hstable
      (fun b c j ↦ hs b c j.castSucc) q hη hU χ₀ χ₁ χ₂
    have he := expect_product (univ : Finset B) (univ : Finset B)
      (fun p : B × B ↦ 𝔼 t : bohr C r,
        χ₀ (q ((t : F)+s p 0))*χ₁ (q ((t : F)+s p 1))*χ₂ (q ((t : F)+s p 2)))
    simp only [univ_product_univ] at he
    rw [he]
    exact h
  have hcount := local_quadratic_model_lower_of_defect C hr hz hstable s
    (fun p j ↦ hs p.1 p.2 j) q Φ hΦ (by positivity) hdef
    (add_nonneg (div_nonneg hη (mul_nonneg (density_nonneg _) (density_nonneg _))) (by positivity)) hd
  have herr := window_sup_counting_bound (bohr C r) ⟨0,bohr_zero C hr.le⟩ s
    (fun t ↦ Φ (q t)) (fun t ↦ H (fun i ↦ Q i t))
    (fun t ↦ hΦ (q t)) (fun t ↦ hH _)
    (fun t ↦ gridObservable_error H hLip (fun i ↦ Q i t) (fun i ↦ hQ i t))
  have hcard : (Fintype.card (I → ZMod N) : ℝ)^2 = (N : ℝ)^(2*Fintype.card I) := by
    rw [Fintype.card_fun,ZMod.card,Nat.cast_pow,← pow_mul,mul_comm]
  rw [hcard] at hcount
  simp only [Fintype.card_fin,Nat.cast_ofNat] at herr
  change (𝔼 y : I → ZMod N, Φ y)^4-_
      -4/(z : ℝ)-96*(L : ℝ)/(N : ℝ) ≤ windowPatternAverage (bohr C r) s (fun t ↦ H (fun i ↦ Q i t))
  have he : (L : ℝ)*(64/(N : ℝ))+4*((L : ℝ)*(8/(N : ℝ))) = 96*(L : ℝ)/(N : ℝ) := by ring
  linarith [(abs_le.mp herr).2]

#print axioms local_circle_count
end Erdos3LocalCircleFactorCounting
