import Submission.LocalQuadraticFlattening

/-! Quantitative simultaneous linear recurrence and arithmetic progressions
inside finite Bohr sets. Natural strides are positive; injectivity, when needed,
must separately be obtained from a bound on the ambient additive order. -/
namespace Erdos3BohrArithmeticProgressions
open Finset Erdos3MaskedPhaseIncrement Erdos3SimultaneousQuadraticRecurrence
  Erdos3LocalQuadraticProgressions Erdos3FiniteBohr
open scoped BigOperators Classical
set_option maxHeartbeats 4000000
set_option maxRecDepth 3000

/-- Elementary simultaneous Dirichlet recurrence for unit complex phases,
proved by a finite coordinate-grid pigeonhole argument. -/
theorem simultaneous_linear_dirichlet {I : Type*} [Fintype I]
    (w : I → ℂ) (hw : ∀ i, ‖w i‖ = 1) (n : ℕ) (hn : 0 < n) :
    ∃ d : ℕ, 0 < d ∧ d ≤ (2*n+1)^(2*Fintype.card I) ∧
      ∀ i, ‖(w i)^d-1‖ ≤ 2/(n : ℝ) := by
  let M := (2*n+1)^(2*Fintype.card I)
  let K := I → PhaseGrid n
  let c : Fin (M+1) → K := fun k i ↦
    phaseLabel n (fun k : ℕ ↦ (w i)^k) (fun k ↦ by simp only [norm_pow,hw,one_pow,le_refl]) k.val
  have hK : Fintype.card K = M := by
    simp only [K,PhaseGrid,Fintype.card_fun,Fintype.card_prod,Fintype.card_fin,M,pow_mul,pow_two]
  obtain ⟨x,y,hne,he⟩ := Fintype.exists_ne_map_eq_of_card_lt c
    (by rw [hK,Fintype.card_fin]; omega)
  have hordered : ∃ x y : Fin (M+1), x.val < y.val ∧ c x = c y := by
    rcases lt_trichotomy x.val y.val with h | h | h
    · exact ⟨x,y,h,he⟩
    · exact False.elim (hne (Fin.ext h))
    · exact ⟨y,x,h,he.symm⟩
  obtain ⟨x,y,hxy,he⟩ := hordered
  let d := y.val-x.val
  have hd : 0 < d := by dsimp [d]; omega
  have hde : x.val+d = y.val := by dsimp [d]; omega
  refine ⟨d,hd,by have := y.isLt; dsimp [d]; omega,?_⟩
  intro i
  have hh := phaseLabel_close n hn (fun k : ℕ ↦ (w i)^k)
    (fun k ↦ by simp only [norm_pow,hw,one_pow,le_refl]) (congr_fun he i)
  calc
    _ = ‖(w i)^x.val*((w i)^d-1)‖ := by rw [norm_mul,norm_pow,hw,one_pow,one_mul]
    _ = ‖(w i)^y.val-(w i)^x.val‖ := by rw [mul_sub,mul_one,← pow_add,hde]
    _ ≤ _ := by simpa only [norm_sub_rev] using hh

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- An inner Bohr point is the base of an arithmetic progression in a slightly
larger Bohr set. The stride has an explicit bound independent of |G|. -/
theorem progression_in_enlarged_bohr (C : Finset (AddChar G ℂ)) (a h : G)
    {R : ℝ} (ha : a ∈ bohr C R) (L n : ℕ) (hn : 0 < n) :
    ∃ d : ℕ, 0 < d ∧ d ≤ (2*n+1)^(2*C.card) ∧
      ∀ j ≤ L, a+(j*d) • h ∈ bohr C (R+2*(L : ℝ)/(n : ℝ)) := by
  obtain ⟨d,hd,hbound,hclose⟩ := simultaneous_linear_dirichlet
    (fun χ : C ↦ (χ : AddChar G ℂ) h) (fun χ ↦ AddChar.norm_apply _ _) n hn
  refine ⟨d,hd,by simpa only [Fintype.card_coe] using hbound,?_⟩
  intro j hj
  apply bohr_add ha
  apply mem_bohr.mpr
  intro χ hχ
  have hh : ‖χ (d • h)-1‖ ≤ 2/(n : ℝ) := by
    simpa only [AddChar.map_nsmul_eq_pow] using hclose ⟨χ,hχ⟩
  have hpow := unit_power_oscillation (χ (d • h)) (AddChar.norm_apply _ _) j
  calc
    _ = ‖(χ (d • h))^j-1‖ := by rw [← AddChar.map_nsmul_eq_pow,smul_smul]
    _ ≤ (j : ℝ)*‖χ (d • h)-1‖ := hpow
    _ ≤ (L : ℝ)*(2/(n : ℝ)) :=
      mul_le_mul (by exact_mod_cast hj) hh (norm_nonneg _) (Nat.cast_nonneg _)
    _ = _ := by ring

#print axioms simultaneous_linear_dirichlet
#print axioms progression_in_enlarged_bohr
end Erdos3BohrArithmeticProgressions
