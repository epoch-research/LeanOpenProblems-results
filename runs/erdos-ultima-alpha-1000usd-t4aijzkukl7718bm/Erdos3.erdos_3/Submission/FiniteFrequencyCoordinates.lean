import Submission.PositiveSpectralSmoothing

/-! Explicit finite-torus frequency coordinates. Integer coefficients retain
an actual size bound rather than being treated as arbitrary residue classes. -/
namespace Erdos3FiniteFrequencyCoordinates
open Finset Erdos3FiniteCircleGrid
open scoped BigOperators Classical ComplexConjugate Pointwise
set_option maxHeartbeats 5000000

variable {I : Type*} [Fintype I] [DecidableEq I] {N : ℕ} [NeZero N]

noncomputable def frequencyCharacter (k : I → ZMod N) : AddChar (I → ZMod N) ℂ where
  toFun x := ∏ i : I, ZMod.stdAddChar (k i*x i)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    simp only [Pi.add_apply,mul_add,AddChar.map_add_eq_mul,prod_mul_distrib]

lemma frequencyCharacter_apply (k x : I → ZMod N) :
    frequencyCharacter k x = ∏ i : I, ZMod.stdAddChar (k i*x i) := rfl

lemma frequencyCharacter_add (k l : I → ZMod N) :
    frequencyCharacter (k+l) = frequencyCharacter k*frequencyCharacter l := by
  ext x
  simp only [frequencyCharacter_apply,Pi.add_apply,add_mul,AddChar.map_add_eq_mul,
    prod_mul_distrib,AddChar.mul_apply]

lemma frequencyCharacter_sub (k l : I → ZMod N) :
    frequencyCharacter (k-l) = frequencyCharacter k/frequencyCharacter l := by
  ext x
  simp only [frequencyCharacter_apply,Pi.sub_apply,sub_mul,AddChar.map_sub_eq_div,
    prod_div_distrib,AddChar.div_apply']

lemma frequencyCharacter_zero : frequencyCharacter (0 : I → ZMod N) = 1 := by
  ext x
  simp only [frequencyCharacter_apply,Pi.zero_apply,zero_mul,AddChar.map_zero_eq_one,
    prod_const_one,AddChar.one_apply]

lemma frequencyCharacter_single_test (k : I → ZMod N) (i : I) :
    frequencyCharacter k (Pi.single i 1) = ZMod.stdAddChar (k i) := by
  rw [frequencyCharacter_apply]
  have he (j : I) : ZMod.stdAddChar (k j*((Pi.single i (1 : ZMod N) : I → ZMod N) j)) =
      if j = i then ZMod.stdAddChar (k i) else 1 := by
    by_cases h : j = i
    · subst j; simp
    · simp [Pi.single_apply,h,Ne.symm h]
  simp only [he,prod_ite_eq',mem_univ,if_true]

theorem frequencyCharacter_injective : Function.Injective (frequencyCharacter (I := I) (N := N)) := by
  intro k l h
  funext i
  have hh := congrArg (fun χ : AddChar (I → ZMod N) ℂ ↦ χ (Pi.single i 1)) h
  simp only [frequencyCharacter_single_test] at hh
  exact ZMod.injective_stdAddChar hh

noncomputable def coordinateCharacter (i : I) : AddChar (I → ZMod N) ℂ :=
  frequencyCharacter (Pi.single i 1)

lemma coordinateCharacter_apply (i : I) (x : I → ZMod N) :
    coordinateCharacter i x = ZMod.stdAddChar (x i) := by
  unfold coordinateCharacter
  have he : frequencyCharacter (Pi.single i (1 : ZMod N)) x = frequencyCharacter x (Pi.single i 1) := by
    simp only [frequencyCharacter_apply,mul_comm]
  rw [he,frequencyCharacter_single_test]

noncomputable def integerCharacter (k : I → ℤ) : AddChar (I → ZMod N) ℂ :=
  frequencyCharacter (fun i ↦ (k i : ZMod N))

lemma integerCharacter_apply (k : I → ℤ) (x : I → ZMod N) :
    integerCharacter k x = ∏ i : I, (ZMod.stdAddChar (x i))^(k i) := by
  unfold integerCharacter
  rw [frequencyCharacter_apply]
  apply prod_congr rfl
  intro i _
  simpa only [zsmul_eq_mul] using (ZMod.stdAddChar (N := N)).map_zsmul_eq_zpow (k i) (x i)

lemma integerCharacter_add (k l : I → ℤ) :
    integerCharacter (N := N) (k+l) = integerCharacter k*integerCharacter l := by
  unfold integerCharacter
  have he : (fun i ↦ ((k+l) i : ZMod N)) = (fun i ↦ (k i : ZMod N))+(fun i ↦ (l i : ZMod N)) := by
    funext i
    simp only [Pi.add_apply,Int.cast_add]
  rw [he,frequencyCharacter_add]

lemma integerCharacter_sub (k l : I → ℤ) :
    integerCharacter (N := N) (k-l) = integerCharacter k/integerCharacter l := by
  unfold integerCharacter
  have he : (fun i ↦ ((k-l) i : ZMod N)) = (fun i ↦ (k i : ZMod N))-(fun i ↦ (l i : ZMod N)) := by
    funext i
    simp only [Pi.sub_apply,Int.cast_sub]
  rw [he,frequencyCharacter_sub]

/-- Frequencies represented by explicitly bounded integer vectors. -/
def HasFrequencyBound (R : ℕ) (χ : AddChar (I → ZMod N) ℂ) : Prop :=
  ∃ k : I → ℤ, (∀ i, |k i| ≤ R) ∧ χ = integerCharacter k

lemma HasFrequencyBound.mul {R T : ℕ} {χ ψ : AddChar (I → ZMod N) ℂ}
    (hχ : HasFrequencyBound R χ) (hψ : HasFrequencyBound T ψ) :
    HasFrequencyBound (R+T) (χ*ψ) := by
  obtain ⟨k,hk,rfl⟩ := hχ
  obtain ⟨l,hl,rfl⟩ := hψ
  refine ⟨k+l,?_,(integerCharacter_add k l).symm⟩
  intro i
  exact (abs_add_le _ _).trans (by simpa only [Nat.cast_add] using add_le_add (hk i) (hl i))

lemma HasFrequencyBound.div {R T : ℕ} {χ ψ : AddChar (I → ZMod N) ℂ}
    (hχ : HasFrequencyBound R χ) (hψ : HasFrequencyBound T ψ) :
    HasFrequencyBound (R+T) (χ/ψ) := by
  obtain ⟨k,hk,rfl⟩ := hχ
  obtain ⟨l,hl,rfl⟩ := hψ
  refine ⟨k-l,?_,(integerCharacter_sub k l).symm⟩
  intro i
  exact (abs_sub _ _).trans (by simpa only [Nat.cast_add] using add_le_add (hk i) (hl i))

lemma HasFrequencyBound.pow {R : ℕ} {χ : AddChar (I → ZMod N) ℂ}
    (hχ : HasFrequencyBound R χ) (n : ℕ) : HasFrequencyBound (n*R) (χ^n) := by
  induction n with
  | zero =>
    refine ⟨0,?_,?_⟩
    · simp
    · simpa only [pow_zero,integerCharacter,Pi.zero_apply,Int.cast_zero] using frequencyCharacter_zero.symm
  | succ n ih =>
    rw [pow_succ,Nat.succ_mul]
    exact ih.mul hχ

#print axioms frequencyCharacter_injective
#print axioms HasFrequencyBound.pow
end Erdos3FiniteFrequencyCoordinates
