import Submission.RobustTopDegreeCounting
import Submission.FiniteBohr

/-! Quantitative mixed-factor counting from a Bohr set of approximate
coefficient returns. The resulting bound depends on character rank and
Lipschitz accuracy, not on the cardinality of the coefficient group. -/
namespace Erdos3BohrTopDegreeCounting
open Finset Erdos3RobustTopDegreeCounting Erdos3TopDegreeFiberCounting Erdos3FiniteBohr
open scoped BigOperators Classical
set_option maxHeartbeats 5000000

variable {H Q C I : Type*} [AddCommGroup H] [Fintype H]
variable [AddCommGroup Q] [Fintype Q] [AddCommGroup C] [Fintype C] [Fintype I]

noncomputable def returnCharacters {k : ℕ} (χ : I → AddChar H ℂ) (L : Fin k → C →+ H) :
    Finset (AddChar C ℂ) := univ.image (fun ij : I × Fin k ↦ (χ ij.1).compAddMonoidHom (L ij.2))

lemma returnCharacters_card {k : ℕ} (χ : I → AddChar H ℂ) (L : Fin k → C →+ H) :
    (returnCharacters χ L).card ≤ Fintype.card I*k := by
  exact (card_image_le).trans_eq (by simp)

lemma character_shift_distance (χ : AddChar H ℂ) (a b : H) :
    ‖χ (a+b)-χ a‖ = ‖χ b-1‖ := by
  rw [χ.map_add_eq_mul,show χ a*χ b-χ a = χ a*(χ b-1) by ring,norm_mul,χ.norm_apply,one_mul]

lemma return_tuple_close {k : ℕ} (χ : I → AddChar H ℂ) (L : Fin k → C →+ H)
    {ρ : ℝ} (hρ : 0 ≤ ρ) {c : C} (hc : c ∈ bohr (returnCharacters χ L) ρ) (a : H) (j : Fin k) :
    ‖(fun i ↦ χ i (a+L j c))-(fun i ↦ χ i a)‖ ≤ ρ := by
  apply (pi_norm_le_iff_of_nonneg hρ).mpr
  intro i
  simp only [Pi.sub_apply,character_shift_distance]
  exact mem_bohr.mp hc ((χ i).compAddMonoidHom (L j)) (mem_image_of_mem _ (mem_univ (i,j)))

lemma return_bohr_density {k q : ℕ} (χ : I → AddChar H ℂ) (L : Fin k → C →+ H) (hq : 0 < q) :
    1/(2*(q : ℝ)+1)^(2*(Fintype.card I*k)) ≤
      ((bohr (returnCharacters χ L) (2/(q : ℝ))).card : ℝ)/(Fintype.card C : ℝ) := by
  have hc := (card_bohr_lower (returnCharacters χ L) hq).trans
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega : 0 < 2*q+1)
      (Nat.mul_le_mul_left 2 (returnCharacters_card χ L))))
  have hP : (0 : ℝ) < (2*(q : ℝ)+1)^(2*(Fintype.card I*k)) := by positivity
  have hC : (0 : ℝ) < Fintype.card C := by exact_mod_cast Fintype.card_pos (α := C)
  apply (div_le_div_iff₀ hP hC).mpr
  rw [one_mul,mul_comm]
  exact_mod_cast hc

/-- The Lipschitz condition is in the supplied character coordinates. A
Lipschitz function of those coordinates satisfies it by composition. -/
theorem bohr_fibered_count (m : ℕ) (χ : I → AddChar H ℂ) (L : Fin (2*m+2) → C →+ H)
    (f : H → Q → ℝ) (hf : ∀ a z, 0 ≤ f a z ∧ f a z ≤ 1) (A : NNReal)
    (hlip : ∀ a b z, |f a z-f b z| ≤ (A : ℝ)*‖(fun i ↦ χ i a)-(fun i ↦ χ i b)‖)
    (q : ℕ) (hq : 0 < q)
    (hbudget : (2*m+2 : ℕ)*(A : ℝ)*(2/(q : ℝ)) ≤ (𝔼 a : H, 𝔼 z : Q, f a z)^(2*m+2)) :
    ((𝔼 a : H, 𝔼 z : Q, f a z)^(2*m+2)-(2*m+2 : ℕ)*(A : ℝ)*(2/(q : ℝ)))/
      (2*(q : ℝ)+1)^(2*(Fintype.card I*(2*m+2))) ≤
      fiberedEvenCount m (fun a c j ↦ a+L j c) f := by
  let S := bohr (returnCharacters χ L) (2/(q : ℝ))
  have hflat : ∀ c ∈ S, ∀ a j z, |f (a+L j c) z-f a z| ≤ (A : ℝ)*(2/(q : ℝ)) := by
    intro c hc a j z
    exact (hlip _ _ _).trans (mul_le_mul_of_nonneg_left
      (return_tuple_close χ L (by positivity) hc a j) A.coe_nonneg)
  have ht := robust_fibered_count m (fun a c j ↦ a+L j c) f hf S hflat
  have hm := return_bohr_density χ L hq
  have hpos : 0 ≤ (𝔼 a : H, 𝔼 z : Q, f a z)^(2*m+2)-(2*m+2 : ℕ)*(A : ℝ)*(2/(q : ℝ)) :=
    sub_nonneg.mpr hbudget
  have hh := mul_le_mul_of_nonneg_right hm hpos
  simp only [← mul_assoc] at ht
  calc
    _ = (1/(2*(q : ℝ)+1)^(2*(Fintype.card I*(2*m+2))))*
        ((𝔼 a : H, 𝔼 z : Q, f a z)^(2*m+2)-(2*m+2 : ℕ)*(A : ℝ)*(2/(q : ℝ))) := by ring
    _ ≤ _ := hh.trans ht

noncomputable def returnMesh (m : ℕ) (A : NNReal) (δ : ℝ) : ℕ :=
  ⌈(4*(2*m+2 : ℕ)*(A : ℝ))/(δ^(2*m+2))⌉₊+1

lemma returnMesh_pos (m : ℕ) (A : NNReal) (δ : ℝ) : 0 < returnMesh m A δ := Nat.succ_pos _

lemma returnMesh_budget (m : ℕ) (A : NNReal) {δ : ℝ} (hδ : 0 < δ) :
    (2*m+2 : ℕ)*(A : ℝ)*(2/(returnMesh m A δ : ℝ)) ≤ δ^(2*m+2)/2 := by
  have hpow : 0 < δ^(2*m+2) := pow_pos hδ _
  have hq : (0 : ℝ) < returnMesh m A δ := by exact_mod_cast returnMesh_pos m A δ
  have hh : (4*(2*m+2 : ℕ)*(A : ℝ))/(δ^(2*m+2)) ≤ (returnMesh m A δ : ℝ) := by
    apply (Nat.le_ceil _).trans
    simp only [returnMesh,Nat.cast_add,Nat.cast_one]
    linarith
  have he := (div_le_iff₀ hpow).mp hh
  rw [show (2*m+2 : ℕ)*(A : ℝ)*(2/(returnMesh m A δ : ℝ)) =
    (2*(2*m+2 : ℕ)*(A : ℝ))/(returnMesh m A δ : ℝ) by ring]
  apply (div_le_iff₀ hq).mpr
  nlinarith only [he]

/-- Explicit cardinality-free counting bound for a positive-mean factor. -/
theorem explicit_bohr_fibered_count (m : ℕ) (χ : I → AddChar H ℂ) (L : Fin (2*m+2) → C →+ H)
    (f : H → Q → ℝ) (hf : ∀ a z, 0 ≤ f a z ∧ f a z ≤ 1) (A : NNReal)
    (hlip : ∀ a b z, |f a z-f b z| ≤ (A : ℝ)*‖(fun i ↦ χ i a)-(fun i ↦ χ i b)‖)
    (hδ : 0 < 𝔼 a : H, 𝔼 z : Q, f a z) :
    let δ := 𝔼 a : H, 𝔼 z : Q, f a z
    let q := returnMesh m A δ
    δ^(2*m+2)/(2*(2*(q : ℝ)+1)^(2*(Fintype.card I*(2*m+2)))) ≤
      fiberedEvenCount m (fun a c j ↦ a+L j c) f := by
  dsimp only
  let δ := 𝔼 a : H, 𝔼 z : Q, f a z
  let q := returnMesh m A δ
  have hb := returnMesh_budget m A hδ
  have hp : 0 ≤ δ^(2*m+2) := (pow_pos hδ _).le
  have hfull : (2*m+2 : ℕ)*(A : ℝ)*(2/(q : ℝ)) ≤ δ^(2*m+2) := by
    change _ ≤ δ^(2*m+2)/2 at hb
    linarith
  have ht := bohr_fibered_count m χ L f hf A hlip q (returnMesh_pos m A δ) hfull
  calc
    _ = (δ^(2*m+2)/2)/(2*(q : ℝ)+1)^(2*(Fintype.card I*(2*m+2))) := by dsimp only [q,δ]; ring
    _ ≤ (δ^(2*m+2)-(2*m+2 : ℕ)*(A : ℝ)*(2/(q : ℝ)))/
        (2*(q : ℝ)+1)^(2*(Fintype.card I*(2*m+2))) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith only [hb]
    _ ≤ _ := ht

#print axioms bohr_fibered_count
#print axioms explicit_bohr_fibered_count
end Erdos3BohrTopDegreeCounting
