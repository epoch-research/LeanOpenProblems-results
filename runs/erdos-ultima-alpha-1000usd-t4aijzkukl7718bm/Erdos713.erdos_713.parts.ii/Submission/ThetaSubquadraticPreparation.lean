import FormalConjecturesUtil
import Submission.ThetaGramSubquadraticSize
import Submission.ThetaCappedGramPreparation

/-! Uniform column caps for the variable-dimension Gram examples. -/
open Finset
open scoped Classical
namespace Erdos713ThetaSubquadraticPreparation
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaBalancedSplit
open Erdos713ThetaCappedGramPreparation Erdos713ThetaGramSubquadraticSize
set_option maxHeartbeats 2000000

lemma cube_le_of_shape (s k m : ℕ) (hm : 0 < m)
    (h : k^(num s) ≤ 2^(num s)*m^(den s)) : k^3 ≤ 8*m^2 := by
  have hExp : 3*den s ≤ 2*num s := by unfold den num; omega
  have hp : (k^3)^(num s) ≤ (8*m^2)^(num s) := by
    calc
      _ = (k^(num s))^3 := by simp only [← pow_mul,Nat.mul_comm]
      _ ≤ (2^(num s)*m^(den s))^3 := Nat.pow_le_pow_left h 3
      _ = 2^(3*num s)*m^(3*den s) := by simp only [mul_pow,← pow_mul,Nat.mul_comm]
      _ ≤ 2^(3*num s)*m^(2*num s) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hm hExp)
      _ = _ := by rw [mul_pow,pow_mul,pow_mul]; norm_num
  exact (Nat.pow_le_pow_iff_left (by unfold num; omega)).mp hp

/-- The maximum degree times the number of columns is at most four
 times the original incidence count. -/
theorem exists_examples (s r : ℕ) (hr : 1 ≤ r) :
    ∃ (A B : Type) (_ : Fintype A) (_ : Fintype B) (R : A → B → Prop) (Q D : ℕ),
      ¬ HasTheta R ∧ 0 < Nat.card A ∧ 0 < Nat.card B ∧ 0 < D ∧
      (Nat.card B)^2 ≤ 4*Nat.card A ∧
      Nat.card A ≤ sizeConst s*r^(sizeExp s) ∧
      (∀ a, Nat.card {b // R a b} = r) ∧
      (∀ b, Nat.card {a // R a b} ≤ D) ∧ D*Nat.card B ≤ 4*(Nat.card A*r) ∧
      (∀ x y, x ≠ y → codegree R x y ≤ Q) ∧
      ∀ T : ℕ, T^2 ≤ Q → (Nat.card B*T)^(num s) ≤ 2^(num s)*(Nat.card A)^(den s) := by
  classical
  obtain ⟨A,B,iA,iB,R,Q,hfree,hkm,hsize,hrows,hQ,hshape⟩ :=
    Erdos713ThetaGramSubquadraticSize.exists_examples s r hr
  have hm : 0 < Nat.card A := lt_of_le_of_lt (Nat.zero_le _) hkm
  have hk : 0 < Nat.card B := columns_pos_of_row_degree R hm r hr hrows
  let E := Nat.card A*r
  let D := E/Nat.card B+1
  obtain ⟨hD,hED,hDE⟩ := balanced_cap (e := E) hk
  have hE : Nat.card {p : A × B // R p.1 p.2} = E := by
    rw [Erdos713ThetaSplit.edge_card_eq_rows]
    simp only [hrows,sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,Nat.card_eq_fintype_card,E]
  have hK : Nat.card (CoreColumns R D) ≤ 2*Nat.card B :=
    core_columns_le R hD (hE ▸ hED)
  have hmE : Nat.card A ≤ E := Nat.le_mul_of_pos_right _ hr
  have hkE : Nat.card B ≤ E := by
    calc
      _ ≤ (Nat.card B)^2 := by simpa only [pow_two] using Nat.le_mul_self (Nat.card B)
      _ ≤ Nat.card A := hkm.le
      _ ≤ E := hmE
  have hrows' (a : A) : Nat.card {b // coreSplit R D a b} = r :=
    (core_row_card R D a).trans (hrows a)
  refine ⟨A,CoreColumns R D,inferInstance,inferInstance,coreSplit R D,Q,D,
    core_no_theta R D hfree,hm,columns_pos_of_row_degree _ hm r hr hrows',hD,
    ?_,hsize,hrows',core_column_le R hD,?_,core_pair_bound R D Q hQ,?_⟩
  · calc
      _ ≤ (2*Nat.card B)^2 := Nat.pow_le_pow_left hK 2
      _ ≤ 4*Nat.card A := by nlinarith only [hkm.le]
  · have hh := Nat.mul_le_mul_left D hK
    change D*Nat.card B ≤ E+Nat.card B at hDE
    change D*Nat.card (CoreColumns R D) ≤ 4*E
    nlinarith only [hh,hDE,hkE]
  · intro T hT
    have hh := Nat.pow_le_pow_left (Nat.mul_le_mul_right T hK) (num s)
    have hs := hshape T hT
    calc
      _ ≤ (2*Nat.card B*T)^(num s) := hh
      _ = 2^(num s)*(Nat.card B*T)^(num s) := by rw [mul_assoc,mul_pow]
      _ ≤ 2^(num s)*(Nat.card A)^(den s) := Nat.mul_le_mul_left (2^(num s)) hs

#print axioms cube_le_of_shape
#print axioms exists_examples
end Erdos713ThetaSubquadraticPreparation
