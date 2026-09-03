import FormalConjecturesUtil
import Submission.ThetaC4DeletionObstruction
import Submission.ThetaCrossCompletion

/-! An unrestricted light-budget C4-deletion bound is false as well.
This is an auxiliary counterexample, not a disproof of Erdős 713.
The examples deliberately violate a fixed linear column-degree cap. -/
open Finset
namespace Erdos713ThetaLightDeletion
open Erdos713ThetaGram Erdos713ThetaCross Erdos713ThetaSplit
open Erdos713ThetaC4Deletion
variable {A B : Type*}
set_option maxHeartbeats 2000000

lemma lightCount_le_columns_square [Fintype A] [Fintype B] (R : A → B → Prop) :
    lightCount R ≤ (Nat.card B)^2 := by
  classical
  have h := Nat.card_le_card_of_injective
    (fun p : {p : B × B // Erdos713GlobalLight.codegree R p.1 p.2 ≤ 2} => p.val)
    Subtype.val_injective
  simpa only [lightCount,Nat.card_prod,pow_two] using h

/-- The light budget can even be arbitrarily small relative to the ROW
count, while every C4-free subrelation has superlinear deletion cost in
m+t. The number of columns is much smaller than sqrt(m). -/
theorem exists_light_deletion_counterexample (N L : ℕ) :
    ∃ (A B : Type) (_ : Fintype A) (_ : Fintype B) (R : A → B → Prop),
      ¬ HasTheta R ∧ 0 < Nat.card A ∧
      (L+1)*(Nat.card B)^2 < Nat.card A ∧ (L+1)*lightCount R < Nat.card A ∧
      (∀ a, Nat.card {b // R a b} = 2*N+3) ∧
      (∃ b, (L+1)*Nat.card B < Nat.card {a // R a b}) ∧
      ∀ Q : A → B → Prop, (∀ a b, Q a b → R a b) → FourFree Q →
        N*(Nat.card A+lightCount R) < loss R Q := by
  classical
  obtain ⟨A,B,instA,instB,R,hf,hsize,hrow,he⟩ :=
    exists_oriented_counterexamples (2*N+3) (L+1)
  have hm : 0 < Nat.card A := by omega
  have hk : (Nat.card B)^2 < Nat.card A := by
    have h := Nat.le_mul_of_pos_left ((Nat.card B)^2) (by omega : 0 < L+1)
    exact h.trans_lt hsize
  have ht := lightCount_le_columns_square R
  have hlight : (L+1)*lightCount R < Nat.card A :=
    (Nat.mul_le_mul_left (L+1) ht).trans_lt hsize
  have hcap : ∃ b, (L+1)*Nat.card B < Nat.card {a // R a b} := by
    by_contra h
    have hb : ∀ b, Nat.card {a // R a b} ≤ (L+1)*Nat.card B := by
      intro b
      by_contra hn
      exact h ⟨b,by omega⟩
    have hu : Nat.card {p : A × B // R p.1 p.2} ≤ (L+1)*(Nat.card B)^2 := by
      rw [edge_card_eq_cols]
      calc
        _ ≤ ∑ _b : B, (L+1)*Nat.card B := sum_le_sum (fun b _ => hb b)
        _ = _ := by simp [Nat.card_eq_fintype_card]; ring
    nlinarith only [hu,he,hsize,hm]
  refine ⟨A,B,instA,instB,R,hf,hm,hsize,hlight,hrow,hcap,?_⟩
  intro Q hQ hfour
  have hu := four_free_edges_le_two_rows hfour hk.le
  have hs := edge_split hQ
  change edges R = Nat.card A*(2*N+3) at he
  have hlt : lightCount R ≤ Nat.card A := ht.trans hk.le
  have hN := Nat.mul_le_mul_left N (Nat.add_le_add_left hlt (Nat.card A))
  nlinarith only [hu,hs,he,hN,hm]

/-- Negation of the UNRESTRICTED auxiliary deletion assertion. No bound on
column degrees is included or contradicted by this statement. -/
theorem no_unrestricted_light_deletion_bound :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ (A B : Type) [Fintype A] [Fintype B] (R : A → B → Prop),
      ¬ HasTheta R → ∃ Q : A → B → Prop,
        (∀ a b, Q a b → R a b) ∧ FourFree Q ∧
        (loss R Q : ℝ) ≤ C*((Nat.card A : ℝ)+lightCount R) := by
  rintro ⟨C,_hC,h⟩
  obtain ⟨N,hN⟩ := exists_nat_gt C
  obtain ⟨A,B,instA,instB,R,hf,_hm,_hsize,_hlight,_hrow,_hcap,hbad⟩ :=
    exists_light_deletion_counterexample N 0
  obtain ⟨Q,hsub,hfour,hu⟩ := h A B R hf
  have hl : (N : ℝ)*((Nat.card A : ℝ)+lightCount R) < loss R Q := by
    exact_mod_cast hbad Q hsub hfour
  have hc := mul_le_mul_of_nonneg_right hN.le
    (show 0 ≤ (Nat.card A : ℝ)+lightCount R by positivity)
  linarith only [hl,hu,hc]

#print axioms lightCount_le_columns_square
#print axioms exists_light_deletion_counterexample
#print axioms no_unrestricted_light_deletion_bound
end Erdos713ThetaLightDeletion
