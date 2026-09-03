import FormalConjecturesUtil
import Submission.ThetaGramCount

/-! Retain a coarse cubic upper size bound for the fixed-Gram examples. -/
open Finset
namespace Erdos713ThetaGramUpperSize
open Erdos713ThetaGram
set_option maxHeartbeats 2000000

lemma fiber_cubic_bound {r N : ℕ} (hr : 1 ≤ r) (g : GramCode 19 N) :
    Nat.card (Fiber g)*r ≤ (Nat.card (Columns 19 r N))^3 := by
  classical
  have hm : Nat.card (Fiber g) ≤ (N^19)^3 := by
    have hh := Fintype.card_subtype_le (fun f : NatCoeffs 19 N => gramCode f = g)
    simpa only [Fiber,NatCoeffs,Nat.card_eq_fintype_card,Fintype.card_fun,Fintype.card_fin] using hh
  have hN : N ≤ ColBound r N := by dsimp [ColBound]; nlinarith
  have hNP := Nat.pow_le_pow_left hN 19
  have hr3 : r ≤ r^3 := by nlinarith [Nat.one_le_pow 3 r (by omega)]
  calc
    Nat.card (Fiber g)*r ≤ (N^19)^3*r := Nat.mul_le_mul_right r hm
    _ ≤ ((ColBound r N)^19)^3*r^3 := Nat.mul_le_mul (Nat.pow_le_pow_left hNP 3) hr3
    _ = (Nat.card (Columns 19 r N))^3 := by
      simp only [Columns,Nat.card_prod,Nat.card_fun,Nat.card_fin]
      ring

lemma exists_examples (r L : ℕ) (hr : 1 ≤ r) :
    ∃ (A B : Type) (_ : Fintype A) (_ : Fintype B) (R : A → B → Prop),
      ¬ HasTheta R ∧ L*(Nat.card B)^2 < Nat.card A ∧
      Nat.card A*r ≤ (Nat.card B)^3 ∧
      (∀ a, Nat.card {b // R a b} = r) ∧
      Nat.card {p : A × B // R p.1 p.2} = Nat.card A*r := by
  classical
  obtain ⟨N,g,hN,hg⟩ := exists_large_fiber r L
  refine ⟨Fiber g,Columns 19 r N,inferInstance,inferInstance,incidence g,
    incidence_no_theta g,?_,fiber_cubic_bound hr g,row_card g,edge_card g⟩
  simpa only [Nat.card_eq_fintype_card] using hg

#print axioms fiber_cubic_bound
#print axioms exists_examples
end Erdos713ThetaGramUpperSize
