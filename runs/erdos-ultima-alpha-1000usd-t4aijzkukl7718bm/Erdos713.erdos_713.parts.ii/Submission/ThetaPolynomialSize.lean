import FormalConjecturesUtil
import Submission.ThetaGramCount

/-! The fixed-dimensional Gram construction has polynomial, not merely
finite, size in its row degree. These are auxiliary counterexamples only. -/
open Finset
namespace Erdos713ThetaPolynomialSize
open Erdos713ThetaGram
set_option maxHeartbeats 2000000

abbrev scale : ℕ := 20^9*3^38+1

lemma scale_pos : 0 < scale := by positivity

lemma parameter_bound {r : ℕ} (hr : 1 ≤ r) :
    20^9*r^2*(1+r+r^2)^38+1 ≤ scale*r^78 := by
  have hr2 : 1+r+r^2 ≤ 3*r^2 := by nlinarith
  have hp := Nat.pow_le_pow_left hr2 38
  have hm := Nat.mul_le_mul_left (20^9*r^2) hp
  have h1 : 1 ≤ r^78 := Nat.one_le_pow _ _ (by omega)
  calc
    _ ≤ 20^9*r^2*(3*r^2)^38+r^78 := Nat.add_le_add hm h1
    _ = scale*r^78 := by unfold scale; ring

lemma exists_small_fiber (r : ℕ) (hr : 1 ≤ r) :
    ∃ (N : ℕ) (g : GramCode 19 N), 0 < N ∧ N ≤ scale*r^78 ∧
      (Fintype.card (Columns 19 r N))^2 < Fintype.card (Fiber g) := by
  classical
  let N := 20^9*r^2*(1+r+r^2)^38+1
  have hN : 0 < N := by dsimp [N]; omega
  have hBig : 20^9*1*r^2*(1+r+r^2)^38 < N := by dsimp [N]; omega
  have hh := count_gap (r := r) (A := 1+r+r^2) hN hBig
  have hCount : Fintype.card (GramCode 19 N) * (Fintype.card (Columns 19 r N))^2 <
      Fintype.card (NatCoeffs 19 N) := by
    simpa only [GramCode,Columns,NatCoeffs,Fintype.card_fun,Fintype.card_prod,
      Fintype.card_fin,ColBound,one_mul] using hh
  obtain ⟨g,hg⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card
    (gramCode (d := 19) (N := N)) hCount
  refine ⟨N,g,hN,parameter_bound hr,?_⟩
  simpa only [Fiber,Fintype.card_subtype] using hg

lemma fiber_size {N : ℕ} (g : GramCode 19 N) :
    Nat.card (Fiber g) ≤ N^57 := by
  classical
  have hh := Fintype.card_subtype_le (fun f : NatCoeffs 19 N => gramCode f = g)
  have hh' : Nat.card (Fiber g) ≤ (N^19)^3 := by
    simpa only [Fiber,NatCoeffs,Nat.card_eq_fintype_card,
      Fintype.card_fun,Fintype.card_fin] using hh
  simpa only [← pow_mul] using hh'

lemma exists_examples (r : ℕ) (hr : 1 ≤ r) :
    ∃ (A B : Type) (_ : Fintype A) (_ : Fintype B) (R : A → B → Prop),
      ¬ HasTheta R ∧ (Nat.card B)^2 < Nat.card A ∧
      Nat.card A ≤ scale^57*r^4446 ∧
      (∀ a, Nat.card {b // R a b} = r) ∧
      Nat.card {p : A × B // R p.1 p.2} = Nat.card A*r := by
  classical
  obtain ⟨N,g,hN,hUpper,hg⟩ := exists_small_fiber r hr
  refine ⟨Fiber g,Columns 19 r N,inferInstance,inferInstance,incidence g,
    incidence_no_theta g,?_,?_,row_card g,edge_card g⟩
  · simpa only [Nat.card_eq_fintype_card] using hg
  · calc
      _ ≤ N^57 := fiber_size g
      _ ≤ (scale*r^78)^57 := Nat.pow_le_pow_left hUpper 57
      _ = scale^57*r^4446 := by rw [mul_pow,← pow_mul]

#print axioms parameter_bound
#print axioms exists_examples
end Erdos713ThetaPolynomialSize
