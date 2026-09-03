import FormalConjecturesUtil
import Submission.DeterminantQuadraticTheta

/-! Square-scale incidence mass can coexist with small row/light budgets
and girth-eight punctured column links. Full theta exclusion is essential. -/
open Finset
open scoped Classical
namespace Erdos713ColumnLinkSquareCounterexample
open Erdos713DeterminantQuadraticIncidence Erdos713DeterminantQuadraticLinks
open Erdos713DeterminantQuadraticTheta Erdos713GlobalLight
open Erdos713ThetaCross (lightCount)
open Erdos713ThetaGram (HasTheta)
set_option maxHeartbeats 2000000

/-- An auxiliary counterexample, NOT a disproof of Erdős 713 or of the
original theta-free SquareVanishing predicate. These relations contain theta. -/
theorem exists_counterexample (N : ℕ) :
    ∃ (A B : Type) (_ : Fintype A) (_ : Fintype B) (R : A → B → Prop),
      N*Nat.card A < (Nat.card B)^2 ∧
      N*lightCount R < (Nat.card B)^2 ∧
      (Nat.card B)^2 < 2*Nat.card {p : A × B // R p.1 p.2} ∧
      (∀ b, Nat.card {a // R a b} ≤ Nat.card B) ∧
      (∀ a, N ≤ Nat.card {b // R a b} ∧ N*(Nat.card {b // R a b})^2 < Nat.card B) ∧
      (∀ a b x y z, x ≠ y → x ≠ z → y ≠ z →
        R a x → R a y → R a z → R b x → R b y → R b z → a = b) ∧
      (∀ (u : B) (a b : {a : A // R a u}) (x y : {x : B // x ≠ u}),
        R a.val x.val → R a.val y.val → R b.val x.val → R b.val y.val → a = b ∨ x = y) ∧
      (∀ (u : B) (a : Fin 3 → A) (b : Fin 3 → B),
        Function.Injective a → Function.Injective b →
        (∀ i, R (a i) u) → (∀ i, b i ≠ u) →
        (∀ i, R (a i) (b i)) → (∀ i, R (a (i+1)) (b i)) → False) ∧
      HasTheta R := by
  obtain ⟨q,hq,hprime⟩ := Nat.exists_infinite_primes (2*N+13)
  haveI : Fact q.Prime := ⟨hprime⟩
  have hqpos : 0 < q := hprime.pos
  have hNq : N < q := by omega
  have h2Nq : 2*N < q := by omega
  have hq3 : 3 ≤ q := by omega
  have hc : Nat.card (ZMod q) = q := by simp [Nat.card_eq_fintype_card]
  have hcast (n : ℕ) (hn : 0 < n) (hnq : n < q) : (n : ZMod q) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff n q).mp h
    exact (not_le_of_gt hnq) (Nat.le_of_dvd hn hd)
  refine ⟨Rows (ZMod q),Cols (ZMod q),inferInstance,inferInstance,incidence,?_,?_,?_,?_,?_,
    (fun a b x y z => @rigid_three (ZMod q) _ a b x y z),column_four,column_hexagon,
    contains_theta (hcast 2 (by omega) (by omega)) (hcast 3 (by omega) (by omega))
      (hcast 11 (by omega) (by omega))⟩
  · rw [rows_card,cols_card,hc]
    have hnm : N*(q-1) < q^2 := by
      have h1 := Nat.mul_le_mul_left N (Nat.sub_le q 1)
      have h2 := Nat.mul_lt_mul_of_pos_right hNq hqpos
      nlinarith only [h1,h2]
    have hh := Nat.mul_lt_mul_of_pos_right hnm (pow_pos hqpos 4)
    nlinarith only [hh]
  · have ht := light_count_upper (K := ZMod q) (by rw [hc]; omega)
    rw [cols_card,hc]
    rw [hc] at ht
    have h1 := Nat.mul_le_mul_left N ht
    have h2 := Nat.mul_lt_mul_of_pos_right h2Nq (pow_pos hqpos 5)
    nlinarith only [h1,h2]
  · rw [cols_card,edge_card,hc]
    have hh := Nat.mul_lt_mul_of_pos_right (show q < 2*(q-1) by omega) (pow_pos hqpos 5)
    nlinarith only [hh]
  · intro b
    rw [column_card,cols_card,hc]
    have hh := Nat.mul_le_mul_right (q^2) (Nat.sub_le q 1)
    nlinarith only [hh]
  · intro a
    rw [row_card,cols_card,hc]
    refine ⟨hNq.le,?_⟩
    have hh := Nat.mul_lt_mul_of_pos_right hNq (pow_pos hqpos 2)
    nlinarith only [hh]

#print axioms exists_counterexample
end Erdos713ColumnLinkSquareCounterexample
