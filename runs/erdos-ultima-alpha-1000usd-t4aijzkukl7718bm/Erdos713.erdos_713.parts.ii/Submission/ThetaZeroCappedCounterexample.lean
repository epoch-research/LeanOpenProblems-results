import FormalConjecturesUtil
import Submission.ThetaTransversalCompletion
import Submission.ThetaColumnPadding
import Submission.ThetaGramUpperSize
import Submission.ThetaTransversalParameters

/-! A capped local zero-pair budget does not give the proposed unbalanced
theta estimate. This auxiliary refutation does not settle Erdős 713. -/
open Finset
namespace Erdos713ThetaZeroCapped
open Erdos713ThetaGram Erdos713ThetaGramUpperSize
open Erdos713ThetaBalancedSplit Erdos713ThetaColumnPadding
open Erdos713ThetaTransversal Erdos713ThetaTransversalParameters
open Erdos713ThetaZeroPairs
set_option maxHeartbeats 2000000

/-- Even a zero-pair budget at most the row count and a column-degree cap
of twice the column count do not imply the oriented square-root estimate. -/
theorem exists_counterexample (N : ℕ) :
    ∃ (A B : Type) (_ : Fintype A) (_ : Fintype B) (R : A → B → Prop),
      ¬ HasTheta R ∧ (zeroSet R).card ≤ Nat.card A ∧
      (∀ b, Nat.card {a // R a b} ≤ 2*Nat.card B) ∧
      (N : ℝ)*((Nat.card A : ℝ)+(Nat.card B : ℝ)*Real.sqrt (Nat.card A)) <
        (Nat.card {p : A × B // R p.1 p.2} : ℝ) := by
  classical
  let s : ℕ := 100*(N+1)
  let r : ℕ := s^2
  have hs : 0 < s := by dsimp [s]; positivity
  have hr : 1 ≤ r := Nat.one_le_pow _ _ hs
  obtain ⟨A,B,hA,hB,R,hFree,hLarge,hCube,hRow,hEdges⟩ := exists_examples r 100 hr
  let m := Nat.card A
  let k := Nat.card B
  change 100*k^2 < m at hLarge
  change m*r ≤ k^3 at hCube
  have hm : 0 < m := by omega
  have hk : 0 < k := by
    by_contra hnp
    have hk0 : k = 0 := by omega
    rw [hk0] at hCube
    simp only [zero_pow (by decide : 3 ≠ 0)] at hCube
    nlinarith
  haveI : Nonempty B := Fintype.card_pos_iff.mp (by simpa only [← Nat.card_eq_fintype_card] using hk)
  let d := m*r/k+1
  have hd := balanced_cap (e := m*r) hk
  change 0 < d ∧ m*r ≤ d*k ∧ d*k ≤ m*r+k at hd
  let B' := CoreColumns R d
  let R' := coreSplit R d
  haveI : Nonempty B' := ⟨⟨Classical.arbitrary B,0⟩⟩
  have hB' : Nat.card B' ≤ 2*k := core_columns_le R hd.1 (by simpa only [hEdges] using hd.2.1)
  have hFree' : ¬ HasTheta R' := core_no_theta R d hFree
  have hEdges' : Nat.card {p : A × B' // R' p.1 p.2} = m*r :=
    (core_edge_card R d).trans hEdges
  obtain ⟨q,hPrime,hqlo,hqhi⟩ := Nat.exists_prime_lt_and_le_two_mul (2*k) (by omega)
  have hqhi' : q ≤ 4*k := by omega
  letI : Fact q.Prime := ⟨hPrime⟩
  let F := ZMod q
  have hF : Nat.card F = q := by simp [F,Nat.card_eq_fintype_card]
  obtain ⟨f : B' ↪ F⟩ := Function.Embedding.nonempty_of_card_le (show Fintype.card B' ≤ Fintype.card F by
    simpa only [← Nat.card_eq_fintype_card,hF] using hB'.trans hqlo.le)
  let P := pad f R'
  have hP : ¬ HasTheta P := pad_no_theta f.injective hFree'
  have hEP : Nat.card {p : A × F // P p.1 p.2} = m*r :=
    (pad_edge_card f.injective R').trans hEdges'
  have hCapP (x : F) : Nat.card {a // P a x} ≤ d :=
    pad_column_le f.injective R' d (core_column_le R hd.1) x
  let T := d/q+1
  obtain ⟨hT,hTq,hqm,hCap,hPower⟩ := parameter_bounds hk hr hLarge hCube hqlo hqhi'
  change 0 < T at hT
  change T ≤ q at hTq
  change d+q ≤ 2*(T*q) at hCap
  change T*q^2 ≤ 8*m*r at hPower
  obtain ⟨i : Fin T ↪ F⟩ := Function.Embedding.nonempty_of_card_le (show Fintype.card (Fin T) ≤ Fintype.card F by
    simpa only [← Nat.card_eq_fintype_card,Nat.card_fin,hF] using hTq)
  let U := Rows (Fin T) A F
  let V := Fin T × F
  let Q := complete i P
  have hU : Nat.card U = T*m+q^2 := by
    simpa only [Nat.card_fin,hF] using (rows_card (A := A) (I := Fin T) (F := F))
  have hV : Nat.card V = T*q := by simp only [V,Nat.card_prod,Nat.card_fin,hF]
  have hEQ : T*(m*r) ≤ Nat.card {p : U × V // Q p.1 p.2} := by
    simpa only [Nat.card_fin,hEP] using edges_lower i P
  refine ⟨U,V,inferInstance,inferInstance,Q,complete_no_theta i i.injective hP,?_,?_,?_⟩
  · have hh : (zeroSet Q).card ≤ T*q^2 := by
      simpa only [Nat.card_fin,hF] using zero_count_le i i.injective P
    rw [hU]
    exact hh.trans ((Nat.mul_le_mul_left T hqm).trans (Nat.le_add_right _ _))
  · intro b
    have hh : Nat.card {a : U // Q a b} ≤ d+q := by
      rw [column_card,hF]
      exact Nat.add_le_add_right (hCapP b.2) q
    rw [hV]
    exact hh.trans hCap
  · have hh := real_gap hm hT hqm hPower (show s = 100*(N+1) from rfl)
    rw [hU,hV]
    have heR : (T*m*s^2 : ℕ) ≤ (Nat.card {p : U × V // Q p.1 p.2} : ℝ) := by
      exact_mod_cast (show T*m*s^2 ≤ Nat.card {p : U × V // Q p.1 p.2} by simpa only [r,Nat.mul_assoc] using hEQ)
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow] using hh.trans_le heR

/-- Negation of an AUXILIARY local inequality, not of the main conjecture. -/
theorem no_capped_zero_unbalanced_bound :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ (A B : Type) [Fintype A] [Fintype B] (R : A → B → Prop),
      ¬ HasTheta R → (zeroSet R).card ≤ Nat.card A →
      (∀ b, Nat.card {a // R a b} ≤ 2*Nat.card B) →
      (Nat.card {p : A × B // R p.1 p.2} : ℝ) ≤
        C*((Nat.card A : ℝ)+(Nat.card B : ℝ)*Real.sqrt (Nat.card A)) := by
  rintro ⟨C,hC,hBound⟩
  obtain ⟨N,hN⟩ := exists_nat_gt C
  obtain ⟨A,B,hA,hB,R,hF,hZ,hD,hGap⟩ := exists_counterexample N
  have hu := hBound A B R hF hZ hD
  have hm : (0 : ℝ) ≤ (Nat.card A : ℝ)+(Nat.card B : ℝ)*Real.sqrt (Nat.card A) := by positivity
  have hh := mul_le_mul_of_nonneg_right hN.le hm
  linarith

#print axioms exists_counterexample
#print axioms no_capped_zero_unbalanced_bound
end Erdos713ThetaZeroCapped
