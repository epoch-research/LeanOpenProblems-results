import FormalConjecturesUtil
import Submission.ThetaColumnSplitting

/-! The local oriented theta estimate fails even with a maximum-column-degree
cap and at most quadratically many rows. This does not assert realization as
a neighbourhood in any particular globally forbidden extremal graph. -/
open Finset
namespace Erdos713ThetaSplit
open Erdos713ThetaGram

lemma exists_capped_counterexample (N : ℕ) :
    ∃ (A B : Type) (_ : Fintype A) (_ : Fintype B) (R : A → B → Prop),
      ¬ HasTheta R ∧ 0 < Nat.card A ∧ Nat.card A ≤ (Nat.card B)^2 ∧
      (∀ b, Nat.card {a // R a b} ≤ Nat.card B) ∧
      N*(Nat.card A+Nat.card B*(Nat.sqrt (Nat.card A)+1)) <
        Nat.card {p : A × B // R p.1 p.2} := by
  classical
  let t := 10*N+10
  have ht : 1 ≤ t := by dsimp [t]; omega
  obtain ⟨A,B,instA,instB,R,hFree,hLarge,hRow,hEdges⟩ := exists_oriented_counterexamples (t^2) 1
  simp only [one_mul] at hLarge
  let m := Nat.card A
  have hm : 0 < m := by dsimp [m]; nlinarith
  haveI : Nonempty A := (Nat.card_pos_iff.mp hm).1
  have hBpos : 0 < Nat.card B := by
    let a : A := Classical.arbitrary A
    have hh := Nat.card_le_card_of_injective
      (fun b : {b // R a b} => b.val) Subtype.val_injective
    rw [hRow a] at hh
    nlinarith
  haveI : Nonempty B := (Nat.card_pos_iff.mp hBpos).1
  let s := Nat.sqrt m+1
  let d := t*s
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hd : 0 < d := Nat.mul_pos (by omega) (by omega)
  have hms : m < s^2 := by simpa only [s,pow_two,Nat.succ_eq_add_one] using Nat.lt_succ_sqrt m
  have hs4 : s^2 ≤ 4*m := by
    have hz := Nat.sqrt_le m
    have hz' := Nat.sqrt_le_self m
    dsimp [s]
    nlinarith
  have hk : Nat.card B ≤ s := by
    have hh : Nat.card B ≤ Nat.sqrt m := Nat.le_sqrt.mpr (by dsimp [m]; nlinarith)
    dsimp [s]
    omega
  have he : Nat.card {p : A × B // R p.1 p.2} ≤ d^2 := by
    calc
      _ = m*t^2 := hEdges
      _ ≤ s^2*t^2 := Nat.mul_le_mul_right _ hms.le
      _ = d^2 := by dsimp [d]; ring
  obtain ⟨hD,hK⟩ := columns_le R hd he
  let K := Nat.card (SplitColumns R d)
  have hK' : K ≤ (2*t+1)*s := by dsimp [K] at *; dsimp [d] at hK; nlinarith
  refine ⟨A,SplitColumns R d,inferInstance,inferInstance,split R d,
    split_no_theta R d hFree,hm,?_,fun b => (col_card_le R hd b).trans hD,?_⟩
  · calc
      m ≤ s^2 := hms.le
      _ ≤ d^2 := Nat.pow_le_pow_left (by dsimp [d]; nlinarith) 2
      _ ≤ (Nat.card (SplitColumns R d))^2 := Nat.pow_le_pow_left hD 2
  · have hSmall : m+K*s ≤ (8*t+5)*m := by
      calc
        _ ≤ m+((2*t+1)*s)*s := Nat.add_le_add_left (Nat.mul_le_mul_right _ hK') _
        _ = m+(2*t+1)*s^2 := by ring
        _ ≤ m+(2*t+1)*(4*m) := Nat.add_le_add_left (Nat.mul_le_mul_left _ hs4) _
        _ = _ := by ring
    have hBig : N*(8*t+5) < t^2 := by dsimp [t]; nlinarith
    change N*(m+K*s) < _
    calc
      _ ≤ N*((8*t+5)*m) := Nat.mul_le_mul_left _ hSmall
      _ = (N*(8*t+5))*m := by ring
      _ < t^2*m := Nat.mul_lt_mul_of_pos_right hBig hm
      _ = Nat.card {p : A × SplitColumns R d // split R d p.1 p.2} := by
        rw [edge_card,hEdges]
        dsimp [m]
        ring

lemma no_capped_unbalanced_bound :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ (A B : Type) [Fintype A] [Fintype B] (R : A → B → Prop),
      ¬ HasTheta R → Nat.card A ≤ (Nat.card B)^2 →
      (∀ b, Nat.card {a // R a b} ≤ Nat.card B) →
        (Nat.card {p : A × B // R p.1 p.2} : ℝ) ≤
          C*((Nat.card A : ℝ)+(Nat.card B : ℝ)*Real.sqrt (Nat.card A)) := by
  rintro ⟨C,hC,hBound⟩
  obtain ⟨N,hN⟩ := exists_nat_gt C
  obtain ⟨A,B,instA,instB,R,hFree,hm,hSize,hCap,hMany⟩ := exists_capped_counterexample N
  have hs : Real.sqrt (Nat.card A) ≤ (Nat.sqrt (Nat.card A) : ℝ)+1 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    have hh := (Nat.lt_succ_sqrt (Nat.card A)).le
    have hh' : Nat.card A ≤ (Nat.sqrt (Nat.card A)+1)^2 := by
      simpa only [Nat.succ_eq_add_one,pow_two] using hh
    exact_mod_cast hh'
  have hM : (Nat.card {p : A × B // R p.1 p.2} : ℝ) ≤
      (N : ℝ)*((Nat.card A : ℝ)+(Nat.card B : ℝ)*((Nat.sqrt (Nat.card A) : ℝ)+1)) := by
    calc
      _ ≤ C*((Nat.card A : ℝ)+(Nat.card B : ℝ)*Real.sqrt (Nat.card A)) :=
        hBound A B R hFree hSize hCap
      _ ≤ C*((Nat.card A : ℝ)+(Nat.card B : ℝ)*((Nat.sqrt (Nat.card A) : ℝ)+1)) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _))) hC.le
      _ ≤ _ := mul_le_mul_of_nonneg_right hN.le (by positivity)
  have hM' : (N : ℝ)*((Nat.card A : ℝ)+(Nat.card B : ℝ)*((Nat.sqrt (Nat.card A) : ℝ)+1)) <
      (Nat.card {p : A × B // R p.1 p.2} : ℝ) := by exact_mod_cast hMany
  exact (not_lt_of_ge hM) hM'

#print axioms exists_capped_counterexample
#print axioms no_capped_unbalanced_bound
end Erdos713ThetaSplit
