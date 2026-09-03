import FormalConjecturesUtil
import Submission.ThetaPolynomialSize
import Submission.ThetaColumnSplitting

/-! Polynomial-size auxiliary counterexamples survive the column cap.
No assertion about the original extremal exponent follows from these examples. -/
open Finset
namespace Erdos713ThetaCappedPolynomial
open Erdos713ThetaGram Erdos713ThetaSplit Erdos713ThetaPolynomialSize
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 10000

def sizeConstant : ℕ := 7*scale^57*10^8893

lemma regroup_scale (c t p : ℕ) : 7*t*(c*t^p) = 7*c*t^(p+1) := by
  rw [pow_succ']
  ac_rfl

lemma substitute_scale (c b n p : ℕ) :
    7*c*(b*(n+1))^p = (7*c*b^p)*(n+1)^p := by
  rw [mul_pow]
  ac_rfl

lemma exists_capped_examples (N : ℕ) :
    ∃ (A B : Type) (_ : Fintype A) (_ : Fintype B) (R : A → B → Prop),
      ¬ HasTheta R ∧ 0 < Nat.card A ∧ Nat.card A ≤ (Nat.card B)^2 ∧
      (∀ b, Nat.card {a // R a b} ≤ Nat.card B) ∧
      Nat.card A+Nat.card B ≤ sizeConstant*(N+1)^8893 ∧
      N*(Nat.card A+Nat.card B*(Nat.sqrt (Nat.card A)+1)) <
        Nat.card {p : A × B // R p.1 p.2} := by
  classical
  let t := 10*N+10
  have ht : 1 ≤ t := by dsimp [t]; omega
  obtain ⟨A,B,instA,instB,R,hFree,hLarge,hUpper,hRow,hEdges⟩ :=
    Erdos713ThetaPolynomialSize.exists_examples (t^2) (by nlinarith only [ht])
  let m := Nat.card A
  have hm : 0 < m := by dsimp [m]; nlinarith only [hLarge]
  haveI : Nonempty A := (Nat.card_pos_iff.mp hm).1
  have hBpos : 0 < Nat.card B := by
    let a : A := Classical.arbitrary A
    have hh := Nat.card_le_card_of_injective
      (fun b : {b // R a b} => b.val) Subtype.val_injective
    rw [hRow a] at hh
    nlinarith only [ht,hh]
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
    nlinarith only [hz,hz',hm]
  have hk : Nat.card B ≤ s := by
    have hh : Nat.card B ≤ Nat.sqrt m := Nat.le_sqrt.mpr (by dsimp [m]; nlinarith only [hLarge])
    dsimp [s]
    omega
  have he : Nat.card {p : A × B // R p.1 p.2} ≤ d^2 := by
    calc
      _ = m*t^2 := hEdges
      _ ≤ s^2*t^2 := Nat.mul_le_mul_right _ hms.le
      _ = d^2 := by dsimp [d]; ring
  obtain ⟨hD,hK⟩ := columns_le R hd he
  let K := Nat.card (SplitColumns R d)
  have hK' : K ≤ (2*t+1)*s := by dsimp [K] at *; dsimp [d] at hK; nlinarith only [hK,hk]
  refine ⟨A,SplitColumns R d,inferInstance,inferInstance,split R d,
    split_no_theta R d hFree,hm,?_,fun b => (col_card_le R hd b).trans hD,?_,?_⟩
  · calc
      m ≤ s^2 := hms.le
      _ ≤ d^2 := Nat.pow_le_pow_left (by dsimp [d]; nlinarith only [ht,hs]) 2
      _ ≤ (Nat.card (SplitColumns R d))^2 := Nat.pow_le_pow_left hD 2
  · have hs2 : s ≤ 2*m := by
      have hz := Nat.sqrt_le_self m
      dsimp [s]
      omega
    have hOrder : m+K ≤ 7*t*m := by
      have hh := Nat.mul_le_mul_left (2*t+1) hs2
      nlinarith only [hh,hK',ht,hm]
    have hmUpper : m ≤ scale^57*t^8892 := by
      rw [← pow_mul] at hUpper
      exact hUpper
    calc
      _ ≤ 7*t*m := hOrder
      _ ≤ 7*t*(scale^57*t^8892) := Nat.mul_le_mul_left _ hmUpper
      _ = 7*scale^57*t^8893 := regroup_scale (scale^57) t 8892
      _ = sizeConstant*(N+1)^8893 := by
        have htEq : t = 10*(N+1) := by dsimp [t]; omega
        rw [htEq]
        exact substitute_scale (scale^57) 10 N 8893
  · have hSmall : m+K*s ≤ (8*t+5)*m := by
      calc
        _ ≤ m+((2*t+1)*s)*s := Nat.add_le_add_left (Nat.mul_le_mul_right _ hK') _
        _ = m+(2*t+1)*s^2 := by ring
        _ ≤ m+(2*t+1)*(4*m) := Nat.add_le_add_left (Nat.mul_le_mul_left _ hs4) _
        _ = _ := by ring
    have hBig : N*(8*t+5) < t^2 := by dsimp [t]; nlinarith only
    change N*(m+K*s) < _
    calc
      _ ≤ N*((8*t+5)*m) := Nat.mul_le_mul_left _ hSmall
      _ = (N*(8*t+5))*m := by ring
      _ < t^2*m := Nat.mul_lt_mul_of_pos_right hBig hm
      _ = Nat.card {p : A × SplitColumns R d // split R d p.1 p.2} := by
        rw [Erdos713ThetaSplit.edge_card,hEdges]
        dsimp [m]
        ring

#print axioms exists_capped_examples
end Erdos713ThetaCappedPolynomial
