import FormalConjecturesUtil
import Submission.ThetaCrossCompletion
import Submission.ThetaBalancedSplit

/-! Counterexample to an UNRESTRICTED light-pair-weighted theta estimate.
No bound D=O(number of columns) is asserted for these relations. -/
open Finset
namespace Erdos713ThetaWeighted
set_option maxHeartbeats 2000000
open Erdos713ThetaGram Erdos713ThetaSplit Erdos713ThetaCross
open Erdos713ThetaBalancedSplit

lemma numeric_bound {m k K r d : ℕ} (hr : 1 ≤ r) (hK : K ≤ 2*k)
    (hd : d*k ≤ 2*m*r) (hm : 100*r^2*k^2 < m) :
    r^2*m+3*(r^2)^2*K^2+(d+12*r^2*k)*(2*r*k) ≤ 7*r^2*m := by
  have hr2 : r ≤ r^2 := by nlinarith
  have hm12 : 12*r^2*k^2 ≤ m := by nlinarith
  have hm24 : 24*r*k^2 ≤ m := by
    calc
      _ ≤ 24*r^2*k^2 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hr2)
      _ ≤ m := by nlinarith
  have hrows : r^2*m+3*(r^2)^2*K^2 ≤ 2*r^2*m := by
    have hK2 := Nat.pow_le_pow_left hK 2
    calc
      _ ≤ r^2*m+3*(r^2)^2*(2*k)^2 :=
        Nat.add_le_add_left (Nat.mul_le_mul_left _ hK2) _
      _ = r^2*m+r^2*(12*r^2*k^2) := by ring
      _ ≤ r^2*m+r^2*m := Nat.add_le_add_left (Nat.mul_le_mul_left _ hm12) _
      _ = _ := by ring
  have hweight : (d+12*r^2*k)*(2*r*k) ≤ 5*r^2*m := by
    calc
      _ = 2*r*(d*k)+r^2*(24*r*k^2) := by ring
      _ ≤ 2*r*(2*m*r)+r^2*m :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hd) (Nat.mul_le_mul_left _ hm24)
      _ = _ := by ring
  nlinarith

lemma exists_weighted_counterexample (N : ℕ) :
    ∃ (A B : Type) (_ : Fintype A) (_ : Fintype B) (R : A → B → Prop) (D S : ℕ),
      ¬ HasTheta R ∧ (∀ b, Nat.card {a // R a b} ≤ D) ∧
      lightCount R ≤ S^2 ∧
      N*(Nat.card A+D*S) < Nat.card {p : A × B // R p.1 p.2} := by
  classical
  let r := 100*N+100
  have hr : 1 ≤ r := by dsimp [r]; omega
  obtain ⟨A,B,instA,instB,R,hFree,hLarge,hRow,hEdges⟩ :=
    exists_oriented_counterexamples r (100*r^2)
  let m := Nat.card A
  let k := Nat.card B
  have hm : 0 < m := by dsimp [m]; nlinarith
  haveI : Nonempty A := (Nat.card_pos_iff.mp hm).1
  have hk : 0 < k := by
    let a : A := Classical.arbitrary A
    have hh := Nat.card_le_card_of_injective
      (fun b : {b // R a b} => b.val) Subtype.val_injective
    rw [hRow a] at hh
    dsimp [k]
    omega
  have hk2 : k ≤ k^2 := by nlinarith
  have hkm : k ≤ m := by
    apply hk2.trans
    have ht : 0 < 100*r^2 := by positivity
    exact (Nat.le_mul_of_pos_left _ ht).trans hLarge.le
  have hke : k ≤ m*r := hkm.trans (Nat.le_mul_of_pos_right _ (by omega))
  let d := (m*r)/k+1
  obtain ⟨hd,hed,hde⟩ := balanced_cap (e := m*r) hk
  let K := Nat.card (CoreColumns R d)
  have hK : K ≤ 2*k := core_columns_le R hd (by simpa only [hEdges] using hed)
  have hdk : d*k ≤ 2*m*r := by
    calc
      _ ≤ m*r+k := hde
      _ ≤ 2*m*r := by nlinarith
  let I := Fin (r^2)
  let R' := coreSplit R d
  let R'' := complete (I := I) R'
  let D := d+12*r^2*k
  let S := 2*r*k
  have hcol (c : Cols I (CoreColumns R d)) :
      Nat.card {a : Rows I A (CoreColumns R d) // R'' a c} ≤ D := by
    have hh := column_le (I := I) R' d (core_column_le R hd) c
    simp only [I,Nat.card_fin] at hh
    change _ ≤ d+12*r^2*k
    change _ ≤ d+6*r^2*K at hh
    have hmul := Nat.mul_le_mul_left (6*r^2) hK
    nlinarith
  have hlight : lightCount R'' ≤ S^2 := by
    have hh := lightCount_le (I := I) R'
    simp only [I,Nat.card_fin] at hh
    change lightCount R'' ≤ r^2*K^2 at hh
    calc
      _ ≤ r^2*K^2 := hh
      _ ≤ r^2*(2*k)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hK 2)
      _ = S^2 := by dsimp [S]; ring
  have htotal : Nat.card (Rows I A (CoreColumns R d))+D*S ≤ 7*r^2*m := by
    rw [rows_card]
    simp only [I,Nat.card_fin]
    exact numeric_bound hr hK hdk hLarge
  have hlo : r^3*m ≤ Nat.card {p : Rows I A (CoreColumns R d) × Cols I (CoreColumns R d) //
      R'' p.1 p.2} := by
    have hh := edges_lower (I := I) R'
    simp only [I,Nat.card_fin] at hh
    change r^2 * Nat.card {p : A × CoreColumns R d // coreSplit R d p.1 p.2} ≤ _ at hh
    rw [core_edge_card,hEdges] at hh
    calc
      _ = r^2 * (Nat.card A*r) := by dsimp [m]; ring
      _ ≤ _ := hh
  refine ⟨Rows I A (CoreColumns R d),Cols I (CoreColumns R d),inferInstance,inferInstance,
    R'',D,S,complete_no_theta (core_no_theta R d hFree),hcol,hlight,?_⟩
  calc
    _ ≤ N*(7*r^2*m) := Nat.mul_le_mul_left _ htotal
    _ = (7*N)*(r^2*m) := by ring
    _ < r*(r^2*m) := Nat.mul_lt_mul_of_pos_right (by dsimp [r]; omega) (by positivity)
    _ = r^3*m := by ring
    _ ≤ _ := hlo

lemma no_unrestricted_weighted_bound :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ (A B : Type) [Fintype A] [Fintype B]
      (R : A → B → Prop) (D : ℕ),
      ¬ HasTheta R → (∀ b, Nat.card {a // R a b} ≤ D) →
        (Nat.card {p : A × B // R p.1 p.2} : ℝ) ≤
          C*((Nat.card A : ℝ)+(D : ℝ)*Real.sqrt (lightCount R)) := by
  rintro ⟨C,hC,hBound⟩
  obtain ⟨N,hN⟩ := exists_nat_gt C
  obtain ⟨A,B,instA,instB,R,D,S,hFree,hCap,hLight,hMany⟩ := exists_weighted_counterexample N
  have hs : Real.sqrt (lightCount R) ≤ (S : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    exact_mod_cast hLight
  have hM : (Nat.card {p : A × B // R p.1 p.2} : ℝ) ≤
      (N : ℝ)*((Nat.card A : ℝ)+(D : ℝ)*S) := by
    calc
      _ ≤ C*((Nat.card A : ℝ)+(D : ℝ)*Real.sqrt (lightCount R)) := hBound A B R D hFree hCap
      _ ≤ C*((Nat.card A : ℝ)+(D : ℝ)*S) := mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _))) hC.le
      _ ≤ _ := mul_le_mul_of_nonneg_right hN.le (by positivity)
  have hM' : (N : ℝ)*((Nat.card A : ℝ)+(D : ℝ)*S) <
      (Nat.card {p : A × B // R p.1 p.2} : ℝ) := by exact_mod_cast hMany
  exact (not_lt_of_ge hM) hM'

#print axioms numeric_bound
#print axioms exists_weighted_counterexample
#print axioms no_unrestricted_weighted_bound
end Erdos713ThetaWeighted
