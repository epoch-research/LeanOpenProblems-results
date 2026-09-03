import FormalConjecturesUtil
import Submission.ThetaGramPairBound

/-! Dimension 25 supplies enough rows to dominate the three-halves power
of every column splitting used in the codegree-band argument. -/
open Finset
namespace Erdos713ThetaGramPowerSize
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaGramPairBound
set_option maxHeartbeats 2000000

def base : ℕ := 26^13+1
def scale : ℕ := base*3^50
def param (r : ℕ) : ℕ := base*r^2*(1+r+r^2)^50
def floorRows (r N : ℕ) : ℕ := 26^4*r^2*(1+r+r^2)^50*N^56

lemma param_pos {r : ℕ} (hr : 1 ≤ r) : 0 < param r := by
  unfold param base
  positivity

lemma param_lower {r : ℕ} (hr : 1 ≤ r) :
    26^13*r^2*(1+r+r^2)^50 < param r := by
  have hp : 0 < r^2*(1+r+r^2)^50 := by positivity
  simpa only [param, base, mul_assoc] using
    Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self (26^13)) hp

lemma param_upper (r : ℕ) : param r ≤ 26^16*r^2*(1+r+r^2)^50 := by
  have h : base ≤ 26^16 := by norm_num [base]
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h)

lemma count_gap {r : ℕ} (hr : 1 ≤ r) :
    (25*(param r)^2+1)^9 * floorRows r (param r) < (param r)^75 := by
  let N := param r
  have hN : 0 < N := param_pos hr
  have hOne : 1 ≤ N^2 := Nat.one_le_pow _ _ hN
  have hg : (25*N^2+1)^9 ≤ 26^9*N^18 := by
    calc
      _ ≤ (26*N^2)^9 := Nat.pow_le_pow_left (by omega) 9
      _ = _ := by ring
  have hl : 26^13*r^2*(1+r+r^2)^50 < N := param_lower hr
  calc
    _ ≤ (26^9*N^18)*floorRows r N := Nat.mul_le_mul_right _ hg
    _ = (26^13*r^2*(1+r+r^2)^50)*N^74 := by unfold floorRows; generalize (1+r+r^2) = A; ring
    _ < N*N^74 := Nat.mul_lt_mul_of_pos_right hl (Nat.pow_pos hN)
    _ = _ := by ring

lemma exists_fiber {r : ℕ} (hr : 1 ≤ r) :
    ∃ g : GramCode 25 (param r), floorRows r (param r) < Fintype.card (Fiber g) := by
  classical
  have hc : Fintype.card (GramCode 25 (param r)) * floorRows r (param r) <
      Fintype.card (NatCoeffs 25 (param r)) := by
    have h := count_gap hr
    simpa only [GramCode, NatCoeffs, Fintype.card_fun, Fintype.card_prod,
      Fintype.card_fin, ← pow_mul] using h
  obtain ⟨g,hg⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card
    (gramCode (d := 25) (N := param r)) hc
  exact ⟨g, by simpa only [Fiber, Fintype.card_subtype] using hg⟩

lemma columns_square_le_floor {r : ℕ} (hr : 1 ≤ r) :
    (Fintype.card (Columns 25 r (param r)))^2 ≤ floorRows r (param r) := by
  let N := param r
  have hN : 0 < N := param_pos hr
  have h6 : 1 ≤ N^6 := Nat.one_le_pow _ _ hN
  have hC : 1 ≤ 26^4*N^6 := by nlinarith only [h6]
  calc
    _ = r^2*(1+r+r^2)^50*N^50 := by
      simp only [Columns, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, ColBound]
      generalize (1+r+r^2) = A
      ring
    _ ≤ (r^2*(1+r+r^2)^50*N^50)*(26^4*N^6) := Nat.le_mul_of_pos_right _ hC
    _ = _ := by unfold floorRows; generalize (1+r+r^2) = A; ring

lemma split_cube_le_floor_square {r : ℕ} (_hr : 1 ≤ r) {T : ℕ}
    (hT : T^2 ≤ (param r)^25) :
    (Fintype.card (Columns 25 r (param r))*T)^3 ≤ (floorRows r (param r))^2 := by
  let N := param r
  have hT6 : T^6 ≤ N^75 := by
    calc
      _ = (T^2)^3 := by ring
      _ ≤ (N^25)^3 := Nat.pow_le_pow_left hT 3
      _ = _ := by ring
  have hNup : N ≤ 26^16*r^2*(1+r+r^2)^50 := param_upper r
  have hp : (Fintype.card (Columns 25 r N)*T)^6 ≤ (floorRows r N)^4 := by
    calc
      _ = (r^6*(1+r+r^2)^150*N^150)*T^6 := by
        simp only [Columns, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, ColBound]
        generalize (1+r+r^2) = A
        ring
      _ ≤ (r^6*(1+r+r^2)^150*N^150)*N^75 := Nat.mul_le_mul_left _ hT6
      _ = (r^6*(1+r+r^2)^150*N^224)*N := by
        generalize (1+r+r^2) = A
        ring
      _ ≤ (r^6*(1+r+r^2)^150*N^224)*(26^16*r^2*(1+r+r^2)^50) :=
        Nat.mul_le_mul_left _ hNup
      _ = _ := by unfold floorRows; generalize (1+r+r^2) = A; ring
  have hs : ((Fintype.card (Columns 25 r N)*T)^3)^2 ≤ ((floorRows r N)^2)^2 := by
    simpa only [← pow_mul] using hp
  exact (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp hs

lemma param_polynomial {r : ℕ} (hr : 1 ≤ r) : param r ≤ scale*r^102 := by
  have hr2 : r ≤ r^2 := by nlinarith only [hr]
  have hA : 1+r+r^2 ≤ 3*r^2 := by nlinarith only [hr,hr2]
  calc
    _ ≤ base*r^2*(3*r^2)^50 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hA 50)
    _ = _ := by unfold scale; ring

lemma fiber_polynomial {r : ℕ} (hr : 1 ≤ r) (g : GramCode 25 (param r)) :
    Nat.card (Fiber g) ≤ scale^75*r^7650 := by
  classical
  have hc : Nat.card (Fiber g) ≤ (param r)^75 := by
    have h := Fintype.card_subtype_le (fun f : NatCoeffs 25 (param r) => gramCode f = g)
    simpa only [Fiber, Nat.card_eq_fintype_card, NatCoeffs, Fintype.card_fun,
      Fintype.card_fin, ← pow_mul] using h
  calc
    _ ≤ (param r)^75 := hc
    _ ≤ (scale*r^102)^75 := Nat.pow_le_pow_left (param_polynomial hr) 75
    _ = _ := by ring

/-- The pair-codegree ceiling controls every relevant splitting size.
No density claim about the heavy shadow is made. -/
theorem exists_examples (r : ℕ) (hr : 1 ≤ r) :
    ∃ (A B : Type) (_ : Fintype A) (_ : Fintype B) (R : A → B → Prop) (Q : ℕ),
      ¬ HasTheta R ∧ (Nat.card B)^2 < Nat.card A ∧
      Nat.card A ≤ scale^75*r^7650 ∧
      (∀ a, Nat.card {b // R a b} = r) ∧
      (∀ x y, x ≠ y → codegree R x y ≤ Q) ∧
      ∀ T : ℕ, T^2 ≤ Q → (Nat.card B*T)^3 ≤ (Nat.card A)^2 := by
  classical
  obtain ⟨g,hg⟩ := exists_fiber hr
  refine ⟨Fiber g, Columns 25 r (param r), inferInstance, inferInstance,
    incidence g, (param r)^25, incidence_no_theta g, ?_, fiber_polynomial hr g,
    row_card g, pair_codegree_le g, ?_⟩
  · have hh := (columns_square_le_floor hr).trans_lt hg
    simpa only [Nat.card_eq_fintype_card] using hh
  · intro T hT
    have hh := (split_cube_le_floor_square hr hT).trans (Nat.pow_le_pow_left hg.le 2)
    simpa only [Nat.card_eq_fintype_card] using hh

#print axioms pair_codegree_le
#print axioms exists_examples
end Erdos713ThetaGramPowerSize
