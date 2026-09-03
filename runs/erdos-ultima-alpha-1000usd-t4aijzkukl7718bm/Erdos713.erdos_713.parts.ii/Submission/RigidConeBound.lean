import FormalConjecturesUtil
import Submission.ThetaConeLinks
import Submission.ThetaHeavyRowCount

/-! An edge bound for the existing rigid cone construction. This does not
bound the extremal number of the apex-theta pattern: it applies only to
hosts built from a relation with three-column rigidity. -/

open Finset
namespace Erdos713RigidConeBound
open Erdos713ThetaThreePoint Erdos713ThetaConeLinks Erdos713ThetaHeavyShadow
open Erdos713ThetaHeavyRowCount Erdos713GlobalLight Erdos713ThetaSplit
variable {A B : Type*}
set_option maxHeartbeats 2000000

lemma common_columns_le_two [Fintype B] {R : A → B → Prop} (hR : Rigid3 R)
    {a b : A} (hab : a ≠ b) : codegree (fun x y => R y x) a b ≤ 2 := by
  classical
  by_contra hn
  let S := (univ : Finset B).filter (fun x => R a x ∧ R b x)
  have hc : 2 < S.card := by
    simpa only [S, codegree, Nat.card_eq_fintype_card, Fintype.card_subtype] using
      (show 2 < codegree (fun x y => R y x) a b by omega)
  obtain ⟨x,y,z,hx,hy,hz,hxy,hxz,hyz⟩ := two_lt_card_iff.mp hc
  apply hab
  apply hR a b ![x,y,z]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i
    fin_cases i
    · exact (mem_filter.mp hx).2.1
    · exact (mem_filter.mp hy).2.1
    · exact (mem_filter.mp hz).2.1
  · intro i
    fin_cases i
    · exact (mem_filter.mp hx).2.2
    · exact (mem_filter.mp hy).2.2
    · exact (mem_filter.mp hz).2.2

lemma incidence_double_count [Fintype A] [Fintype B] (R : A → B → Prop) :
    (∑ a : A, (row R a).card) = ∑ b : B, (row (fun x y => R y x) b).card := by
  classical
  exact sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow R (s := univ) (t := univ)

/-- A one-sided KST count, retaining the dimensions of both shores. -/
theorem incidence_square [Fintype A] [Fintype B] {R : A → B → Prop} (hR : Rigid3 R) :
    (∑ a : A, (row R a).card)^2 ≤
      2*Fintype.card B*(Fintype.card A)^2 +
        Fintype.card B*(∑ a : A, (row R a).card) := by
  classical
  let T : B → A → Prop := fun b a => R a b
  let E := ∑ a : A, (row R a).card
  let Z := ∑ b : B, (row T b).card^2
  let Q := ∑ b : B, (row T b).card.choose 2
  have hPair : 2*Q ≤ 2*(Fintype.card A)^2 := by
    dsimp only [Q]
    rw [pair_sum_eq_codegrees]
    calc
      _ ≤ ∑ _p ∈ (univ : Finset A).offDiag, 2 := by
        apply sum_le_sum
        intro p hp
        exact common_columns_le_two hR (mem_offDiag.mp hp).2.2
      _ ≤ 2*(Fintype.card A)^2 := by
        simp only [sum_const, Nat.nsmul_eq_mul, offDiag_card, card_univ, pow_two]
        nlinarith [Nat.sub_le (Fintype.card A * Fintype.card A) (Fintype.card A)]
  have hZ : Z = 2*Q + E := by
    have hpt (b : B) : (row T b).card^2 =
        2*(row T b).card.choose 2 + (row T b).card := by
      have hChoose := twice_choose_two (row T b).card
      have hSub := Nat.sub_add_cancel (Nat.le_mul_self (row T b).card)
      nlinarith only [hChoose,hSub]
    dsimp only [Z,Q]
    simp_rw [hpt]
    rw [sum_add_distrib, ← mul_sum]
    have heq : E = ∑ b : B, (row T b).card := incidence_double_count R
    rw [heq]
  have hC : E^2 ≤ Fintype.card B*Z := by
    dsimp only [E,Z]
    rw [incidence_double_count R]
    simpa only [card_univ] using
      (sq_sum_le_card_mul_sum_sq (s := (univ : Finset B))
        (f := fun b => (row T b).card))
  have hM := Nat.mul_le_mul_left (Fintype.card B) hPair
  change E^2 ≤ 2*Fintype.card B*(Fintype.card A)^2 + Fintype.card B*E
  rw [hZ] at hC
  nlinarith only [hC,hM]

lemma incidence_le_product [Fintype A] [Fintype B] (R : A → B → Prop) :
    (∑ a : A, (row R a).card) ≤ Fintype.card A*Fintype.card B := by
  classical
  calc
    _ ≤ ∑ _a : A, Fintype.card B := sum_le_sum (fun a _ => card_le_univ _)
    _ = _ := by simp

/-- Adding one universal row still leaves a cubic bound on the square of
the incidence count. Theta exclusion is not needed for this upper bound. -/
theorem cone_incidence_square [Fintype A] [Fintype B] {R : A → B → Prop}
    (hR : Rigid3 R) :
    (∑ a : Option A, (row (cone R) a).card)^2 ≤
      (Fintype.card A + Fintype.card B + 1)^3 := by
  classical
  have hSum : (∑ a : Option A, (row (cone R) a).card) =
      (∑ a : A, (row R a).card) + Fintype.card B := by
    have hn : row (cone R) none = (univ : Finset B) := by
      ext b
      simp [mem_row, Erdos713ThetaConeLinks.cone]
    have hs (a : A) : row (cone R) (some a) = row R a := rfl
    rw [Fintype.sum_option]
    simp only [hn, hs, card_univ, add_comm]
  rw [hSum]
  have hE := incidence_square hR
  have hP := incidence_le_product R
  have hM := Nat.mul_le_mul_left (3*Fintype.card B) hP
  nlinarith only [hE,hM,
    Nat.zero_le ((Fintype.card A)^3), Nat.zero_le ((Fintype.card B)^3),
    Nat.zero_le ((Fintype.card A)^2*Fintype.card B),
    Nat.zero_le ((Fintype.card A)^2), Nat.zero_le ((Fintype.card B)^2),
    Nat.zero_le (Fintype.card A*Fintype.card B)]

/-- Cardinality formulation: each related pair is one edge of the
bipartite incidence graph, and the cone has `m+k+1` vertices. -/
theorem cone_card_square [Fintype A] [Fintype B] {R : A → B → Prop}
    (hR : Rigid3 R) :
    (Nat.card {p : Option A × B // cone R p.1 p.2})^2 ≤
      (Fintype.card A + Fintype.card B + 1)^3 := by
  classical
  rw [edge_card_eq_rows]
  simpa only [row, Nat.card_eq_fintype_card, Fintype.card_subtype] using
    cone_incidence_square hR

end Erdos713RigidConeBound

#print axioms Erdos713RigidConeBound.cone_card_square
#print axioms Erdos713RigidConeBound.incidence_square
#print axioms Erdos713RigidConeBound.cone_incidence_square
