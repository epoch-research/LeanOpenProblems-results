import FormalConjecturesUtil
import Submission.ThetaZeroPairs

/-! Private petals in a heavy book have disjoint sets of supporting rows.
These finite bounds do not settle the general rational-exponent conjecture. -/
open Finset
namespace Erdos713ThetaDisjointSupports
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaHeavyShadow
open Erdos713ThetaAnchorPacking Erdos713ThetaPrivatePetals Erdos713ThetaZeroPairs
variable {A B : Type*}
set_option maxHeartbeats 2000000

lemma not_common_of_codegree_zero [Fintype A] {R : A → B → Prop}
    {x y : B} (h : codegree R x y = 0) (a : A) : ¬ (R a x ∧ R a y) := by
  classical
  intro ha
  letI : Nonempty {a // R a x ∧ R a y} := ⟨⟨a,ha⟩⟩
  have hp : 0 < codegree R x y := by
    simpa only [codegree,Nat.card_eq_fintype_card] using
      (Fintype.card_pos : 0 < Fintype.card {a // R a x ∧ R a y})
  omega

/-- The degree sum of a family of columns with pairwise zero codegree
is at most the number of rows. The indexing map need not be injective:
any repeated column must itself have degree zero. -/
theorem sum_column_degrees_le_rows [Fintype A] {I : Type*} [Fintype I]
    (R : A → B → Prop) (x : I → B)
    (hz : ∀ i j, i ≠ j → codegree R (x i) (x j) = 0) :
    (∑ i : I, Nat.card {a // R a (x i)}) ≤ Fintype.card A := by
  classical
  let T := (i : I) × {a // R a (x i)}
  let f : T → A := fun t => t.2.val
  have hf : Function.Injective f := by
    rintro ⟨i,a⟩ ⟨j,b⟩ he
    have hab : a.val = b.val := he
    have hij : i = j := by
      by_contra hn
      exact not_common_of_codegree_zero (hz i j hn) a.val
        ⟨a.property,hab ▸ b.property⟩
    subst j
    exact Sigma.ext rfl (heq_of_eq (Subtype.ext hab))
  have hc := Fintype.card_le_of_injective f hf
  simpa only [T,Fintype.card_sigma,Nat.card_eq_fintype_card] using hc

/-- Private petals belonging to distinct rows of one book have codegree
zero in the ORIGINAL relation, not just in its retained restriction. -/
theorem private_cross_zero [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (S : Finset A) {p : B × B}
    (hp : p.1 ≠ p.2) {a b : A} (ha : a ∈ commonRows R S p)
    (hb : b ∈ commonRows R S p) (hab : a ≠ b) {x y : B}
    (hx : x ∈ privatePetal R S p a) (hy : y ∈ privatePetal R S p b) :
    codegree R x y = 0 := by
  classical
  have hx' := (mem_privatePetal R S p a x).mp hx
  have hy' := (mem_privatePetal R S p b y).mp hy
  have ha' := (mem_filter.mp ha).2
  have hb' := (mem_filter.mp hb).2
  exact cross_codegree_zero hf hab hp ha'.1 ha'.2 hb'.1 hb'.2
    hx'.1 (hx'.2.2.2 b hb hab.symm) hy'.1 (hy'.2.2.2 a ha hab)

/-- Select one private petal per retained book row. At minimum row degree
four this gives an injective zero-codegree family of the same size as the book. -/
theorem exists_private_zero_family [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (S : Finset A) {p : B × B}
    (hp : p.1 ≠ p.2) (hh : 3 ≤ codegree R p.1 p.2)
    (hmin : ∀ a ∈ commonRows R S p, 4 ≤ (row R a).card) :
    ∃ x : ↥(commonRows R S p) → B,
      (∀ a, x a ∈ privatePetal R S p a.val) ∧ Function.Injective x ∧
      ∀ a b, a ≠ b → codegree R (x a) (x b) = 0 := by
  classical
  have hex (a : ↥(commonRows R S p)) : (privatePetal R S p a.val).Nonempty := by
    have hdeg := hmin a.val a.property
    have hl := privatePetal_card_lower hf S hp hh (mem_filter.mp a.property).2
    exact card_pos.mp (by omega)
  choose x hx using hex
  have hz (a b : ↥(commonRows R S p)) (hab : a ≠ b) :
      codegree R (x a) (x b) = 0 :=
    private_cross_zero hf S hp a.property b.property
      (fun he => hab (Subtype.ext he)) (hx a) (hx b)
  refine ⟨x,hx,?_,hz⟩
  intro a b he
  by_contra hab
  have ha := (mem_privatePetal R S p a.val (x a)).mp (hx a)
  exact not_common_of_codegree_zero (hz a b hab) a.val
    ⟨ha.1,he ▸ ha.1⟩

/-- A lower column-degree bound controls the number of large retained
rows through any original heavy anchor pair. -/
theorem book_size_mul_min_column_le_rows [Fintype A] [Fintype B]
    {R : A → B → Prop} (hf : ¬ HasTheta R) (S : Finset A) {p : B × B}
    (hp : p.1 ≠ p.2) (hh : 3 ≤ codegree R p.1 p.2)
    (hmin : ∀ a ∈ commonRows R S p, 4 ≤ (row R a).card)
    (d : ℕ) (hd : ∀ x : B, d ≤ Nat.card {a // R a x}) :
    (commonRows R S p).card*d ≤ Fintype.card A := by
  classical
  obtain ⟨x,_,_,hz⟩ := exists_private_zero_family hf S hp hh hmin
  calc
    _ = ∑ _a : ↥(commonRows R S p), d := by simp
    _ ≤ ∑ a : ↥(commonRows R S p), Nat.card {b // R b (x a)} :=
      sum_le_sum (fun a _ => hd (x a))
    _ ≤ _ := sum_column_degrees_le_rows R x hz

#print axioms sum_column_degrees_le_rows
#print axioms private_cross_zero
#print axioms exists_private_zero_family
#print axioms book_size_mul_min_column_le_rows
end Erdos713ThetaDisjointSupports
