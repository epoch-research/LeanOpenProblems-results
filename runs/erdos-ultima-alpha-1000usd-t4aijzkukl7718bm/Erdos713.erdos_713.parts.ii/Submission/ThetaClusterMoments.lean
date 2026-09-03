import FormalConjecturesUtil
import Submission.ThetaClusterHighRows
import Submission.ThetaCrossCompletion

/-! A conditional quadratic incidence bound when the light graph is a
union of complete graphs. The partition hypothesis is not asserted in general. -/
open Finset
open scoped Classical
namespace Erdos713ThetaCluster
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaHeavyShadow Erdos713ThetaCross
variable {A B I : Type*}
set_option maxHeartbeats 2000000

noncomputable def intraPairs (S : Finset B) (τ : B → I) : Finset (B × B) :=
  S.offDiag.filter (fun p => τ p.1 = τ p.2)

lemma fiber_square_sum (S : Finset B) (τ : B → I) :
    (∑ i ∈ S.image τ, (S.filter (fun x => τ x = i)).card^2) = S.card+(intraPairs S τ).card := by
  let Q := (S ×ˢ S).filter (fun p => τ p.1 = τ p.2)
  have hf (p : B × B) (hp : p ∈ Q) : τ p.1 ∈ S.image τ :=
    mem_image_of_mem τ (mem_product.mp (mem_filter.mp hp).1).1
  have hF (i : I) : Q.filter (fun p => τ p.1 = i) =
      (S.filter (fun x => τ x = i)) ×ˢ (S.filter (fun x => τ x = i)) := by
    ext p
    simp only [Q,mem_filter,mem_product]
    aesop
  have hcard := card_eq_sum_card_fiberwise hf
  simp only [hF,card_product,← pow_two] at hcard
  rw [show Q = intraPairs S τ ∪ S.diag by
    ext p
    simp only [Q,intraPairs,mem_filter,mem_product,mem_union,mem_offDiag,mem_diag]
    by_cases h : p.1 = p.2 <;> simp_all] at hcard
  have hdis : Disjoint (intraPairs S τ) S.diag := by
    apply disjoint_left.mpr
    intro p hp hq
    exact (mem_offDiag.mp (mem_filter.mp hp).1).2.2 (mem_diag.mp hq).2
  rw [card_union_of_disjoint hdis,diag_card] at hcard
  simpa only [Nat.add_comm] using hcard.symm

lemma few_blocks_square (S : Finset B) (τ : B → I) (h : (S.image τ).card ≤ 3) :
    S.card^2 ≤ 3*(S.card+(intraPairs S τ).card) := by
  have hsum : S.card = ∑ i ∈ S.image τ, (S.filter (fun x => τ x = i)).card :=
    card_eq_sum_card_fiberwise (fun x hx => mem_image_of_mem τ hx)
  have hc := sum_mul_sq_le_sq_mul_sq (S.image τ)
    (fun _ : I => (1 : ℕ)) (fun i => (S.filter (fun x => τ x = i)).card)
  simp only [one_mul,one_pow,sum_const,Nat.nsmul_eq_mul,mul_one,← hsum] at hc
  exact hc.trans ((Nat.mul_le_mul_right _ h).trans_eq (by rw [fiber_square_sum]))

def SameLight (R : A → B → Prop) (τ : B → I) : Prop :=
  ∀ x y, x ≠ y → τ x = τ y → codegree R x y ≤ 2

lemma intra_budget [Fintype A] [Fintype B] (R : A → B → Prop) (τ : B → I)
    (hl : SameLight R τ) :
    (∑ a : A, (intraPairs (row R a) τ).card) ≤ 2*lightCount R := by
  let L : Finset (B × B) := univ.filter (fun p => codegree R p.1 p.2 ≤ 2)
  let Inc : A → B × B → Prop := fun a p =>
    R a p.1 ∧ R a p.2 ∧ p.1 ≠ p.2 ∧ τ p.1 = τ p.2
  have ha (a : A) : L.bipartiteAbove Inc a = intraPairs (row R a) τ := by
    ext p
    simp only [L,bipartiteAbove,intraPairs,mem_filter,mem_univ,true_and,
      mem_offDiag,mem_row,Inc]
    constructor
    · tauto
    · rintro ⟨⟨h1,h2,hne⟩,he⟩
      exact ⟨hl p.1 p.2 hne he,h1,h2,hne,he⟩
  have hb (p : B × B) (hp : p ∈ L) : ((univ : Finset A).bipartiteBelow Inc p).card ≤ 2 := by
    have hc : codegree R p.1 p.2 ≤ 2 := (mem_filter.mp hp).2
    have hsub : (univ : Finset A).bipartiteBelow Inc p ⊆
        univ.filter (fun a => R a p.1 ∧ R a p.2) := by
      intro a ha
      exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp ha).2.1,(mem_filter.mp ha).2.2.1⟩
    apply (card_le_card hsub).trans
    simpa only [codegree,Nat.card_eq_fintype_card,Fintype.card_subtype] using hc
  have hL : L.card = lightCount R := by
    simp only [L,lightCount,Nat.card_eq_fintype_card,Fintype.card_subtype]
  calc
    _ = ∑ a : A, (L.bipartiteAbove Inc a).card := by simp only [ha]
    _ = ∑ p ∈ L, ((univ : Finset A).bipartiteBelow Inc p).card :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow Inc
    _ ≤ ∑ _p ∈ L, 2 := sum_le_sum hb
    _ = 2*lightCount R := by simp [hL,Nat.mul_comm]

lemma numeric_moment {e m x t : ℝ} (he : 0 ≤ e)
    (hE : e ≤ 2*m+x) (hX : x^2 ≤ m*(3*x+6*t)) :
    e^2 ≤ 26*m^2+24*m*t := by
  have hx2 : x^2 ≤ 9*m^2+12*m*t := by nlinarith [sq_nonneg (x-3*m)]
  have he2 : e^2 ≤ (2*m+x)^2 := pow_le_pow_left₀ he hE 2
  nlinarith [sq_nonneg (2*m-x)]

lemma incidence_square_le [Fintype A] [Fintype B] {R : A → B → Prop} {τ : B → I}
    (hf : ¬ HasTheta R) (hh : CrossHeavy R τ) (hl : SameLight R τ) :
    (∑ a : A, (row R a).card)^2 ≤
      26*(Fintype.card A)^2+24*Fintype.card A*lightCount R := by
  let U := (univ : Finset A) \ manyBlocks R τ
  let m := Fintype.card A
  let x := ∑ a ∈ U, (row R a).card
  let e := ∑ a : A, (row R a).card
  let t := lightCount R
  have hU : U.card ≤ m := (card_le_card (subset_univ _)).trans_eq (card_univ)
  have hsplit : e ≤ 2*m+x := by
    have he : e = (∑ a ∈ manyBlocks R τ, (row R a).card)+x := by
      exact (sum_add_sum_compl (manyBlocks R τ) (fun a => (row R a).card)).symm
    rw [he]
    exact Nat.add_le_add_right (high_incidence_le hf hh) x
  have hsquare : (∑ a ∈ U, (row R a).card^2) ≤ 3*x+6*t := by
    have hp (a : A) (ha : a ∈ U) : (row R a).card^2 ≤
        3*((row R a).card+(intraPairs (row R a) τ).card) := by
      apply few_blocks_square
      have hh : ¬ 4 ≤ (blocks R τ a).card := by
        simpa only [manyBlocks,mem_filter,mem_univ,true_and] using (mem_sdiff.mp ha).2
      change (blocks R τ a).card ≤ 3
      omega
    have hi : (∑ a ∈ U, (intraPairs (row R a) τ).card) ≤ 2*t :=
      (sum_le_sum_of_subset (subset_univ _)).trans (intra_budget R τ hl)
    have hs := sum_le_sum hp
    simp only [mul_add,sum_add_distrib,← mul_sum] at hs
    dsimp only [x]
    nlinarith
  have hc := sum_mul_sq_le_sq_mul_sq U (fun _ : A => (1 : ℕ)) (fun a => (row R a).card)
  have hx2 : x^2 ≤ m*(3*x+6*t) := by
    simp only [one_mul,one_pow,sum_const,Nat.nsmul_eq_mul,mul_one] at hc
    exact hc.trans (Nat.mul_le_mul hU hsquare)
  have hr : (e : ℝ)^2 ≤ 26*(m : ℝ)^2+24*(m : ℝ)*(t : ℝ) :=
    numeric_moment (x := (x : ℝ)) (Nat.cast_nonneg _)
      (by exact_mod_cast hsplit) (by exact_mod_cast hx2)
  exact_mod_cast hr

#print axioms few_blocks_square
#print axioms intra_budget
#print axioms incidence_square_le
end Erdos713ThetaCluster
