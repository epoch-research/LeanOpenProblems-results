import FormalConjecturesUtil
import Submission.ThetaZeroTriangle

/-! Zero-codegree families of arbitrary size. These are finite structural
results, not a rationality theorem for arbitrary forbidden graphs. -/
open Finset
namespace Erdos713ThetaZeroClique
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaHeavyShadow
open Erdos713ThetaAnchorPacking Erdos713ThetaDisjointSupports
open Erdos713ThetaZeroTriangle
variable {A B : Type*}
set_option maxHeartbeats 2000000

def ZeroClique (R : A → B → Prop) (s : ℕ) : Prop :=
  ∃ x : Fin s → B, Function.Injective x ∧
    ∀ i j, i ≠ j → codegree R (x i) (x j) = 0

noncomputable def lightCountAt (R : A → B → Prop) (s : ℕ) : ℕ :=
  Nat.card {p : B × B // codegree R p.1 p.2 < s}

lemma high_book_card_lt [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) {s : ℕ} (hz : ¬ ZeroClique R s) {p : B × B}
    (hp : p.1 ≠ p.2) (hh : 3 ≤ codegree R p.1 p.2) :
    (commonRows R (highRows R) p).card < s := by
  classical
  obtain ⟨x,_,hinj,hzero⟩ := exists_private_zero_family hf (highRows R) hp hh
    (fun a ha => (mem_filter.mp (mem_filter.mp ha).1).2)
  by_contra h
  have hc : Fintype.card (Fin s) ≤ Fintype.card ↥(commonRows R (highRows R) p) := by
    simp only [Fintype.card_fin,Fintype.card_coe]
    omega
  obtain ⟨f : Fin s ↪ ↥(commonRows R (highRows R) p)⟩ :=
    Function.Embedding.nonempty_of_card_le hc
  exact hz ⟨fun i => x (f i),hinj.comp f.injective,
    fun i j hij => hzero (f i) (f j) (fun he => hij (f.injective he))⟩

lemma heavy_at_has_small_row [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) {s : ℕ} (hs : 3 ≤ s) (hz : ¬ ZeroClique R s) {x y : B}
    (hxy : x ≠ y) (hh : s ≤ codegree R x y) :
    ∃ a : A, R a x ∧ R a y ∧ (row R a).card ≤ 3 := by
  classical
  by_contra h
  have hlarge : ∀ a, R a x → R a y → 4 ≤ (row R a).card := by
    intro a hx hy
    by_contra ha
    exact h ⟨a,hx,hy,by omega⟩
  have he : commonRows R (highRows R) (x,y) =
      (univ : Finset A).filter (fun a => R a x ∧ R a y) := by
    ext a
    simp only [commonRows,highRows,mem_filter,mem_univ,true_and]
    exact ⟨fun ha => ha.2,fun ha => ⟨hlarge a ha.1 ha.2,ha⟩⟩
  have hl := high_book_card_lt hf hz (p := (x,y)) hxy (hs.trans hh)
  rw [he] at hl
  have hh' : s ≤ ((univ : Finset A).filter (fun a => R a x ∧ R a y)).card := by
    simpa only [codegree,Nat.card_eq_fintype_card,Fintype.card_subtype] using hh
  omega

open scoped Classical in
noncomputable def heavyOffDiagAt [Fintype A] [Fintype B] (R : A → B → Prop) (s : ℕ) : Finset (B × B) :=
  univ.filter (fun p => p.1 ≠ p.2 ∧ s ≤ codegree R p.1 p.2)

/-- Only rows of degree at most three are charged, each by at most six
ordered distinct pairs. -/
theorem heavy_off_diag_at_le_six_rows [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) {s : ℕ} (hs : 3 ≤ s) (hz : ¬ ZeroClique R s) :
    (heavyOffDiagAt R s).card ≤ 6*Fintype.card A := by
  classical
  let S := (univ : Finset A).filter (fun a => (row R a).card ≤ 3)
  have hsub : heavyOffDiagAt R s ⊆ S.biUnion (fun a => (row R a).offDiag) := by
    intro p hp
    obtain ⟨a,ha1,ha2,ha⟩ := heavy_at_has_small_row hf hs hz (mem_filter.mp hp).2.1
      (mem_filter.mp hp).2.2
    exact mem_biUnion.mpr ⟨a,mem_filter.mpr ⟨mem_univ _,ha⟩,
      mem_offDiag.mpr ⟨(mem_row R _ _).mpr ha1,(mem_row R _ _).mpr ha2,
        (mem_filter.mp hp).2.1⟩⟩
  calc
    _ ≤ (S.biUnion (fun a => (row R a).offDiag)).card := card_le_card hsub
    _ ≤ ∑ a ∈ S, (row R a).offDiag.card := card_biUnion_le
    _ ≤ ∑ _a ∈ S, 6 := sum_le_sum (fun a ha =>
      small_row_pairs_le_six R a (mem_filter.mp ha).2)
    _ = S.card*6 := by simp
    _ ≤ Fintype.card A*6 := Nat.mul_le_mul_right 6 (card_le_univ S)
    _ = _ := by omega

/-- A quadratic density gap under an explicit zero-clique exclusion.
The light count includes ordered diagonal pairs. -/
theorem density_gap_at [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) {s : ℕ} (hs : 3 ≤ s) (hz : ¬ ZeroClique R s) :
    (Fintype.card B)^2 ≤ 12*Fintype.card A+2*lightCountAt R s := by
  classical
  let T : Finset (B × B) := univ.filter (fun p => codegree R p.1 p.2 < s)
  have hT : T.card = lightCountAt R s := by
    simp only [T,lightCountAt,Nat.card_eq_fintype_card,Fintype.card_subtype]
  have hsub : (univ : Finset B).offDiag ⊆ heavyOffDiagAt R s ∪ T := by
    intro p hp
    by_cases hh : s ≤ codegree R p.1 p.2
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,(mem_offDiag.mp hp).2.2,hh⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,by omega⟩)
  have hc := (card_le_card hsub).trans (card_union_le _ _)
  have hu := heavy_off_diag_at_le_six_rows hf hs hz
  rw [offDiag_card,card_univ,hT] at hc
  by_cases hk : 2 ≤ Fintype.card B
  · have h1 : Fintype.card B ≤ Fintype.card B*Fintype.card B := by
      nlinarith only [hk]
    have h2 := Nat.sub_add_cancel h1
    nlinarith only [hc,hu,hk,h2]
  · by_cases hm : 0 < Fintype.card A
    · have hsmall : Fintype.card B ≤ 1 := by omega
      nlinarith only [hsmall,hm]
    · have hempty : Fintype.card A = 0 := by omega
      letI : IsEmpty A := Fintype.card_eq_zero_iff.mp hempty
      have hz' (x y : B) : codegree R x y = 0 := by
        simp only [codegree,Nat.card_of_isEmpty]
      have ht : T = univ := by
        ext p
        simp only [T,mem_filter,mem_univ,hz',true_and]
        exact iff_true_intro (by omega)
      have he : lightCountAt R s = (Fintype.card B)^2 := by
        rw [← hT,ht,card_univ,Fintype.card_prod,pow_two]
      rw [he]
      omega

#print axioms high_book_card_lt
#print axioms heavy_at_has_small_row
#print axioms heavy_off_diag_at_le_six_rows
#print axioms density_gap_at
end Erdos713ThetaZeroClique
