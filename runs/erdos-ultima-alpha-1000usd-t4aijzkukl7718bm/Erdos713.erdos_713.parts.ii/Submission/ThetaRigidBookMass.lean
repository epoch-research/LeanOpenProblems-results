import FormalConjecturesUtil
import Submission.ThetaDisjointSupports

/-! A book bound using all private columns under triple-intersection rigidity.
This is a finite auxiliary estimate, not a rationality theorem. -/
open Finset
open scoped Classical
namespace Erdos713ThetaRigidBookMass
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaHeavyShadow
open Erdos713ThetaAnchorPacking Erdos713ThetaPrivatePetals Erdos713ThetaDisjointSupports
variable {A B : Type*}
set_option maxHeartbeats 2000000

lemma private_eq_sdiff [Fintype B] {R : A → B → Prop}
    (hR : ∀ a b, a ≠ b → (row R a ∩ row R b).card ≤ 2)
    (S : Finset A) {p : B × B} (hp : p.1 ≠ p.2)
    {a : A} (ha : a ∈ commonRows R S p) :
    privatePetal R S p a = row R a \ {p.1,p.2} := by
  ext x
  rw [mem_privatePetal]
  simp only [mem_sdiff,mem_row,mem_insert,mem_singleton,not_or]
  constructor
  · rintro ⟨hx,hx1,hx2,_⟩
    exact ⟨hx,hx1,hx2⟩
  · rintro ⟨hx,hx1,hx2⟩
    refine ⟨hx,hx1,hx2,?_⟩
    intro b hb hba hbx
    have ha' := (mem_filter.mp ha).2
    have hb' := (mem_filter.mp hb).2
    have hs : ({p.1,p.2,x} : Finset B) ⊆ row R a ∩ row R b := by
      intro z hz
      simp only [mem_insert,mem_singleton] at hz
      rcases hz with rfl | rfl | rfl <;> simp [mem_row,ha',hb',hx,hbx]
    have hc : ({p.1,p.2,x} : Finset B).card = 3 := by simp [hp,Ne.symm hx1,Ne.symm hx2]
    have hh := card_le_card hs
    have hlim := hR a b hba.symm
    omega

lemma private_card [Fintype B] {R : A → B → Prop}
    (hR : ∀ a b, a ≠ b → (row R a ∩ row R b).card ≤ 2)
    (S : Finset A) {p : B × B} (hp : p.1 ≠ p.2)
    {a : A} (ha : a ∈ commonRows R S p) :
    (privatePetal R S p a).card = (row R a).card-2 := by
  rw [private_eq_sdiff hR S hp ha,card_sdiff_of_subset]
  · simp [hp]
  · intro x hx
    have ha' := (mem_filter.mp ha).2
    simp only [mem_insert,mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [mem_row,ha']

abbrev Petals [Fintype B] (R : A → B → Prop) (S : Finset A) (p : B × B) :=
  (a : ↥(commonRows R S p)) × ↥(privatePetal R S p a.val)

/-- After excluding its own book row, a private column has lost exactly
one supporting row. -/
lemma outside_support_card [Fintype A] [Fintype B] (R : A → B → Prop)
    (S : Finset A) (p : B × B) (w : Petals R S p) :
    ((univ : Finset A).filter (fun b => b ≠ w.1.val ∧ R b w.2.val)).card+1 =
      Nat.card {b // R b w.2.val} := by
  have hx := (mem_privatePetal R S p w.1.val w.2.val).mp w.2.property
  let T := (univ : Finset A).filter (fun b => R b w.2.val)
  have ha : w.1.val ∈ T := mem_filter.mpr ⟨mem_univ _,hx.1⟩
  have he : (univ : Finset A).filter (fun b => b ≠ w.1.val ∧ R b w.2.val) =
      T.erase w.1.val := by
    ext b
    simp [T,and_comm]
  rw [he,card_erase_of_mem ha,Nat.sub_add_cancel (card_pos.mpr ⟨_,ha⟩)]
  simp only [T,Nat.card_eq_fintype_card,Fintype.card_subtype]

/-- Any other row can meet private petals from only one book row, and at
most two columns there. This uses the FULL theta exclusion. -/
theorem outside_mass_le [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R)
    (hR : ∀ a b, a ≠ b → (row R a ∩ row R b).card ≤ 2)
    (S : Finset A) {p : B × B} (hp : p.1 ≠ p.2) :
    (∑ w : Petals R S p,
      ((univ : Finset A).filter (fun b => b ≠ w.1.val ∧ R b w.2.val)).card) ≤
        2*Fintype.card A := by
  let Inc : Petals R S p → A → Prop := fun w b => b ≠ w.1.val ∧ R b w.2.val
  have hbelow (b : A) : ((univ : Finset (Petals R S p)).bipartiteBelow Inc b).card ≤ 2 := by
    let T := ((univ : Finset (Petals R S p)).bipartiteBelow Inc b)
    by_cases hT : T.Nonempty
    · obtain ⟨w₀,hw₀⟩ := hT
      have h₀ : b ≠ w₀.1.val ∧ R b w₀.2.val := (mem_filter.mp hw₀).2
      have heq (w : Petals R S p) (hw : w ∈ T) : w.1 = w₀.1 := by
        apply Subtype.ext
        by_contra ha
        have hz := private_cross_zero hf S hp w.1.property w₀.1.property ha
          w.2.property w₀.2.property
        exact not_common_of_codegree_zero hz b ⟨(mem_filter.mp hw).2.2,h₀.2⟩
      have hmaps (w : Petals R S p) (hw : w ∈ T) :
          w.2.val ∈ row R w₀.1.val ∩ row R b := by
        have hx := (mem_privatePetal R S p w.1.val w.2.val).mp w.2.property
        have he := congrArg Subtype.val (heq w hw)
        refine mem_inter.mpr ⟨(mem_row _ _ _).mpr ?_,
          (mem_row _ _ _).mpr (mem_filter.mp hw).2.2⟩
        simpa only [he] using hx.1
      have hi : Set.InjOn (fun w : Petals R S p => w.2.val) (T : Set (Petals R S p)) := by
        intro w hw v hv he
        have ha : w.1 = v.1 := (heq w hw).trans (heq v hv).symm
        cases w with
        | mk a x =>
          cases v with
          | mk a' y =>
            dsimp at ha he ⊢
            subst a'
            exact Sigma.ext rfl (heq_of_eq (Subtype.ext he))
      exact (card_le_card_of_injOn _ hmaps hi).trans (hR _ _ h₀.1.symm)
    · have he : T = ∅ := not_nonempty_iff_eq_empty.mp hT
      change T.card ≤ 2
      simp [he]
  calc
    _ = ∑ w : Petals R S p, ((univ : Finset A).bipartiteAbove Inc w).card := rfl
    _ = ∑ b : A, ((univ : Finset (Petals R S p)).bipartiteBelow Inc b).card :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow Inc
    _ ≤ ∑ _b : A, 2 := sum_le_sum (fun b _ => hbelow b)
    _ = _ := by simp [Nat.mul_comm]

/-- All private columns, rather than just one representative per book row,
contribute to this bound. Original column degrees are used. -/
theorem book_mass_bound [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R)
    (hR : ∀ a b, a ≠ b → (row R a ∩ row R b).card ≤ 2)
    (S : Finset A) {p : B × B} (hp : p.1 ≠ p.2)
    (r d : ℕ) (hmin : ∀ a ∈ commonRows R S p, r ≤ (row R a).card)
    (hd : ∀ x : B, d ≤ Nat.card {a // R a x}) :
    (commonRows R S p).card*(r-2)*(d-1) ≤ 2*Fintype.card A := by
  have hcount : (commonRows R S p).card*(r-2) ≤ Fintype.card (Petals R S p) := by
    simp only [Petals,Fintype.card_sigma,Fintype.card_coe]
    calc
      _ = ∑ _a : ↥(commonRows R S p), (r-2) := by simp
      _ ≤ _ := sum_le_sum (fun a _ => by
        rw [private_card hR S hp a.property]
        exact Nat.sub_le_sub_right (hmin a.val a.property) 2)
  have hs : Fintype.card (Petals R S p)*(d-1) ≤
      ∑ w : Petals R S p,
        ((univ : Finset A).filter (fun b => b ≠ w.1.val ∧ R b w.2.val)).card := by
    calc
      _ = ∑ _w : Petals R S p, (d-1) := by simp
      _ ≤ _ := sum_le_sum (fun w _ => by
        have hh := outside_support_card R S p w
        have hm := hd w.2.val
        omega)
  exact (Nat.mul_le_mul_right (d-1) hcount).trans
    (hs.trans (outside_mass_le hf hR S hp))

#print axioms private_card
#print axioms outside_mass_le
#print axioms book_mass_bound
end Erdos713ThetaRigidBookMass
