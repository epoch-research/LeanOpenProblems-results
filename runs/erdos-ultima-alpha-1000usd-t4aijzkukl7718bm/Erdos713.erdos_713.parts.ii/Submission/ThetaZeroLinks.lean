import FormalConjecturesUtil
import Submission.ThetaZeroAlternative

/-! The zero-pair budget of punctured links is the global singleton-codegree budget. -/
open Finset
namespace Erdos713ThetaZeroLinks
open Erdos713GlobalLight Erdos713ThetaZeroPairs
variable {A B : Type*}
set_option maxHeartbeats 2000000

def link (R : A → B → Prop) (a : A) :
    {x : A // x ≠ a} → {b : B // R a b} → Prop := fun x b => R x.val b.val

lemma card_restrict_ne_add_one [Fintype A]
    (P : A → Prop) (d : A) (hd : P d) :
    Nat.card {a : {a : A // a ≠ d} // P a.val}+1 = Nat.card {a : A // P a} := by
  classical
  rw [Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun a => a ≠ d) P)]
  simp only [Nat.card_eq_fintype_card,Fintype.card_subtype]
  have he : (univ.filter (fun a => a ≠ d ∧ P a)) = (univ.filter P).erase d := by
    ext a
    simp [and_comm]
  rw [he]
  exact card_erase_add_one (by simp [hd])

lemma link_codegree_add_one [Fintype A]
    (R : A → B → Prop) (d : A) (x y : {b : B // R d b}) :
    codegree (link R d) x y+1 = codegree R x.val y.val :=
  card_restrict_ne_add_one (fun a => R a x.val ∧ R a y.val) d ⟨x.property,y.property⟩

lemma link_column_add_one [Fintype A]
    (R : A → B → Prop) (d : A) (x : {b : B // R d b}) :
    Nat.card {a : {a : A // a ≠ d} // link R d a x}+1 = Nat.card {a : A // R a x.val} :=
  card_restrict_ne_add_one (fun a => R a x.val) d x.property

open scoped Classical in
noncomputable def singleSet [Fintype A] [Fintype B] (R : A → B → Prop) : Finset (B × B) :=
  univ.filter (fun p => codegree R p.1 p.2 = 1)

open scoped Classical in
noncomputable def singleAt [Fintype A] [Fintype B] (R : A → B → Prop) (a : A) : Finset (B × B) :=
  univ.filter (fun p => R a p.1 ∧ R a p.2 ∧ codegree R p.1 p.2 = 1)

open scoped Classical in
lemma link_zeroSet_card [Fintype A] [Fintype B] (R : A → B → Prop) (d : A) :
    (zeroSet (link R d)).card = (singleAt R d).card := by
  classical
  let e : {p : {b : B // R d b} × {b : B // R d b} // codegree (link R d) p.1 p.2 = 0} ≃
      ↥(singleAt R d) :=
    { toFun := fun p => ⟨(p.val.1.val,p.val.2.val),by
        have hc := link_codegree_add_one R d p.val.1 p.val.2
        have hp := p.property
        simp only [singleAt,mem_filter,mem_univ,true_and]
        exact ⟨p.val.1.property,p.val.2.property,by omega⟩⟩
      invFun := fun p => by
        have hp := p.property
        simp only [singleAt,mem_filter,mem_univ,true_and] at hp
        let x : {b : B // R d b} := ⟨p.val.1,hp.1⟩
        let y : {b : B // R d b} := ⟨p.val.2,hp.2.1⟩
        exact ⟨(x,y),by
          change codegree (link R d) x y = 0
          have hc := link_codegree_add_one R d x y
          have hp' : codegree R x.val y.val = 1 := hp.2.2
          omega⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simpa [zeroSet,Nat.card_eq_fintype_card,Fintype.card_subtype] using Nat.card_congr e

open scoped Classical in
lemma sum_singleAt [Fintype A] [Fintype B] (R : A → B → Prop) :
    (∑ a, (singleAt R a).card) = (singleSet R).card := by
  classical
  let Inc : A → B × B → Prop := fun a p => R a p.1 ∧ R a p.2
  have ha (a : A) : (singleSet R).bipartiteAbove Inc a = singleAt R a := by
    ext p
    simp only [bipartiteAbove,singleSet,singleAt,mem_filter,mem_univ,true_and,Inc]
    tauto
  have hb (p : B × B) (hp : p ∈ singleSet R) :
      ((univ : Finset A).bipartiteBelow Inc p).card = 1 := by
    have hh : ((univ : Finset A).bipartiteBelow Inc p).card = codegree R p.1 p.2 := by
      simp [bipartiteBelow,Inc,codegree,Nat.card_eq_fintype_card,Fintype.card_subtype]
    exact hh.trans (mem_filter.mp hp).2
  calc
    _ = ∑ a, ((singleSet R).bipartiteAbove Inc a).card := by simp only [ha]
    _ = ∑ p ∈ singleSet R, ((univ : Finset A).bipartiteBelow Inc p).card :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow Inc
    _ = ∑ _p ∈ singleSet R, 1 := sum_congr rfl hb
    _ = _ := by simp

open scoped Classical in
lemma sum_link_zeroSet [Fintype A] [Fintype B] (R : A → B → Prop) :
    (∑ a, (zeroSet (link R a)).card) = (singleSet R).card := by
  simp only [link_zeroSet_card,sum_singleAt]

open scoped Classical in
lemma exists_row_with_few_zero_pairs [Fintype A] [Fintype B] [Nonempty A]
    (R : A → B → Prop) :
    ∃ a : A, Fintype.card A*(zeroSet (link R a)).card ≤ (singleSet R).card := by
  classical
  obtain ⟨a,_,ha⟩ := (univ : Finset A).exists_min_image (fun a => (zeroSet (link R a)).card)
    (univ_nonempty)
  refine ⟨a,?_⟩
  calc
    Fintype.card A*(zeroSet (link R a)).card = ∑ _b : A, (zeroSet (link R a)).card := by simp
    _ ≤ ∑ b : A, (zeroSet (link R b)).card := sum_le_sum (fun b _ => ha b (mem_univ _))
    _ = _ := sum_link_zeroSet R

#print axioms link_zeroSet_card
#print axioms sum_link_zeroSet
#print axioms exists_row_with_few_zero_pairs
end Erdos713ThetaZeroLinks
