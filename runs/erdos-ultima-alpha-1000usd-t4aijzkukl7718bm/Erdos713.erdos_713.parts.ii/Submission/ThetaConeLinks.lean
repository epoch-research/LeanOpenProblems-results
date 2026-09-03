import FormalConjecturesUtil
import Submission.ThetaThreePointRigidity
import Submission.ThetaZeroLinks

/-! Adjoining a universal row preserves both apex-theta link exclusions
for a theta-free relation with three-common-column rigidity. -/
namespace Erdos713ThetaConeLinks
open Erdos713ThetaGram Erdos713ThetaThreePoint Erdos713ThetaZeroLinks
open Erdos713ThetaPrivatePetals
variable {A B C D : Type*}
set_option maxHeartbeats 2000000

def cone (R : A → B → Prop) : Option A → B → Prop
  | none, _ => True
  | some a, b => R a b

lemma no_theta_of_maps {R : A → B → Prop} {S : C → D → Prop}
    (hR : ¬ HasTheta R) (p : C → A) (q : D → B)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hmap : ∀ a b, S a b → R (p a) (q b)) : ¬ HasTheta S := by
  rintro ⟨f,g,hf,hg,h00,h10,h01,h11,h02,h22,h13,h23⟩
  exact hR ⟨p ∘ f,q ∘ g,hp.comp hf,hq.comp hg,
    hmap _ _ h00,hmap _ _ h10,hmap _ _ h01,hmap _ _ h11,
    hmap _ _ h02,hmap _ _ h22,hmap _ _ h13,hmap _ _ h23⟩

lemma row_link_projection (R : A → B → Prop) (d : Option A) :
    ∃ p : {a : Option A // a ≠ d} → A, Function.Injective p ∧
      ∀ a b, link (cone R) d a b → R (p a) b.val := by
  cases d with
  | none =>
    let p : {a : Option A // a ≠ none} → A := fun a => match a with
      | ⟨none,h⟩ => (h rfl).elim
      | ⟨some a,_⟩ => a
    refine ⟨p,?_,?_⟩
    · rintro ⟨a,ha⟩ ⟨b,hb⟩ he
      cases a with
      | none => exact (ha rfl).elim
      | some a =>
        cases b with
        | none => exact (hb rfl).elim
        | some b => exact Subtype.ext (congrArg some he)
    · rintro ⟨a,ha⟩ b he
      cases a with
      | none => exact (ha rfl).elim
      | some a => exact he
  | some d =>
    let p : {a : Option A // a ≠ some d} → A := fun a => a.val.getD d
    refine ⟨p,?_,?_⟩
    · rintro ⟨a,ha⟩ ⟨b,hb⟩ he
      cases a with
      | none =>
        cases b with
        | none => rfl
        | some b =>
          change d = b at he
          exact (hb (congrArg some he.symm)).elim
      | some a =>
        cases b with
        | none =>
          change a = d at he
          exact (ha (congrArg some he)).elim
        | some b => exact Subtype.ext (congrArg some he)
    · rintro ⟨a,ha⟩ b he
      cases a with
      | none => exact b.property
      | some a => exact he

lemma no_theta_row_links {R : A → B → Prop} (hR : ¬ HasTheta R) (d : Option A) :
    ¬ HasTheta (link (cone R) d) := by
  obtain ⟨p,hp,hmap⟩ := row_link_projection R d
  exact no_theta_of_maps hR p Subtype.val hp Subtype.val_injective hmap

lemma no_theta_column_links {R : A → B → Prop} (hR : ¬ HasTheta R)
    (hRigid : Rigid3 R) (d : B) :
    ¬ HasTheta (link (fun b a => cone R a b) d) := by
  classical
  rintro ⟨f,g,hf,hg,h00,h10,h01,h11,h02,h22,h13,h23⟩
  have hfi := Subtype.val_injective.comp hf
  have hgi := Subtype.val_injective.comp hg
  have old (j : Fin 4) (hj : (g j).val ≠ none) : ∃ a : A, (g j).val = some a := by
    cases he : (g j).val with
    | none => exact (hj he).elim
    | some a => exact ⟨a,rfl⟩
  have incidence {j : Fin 4} {a : A} (he : (g j).val = some a) :
      R a d ∧ ∀ i, link (fun b a => cone R a b) d (f i) (g j) → R a (f i).val := by
    refine ⟨?_,?_⟩
    · have hh := (g j).property
      change cone R (g j).val d at hh
      simpa only [he,cone] using hh
    · intro i hi
      change cone R (g j).val (f i).val at hi
      simpa only [he,cone] using hi
  have hNone : (g 0).val = none ∨ (g 1).val = none := by
    by_contra hn
    push_neg at hn
    obtain ⟨a,ha⟩ := old 0 hn.1
    obtain ⟨b,hb⟩ := old 1 hn.2
    have hai := incidence ha
    have hbi := incidence hb
    have hab : a = b := by
      apply hRigid a b ![d,(f 0).val,(f 1).val]
      · intro i j he
        have h0 := (f 0).property
        have h1 := (f 1).property
        have h01 : (f 0).val ≠ (f 1).val := fun he => (by decide : (0 : Fin 3) ≠ 1) (hfi he)
        fin_cases i <;> fin_cases j <;> simp_all
      · intro i
        fin_cases i
        · exact hai.1
        · exact hai.2 0 h00
        · exact hai.2 1 h10
      · intro i
        fin_cases i
        · exact hbi.1
        · exact hbi.2 0 h01
        · exact hbi.2 1 h11
    exact (by decide : (0 : Fin 4) ≠ 1) (hgi ((ha.trans (congrArg some hab)).trans hb.symm))
  have hOldPetal (j : Fin 4) (hj0 : j ≠ 0) (hj1 : j ≠ 1) : (g j).val ≠ none := by
    intro hj
    rcases hNone with h0 | h1
    · exact hj0 (hgi (hj.trans h0.symm))
    · exact hj1 (hgi (hj.trans h1.symm))
  obtain ⟨b,hb⟩ := old 2 (hOldPetal 2 (by decide) (by decide))
  obtain ⟨c,hc⟩ := old 3 (hOldPetal 3 (by decide) (by decide))
  obtain ⟨j,hj,a,ha⟩ : ∃ j : Fin 4, (j = 0 ∨ j = 1) ∧ ∃ a : A, (g j).val = some a := by
    by_cases h0 : (g 0).val = none
    · have h1 : (g 1).val ≠ none := fun h1 => (by decide : (1 : Fin 4) ≠ 0) (hgi (h1.trans h0.symm))
      obtain ⟨a,ha⟩ := old 1 h1
      exact ⟨1,Or.inr rfl,a,ha⟩
    · obtain ⟨a,ha⟩ := old 0 h0
      exact ⟨0,Or.inl rfl,a,ha⟩
  have hbc : b ≠ c := fun he => (by decide : (2 : Fin 4) ≠ 3)
    (hgi ((hb.trans (congrArg some he)).trans hc.symm))
  have hab : a ≠ b := by
    intro he
    have hh : j = 2 := hgi ((ha.trans (congrArg some he)).trans hb.symm)
    rcases hj with rfl | rfl <;> contradiction
  have hac : a ≠ c := by
    intro he
    have hh : j = 3 := hgi ((ha.trans (congrArg some he)).trans hc.symm)
    rcases hj with rfl | rfl <;> contradiction
  have hai := incidence ha
  have hbi := incidence hb
  have hci := incidence hc
  have ha0 : R a (f 0).val := by
    rcases hj with rfl | rfl
    · exact hai.2 0 h00
    · exact hai.2 0 h01
  have ha1 : R a (f 1).val := by
    rcases hj with rfl | rfl
    · exact hai.2 1 h10
    · exact hai.2 1 h11
  have hne (i j : Fin 3) (hij : i ≠ j) : (f i).val ≠ (f j).val := fun he => hij (hfi he)
  apply hR
  exact theta_of_rows hbc hab hac (f 2).property.symm
    (f 0).property (hne 0 2 (by decide)) (f 1).property (hne 1 2 (by decide))
    (hne 0 1 (by decide)) hbi.1 (hbi.2 2 h22) hci.1 (hci.2 2 h23)
    (hbi.2 0 h02) (hci.2 1 h13) ha0 ha1

/-- Both exclusions concern the same cone relation. This says nothing
about degree regularity or exact extremality of the cone. -/
theorem both_links {R : A → B → Prop} (hR : ¬ HasTheta R) (hRigid : Rigid3 R) :
    (∀ d, ¬ HasTheta (link (cone R) d)) ∧
    (∀ d, ¬ HasTheta (link (fun b a => cone R a b) d)) :=
  ⟨no_theta_row_links hR,no_theta_column_links hR hRigid⟩

#print axioms no_theta_row_links
#print axioms no_theta_column_links
#print axioms both_links
end Erdos713ThetaConeLinks
