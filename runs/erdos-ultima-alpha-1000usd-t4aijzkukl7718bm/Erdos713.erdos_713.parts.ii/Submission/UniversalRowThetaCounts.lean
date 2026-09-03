import FormalConjecturesUtil
import Submission.UniversalRowThetaExtension

/-! Exact root-link realization and counts for universal-row extensions.
Connectivity is available, but degree balance and extremality are not claimed. -/

open SimpleGraph
namespace Erdos713UniversalRowTheta
open Erdos713ThetaGram Erdos713ThetaThreePoint Erdos713GlobalTheta
open Erdos713C6 Erdos713ThetaSplit
set_option maxHeartbeats 1000000
variable {A B : Type*}

noncomputable def rootRows : A ≃ {a : Option A // a ≠ none} :=
  Equiv.ofBijective (fun a => ⟨some a,by simp⟩) ⟨by
    intro a b h
    exact Option.some.inj (congrArg Subtype.val h), by
    rintro ⟨a,ha⟩
    cases a with
    | none => exact (ha rfl).elim
    | some a => exact ⟨a,rfl⟩⟩

def rootColumns (R : A → B → Prop) : B ≃ {b : B // extension R none b} :=
  { toFun := fun b => ⟨b,True.intro⟩
    invFun := Subtype.val
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

lemma root_link (R : A → B → Prop) (a : A) (b : B) :
    link (extension R) none (rootRows a) (rootColumns R b) ↔ R a b := Iff.rfl

lemma theta_in_root_link {R : A → B → Prop} (h : HasTheta R) :
    HasTheta (link (extension R) none) := by
  obtain ⟨a,b,ha,hb,h00,h10,h01,h11,h02,h22,h13,h23⟩ := h
  exact ⟨rootRows ∘ a,rootColumns R ∘ b,rootRows.injective.comp ha,
    (rootColumns R).injective.comp hb,h00,h10,h01,h11,h02,h22,h13,h23⟩

/-- Under rigidity, this is an exact reduction from the local oriented
problem to freeness of the actual unoriented apex-theta graph. -/
theorem pattern_free_iff {R : A → B → Prop} (hR : Rigid3 R) :
    pattern.Free (bipGraph (extension R)) ↔ ¬ HasTheta R := by
  refine ⟨fun hf h => no_theta_links hf none (theta_in_root_link h), pattern_free hR⟩

lemma root_card [Fintype B] (R : A → B → Prop) :
    Nat.card {b : B // extension R none b} = Nat.card B :=
  (Nat.card_congr (rootColumns R)).symm

lemma old_row_card (R : A → B → Prop) (a : A) :
    Nat.card {b : B // extension R (some a) b} = Nat.card {b : B // R a b} := rfl

private def optionPredEquiv (P : A → Prop) :
    {a : Option A // a.elim True P} ≃ Option {a : A // P a} where
  toFun a := match a with
    | ⟨none,_⟩ => none
    | ⟨some a,ha⟩ => some ⟨a,ha⟩
  invFun a := match a with
    | none => ⟨none,True.intro⟩
    | some a => ⟨some a.val,a.property⟩
  left_inv := by rintro ⟨a,ha⟩; cases a <;> rfl
  right_inv := by intro a; cases a <;> rfl

lemma column_card [Fintype A] (R : A → B → Prop) (b : B) :
    Nat.card {a : Option A // extension R a b} = Nat.card {a : A // R a b}+1 := by
  classical
  let e : {a : Option A // extension R a b} ≃
      {a : Option A // a.elim True (fun a => R a b)} :=
    Equiv.subtypeEquivRight (by intro a; cases a <;> rfl)
  rw [Nat.card_congr (e.trans (optionPredEquiv (fun a => R a b)))]
  simp [Nat.card_eq_fintype_card]

lemma codegree_add_one [Fintype A] (R : A → B → Prop) (x y : B) :
    Erdos713GlobalLight.codegree (extension R) x y =
      Erdos713GlobalLight.codegree R x y+1 := by
  classical
  let e : {a : Option A // extension R a x ∧ extension R a y} ≃
      {a : Option A // a.elim True (fun a => R a x ∧ R a y)} :=
    Equiv.subtypeEquivRight (by intro a; cases a <;> simp [extension])
  unfold Erdos713GlobalLight.codegree
  rw [Nat.card_congr (e.trans (optionPredEquiv (fun a => R a x ∧ R a y)))]
  simp [Nat.card_eq_fintype_card]

lemma incidence_card [Fintype A] [Fintype B] (R : A → B → Prop) :
    Nat.card {p : Option A × B // extension R p.1 p.2} =
      Nat.card {p : A × B // R p.1 p.2}+Nat.card B := by
  classical
  rw [edge_card_eq_rows,Fintype.sum_option,root_card]
  simp only [old_row_card,← edge_card_eq_rows,Nat.add_comm]

lemma vertex_card [Fintype A] [Fintype B] :
    Nat.card (Option A ⊕ B) = Nat.card A+Nat.card B+1 := by
  simp [Nat.card_eq_fintype_card,Fintype.card_option,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

/-- With no empty old row, the extension is connected. The newly added row
itself supplies a vertex even if the original types are empty. -/
theorem connected {R : A → B → Prop} (hrow : ∀ a, ∃ b, R a b) :
    (bipGraph (extension R)).Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨.inl none,?_⟩
  rintro (a | b)
  · cases a with
    | none => exact Reachable.refl _
    | some a =>
      obtain ⟨b,hab⟩ := hrow a
      exact (show (bipGraph (extension R)).Adj (.inl none) (.inr b) from True.intro).reachable.trans
        (show (bipGraph (extension R)).Adj (.inr b) (.inl (some a)) from hab).reachable
  · exact (show (bipGraph (extension R)).Adj (.inl none) (.inr b) from True.intro).reachable

end Erdos713UniversalRowTheta
