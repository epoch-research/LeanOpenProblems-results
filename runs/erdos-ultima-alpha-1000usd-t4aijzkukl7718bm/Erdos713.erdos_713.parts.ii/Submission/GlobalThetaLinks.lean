import FormalConjecturesUtil
import Submission.CompactEdgeAttachmentsAudit
import Submission.ThetaGram
import Submission.GlobalLightPairs

/-! Exact whole-host link restrictions for the eight-vertex apex-theta
pattern. These restrictions do not yet give a sharp extremal bound. -/
open SimpleGraph Finset
namespace Erdos713GlobalTheta
set_option maxHeartbeats 2000000
open Erdos713ThetaGram Erdos713C6

/-- Rows 0,1 have the two common columns 0,1; row 2 joins columns 2,3. -/
def thetaRel (i : Fin 3) (j : Fin 4) : Prop :=
  Nat.testBit ((![7,11,12] : Fin 3 → ℕ) i) j.val = true

def apexRel (i : Option (Fin 3)) (j : Fin 4) : Prop := i.elim True (fun i => thetaRel i j)
abbrev pattern := bipGraph apexRel

def link {A B : Type*} (R : A → B → Prop) (d : A) :
    {a : A // a ≠ d} → {b : B // R d b} → Prop := fun a b => R a.val b.val

lemma pattern_contained_of_link {A B : Type*} (R : A → B → Prop) (d : A)
    (h : HasTheta (link R d)) : pattern ⊑ bipGraph R := by
  obtain ⟨a,b,ha,hb,h00,h10,h01,h11,h02,h22,h13,h23⟩ := h
  let f : Option (Fin 3) → A := fun i => i.elim d (fun i => (a i).val)
  have hf : Function.Injective f := Erdos713Theta3.option_injective d
    (fun i => (a i).val) (Subtype.val_injective.comp ha) (fun i => (a i).prop.symm)
  apply Erdos713Anchors.bipGraph_contained_of_maps apexRel (bipGraph R)
    (fun i => .inl (f i)) (fun j => .inr (b j).val)
    (Sum.inl_injective.comp hf) (Sum.inr_injective.comp (Subtype.val_injective.comp hb))
    (fun _ _ => Sum.inl_ne_inr) _
  intro i j hij
  cases i with
  | none => exact (b j).prop
  | some i =>
    change thetaRel i j at hij
    fin_cases i <;> fin_cases j <;> simp [thetaRel] at hij <;> first | contradiction | assumption

lemma no_theta_links {A B : Type*} {R : A → B → Prop} (h : pattern.Free (bipGraph R)) (d : A) :
    ¬ HasTheta (link R d) := fun hh => h (pattern_contained_of_link R d hh)

def transposeIso {A B : Type*} (R : A → B → Prop) :
    bipGraph (fun b a => R a b) ≃g bipGraph R :=
  ⟨Equiv.sumComm _ _,by rintro (a | a) (b | b) <;> rfl⟩

lemma no_theta_both_links {A B : Type*} {R : A → B → Prop} (h : pattern.Free (bipGraph R)) :
    (∀ d : A, ¬ HasTheta (link R d)) ∧
    (∀ d : B, ¬ HasTheta (link (fun b a => R a b) d)) := by
  refine ⟨no_theta_links h,?_⟩
  intro d hh
  exact h ((pattern_contained_of_link (fun b a => R a b) d hh).trans ⟨(transposeIso R).toCopy⟩)

/-- An explicit connection to row masks [3,13,14,15]. -/
def bitRel (i j : Fin 4) : Prop :=
  Nat.testBit ((![3,13,14,15] : Fin 4 → ℕ) i) j.val = true

noncomputable def bitIso : bipGraph bitRel ≃g pattern := by
  let f : Fin 4 → Option (Fin 3) := ![some 2,some 0,some 1,none]
  let g : Fin 4 → Fin 4 := ![2,3,0,1]
  let e : Fin 4 ≃ Option (Fin 3) := Equiv.ofBijective f ⟨by decide,by decide⟩
  let e' : Fin 4 ≃ Fin 4 := Equiv.ofBijective g ⟨by decide,by decide⟩
  refine ⟨Equiv.sumCongr e e',?_⟩
  rintro (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [e,e',f,g,pattern,bipGraph,apexRel,thetaRel,bitRel] <;> decide

#print axioms pattern_contained_of_link
#print axioms no_theta_both_links
#print axioms bitIso
end Erdos713GlobalTheta

namespace Erdos713GlobalTheta
open Erdos713ThetaGram Erdos713C6 Erdos713GlobalLight

/-- A potential apex-theta with its last row missing forces the remaining
column pair to have at most three common rows in the WHOLE host. -/
lemma closing_pair_light {A B : Type*} [Fintype A] {R : A → B → Prop}
    (hFree : pattern.Free (bipGraph R)) {d b c : A}
    (hbd : b ≠ d) (hcd : c ≠ d) (hbc : b ≠ c)
    (f : Fin 4 → B) (hf : Function.Injective f) (hd : ∀ j, R d (f j))
    (hb : R b (f 0) ∧ R b (f 1) ∧ R b (f 2))
    (hc : R c (f 0) ∧ R c (f 1) ∧ R c (f 3)) :
    codegree R (f 2) (f 3) ≤ 3 := by
  classical
  have hSub : (univ.filter (fun a => R a (f 2) ∧ R a (f 3))) ⊆ ({d,b,c} : Finset A) := by
    intro a ha
    by_contra hNot
    simp only [mem_insert,mem_singleton,not_or] at hNot
    have ha₂ := (mem_filter.mp ha).2.1
    have ha₃ := (mem_filter.mp ha).2.2
    let rows : Fin 3 → {a : A // a ≠ d} := ![⟨b,hbd⟩,⟨c,hcd⟩,⟨a,hNot.1⟩]
    let cols : Fin 4 → {z : B // R d z} := fun j => ⟨f j,hd j⟩
    have hRows : Function.Injective rows := injective_triple
      (fun hh => hbc (congrArg Subtype.val hh))
      (fun hh => hNot.2.1 (congrArg Subtype.val hh).symm)
      (fun hh => hNot.2.2 (congrArg Subtype.val hh).symm)
    have hCols : Function.Injective cols := fun i j hij => hf (congrArg Subtype.val hij)
    apply no_theta_links hFree d
    exact ⟨rows,cols,hRows,hCols,hb.1,hc.1,hb.2.1,hc.2.1,hb.2.2,ha₂,hc.2.2,ha₃⟩
  have hCard : ({d,b,c} : Finset A).card ≤ 3 := by
    have h₁ := card_insert_le d ({b,c} : Finset A)
    have h₂ := card_insert_le b ({c} : Finset A)
    simp only [card_singleton] at h₂
    omega
  have hh := (card_le_card hSub).trans hCard
  simpa only [codegree,Nat.card_eq_fintype_card,Fintype.card_subtype] using hh

/-- The link exclusions and light-pair count apply simultaneously to one
relation, in both orientations. No assertion about a generic local relation
can replace these whole-host conditions. -/
lemma same_host_restrictions {A B : Type*} [Fintype A] [Fintype B] {R : A → B → Prop}
    (h : pattern.Free (bipGraph R)) :
    (∀ d : A, ¬ HasTheta (link R d)) ∧
    (∀ d : B, ¬ HasTheta (link (fun b a => R a b) d)) ∧
    (∑ a, (lightPairs R 3 a).card) ≤ 3*(Fintype.card B)^2 ∧
    (∑ b, (lightPairs (fun b a => R a b) 3 b).card) ≤ 3*(Fintype.card A)^2 :=
  ⟨(no_theta_both_links h).1,(no_theta_both_links h).2,
    sum_lightPairs_le R 3,sum_lightPairs_le (fun b a => R a b) 3⟩

#print axioms closing_pair_light
#print axioms same_host_restrictions
end Erdos713GlobalTheta

namespace Erdos713GlobalTheta
open Erdos713ThetaGram Erdos713C6

/-- Any pattern-copy with its universal row in the left shore yields an
oriented theta in that row's link. -/
lemma theta_link_of_copy_left {A B : Type*} {R : A → B → Prop}
    (f : pattern.Copy (bipGraph R)) {d : A} (hd : f (.inl none) = .inl d) :
    HasTheta (link R d) := by
  classical
  have hCols (j : Fin 4) : ∃ b : B, f (.inr j) = .inr b ∧ R d b := by
    have hh := f.toHom.map_adj (show pattern.Adj (.inl none) (.inr j) from trivial)
    change (bipGraph R).Adj (f (.inl none)) (f (.inr j)) at hh
    rw [hd] at hh
    exact right_of_adj_left hh
  choose b hb hdb using hCols
  let j : Fin 3 → Fin 4 := ![0,0,2]
  have hij (i : Fin 3) : thetaRel i (j i) := by fin_cases i <;> simp [j,thetaRel] <;> rfl
  have hRows (i : Fin 3) : ∃ a : A, f (.inl (some i)) = .inl a := by
    have hh := f.toHom.map_adj
      (show pattern.Adj (.inl (some i)) (.inr (j i)) from hij i)
    change (bipGraph R).Adj (f (.inl (some i))) (f (.inr (j i))) at hh
    rw [hb] at hh
    obtain ⟨a,ha,_⟩ := left_of_adj_right hh.symm
    exact ⟨a,ha⟩
  choose a ha using hRows
  have had (i : Fin 3) : a i ≠ d := by
    intro he
    have hh : f (.inl (some i)) = f (.inl none) := by rw [ha,hd,he]
    have hn := f.injective hh
    simp at hn
  let rows : Fin 3 → {a : A // a ≠ d} := fun i => ⟨a i,had i⟩
  let cols : Fin 4 → {b : B // R d b} := fun i => ⟨b i,hdb i⟩
  have hrows : Function.Injective rows := by
    intro i k he
    have hh : a i = a k := congrArg Subtype.val he
    have hfk : f (.inl (some i)) = f (.inl (some k)) := by rw [ha,ha,hh]
    simpa using f.injective hfk
  have hcols : Function.Injective cols := by
    intro i k he
    have hh : b i = b k := congrArg Subtype.val he
    have hfk : f (.inr i) = f (.inr k) := by rw [hb,hb,hh]
    simpa using f.injective hfk
  have hEdge (i : Fin 3) (k : Fin 4) (hik : thetaRel i k) : link R d (rows i) (cols k) := by
    have hh := f.toHom.map_adj (show pattern.Adj (.inl (some i)) (.inr k) from hik)
    change (bipGraph R).Adj (f (.inl (some i))) (f (.inr k)) at hh
    rw [ha,hb] at hh
    exact hh
  exact ⟨rows,cols,hrows,hcols,hEdge 0 0 (by rfl),hEdge 1 0 (by rfl),
    hEdge 0 1 (by rfl),hEdge 1 1 (by rfl),hEdge 0 2 (by rfl),
    hEdge 2 2 (by rfl),hEdge 1 3 (by rfl),hEdge 2 3 (by rfl)⟩

lemma free_iff_both_links {A B : Type*} (R : A → B → Prop) :
    pattern.Free (bipGraph R) ↔
      (∀ d : A, ¬ HasTheta (link R d)) ∧
      (∀ d : B, ¬ HasTheta (link (fun b a => R a b) d)) := by
  refine ⟨no_theta_both_links,?_⟩
  rintro ⟨hLeft,hRight⟩ ⟨f⟩
  cases he : f (.inl none) with
  | inl d => exact hLeft d (theta_link_of_copy_left f he)
  | inr d =>
    apply hRight d
    apply theta_link_of_copy_left ((transposeIso R).symm.toCopy.comp f)
    change (transposeIso R).symm (f (.inl none)) = .inl d
    rw [he]
    rfl

#print axioms theta_link_of_copy_left
#print axioms free_iff_both_links
end Erdos713GlobalTheta
