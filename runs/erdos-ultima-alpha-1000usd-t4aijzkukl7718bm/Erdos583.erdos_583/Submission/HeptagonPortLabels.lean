import Submission.Work
import Submission.FinitePortLabels
import Submission.HeptagonPortRoutes

/-! Every seven-vertex graph with two missing edges is a relabeling of one of the two port cores. -/
namespace Erdos583HeptagonPortLabelsDevelopment
open SimpleGraph Erdos583Work Erdos583FinitePortLabelsDevelopment Erdos583HeptagonPortRoutesDevelopment
open scoped Classical
set_option maxHeartbeats 2200000

lemma adjacency_from_complement {V : Type*} (H : SimpleGraph V) (x y : V) :
    H.Adj x y ↔ x ≠ y ∧ s(x,y) ∉ Hᶜ.edgeSet := by
  change H.Adj x y ↔ x ≠ y ∧ ¬Hᶜ.Adj x y
  rw [compl_adj]
  constructor
  · intro h
    exact ⟨h.ne,fun hh ↦ hh.2 h⟩
  · rintro ⟨hne,hno⟩
    by_contra hn
    exact hno ⟨hne,hn⟩

lemma image_deleted_true (e : Equiv.Perm (Fin 7)) :
    Sym2.map e '' (deleted true : Set (Sym2 (Fin 7)))={s(e 0,e 1),s(e 0,e 2)} := by
  simp [deleted,Set.image_pair]

lemma image_deleted_false (e : Equiv.Perm (Fin 7)) :
    Sym2.map e '' (deleted false : Set (Sym2 (Fin 7)))={s(e 0,e 1),s(e 2,e 3)} := by
  simp [deleted,Set.image_pair]

lemma two_edges_normal_form {a b c d : Fin 7} (hab : a ≠ b) (hcd : c ≠ d)
    (hne : s(a,b) ≠ s(c,d)) :
    ∃ t : Bool, ∃ e : Equiv.Perm (Fin 7),
      ({s(a,b),s(c,d)} : Set (Sym2 (Fin 7)))=Sym2.map e '' (deleted t : Set (Sym2 (Fin 7))) := by
  by_cases hca : c=a
  · subst c
    have hbd : b ≠ d := by rintro rfl; exact hne rfl
    obtain ⟨e,h0,h1,h2⟩ := label_three hab hcd hbd
    exact ⟨true,e,by rw [image_deleted_true,h0,h1,h2]⟩
  by_cases hda : d=a
  · subst d
    have hbc : b ≠ c := by
      rintro rfl
      exact hne Sym2.eq_swap
    obtain ⟨e,h0,h1,h2⟩ := label_three hab (Ne.symm hca) hbc
    exact ⟨true,e,by rw [image_deleted_true,h0,h1,h2,Sym2.eq_swap (a := c) (b := a)]⟩
  by_cases hcb : c=b
  · subst c
    have had : a ≠ d := by
      rintro rfl
      exact hne Sym2.eq_swap
    obtain ⟨e,h0,h1,h2⟩ := label_three hab.symm hcd had
    exact ⟨true,e,by rw [image_deleted_true,h0,h1,h2,Sym2.eq_swap (a := a) (b := b)]⟩
  by_cases hdb : d=b
  · subst d
    have hac : a ≠ c := by
      rintro rfl
      exact hne rfl
    obtain ⟨e,h0,h1,h2⟩ := label_three hab.symm (Ne.symm hcb) hac
    exact ⟨true,e,by rw [image_deleted_true,h0,h1,h2,
      Sym2.eq_swap (a := a) (b := b),Sym2.eq_swap (a := c) (b := b)]⟩
  obtain ⟨e,h0,h1,h2,h3⟩ := label_four hab (Ne.symm hca) (Ne.symm hda) (Ne.symm hcb) (Ne.symm hdb) hcd
  exact ⟨false,e,by rw [image_deleted_false,h0,h1,h2,h3]⟩

lemma complement_normal_form (H : SimpleGraph (Fin 7)) (hc : Hᶜ.edgeSet.ncard=2) :
    ∃ t : Bool, ∃ e : Equiv.Perm (Fin 7), Hᶜ.edgeSet=Sym2.map e '' (deleted t : Set (Sym2 (Fin 7))) := by
  obtain ⟨p,q,hpq,he⟩ := Set.ncard_eq_two.mp hc
  induction p using Sym2.ind with
  | h a b =>
    induction q using Sym2.ind with
    | h c d =>
      have hab : a ≠ b := by
        rintro rfl
        have ha : s(a,a) ∈ Hᶜ.edgeSet := by rw [he]; simp
        exact Hᶜ.loopless a ha
      have hcd : c ≠ d := by
        rintro rfl
        have ha : s(c,c) ∈ Hᶜ.edgeSet := by rw [he]; simp
        exact Hᶜ.loopless c ha
      obtain ⟨t,e,hh⟩ := two_edges_normal_form hab hcd hpq
      exact ⟨t,e,he.trans hh⟩

lemma iso_of_complement (H : SimpleGraph (Fin 7)) (t : Bool) (e : Equiv.Perm (Fin 7))
    (he : Hᶜ.edgeSet=Sym2.map e '' (deleted t : Set (Sym2 (Fin 7)))) :
    Nonempty (graph t ≃g H) := by
  refine ⟨{ toEquiv := e, map_rel_iff' := ?_ }⟩
  intro a b
  change H.Adj (e a) (e b) ↔ a ≠ b ∧ s(a,b) ∉ deleted t
  rw [adjacency_from_complement,he]
  have him : s(e a,e b) ∈ Sym2.map e '' (deleted t : Set (Sym2 (Fin 7))) ↔ s(a,b) ∈ deleted t := by
    constructor
    · rintro ⟨z,hz,hze⟩
      have hz' : z=s(a,b) := Sym2.map.injective e.injective hze
      simpa only [hz'] using hz
    · intro hz
      exact ⟨s(a,b),hz,rfl⟩
  rw [him]
  have hen : (e a ≠ e b) ↔ a ≠ b := not_congr (show e a=e b ↔ a=b from e.injective.eq_iff)
  rw [hen]

lemma exists_core_iso (H : SimpleGraph (Fin 7)) (hc : Hᶜ.edgeSet.ncard=2) :
    ∃ t : Bool, Nonempty (graph t ≃g H) := by
  obtain ⟨t,e,he⟩ := complement_normal_form H hc
  exact ⟨t,iso_of_complement H t e he⟩

def complIso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) : Gᶜ ≃g Hᶜ where
  toEquiv := e.toEquiv
  map_rel_iff' := by
    intro x y
    change (e x ≠ e y ∧ ¬H.Adj (e x) (e y)) ↔ x ≠ y ∧ ¬G.Adj x y
    rw [e.injective.ne_iff,e.map_adj_iff]

lemma exists_core_iso_finite {V : Type*} [Fintype V] (H : SimpleGraph V)
    (hv : Fintype.card V=7) (hc : Hᶜ.edgeSet.ncard=2) :
    ∃ t : Bool, Nonempty (graph t ≃g H) := by
  let e := H.overFinIso hv
  have hcomp : (H.overFin hv)ᶜ.edgeSet.ncard=2 := by
    rw [←GlobalCritical.edge_ncard_iso (complIso e)]
    exact hc
  obtain ⟨t,⟨f⟩⟩ := exists_core_iso (H.overFin hv) hcomp
  exact ⟨t,⟨f.trans e.symm⟩⟩

end Erdos583HeptagonPortLabelsDevelopment
