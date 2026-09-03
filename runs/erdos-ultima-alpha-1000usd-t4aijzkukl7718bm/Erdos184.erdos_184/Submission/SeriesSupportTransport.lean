import Submission.SupportTransport
import Submission.PointCode

/-! Exact support transport for duplicating a coordinate in series. -/
open scoped Classical
namespace Erdos184Serial
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
variable {E F H : Type*} [DecidableEq E] [DecidableEq F] [DecidableEq H]

namespace SupportTransport

def refl (C : Code E) : SupportTransport C C where
  expand := id
  empty := rfl
  union _ _ := rfl
  subset _ _ := Iff.rfl
  disjoint _ _ := Iff.rfl
  valid _ := Iff.rfl
  lift _ t _ _ := ⟨t,rfl⟩

def trans {C : Code E} {B : Code F} {A : Code H}
    (M : SupportTransport C B) (N : SupportTransport B A) : SupportTransport C A where
  expand := N.expand ∘ M.expand
  empty := by simp only [Function.comp_apply,M.empty,N.empty]
  union s t := by simp only [Function.comp_apply,M.union,N.union]
  subset s t := (N.subset _ _).trans (M.subset s t)
  disjoint s t := (N.disjoint _ _).trans (M.disjoint s t)
  valid s := (N.valid _).trans (M.valid s)
  lift s t hts ht := by
    obtain ⟨v,rfl⟩ := N.lift (M.expand s) t hts ht
    obtain ⟨u,rfl⟩ := M.lift s v ((N.subset _ _).mp hts) ((N.valid v).mp ht)
    exact ⟨u,rfl⟩

def ofEmbedding {C : Code E} {B : Code F} (f : E ↪ F)
    (hv : ∀ s, C.valid s ↔ B.valid (s.map f)) : SupportTransport C B where
  expand s := s.map f
  empty := Finset.map_empty _
  union s t := Finset.map_union _ _
  subset _ _ := Finset.map_subset_map
  disjoint _ _ := Finset.disjoint_map f
  valid s := (hv s).symm
  lift _ t hts _ := by
    obtain ⟨u,_,he⟩ := Finset.subset_map_iff.mp hts
    exact ⟨u,he.symm⟩

lemma upper_bound_iff {C : Code E} {B : Code F} (M : SupportTransport C B)
    (s : Finset E) (k : ℕ) :
    (∀ D, Partition B (M.expand s) D → D.card ≤ k) ↔
      (∀ D, Partition C s D → D.card ≤ k) := by
  constructor
  · intro h D hD
    have hb := h _ (M.map_partition hD)
    rwa [M.map_card] at hb
  · intro h D hD
    obtain ⟨A,hA,hcard⟩ := M.unmap_partition hD
    exact hcard ▸ h A hA

lemma exists_partition_card_iff {C : Code E} {B : Code F} (M : SupportTransport C B)
    (s : Finset E) (P : ℕ → Prop) :
    (∃ D, Partition B (M.expand s) D ∧ P D.card) ↔
      (∃ D, Partition C s D ∧ P D.card) := by
  constructor
  · rintro ⟨D,hD,hP⟩
    obtain ⟨A,hA,hcard⟩ := M.unmap_partition hD
    exact ⟨A,hA,hcard.symm ▸ hP⟩
  · rintro ⟨D,hD,hP⟩
    exact ⟨D.image M.expand,M.map_partition hD,(M.map_card D).symm ▸ hP⟩

end SupportTransport

namespace Series
variable (p : E)

def expand (s : Finset E) : Finset (E ⊕ Unit) :=
  s.disjSum (if p ∈ s then {()} else ∅)

@[simp] lemma toLeft_expand (s : Finset E) : (expand p s).toLeft = s := by
  simp [expand]

@[simp] lemma mem_expand_left (s : Finset E) (e : E) :
    Sum.inl e ∈ expand p s ↔ e ∈ s := by simp [expand]

@[simp] lemma mem_expand_right (s : Finset E) (u : Unit) :
    Sum.inr u ∈ expand p s ↔ p ∈ s := by
  cases u
  by_cases hp : p ∈ s <;> simp [expand,hp]

lemma expand_eq_of_match (t : Finset (E ⊕ Unit))
    (h : p ∈ t.toLeft ↔ () ∈ t.toRight) : expand p t.toLeft = t := by
  ext x
  cases x with
  | inl e => simp
  | inr u => cases u; simpa using h

noncomputable def transport (C : Code E) : SupportTransport C (serial C pointCode p ()) where
  expand := expand p
  empty := by simp [expand]
  union s t := by
    ext x
    cases x <;> simp
  subset s t := by
    constructor
    · intro h e he
      exact (mem_expand_left p t e).mp (h ((mem_expand_left p s e).mpr he))
    · intro h x hx
      cases x with
      | inl e => exact (mem_expand_left p t e).mpr (h ((mem_expand_left p s e).mp hx))
      | inr u => exact (mem_expand_right p t u).mpr (h ((mem_expand_right p s u).mp hx))
  disjoint s t := by
    simp only [Finset.disjoint_left]
    constructor
    · intro h e hs ht
      exact h ((mem_expand_left p s e).mpr hs) ((mem_expand_left p t e).mpr ht)
    · intro h x hs ht
      cases x with
      | inl e => exact h ((mem_expand_left p s e).mp hs) ((mem_expand_left p t e).mp ht)
      | inr u => exact h ((mem_expand_right p s u).mp hs) ((mem_expand_right p t u).mp ht)
  valid s := by
    change (C.valid (expand p s).toLeft ∧ True ∧
      (p ∈ (expand p s).toLeft ↔ () ∈ (expand p s).toRight)) ↔ C.valid s
    simp only [toLeft_expand]
    have hm : (() ∈ (expand p s).toRight) ↔ p ∈ s := by
      simpa only [Finset.mem_toRight] using mem_expand_right p s ()
    simp [hm]
  lift s t hts ht := ⟨t.toLeft,expand_eq_of_match p t ht.2.2⟩

#print axioms transport
#print axioms SupportTransport.trans
end Series
end Erdos184Serial
