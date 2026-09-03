import Submission.LabelKernelEmbedding
import Submission.SeriesSupportTransport

/-! A non-loop labelled edge can be subdivided through a fresh private vertex.
All circuit-partition counts are preserved, including in parallel-edge kernels. -/
open scoped Classical
namespace Erdos184Work.LabelKernel.Subdivision
open Erdos184Serial
set_option maxHeartbeats 1500000
set_option linter.unusedSectionVars false
variable {J W : Type*} [DecidableEq J] [DecidableEq W]
variable (src dst : J → W) (p : J)

def source : J ⊕ Unit → W ⊕ Unit
  | .inl j => .inl (src j)
  | .inr _ => .inr ()

def target : J ⊕ Unit → W ⊕ Unit
  | .inl j => if j = p then .inr () else .inl (dst j)
  | .inr _ => .inl (dst p)

private def replacement (w : W) : J ↪ J ⊕ Unit where
  toFun j := if j = p ∧ w = dst p then .inr () else .inl j
  inj' := by
    intro i j h
    dsimp only at h
    split_ifs at h with hi hj hj
    · exact hi.1.trans hj.1.symm
    · exact Sum.inl.inj h

lemma filter_new (t : Finset (J ⊕ Unit)) :
    t.filter (fun j => source src j = .inr () ∨ target dst p j = .inr ()) =
      ({Sum.inl p,Sum.inr ()} : Finset (J ⊕ Unit)).filter (fun j => j ∈ t) := by
  ext j
  cases j with
  | inl j => by_cases hj : j = p <;> simp [source,target,hj]
  | inr u => cases u; simp [source,target]

lemma valid_match {t : Finset (J ⊕ Unit)}
    (ht : (code (source src) (target dst p)).valid t) :
    p ∈ t.toLeft ↔ () ∈ t.toRight := by
  have he := ht (.inr ())
  rw [filter_new] at he
  by_cases hp : Sum.inl p ∈ t <;> by_cases hq : Sum.inr () ∈ t <;>
    simp [Finset.filter_insert,Finset.filter_singleton,hp,hq] at he ⊢

lemma filter_expansion_old (hloop : src p ≠ dst p) (s : Finset J) (w : W) :
    (Series.expand p s).filter (fun j => source src j = .inl w ∨ target dst p j = .inl w) =
      (s.filter (fun j => src j = w ∨ dst j = w)).map (replacement dst p w) := by
  ext x
  cases x with
  | inl j =>
    simp only [Finset.mem_filter,Series.mem_expand_left,source,target,Sum.inl.injEq,
      Finset.mem_map]
    constructor
    · rintro ⟨hjs,hj⟩
      by_cases hjp : j = p
      · subst j
        have hsrc : src p = w := by simpa using hj
        have hw : w ≠ dst p := fun h => hloop (hsrc.trans h)
        exact ⟨p,⟨hjs,Or.inl hsrc⟩,by simp [replacement,hw]⟩
      · have hh : src j = w ∨ dst j = w := by simpa [hjp] using hj
        exact ⟨j,⟨hjs,hh⟩,by simp [replacement,hjp]⟩
    · rintro ⟨i,⟨his,hi⟩,heq⟩
      by_cases hrep : i = p ∧ w = dst p
      · simp [replacement,hrep] at heq
      · have hij : i = j := by simpa [replacement,hrep] using heq
        subst i
        refine ⟨his,?_⟩
        by_cases hjp : j = p
        · subst j
          have hw : w ≠ dst p := fun h => hrep ⟨rfl,h⟩
          simpa [Ne.symm hw] using hi
        · simpa [hjp] using hi
  | inr u =>
    cases u
    simp only [Finset.mem_filter,Series.mem_expand_right,source,target,
      Sum.inl.injEq,Sum.inr_ne_inl,false_or,Finset.mem_map]
    constructor
    · rintro ⟨hp,hw⟩
      exact ⟨p,⟨hp,Or.inr hw⟩,by simp [replacement,hw]⟩
    · rintro ⟨j,⟨hjs,hj⟩,heq⟩
      by_cases hrep : j = p ∧ w = dst p
      · exact ⟨hrep.1 ▸ hjs,hrep.2.symm⟩
      · simp [replacement,hrep] at heq

lemma valid_expansion_iff (hloop : src p ≠ dst p) (s : Finset J) :
    (code (source src) (target dst p)).valid (Series.expand p s) ↔
      (code src dst).valid s := by
  constructor
  · intro h w
    have hw := h (.inl w)
    rw [filter_expansion_old src dst p hloop,Finset.card_map] at hw
    exact hw
  · intro h w
    cases w with
    | inl w =>
      rw [filter_expansion_old src dst p hloop,Finset.card_map]
      exact h w
    | inr u =>
      cases u
      rw [filter_new]
      by_cases hp : p ∈ s <;>
        simp [Finset.filter_insert,Finset.filter_singleton,hp]

noncomputable def transport (hloop : src p ≠ dst p) :
    SupportTransport (code src dst) (code (source src) (target dst p)) where
  expand := Series.expand p
  empty := (Series.transport p (code src dst)).empty
  union := (Series.transport p (code src dst)).union
  subset := (Series.transport p (code src dst)).subset
  disjoint := (Series.transport p (code src dst)).disjoint
  valid := valid_expansion_iff src dst p hloop
  lift _ t _ ht := ⟨t.toLeft,Series.expand_eq_of_match p t (valid_match src dst p ht)⟩

lemma hasNumber_iff (hloop : src p ≠ dst p) (s : Finset J) (k : ℕ) :
    HasNumber (code (source src) (target dst p)) (Series.expand p s) k ↔
      HasNumber (code src dst) s k :=
  (transport src dst p hloop).hasNumber_iff s k

lemma minimalCore_iff (hloop : src p ≠ dst p) (s : Finset J) (k : ℕ) :
    MinimalCore (code (source src) (target dst p)) (Series.expand p s) k ↔
      MinimalCore (code src dst) s k :=
  (transport src dst p hloop).minimalCore_iff s k

lemma rigid_iff (hloop : src p ≠ dst p) (s : Finset J) (k : ℕ) :
    Rigid (code (source src) (target dst p)) (Series.expand p s) k ↔
      Rigid (code src dst) s k :=
  (transport src dst p hloop).rigid_iff s k

lemma partition_spectrum_iff (hloop : src p ≠ dst p) (s : Finset J) (P : ℕ → Prop) :
    (∃ D, Partition (code (source src) (target dst p)) (Series.expand p s) D ∧ P D.card) ↔
      (∃ D, Partition (code src dst) s D ∧ P D.card) :=
  (transport src dst p hloop).exists_partition_card_iff s P

#print axioms transport
#print axioms partition_spectrum_iff
#print axioms minimalCore_iff
end Erdos184Work.LabelKernel.Subdivision
