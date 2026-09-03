import Submission.SerialMinimum

/-! Circuit partitions transported by an embedding of valid supports.
This includes series expansions, not just relabeling coordinates. -/
open scoped Classical
namespace Erdos184Serial
set_option maxHeartbeats 1500000
set_option linter.unusedSectionVars false
variable {E F : Type*} [DecidableEq E] [DecidableEq F]

structure SupportTransport (C : Code E) (B : Code F) where
  expand : Finset E → Finset F
  empty : expand ∅ = ∅
  union : ∀ s t, expand (s ∪ t) = expand s ∪ expand t
  subset : ∀ s t, expand s ⊆ expand t ↔ s ⊆ t
  disjoint : ∀ s t, Disjoint (expand s) (expand t) ↔ Disjoint s t
  valid : ∀ s, B.valid (expand s) ↔ C.valid s
  lift : ∀ s t, t ⊆ expand s → B.valid t → ∃ u, expand u = t

namespace SupportTransport
variable {C : Code E} {B : Code F} (M : SupportTransport C B)

lemma injective : Function.Injective M.expand := by
  intro s t h
  exact Finset.Subset.antisymm ((M.subset s t).mp (h ▸ Finset.Subset.refl _))
    ((M.subset t s).mp (h.symm ▸ Finset.Subset.refl _))

lemma nonempty (s : Finset E) : (M.expand s).Nonempty ↔ s.Nonempty := by
  simp only [Finset.nonempty_iff_ne_empty,← M.empty]
  exact not_congr M.injective.eq_iff

lemma circuit_iff (s : Finset E) : Circuit B (M.expand s) ↔ Circuit C s := by
  constructor
  · intro hc
    refine ⟨(M.valid s).mp hc.1,(M.nonempty s).mp hc.2.1,?_⟩
    intro t hts ht htne
    apply M.injective
    exact hc.2.2 _ ((M.subset t s).mpr hts) ((M.valid t).mpr ht) ((M.nonempty t).mpr htne)
  · intro hc
    refine ⟨(M.valid s).mpr hc.1,(M.nonempty s).mpr hc.2.1,?_⟩
    intro t hts ht htne
    obtain ⟨u,rfl⟩ := M.lift s t hts ht
    have he := hc.2.2 u ((M.subset u s).mp hts) ((M.valid u).mp ht) ((M.nonempty u).mp htne)
    rw [he]

lemma biUnion (D : Finset (Finset E)) :
    M.expand (D.biUnion id) = (D.image M.expand).biUnion id := by
  induction D using Finset.induction_on with
  | empty => simp [M.empty]
  | @insert s D hs ih => simp only [Finset.biUnion_insert,id_eq,M.union,Finset.image_insert,ih]

lemma map_partition {s : Finset E} {D : Finset (Finset E)} (hD : Partition C s D) :
    Partition B (M.expand s) (D.image M.expand) := by
  refine ⟨?_,?_,?_⟩
  · intro t ht
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp ht
    exact (M.circuit_iff u).mpr (hD.1 u hu)
  · intro s hs t ht hne
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ht
    exact (M.disjoint u v).mpr (hD.2.1 hu hv (fun h => hne (congrArg M.expand h)))
  · rw [← M.biUnion,hD.2.2]

lemma map_card (D : Finset (Finset E)) : (D.image M.expand).card = D.card :=
  Finset.card_image_of_injective _ M.injective

lemma unmap_partition {s : Finset E} {D : Finset (Finset F)} (hD : Partition B (M.expand s) D) :
    ∃ A, Partition C s A ∧ A.card = D.card := by
  have hlift (i : D) : ∃ u, M.expand u = i.val :=
    M.lift s i.val (hD.piece_subset i.property) (hD.1 i.val i.property).1
  choose a ha using hlift
  let A : Finset (Finset E) := Finset.univ.image a
  have hmap : A.image M.expand = D := by
    ext t
    simp only [A,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨u,⟨i,rfl⟩,rfl⟩
      rw [ha i]
      exact i.property
    · intro ht
      exact ⟨a ⟨t,ht⟩,⟨⟨t,ht⟩,rfl⟩,ha ⟨t,ht⟩⟩
  refine ⟨A,⟨?_,?_,?_⟩,?_⟩
  · intro t ht
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ht
    apply (M.circuit_iff _).mp
    rw [ha i]
    exact hD.1 i.val i.property
  · intro t ht u hu hne
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hu
    apply (M.disjoint _ _).mp
    rw [ha i,ha j]
    exact hD.2.1 i.property j.property (fun h => hne (congrArg a (Subtype.ext h)))
  · apply M.injective
    rw [M.biUnion,hmap,hD.2.2]
  · rw [← M.map_card A,hmap]

lemma hasNumber_iff (s : Finset E) (k : ℕ) :
    HasNumber B (M.expand s) k ↔ HasNumber C s k := by
  constructor
  · rintro ⟨⟨D,hD,hcD⟩,hlo⟩
    obtain ⟨A,hA,hcA⟩ := M.unmap_partition hD
    refine ⟨⟨A,hA,hcA.trans hcD⟩,?_⟩
    intro P hP
    have h := hlo _ (M.map_partition hP)
    rwa [M.map_card] at h
  · rintro ⟨⟨D,hD,hcD⟩,hlo⟩
    refine ⟨⟨D.image M.expand,M.map_partition hD,(M.map_card D).trans hcD⟩,?_⟩
    intro P hP
    obtain ⟨A,hA,hcA⟩ := M.unmap_partition hP
    have h := hlo A hA
    omega

lemma rigid_iff (s : Finset E) (k : ℕ) :
    Rigid B (M.expand s) k ↔ Rigid C s k := by
  constructor
  · intro hr D hD
    have h := hr _ (M.map_partition hD)
    rwa [M.map_card] at h
  · intro hr D hD
    obtain ⟨A,hA,hcA⟩ := M.unmap_partition hD
    have h := hr A hA
    omega

lemma minimalCore_iff (s : Finset E) (k : ℕ) :
    MinimalCore B (M.expand s) k ↔ MinimalCore C s k := by
  constructor
  · intro hm
    refine ⟨(M.hasNumber_iff s k).mp hm.1,?_⟩
    intro t hts ht
    have hstrict : M.expand t ⊂ M.expand s := Finset.ssubset_iff_subset_ne.mpr
      ⟨(M.subset t s).mpr hts.1,fun h => (Finset.ssubset_iff_subset_ne.mp hts).2 (M.injective h)⟩
    obtain ⟨P,hP,hcP⟩ := hm.2 _ hstrict ((M.valid t).mpr ht)
    obtain ⟨D,hD,hcD⟩ := M.unmap_partition hP
    exact ⟨D,hD,by omega⟩
  · intro hm
    refine ⟨(M.hasNumber_iff s k).mpr hm.1,?_⟩
    intro t hts ht
    obtain ⟨u,rfl⟩ := M.lift s t hts.1 ht
    have hstrict : u ⊂ s := Finset.ssubset_iff_subset_ne.mpr
      ⟨(M.subset u s).mp hts.1,fun h => (Finset.ssubset_iff_subset_ne.mp hts).2 (congrArg M.expand h)⟩
    obtain ⟨D,hD,hcD⟩ := hm.2 u hstrict ((M.valid u).mp ht)
    exact ⟨D.image M.expand,M.map_partition hD,by rw [M.map_card]; exact hcD⟩

#print axioms hasNumber_iff
#print axioms minimalCore_iff
#print axioms rigid_iff
end SupportTransport
end Erdos184Serial
