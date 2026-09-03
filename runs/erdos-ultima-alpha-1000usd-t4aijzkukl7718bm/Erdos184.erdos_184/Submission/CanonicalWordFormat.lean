import Submission.CanonicalPairKernel
import Submission.RestrictedWordKernel

/-! Canonical pair kernels have normalized cyclic words. A slot whose other
color is outside a selected subfamily is a private marker in that subfamily. -/
open scoped Classical
namespace Erdos184Work.CanonicalPairKernel
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CycleSegments
open LabelKernel Erdos184Serial
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
variable {l : ℕ} (b : PairIndex l → Fin 3) (hb : ∀ i, 2 ≤ (markers b i).card)
    (o : ∀ i, Marked.Order (arity b i))

noncomputable local instance {I : Type*} {m : I → ℕ} :
    DecidableEq (Σ i, Fin (m i)) := Classical.decEq _

def word (i : Fin l) : Fin (arity b i+2) → Fin ((l*l)*2) :=
  NormalizedKernel.word (place b hb) o i

lemma word_injective (i : Fin l) : Function.Injective (word b hb o i) :=
  NormalizedKernel.word_injective (place b hb) o (place_injective b hb) i

lemma word_mem (i : Fin l) (j : Fin (arity b i+2)) : word b hb o i j ∈ markers b i := by
  exact (markers b i).orderEmbOfFin_mem (Nat.sub_add_cancel (hb i)).symm _

lemma word_range (i : Fin l) (z : Fin ((l*l)*2)) :
    (∃ j, word b hb o i j = z) ↔ z ∈ markers b i := by
  constructor
  · rintro ⟨j,rfl⟩
    exact word_mem b hb o i j
  · intro hz
    let e := (markers b i).orderIsoOfFin (Nat.sub_add_cancel (hb i)).symm
    let a := e.symm ⟨z,hz⟩
    have hs := Finite.surjective_of_injective
      (SmallOrderNormalization.normalized_valid_all (arity b i) (o i)).2.1
    obtain ⟨j,hj⟩ := hs a
    refine ⟨j,?_⟩
    change place b hb i ((SmallOrderNormalization.normalized _ (o i)).vertex j) = z
    rw [hj]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨z,hz⟩)

lemma word_first (i : Fin l) : word b hb o i 0 = place b hb i 0 :=
  NormalizedKernel.word_first (place b hb) o i

lemma word_first_le (i : Fin l) (j : Fin (arity b i+2)) :
    word b hb o i 0 ≤ word b hb o i j := by
  rw [word_first]
  exact (place_strictMono b hb i).monotone (Fin.zero_le _)

lemma word_orientation (i : Fin l) : arity b i = 0 ∨
    word b hb o i 1 < word b hb o i (Fin.last (arity b i+1)) := by
  rcases SmallOrderNormalization.normalized_orientation_all (arity b i) (o i) with h | h
  · exact Or.inl h
  · exact Or.inr (place_strictMono b hb i h)

lemma slot_mem_markers (p : PairIndex l) (r : Fin 2) (i : Fin l) :
    slot (p,r) ∈ markers b i ↔ i ∈ pairSet p ∧ r.val < (b p).val := by
  rw [mem_markers]
  constructor
  · rintro ⟨q,s,hi,hs,he⟩
    have heq := slot.injective he
    have hq : q = p := congrArg Prod.fst heq
    have hr : s = r := congrArg Prod.snd heq
    subst q
    subst s
    exact ⟨hi,hs⟩
  · rintro ⟨hi,hr⟩
    exact ⟨p,r,hi,hr,rfl⟩

lemma private_slot (A : Finset (Fin l)) (i : A) (j : Fin (arity b i.val+2))
    (p : PairIndex l) (r : Fin 2) (hword : word b hb o i.val j = slot (p,r))
    (hpair : A ∩ pairSet p = {i.val}) :
    ∀ k ∈ A, ∀ t : Fin (arity b k+2), word b hb o k t = word b hb o i.val j → k = i.val := by
  intro k hk t ht
  have hm := word_mem b hb o k t
  rw [ht,hword] at hm
  have hkp := (slot_mem_markers b p r k).mp hm
  have hi : k ∈ A ∩ pairSet p := Finset.mem_inter.mpr ⟨hk,hkp.1⟩
  rw [hpair,Finset.mem_singleton] at hi
  exact hi

noncomputable def suppressPrivateSlot
    (A : Finset (Fin l)) (i : A) (j : Fin (arity b i.val+2))
    (p : PairIndex l) (r : Fin 2) (hword : word b hb o i.val j = slot (p,r))
    (hpair : A ∩ pairSet p = {i.val}) (hsize : 1 ≤ arity b i.val) :
    Suppression (WordKernel.source (WordKernel.restrictedPlace (word b hb o) A))
      (WordKernel.target (WordKernel.restrictedPlace (word b hb o) A)) :=
  WordKernel.restrictedSuppression (word b hb o) A (word_injective b hb o) i j
    (private_slot b hb o A i j p r hword hpair) hsize

lemma private_slot_spectrum
    (A : Finset (Fin l)) (i : A) (j : Fin (arity b i.val+2))
    (p : PairIndex l) (r : Fin 2) (hword : word b hb o i.val j = slot (p,r))
    (hpair : A ∩ pairSet p = {i.val}) (hsize : 1 ≤ arity b i.val) (P : ℕ → Prop) :
    (∃ D, Partition (code (source b hb o) (target b hb o))
      (PathSubstitution.Family.colorLabels A) D ∧ P D.card) ↔
    (∃ D, Partition
      (code (suppressPrivateSlot b hb o A i j p r hword hpair hsize).source
        (suppressPrivateSlot b hb o A i j p r hword hpair hsize).target)
      Finset.univ D ∧ P D.card) := by
  have h := WordKernel.restrictSuppress_spectrum (word b hb o) A (word_injective b hb o) i j
    (private_slot b hb o A i j p r hword hpair) hsize P
  have hs : WordKernel.source (word b hb o) = source b hb o := rfl
  have ht : WordKernel.target (word b hb o) = target b hb o := rfl
  convert h using 1
  rw [hs,ht]
  constructor <;> rintro ⟨D,hD,hP⟩
  · refine ⟨D,?_,hP⟩
    convert hD using 1
    ext e
    simp [PathSubstitution.Family.colorLabels]
  · refine ⟨D,?_,hP⟩
    convert hD using 1
    ext e
    simp [PathSubstitution.Family.colorLabels]

#print axioms word_range
#print axioms word_orientation
#print axioms private_slot_spectrum
end Erdos184Work.CanonicalPairKernel
