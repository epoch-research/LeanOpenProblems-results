import Submission.FourCanonicalCounts
import Submission.FilteredCyclicWord

/-! Local alternation at colors 0, 2, 3 of numerical pattern 0.
Only a necessary local constraint is proved here, not a global bound. -/
open scoped Classical
namespace Erdos184Work.FourFork00
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open LabelKernel Erdos184Serial CanonicalSubsetCoarsening LocalCanonicalRows TripleAlternationKernels
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option Elab.async false
noncomputable local instance {I : Type*} {m : I → ℕ} : DecidableEq (Σ i, Fin (m i)) := Classical.decEq _

abbrev b := FourCanonicalCounts.counts 0
lemma hb : ∀ i, 2 ≤ (markers b i).card := FourCanonicalCounts.marker_bound 0
abbrev Orders := FourCanonicalCounts.Orders 0
def A : Finset (Fin 4) := {0,2,3}
lemma hA : A.card = 3 := by decide +kernel
lemma hr : ∀ i : A, 2 ≤ (retained b A i.val).card := by decide +kernel
def c : A := ⟨0,by decide⟩
def a : A := ⟨2,by decide⟩
def z : A := ⟨3,by decide⟩
abbrev E := Σ i : A, Fin (StableCanonicalCoarsening.arity b A i+2)
noncomputable local instance : DecidableEq E := Classical.decEq _
def phi : Fin 4 → Fin 32 := ![4,5,6,7]
lemma phi_injective : Function.Injective phi := by decide +kernel

def rowC (q : Marked.Order 2) : Fin 4 → Fin 32 :=
  StableCanonicalCoarsening.word b hb (oneOrder b 0 q) A hr c
def markersC : Fin 4 → Fin 32 := ![4,5,6,7]
lemma placeC : fastPlace b hb 0 = markersC := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b hb 0 j = markersC j) j
lemma retainedC : retained b A 0 = {4,5,6,7} := by decide +kernel

def fastRowC (q : Marked.Order 2) (j : Fin 4) : Fin 32 :=
  (FilteredWord.filtered (fun t : Fin 4 => markersC ((SmallOrderNormalization.normalized 2 q).vertex t)) {4,5,6,7}).getD j.val 0

lemma rowC_eq_fast (q : Marked.Order 2) : rowC q = fastRowC q := by
  funext j
  change StableCanonicalCoarsening.word b hb (oneOrder b 0 q) A hr c j = _
  rw [StableCanonicalCoarsening.word_eq_getD b hb (oneOrder b 0 q) A hr c j 0]
  have hw : fastWord b hb (oneOrder b 0 q) 0 =
      fun t => markersC ((SmallOrderNormalization.normalized 2 q).vertex t) := by
    funext t
    unfold fastWord
    rw [oneOrder_self,placeC]
    rfl
  change (FilteredWord.filtered (fastWord b hb (oneOrder b 0 q) 0) (retained b A 0)).getD j.val 0 = _
  rw [hw,retainedC]
  rfl

def pullC (v : Fin 32) : Fin 4 := if v=4 then 0 else if v=5 then 1 else if v=6 then 2 else 3
def mapC (q : Marked.Order 2) : Fin 4 → Fin 4 := pullC ∘ fastRowC q
lemma fastRowC_valid : ∀ q, Function.Injective (mapC q) ∧
    ∀ j, fastRowC q j = phi (mapC q j) := by decide +kernel
lemma rowC_valid (q) : Function.Injective (mapC q) ∧
    ∀ j, rowC q j = phi (mapC q j) := by
  rw [rowC_eq_fast]
  exact fastRowC_valid q
noncomputable def permC (q : Marked.Order 2) : P4 :=
  Equiv.ofBijective (mapC q) ⟨(rowC_valid q).1,Finite.surjective_of_injective (rowC_valid q).1⟩

lemma rowC_match (o : Orders) (j : Fin 4) :
    phi (permC (o 0) j) = StableCanonicalCoarsening.word b hb o A hr c j := by
  have hh : StableCanonicalCoarsening.word b hb o A hr c j = rowC (o 0) j := by
    unfold rowC
    exact stableWord_local b hb o A hr c j
  rw [hh]
  simp only [permC,Equiv.ofBijective_apply]
  exact ((rowC_valid (o 0)).2 j).symm

def rowA (q : Marked.Order 2) : Fin 2 → Fin 32 :=
  StableCanonicalCoarsening.word b hb (oneOrder b 2 q) A hr a
def markersA : Fin 4 → Fin 32 := ![4,5,12,13]
lemma placeA : fastPlace b hb 2 = markersA := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b hb 2 j = markersA j) j
lemma retainedA : retained b A 2 = {4,5} := by decide +kernel

def fastRowA (q : Marked.Order 2) (j : Fin 2) : Fin 32 :=
  (FilteredWord.filtered (fun t : Fin 4 => markersA ((SmallOrderNormalization.normalized 2 q).vertex t)) {4,5}).getD j.val 0

lemma rowA_eq_fast (q : Marked.Order 2) : rowA q = fastRowA q := by
  funext j
  change StableCanonicalCoarsening.word b hb (oneOrder b 2 q) A hr a j = _
  rw [StableCanonicalCoarsening.word_eq_getD b hb (oneOrder b 2 q) A hr a j 0]
  have hw : fastWord b hb (oneOrder b 2 q) 2 =
      fun t => markersA ((SmallOrderNormalization.normalized 2 q).vertex t) := by
    funext t
    unfold fastWord
    rw [oneOrder_self,placeA]
    rfl
  change (FilteredWord.filtered (fastWord b hb (oneOrder b 2 q) 2) (retained b A 2)).getD j.val 0 = _
  rw [hw,retainedA]
  rfl

def pullA (v : Fin 32) : Fin 2 := if v=4 then 0 else 1
def mapA (q : Marked.Order 2) : Fin 2 → Fin 2 := pullA ∘ fastRowA q
lemma fastRowA_valid : ∀ q, Function.Injective (mapA q) ∧
    ∀ j, fastRowA q j = phi ((![0,1] : Fin 2 → Fin 4) (mapA q j)) := by decide +kernel
lemma rowA_valid (q) : Function.Injective (mapA q) ∧
    ∀ j, rowA q j = phi ((![0,1] : Fin 2 → Fin 4) (mapA q j)) := by
  rw [rowA_eq_fast]
  exact fastRowA_valid q
noncomputable def permA (q : Marked.Order 2) : P2 :=
  Equiv.ofBijective (mapA q) ⟨(rowA_valid q).1,Finite.surjective_of_injective (rowA_valid q).1⟩

lemma rowA_match (o : Orders) (j : Fin 2) :
    phi ((![0,1] : Fin 2 → Fin 4) (permA (o 2) j)) = StableCanonicalCoarsening.word b hb o A hr a j := by
  have hh : StableCanonicalCoarsening.word b hb o A hr a j = rowA (o 2) j := by
    unfold rowA
    exact stableWord_local b hb o A hr a j
  rw [hh]
  simp only [permA,Equiv.ofBijective_apply]
  exact ((rowA_valid (o 2)).2 j).symm

def rowZ (q : Marked.Order 2) : Fin 2 → Fin 32 :=
  StableCanonicalCoarsening.word b hb (oneOrder b 3 q) A hr z
def markersZ : Fin 4 → Fin 32 := ![6,7,14,15]
lemma placeZ : fastPlace b hb 3 = markersZ := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b hb 3 j = markersZ j) j
lemma retainedZ : retained b A 3 = {6,7} := by decide +kernel

def fastRowZ (q : Marked.Order 2) (j : Fin 2) : Fin 32 :=
  (FilteredWord.filtered (fun t : Fin 4 => markersZ ((SmallOrderNormalization.normalized 2 q).vertex t)) {6,7}).getD j.val 0

lemma rowZ_eq_fast (q : Marked.Order 2) : rowZ q = fastRowZ q := by
  funext j
  change StableCanonicalCoarsening.word b hb (oneOrder b 3 q) A hr z j = _
  rw [StableCanonicalCoarsening.word_eq_getD b hb (oneOrder b 3 q) A hr z j 0]
  have hw : fastWord b hb (oneOrder b 3 q) 3 =
      fun t => markersZ ((SmallOrderNormalization.normalized 2 q).vertex t) := by
    funext t
    unfold fastWord
    rw [oneOrder_self,placeZ]
    rfl
  change (FilteredWord.filtered (fastWord b hb (oneOrder b 3 q) 3) (retained b A 3)).getD j.val 0 = _
  rw [hw,retainedZ]
  rfl

def pullZ (v : Fin 32) : Fin 2 := if v=6 then 0 else 1
def mapZ (q : Marked.Order 2) : Fin 2 → Fin 2 := pullZ ∘ fastRowZ q
lemma fastRowZ_valid : ∀ q, Function.Injective (mapZ q) ∧
    ∀ j, fastRowZ q j = phi ((![2,3] : Fin 2 → Fin 4) (mapZ q j)) := by decide +kernel
lemma rowZ_valid (q) : Function.Injective (mapZ q) ∧
    ∀ j, rowZ q j = phi ((![2,3] : Fin 2 → Fin 4) (mapZ q j)) := by
  rw [rowZ_eq_fast]
  exact fastRowZ_valid q
noncomputable def permZ (q : Marked.Order 2) : P2 :=
  Equiv.ofBijective (mapZ q) ⟨(rowZ_valid q).1,Finite.surjective_of_injective (rowZ_valid q).1⟩

lemma rowZ_match (o : Orders) (j : Fin 2) :
    phi ((![2,3] : Fin 2 → Fin 4) (permZ (o 3) j)) = StableCanonicalCoarsening.word b hb o A hr z j := by
  have hh : StableCanonicalCoarsening.word b hb o A hr z j = rowZ (o 3) j := by
    unfold rowZ
    exact stableWord_local b hb o A hr z j
  rw [hh]
  simp only [permZ,Equiv.ofBijective_apply]
  exact ((rowZ_valid (o 3)).2 j).symm

def edge : Fin 8 → E := ![⟨c,0⟩,⟨c,1⟩,⟨c,2⟩,⟨c,3⟩,⟨a,0⟩,⟨a,1⟩,⟨z,0⟩,⟨z,1⟩]
def back (e : E) : ℕ := if e.1.val = 0 then e.2.val else if e.1.val = 2 then 4+e.2.val else 6+e.2.val
lemma back_edge : ∀ e, back (edge e) = e.val := by decide +kernel
lemma edge_injective : Function.Injective edge := by
  intro e f h
  apply Fin.ext
  simpa only [back_edge] using congrArg back h
lemma edge_card : Fintype.card E = 8 := by decide +kernel
lemma edge_surjective : Function.Surjective edge :=
  ((Fintype.bijective_iff_injective_and_card edge).mpr
    ⟨edge_injective,by rw [Fintype.card_fin,edge_card]⟩).2

noncomputable def embedding (o : Orders) :
    Embedding (src220 (permC (o 0)) (permA (o 2)) (permZ (o 3)))
      (dst220 (permC (o 0)) (permA (o 2)) (permZ (o 3)))
      (StableCanonicalCoarsening.source b hb o A hr) (StableCanonicalCoarsening.target b hb o A hr) where
  edge := ⟨edge,edge_injective⟩
  vertex := ⟨phi,phi_injective⟩
  endpoints e := by
    fin_cases e <;>
      simp only [src220, dst220, edge, StableCanonicalCoarsening.source,
        StableCanonicalCoarsening.target, Matrix.cons_val_zero',
        Matrix.cons_val_succ', Fin.reduceAdd, Function.Embedding.coeFn_mk]
    · exact congrArg₂ (fun x y : Fin 32 => s(x,y)) (rowC_match o 0) (rowC_match o 1)
    · exact congrArg₂ (fun x y : Fin 32 => s(x,y)) (rowC_match o 1) (rowC_match o 2)
    · exact congrArg₂ (fun x y : Fin 32 => s(x,y)) (rowC_match o 2) (rowC_match o 3)
    · exact congrArg₂ (fun x y : Fin 32 => s(x,y)) (rowC_match o 3) (rowC_match o 0)
    · exact congrArg₂ (fun x y : Fin 32 => s(x,y)) (rowA_match o 0) (rowA_match o 1)
    · exact congrArg₂ (fun x y : Fin 32 => s(x,y)) (rowA_match o 1) (rowA_match o 0)
    · exact congrArg₂ (fun x y : Fin 32 => s(x,y)) (rowZ_match o 0) (rowZ_match o 1)
    · exact congrArg₂ (fun x y : Fin 32 => s(x,y)) (rowZ_match o 1) (rowZ_match o 0)

lemma map_univ (o : Orders) : Finset.univ.map (embedding o).edge = Finset.univ :=
  Finset.map_univ_of_surjective edge_surjective

lemma forced_of_lower (o : Orders)
    (h : ∃ P, Partition (code (CanonicalPairKernel.source b hb o) (CanonicalPairKernel.target b hb o))
      (PathSubstitution.Family.colorLabels A) P ∧ P.card ≤ 2) :
    ForwardAlternating (mapC (o 0)) := by
  by_contra hn
  have hp : ¬ Alternating (permC (o 0)) := by
    intro hp
    have hf := (alternating_iff_forward _).mp hp
    apply hn
    intro j
    simpa only [permC, Equiv.ofBijective_apply] using hf j
  have hnum := (embedding o).hasNumber_map_iff Finset.univ 3
  rw [map_univ] at hnum
  have hN := hnum.mpr (number220 (permC (o 0)) (permA (o 2)) (permZ (o 3)) hp)
  obtain ⟨R,hR,hcR⟩ := h
  obtain ⟨Q,hQ,hcQ⟩ := (StableCanonicalCoarsening.spectrum b hb o A hr
    (fun i => FourCanonicalCounts.arity_bound 0 i.val) (fun k => k≤2)).mp ⟨R,hR,hcR⟩
  have hlo := hN.2 Q hQ
  omega

lemma forced (o : Orders) (h : CanonicalThreeReduction.Restrictions b hb o) :
    ForwardAlternating (mapC (o 0)) := forced_of_lower o (h.2.2.2 A hA)

#print axioms forced
end Erdos184Work.FourFork00
