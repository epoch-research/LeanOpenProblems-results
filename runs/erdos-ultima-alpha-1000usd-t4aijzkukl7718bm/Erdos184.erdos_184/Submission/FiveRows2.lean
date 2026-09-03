import Submission.CanonicalLocalBounds
import Submission.FiveCanonicalCounts

/-! Row-by-row normalized-word choices for numerical pattern 2.
The hypotheses are only the selected-color maximum and three-color minimum bounds. -/
namespace Erdos184Work.FiveRows2
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open LabelKernel Erdos184Serial CanonicalThreeReduction
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option Elab.async false
noncomputable local instance {I : Type*} {m : I → ℕ} : DecidableEq (Σ i, Fin (m i)) := Classical.decEq _
abbrev b := FiveCanonicalCounts.counts 2
lemma hb : ∀ i, 2 ≤ (markers b i).card := FiveCanonicalCounts.marker_bound 2
abbrev Orders := FiveCanonicalCounts.Orders 2
abbrev E := Fin 24
abbrev W := Fin 50
lemma size_eq : FlatCanonicalKernel.size b = 24 := by decide +kernel
instance : NeZero (FlatCanonicalKernel.size b) := ⟨by rw [size_eq]; decide⟩

def words0 : Fin 60 → Fin 6 → Fin 6 := ![![0,1,2,3,4,5],![0,1,2,3,5,4],![0,1,2,4,3,5],![0,1,2,4,5,3],![0,1,2,5,3,4],![0,1,2,5,4,3],![0,1,3,2,4,5],![0,1,3,2,5,4],![0,1,3,4,2,5],![0,1,3,4,5,2],![0,1,3,5,2,4],![0,1,3,5,4,2],![0,1,4,2,3,5],![0,1,4,2,5,3],![0,1,4,3,2,5],![0,1,4,3,5,2],![0,1,4,5,2,3],![0,1,4,5,3,2],![0,1,5,2,3,4],![0,1,5,2,4,3],![0,1,5,3,2,4],![0,1,5,3,4,2],![0,1,5,4,2,3],![0,1,5,4,3,2],![0,2,1,3,4,5],![0,2,1,3,5,4],![0,2,1,4,3,5],![0,2,1,4,5,3],![0,2,1,5,3,4],![0,2,1,5,4,3],![0,2,3,1,4,5],![0,2,3,1,5,4],![0,2,3,4,1,5],![0,2,3,5,1,4],![0,2,4,1,3,5],![0,2,4,1,5,3],![0,2,4,3,1,5],![0,2,4,5,1,3],![0,2,5,1,3,4],![0,2,5,1,4,3],![0,2,5,3,1,4],![0,2,5,4,1,3],![0,3,1,2,4,5],![0,3,1,2,5,4],![0,3,1,4,2,5],![0,3,1,5,2,4],![0,3,2,1,4,5],![0,3,2,1,5,4],![0,3,2,4,1,5],![0,3,2,5,1,4],![0,3,4,1,2,5],![0,3,4,2,1,5],![0,3,5,1,2,4],![0,3,5,2,1,4],![0,4,1,2,3,5],![0,4,1,3,2,5],![0,4,2,1,3,5],![0,4,2,3,1,5],![0,4,3,1,2,5],![0,4,3,2,1,5]]
def key0 (q : Marked.Order 4) : Fin 60 := if (SmallOrderNormalization.normalized 4 q).vertex = words0 0 then 0 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 1 then 1 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 2 then 2 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 3 then 3 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 4 then 4 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 5 then 5 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 6 then 6 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 7 then 7 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 8 then 8 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 9 then 9 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 10 then 10 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 11 then 11 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 12 then 12 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 13 then 13 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 14 then 14 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 15 then 15 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 16 then 16 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 17 then 17 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 18 then 18 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 19 then 19 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 20 then 20 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 21 then 21 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 22 then 22 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 23 then 23 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 24 then 24 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 25 then 25 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 26 then 26 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 27 then 27 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 28 then 28 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 29 then 29 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 30 then 30 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 31 then 31 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 32 then 32 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 33 then 33 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 34 then 34 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 35 then 35 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 36 then 36 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 37 then 37 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 38 then 38 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 39 then 39 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 40 then 40 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 41 then 41 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 42 then 42 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 43 then 43 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 44 then 44 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 45 then 45 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 46 then 46 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 47 then 47 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 48 then 48 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 49 then 49 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 50 then 50 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 51 then 51 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 52 then 52 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 53 then 53 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 54 then 54 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 55 then 55 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 56 then 56 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 57 then 57 else if (SmallOrderNormalization.normalized 4 q).vertex = words0 58 then 58 else 59
def markers0 : Fin 6 → W := ![2,3,4,5,6,8]
lemma place0 : fastPlace b hb 0 = markers0 := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b hb 0 j = markers0 j) j

lemma valid0 : ∀ q : Marked.Order 4,
    (SmallOrderNormalization.normalized 4 q).vertex = words0 (key0 q) := by decide +kernel

lemma chosen0 (o : Orders) (h : LocalBounds b hb o) :
    (SmallOrderNormalization.normalized 4 (o 0)).vertex = words0 (key0 (o 0)) := by
  apply valid0

lemma local_word0 (o : Orders) (h : LocalBounds b hb o) (j : Fin 6) :
    fastPlace b hb 0 ((SmallOrderNormalization.normalized 4 (o 0)).vertex j) =
      markers0 (words0 (key0 (o 0)) j) := by
  rw [place0,chosen0 o h]

def words1 : Fin 12 → Fin 5 → Fin 5 := ![![0,1,2,3,4],![0,1,2,4,3],![0,1,3,2,4],![0,1,3,4,2],![0,1,4,2,3],![0,1,4,3,2],![0,2,1,3,4],![0,2,1,4,3],![0,2,3,1,4],![0,2,4,1,3],![0,3,1,2,4],![0,3,2,1,4]]
def key1 (q : Marked.Order 3) : Fin 12 := if (SmallOrderNormalization.normalized 3 q).vertex = words1 0 then 0 else if (SmallOrderNormalization.normalized 3 q).vertex = words1 1 then 1 else if (SmallOrderNormalization.normalized 3 q).vertex = words1 2 then 2 else if (SmallOrderNormalization.normalized 3 q).vertex = words1 3 then 3 else if (SmallOrderNormalization.normalized 3 q).vertex = words1 4 then 4 else if (SmallOrderNormalization.normalized 3 q).vertex = words1 5 then 5 else if (SmallOrderNormalization.normalized 3 q).vertex = words1 6 then 6 else if (SmallOrderNormalization.normalized 3 q).vertex = words1 7 then 7 else if (SmallOrderNormalization.normalized 3 q).vertex = words1 8 then 8 else if (SmallOrderNormalization.normalized 3 q).vertex = words1 9 then 9 else if (SmallOrderNormalization.normalized 3 q).vertex = words1 10 then 10 else 11
def markers1 : Fin 5 → W := ![2,3,14,16,18]
lemma place1 : fastPlace b hb 1 = markers1 := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b hb 1 j = markers1 j) j

lemma valid1 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 q).vertex = words1 (key1 q) := by decide +kernel

lemma chosen1 (o : Orders) (h : LocalBounds b hb o) :
    (SmallOrderNormalization.normalized 3 (o 1)).vertex = words1 (key1 (o 1)) := by
  apply valid1

lemma local_word1 (o : Orders) (h : LocalBounds b hb o) (j : Fin 5) :
    fastPlace b hb 1 ((SmallOrderNormalization.normalized 3 (o 1)).vertex j) =
      markers1 (words1 (key1 (o 1)) j) := by
  rw [place1,chosen1 o h]

def words2 : Fin 12 → Fin 5 → Fin 5 := ![![0,1,2,3,4],![0,1,2,4,3],![0,1,3,2,4],![0,1,3,4,2],![0,1,4,2,3],![0,1,4,3,2],![0,2,1,3,4],![0,2,1,4,3],![0,2,3,1,4],![0,2,4,1,3],![0,3,1,2,4],![0,3,2,1,4]]
def key2 (q : Marked.Order 3) : Fin 12 := if (SmallOrderNormalization.normalized 3 q).vertex = words2 0 then 0 else if (SmallOrderNormalization.normalized 3 q).vertex = words2 1 then 1 else if (SmallOrderNormalization.normalized 3 q).vertex = words2 2 then 2 else if (SmallOrderNormalization.normalized 3 q).vertex = words2 3 then 3 else if (SmallOrderNormalization.normalized 3 q).vertex = words2 4 then 4 else if (SmallOrderNormalization.normalized 3 q).vertex = words2 5 then 5 else if (SmallOrderNormalization.normalized 3 q).vertex = words2 6 then 6 else if (SmallOrderNormalization.normalized 3 q).vertex = words2 7 then 7 else if (SmallOrderNormalization.normalized 3 q).vertex = words2 8 then 8 else if (SmallOrderNormalization.normalized 3 q).vertex = words2 9 then 9 else if (SmallOrderNormalization.normalized 3 q).vertex = words2 10 then 10 else 11
def markers2 : Fin 5 → W := ![4,5,14,26,28]
lemma place2 : fastPlace b hb 2 = markers2 := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b hb 2 j = markers2 j) j

lemma valid2 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 q).vertex = words2 (key2 q) := by decide +kernel

lemma chosen2 (o : Orders) (h : LocalBounds b hb o) :
    (SmallOrderNormalization.normalized 3 (o 2)).vertex = words2 (key2 (o 2)) := by
  apply valid2

lemma local_word2 (o : Orders) (h : LocalBounds b hb o) (j : Fin 5) :
    fastPlace b hb 2 ((SmallOrderNormalization.normalized 3 (o 2)).vertex j) =
      markers2 (words2 (key2 (o 2)) j) := by
  rw [place2,chosen2 o h]

def words3 : Fin 3 → Fin 4 → Fin 4 := ![![0,1,2,3],![0,1,3,2],![0,2,1,3]]
def key3 (q : Marked.Order 2) : Fin 3 := if (SmallOrderNormalization.normalized 2 q).vertex = words3 0 then 0 else if (SmallOrderNormalization.normalized 2 q).vertex = words3 1 then 1 else 2
def markers3 : Fin 4 → W := ![6,16,26,38]
lemma place3 : fastPlace b hb 3 = markers3 := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b hb 3 j = markers3 j) j

lemma valid3 : ∀ q : Marked.Order 2,
    (SmallOrderNormalization.normalized 2 q).vertex = words3 (key3 q) := by decide +kernel

lemma chosen3 (o : Orders) (h : LocalBounds b hb o) :
    (SmallOrderNormalization.normalized 2 (o 3)).vertex = words3 (key3 (o 3)) := by
  apply valid3

lemma local_word3 (o : Orders) (h : LocalBounds b hb o) (j : Fin 4) :
    fastPlace b hb 3 ((SmallOrderNormalization.normalized 2 (o 3)).vertex j) =
      markers3 (words3 (key3 (o 3)) j) := by
  rw [place3,chosen3 o h]

def words4 : Fin 3 → Fin 4 → Fin 4 := ![![0,1,2,3],![0,1,3,2],![0,2,1,3]]
def key4 (q : Marked.Order 2) : Fin 3 := if (SmallOrderNormalization.normalized 2 q).vertex = words4 0 then 0 else if (SmallOrderNormalization.normalized 2 q).vertex = words4 1 then 1 else 2
def markers4 : Fin 4 → W := ![8,18,28,38]
lemma place4 : fastPlace b hb 4 = markers4 := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b hb 4 j = markers4 j) j

lemma valid4 : ∀ q : Marked.Order 2,
    (SmallOrderNormalization.normalized 2 q).vertex = words4 (key4 q) := by decide +kernel

lemma chosen4 (o : Orders) (h : LocalBounds b hb o) :
    (SmallOrderNormalization.normalized 2 (o 4)).vertex = words4 (key4 (o 4)) := by
  apply valid4

lemma local_word4 (o : Orders) (h : LocalBounds b hb o) (j : Fin 4) :
    fastPlace b hb 4 ((SmallOrderNormalization.normalized 2 (o 4)).vertex j) =
      markers4 (words4 (key4 (o 4)) j) := by
  rw [place4,chosen4 o h]

def srcAt (q0 : Fin 60) (q1 : Fin 12) (q2 : Fin 12) (q3 : Fin 3) (q4 : Fin 3) : E → W := ![markers0 (words0 q0 0),markers0 (words0 q0 1),markers0 (words0 q0 2),markers0 (words0 q0 3),markers0 (words0 q0 4),markers0 (words0 q0 5),markers1 (words1 q1 0),markers1 (words1 q1 1),markers1 (words1 q1 2),markers1 (words1 q1 3),markers1 (words1 q1 4),markers2 (words2 q2 0),markers2 (words2 q2 1),markers2 (words2 q2 2),markers2 (words2 q2 3),markers2 (words2 q2 4),markers3 (words3 q3 0),markers3 (words3 q3 1),markers3 (words3 q3 2),markers3 (words3 q3 3),markers4 (words4 q4 0),markers4 (words4 q4 1),markers4 (words4 q4 2),markers4 (words4 q4 3)]
def dstAt (q0 : Fin 60) (q1 : Fin 12) (q2 : Fin 12) (q3 : Fin 3) (q4 : Fin 3) : E → W := ![markers0 (words0 q0 1),markers0 (words0 q0 2),markers0 (words0 q0 3),markers0 (words0 q0 4),markers0 (words0 q0 5),markers0 (words0 q0 0),markers1 (words1 q1 1),markers1 (words1 q1 2),markers1 (words1 q1 3),markers1 (words1 q1 4),markers1 (words1 q1 0),markers2 (words2 q2 1),markers2 (words2 q2 2),markers2 (words2 q2 3),markers2 (words2 q2 4),markers2 (words2 q2 0),markers3 (words3 q3 1),markers3 (words3 q3 2),markers3 (words3 q3 3),markers3 (words3 q3 0),markers4 (words4 q4 1),markers4 (words4 q4 2),markers4 (words4 q4 3),markers4 (words4 q4 0)]

lemma flat_src (o : Orders) (h : LocalBounds b hb o) (e : E) :
    FlatCanonicalKernel.src b hb o e = srcAt (key0 (o 0)) (key1 (o 1)) (key2 (o 2)) (key3 (o 3)) (key4 (o 4)) e := by
  fin_cases e <;> simp only [srcAt,Matrix.cons_val_zero',Matrix.cons_val_succ']
  · exact local_word0 o h 0
  · exact local_word0 o h 1
  · exact local_word0 o h 2
  · exact local_word0 o h 3
  · exact local_word0 o h 4
  · exact local_word0 o h 5
  · exact local_word1 o h 0
  · exact local_word1 o h 1
  · exact local_word1 o h 2
  · exact local_word1 o h 3
  · exact local_word1 o h 4
  · exact local_word2 o h 0
  · exact local_word2 o h 1
  · exact local_word2 o h 2
  · exact local_word2 o h 3
  · exact local_word2 o h 4
  · exact local_word3 o h 0
  · exact local_word3 o h 1
  · exact local_word3 o h 2
  · exact local_word3 o h 3
  · exact local_word4 o h 0
  · exact local_word4 o h 1
  · exact local_word4 o h 2
  · exact local_word4 o h 3

lemma flat_dst (o : Orders) (h : LocalBounds b hb o) (e : E) :
    FlatCanonicalKernel.dst b hb o e = dstAt (key0 (o 0)) (key1 (o 1)) (key2 (o 2)) (key3 (o 3)) (key4 (o 4)) e := by
  fin_cases e <;> simp only [dstAt,Matrix.cons_val_zero',Matrix.cons_val_succ']
  · exact local_word0 o h 1
  · exact local_word0 o h 2
  · exact local_word0 o h 3
  · exact local_word0 o h 4
  · exact local_word0 o h 5
  · exact local_word0 o h 0
  · exact local_word1 o h 1
  · exact local_word1 o h 2
  · exact local_word1 o h 3
  · exact local_word1 o h 4
  · exact local_word1 o h 0
  · exact local_word2 o h 1
  · exact local_word2 o h 2
  · exact local_word2 o h 3
  · exact local_word2 o h 4
  · exact local_word2 o h 0
  · exact local_word3 o h 1
  · exact local_word3 o h 2
  · exact local_word3 o h 3
  · exact local_word3 o h 0
  · exact local_word4 o h 1
  · exact local_word4 o h 2
  · exact local_word4 o h 3
  · exact local_word4 o h 0

def key (o : Orders) : ℕ := 1296 * (key0 (o 0)).val + 108 * (key1 (o 1)).val + 9 * (key2 (o 2)).val + 3 * (key3 (o 3)).val + 1 * (key4 (o 4)).val
lemma key_lt (o : Orders) : key o < 77760 := by
  have h0 := (key0 (o 0)).isLt
  have h1 := (key1 (o 1)).isLt
  have h2 := (key2 (o 2)).isLt
  have h3 := (key3 (o 3)).isLt
  have h4 := (key4 (o 4)).isLt
  unfold key
  omega

def digit0 (k : ℕ) : Fin 60 := ⟨k / 1296 % 60,Nat.mod_lt _ (by decide)⟩
lemma digit_key0 (o : Orders) : digit0 (key o) = key0 (o 0) := by
  apply Fin.ext
  have h0 := (key0 (o 0)).isLt
  have h1 := (key1 (o 1)).isLt
  have h2 := (key2 (o 2)).isLt
  have h3 := (key3 (o 3)).isLt
  have h4 := (key4 (o 4)).isLt
  dsimp only [digit0,key]
  omega

def digit1 (k : ℕ) : Fin 12 := ⟨k / 108 % 12,Nat.mod_lt _ (by decide)⟩
lemma digit_key1 (o : Orders) : digit1 (key o) = key1 (o 1) := by
  apply Fin.ext
  have h0 := (key0 (o 0)).isLt
  have h1 := (key1 (o 1)).isLt
  have h2 := (key2 (o 2)).isLt
  have h3 := (key3 (o 3)).isLt
  have h4 := (key4 (o 4)).isLt
  dsimp only [digit1,key]
  omega

def digit2 (k : ℕ) : Fin 12 := ⟨k / 9 % 12,Nat.mod_lt _ (by decide)⟩
lemma digit_key2 (o : Orders) : digit2 (key o) = key2 (o 2) := by
  apply Fin.ext
  have h0 := (key0 (o 0)).isLt
  have h1 := (key1 (o 1)).isLt
  have h2 := (key2 (o 2)).isLt
  have h3 := (key3 (o 3)).isLt
  have h4 := (key4 (o 4)).isLt
  dsimp only [digit2,key]
  omega

def digit3 (k : ℕ) : Fin 3 := ⟨k / 3 % 3,Nat.mod_lt _ (by decide)⟩
lemma digit_key3 (o : Orders) : digit3 (key o) = key3 (o 3) := by
  apply Fin.ext
  have h0 := (key0 (o 0)).isLt
  have h1 := (key1 (o 1)).isLt
  have h2 := (key2 (o 2)).isLt
  have h3 := (key3 (o 3)).isLt
  have h4 := (key4 (o 4)).isLt
  dsimp only [digit3,key]
  omega

def digit4 (k : ℕ) : Fin 3 := ⟨k / 1 % 3,Nat.mod_lt _ (by decide)⟩
lemma digit_key4 (o : Orders) : digit4 (key o) = key4 (o 4) := by
  apply Fin.ext
  have h0 := (key0 (o 0)).isLt
  have h1 := (key1 (o 1)).isLt
  have h2 := (key2 (o 2)).isLt
  have h3 := (key3 (o 3)).isLt
  have h4 := (key4 (o 4)).isLt
  dsimp only [digit4,key]
  omega

#print axioms flat_src
#print axioms flat_dst
end Erdos184Work.FiveRows2
