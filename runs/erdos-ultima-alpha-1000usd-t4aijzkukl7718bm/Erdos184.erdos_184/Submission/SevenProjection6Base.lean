import Submission.SevenCanonicalCounts
import Submission.LargerColoredCoarsening
import Submission.FilteredCyclicWord
import Submission.SixCanonicalCounts

/-! Five-color projection of seven-color pattern 0, omitting color 6.
The result is a necessary word catalogue, not a global exclusion. -/
open scoped Classical
namespace Erdos184Work.SevenProjection6
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open LabelKernel Erdos184Serial CanonicalSubsetCoarsening LocalCanonicalRows CanonicalThreeReduction
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.unusedSimpArgs false
noncomputable local instance projectionDecEq {I : Type*} {m : I → ℕ} :
    DecidableEq (Σ i, Fin (m i)) := Classical.decEq _
abbrev b := SevenCanonicalCounts.counts 0
lemma hb : ∀ i, 2 ≤ (markers b i).card := SevenCanonicalCounts.marker_bound 0
abbrev Orders := SevenCanonicalCounts.Orders 0
abbrev b₀ := SixCanonicalCounts.counts 0
lemma hb₀ : ∀ i, 2 ≤ (markers b₀ i).card := SixCanonicalCounts.marker_bound 0
abbrev SmallOrders := SixCanonicalCounts.Orders 0
def A : Finset (Fin 7) := {0,1,2,3,4,5}
lemma hr : ∀ i : A, 2 ≤ (retained b A i.val).card := by decide +kernel
def c0 : A := ⟨0,by decide⟩
def c1 : A := ⟨1,by decide⟩
def c2 : A := ⟨2,by decide⟩
def c3 : A := ⟨3,by decide⟩
def c4 : A := ⟨4,by decide⟩
def c5 : A := ⟨5,by decide⟩
def color : Fin 6 → A := ![c0,c1,c2,c3,c4,c5]
lemma color_bijective : Function.Bijective color := by decide +kernel
noncomputable def T : Fin 6 ≃ A := Equiv.ofBijective color color_bijective
def phi : Fin 72 → Fin 98 := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,18,16,20,17,22,19,24,21,23,25,26,27,28,29,34,30,36,31,38,32,33,35,37,39,40,41,42,43,50,44,52,45,46,47,48,49,51,53,54,55,56,57,66,58,59,60,61,62,63,64,65,67,68,69,70,71]
lemma phi_injective : Function.Injective phi := by decide +kernel

def markers0 : Fin 6 → Fin 98 := ![2,4,6,8,10,12]
lemma place0 : fastPlace b hb 0 = markers0 := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b hb 0 j = markers0 j) j
lemma retained0 : retained b A 0 = {2,4,6,8,10} := by decide +kernel

def smallMarkers0 : Fin 5 → Fin 72 := ![2,4,6,8,10]
lemma smallPlace0 : fastPlace b₀ hb₀ 0 = smallMarkers0 := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b₀ hb₀ 0 j = smallMarkers0 j) j

def row0 (q : Marked.Order 4) : Fin 5 → Fin 98 :=
  StableCanonicalCoarsening.word b hb (oneOrder b 0 q) A hr c0
def fastRow0 (q : Marked.Order 4) (j : Fin 5) : Fin 98 :=
  (FilteredWord.filtered (fun t : Fin 6 => markers0 ((SmallOrderNormalization.normalized 4 q).vertex t))
    {2,4,6,8,10}).getD j.val 0
lemma row0_eq_fast (q : Marked.Order 4) : row0 q = fastRow0 q := by
  funext j
  change StableCanonicalCoarsening.word b hb (oneOrder b 0 q) A hr c0 j = _
  rw [StableCanonicalCoarsening.word_eq_getD b hb (oneOrder b 0 q) A hr c0 j 0]
  have hw : fastWord b hb (oneOrder b 0 q) 0 =
      fun s => markers0 ((SmallOrderNormalization.normalized 4 q).vertex s) := by
    funext s
    unfold fastWord
    rw [oneOrder_self,place0]
    rfl
  change (FilteredWord.filtered (fastWord b hb (oneOrder b 0 q) 0) (retained b A 0)).getD j.val 0 = _
  rw [hw,retained0]
  rfl

def wordCode0 (q : Marked.Order 4) : ℕ :=
  6 * ((SmallOrderNormalization.normalized 4 q).vertex 1).val + 36 * ((SmallOrderNormalization.normalized 4 q).vertex 2).val + 216 * ((SmallOrderNormalization.normalized 4 q).vertex 3).val + 1296 * ((SmallOrderNormalization.normalized 4 q).vertex 4).val + 7776 * ((SmallOrderNormalization.normalized 4 q).vertex 5).val
def data0 : ℕ → Marked.Order 3 × (Fin 5 → Fin 5)
  | 44790 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 38310 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 43710 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 30750 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 36150 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 29670 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 44610 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 38130 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 42450 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 23010 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 34890 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 21930 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 43350 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 30390 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 42270 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 22830 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 27150 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 20670 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 35610 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 29130 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 34530 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 21570 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 26970 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 20490 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 44760 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 38280 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 43680 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 30720 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 36120 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 29640 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 44400 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 37920 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 41160 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 33600 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 43140 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 30180 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 40980 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![4,3,2,1,0])
  | 25860 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 35400 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 28920 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 33240 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 25680 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 44550 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 38070 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 42390 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 34830 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 44370 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 37890 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 41130 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 33570 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 41850 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 40770 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 34110 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 33030 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 43260 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 42180 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 43080 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 40920 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 41820 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![4,3,2,1,0])
  | 40740 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![4,3,2,1,0])
  | _ => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])

def smallOrder0 (q : Marked.Order 4) : Marked.Order 3 := (data0 (wordCode0 q)).1
def edgeMap0 (q : Marked.Order 4) : Fin 5 → Fin 5 := (data0 (wordCode0 q)).2
lemma edgeMap0_bijective : ∀ q, Function.Bijective (edgeMap0 q) := by decide +kernel
noncomputable def edgeEquiv0 (q : Marked.Order 4) : Equiv.Perm (Fin 5) :=
  Equiv.ofBijective (edgeMap0 q) (edgeMap0_bijective q)
lemma endpoints0_valid : ∀ q : Marked.Order 4, ∀ j : Fin 5,
    s(phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 q)).vertex j)),
      phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 q)).vertex (j+(1 : Fin 5))))) =
    s(fastRow0 q (edgeMap0 q j),fastRow0 q (edgeMap0 q j+1)) := by decide +kernel
lemma row0_local (o : Orders) (j : Fin 5) :
    StableCanonicalCoarsening.word b hb o A hr c0 j = fastRow0 (o 0) j := by
  rw [stableWord_local]
  exact congrFun (row0_eq_fast (o 0)) j
#check endpoints0_valid

def markers1 : Fin 6 → Fin 98 := ![2,18,20,22,24,26]
lemma place1 : fastPlace b hb 1 = markers1 := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b hb 1 j = markers1 j) j
lemma retained1 : retained b A 1 = {2,18,20,22,24} := by decide +kernel

def smallMarkers1 : Fin 5 → Fin 72 := ![2,16,18,20,22]
lemma smallPlace1 : fastPlace b₀ hb₀ 1 = smallMarkers1 := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b₀ hb₀ 1 j = smallMarkers1 j) j

def row1 (q : Marked.Order 4) : Fin 5 → Fin 98 :=
  StableCanonicalCoarsening.word b hb (oneOrder b 1 q) A hr c1
def fastRow1 (q : Marked.Order 4) (j : Fin 5) : Fin 98 :=
  (FilteredWord.filtered (fun t : Fin 6 => markers1 ((SmallOrderNormalization.normalized 4 q).vertex t))
    {2,18,20,22,24}).getD j.val 0
lemma row1_eq_fast (q : Marked.Order 4) : row1 q = fastRow1 q := by
  funext j
  change StableCanonicalCoarsening.word b hb (oneOrder b 1 q) A hr c1 j = _
  rw [StableCanonicalCoarsening.word_eq_getD b hb (oneOrder b 1 q) A hr c1 j 0]
  have hw : fastWord b hb (oneOrder b 1 q) 1 =
      fun s => markers1 ((SmallOrderNormalization.normalized 4 q).vertex s) := by
    funext s
    unfold fastWord
    rw [oneOrder_self,place1]
    rfl
  change (FilteredWord.filtered (fastWord b hb (oneOrder b 1 q) 1) (retained b A 1)).getD j.val 0 = _
  rw [hw,retained1]
  rfl

def wordCode1 (q : Marked.Order 4) : ℕ :=
  6 * ((SmallOrderNormalization.normalized 4 q).vertex 1).val + 36 * ((SmallOrderNormalization.normalized 4 q).vertex 2).val + 216 * ((SmallOrderNormalization.normalized 4 q).vertex 3).val + 1296 * ((SmallOrderNormalization.normalized 4 q).vertex 4).val + 7776 * ((SmallOrderNormalization.normalized 4 q).vertex 5).val
def data1 : ℕ → Marked.Order 3 × (Fin 5 → Fin 5)
  | 44790 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 38310 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 43710 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 30750 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 36150 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 29670 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 44610 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 38130 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 42450 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 23010 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 34890 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 21930 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 43350 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 30390 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 42270 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 22830 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 27150 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 20670 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 35610 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 29130 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 34530 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 21570 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 26970 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 20490 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 44760 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 38280 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 43680 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 30720 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 36120 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 29640 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 44400 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 37920 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 41160 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 33600 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 43140 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 30180 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 40980 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![4,3,2,1,0])
  | 25860 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 35400 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 28920 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 33240 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 25680 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 44550 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 38070 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 42390 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 34830 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 44370 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 37890 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 41130 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 33570 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 41850 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 40770 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 34110 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 33030 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 43260 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 42180 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 43080 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 40920 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 41820 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![4,3,2,1,0])
  | 40740 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![4,3,2,1,0])
  | _ => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])

def smallOrder1 (q : Marked.Order 4) : Marked.Order 3 := (data1 (wordCode1 q)).1
def edgeMap1 (q : Marked.Order 4) : Fin 5 → Fin 5 := (data1 (wordCode1 q)).2
lemma edgeMap1_bijective : ∀ q, Function.Bijective (edgeMap1 q) := by decide +kernel
noncomputable def edgeEquiv1 (q : Marked.Order 4) : Equiv.Perm (Fin 5) :=
  Equiv.ofBijective (edgeMap1 q) (edgeMap1_bijective q)
lemma endpoints1_valid : ∀ q : Marked.Order 4, ∀ j : Fin 5,
    s(phi (smallMarkers1 ((SmallOrderNormalization.normalized 3 (smallOrder1 q)).vertex j)),
      phi (smallMarkers1 ((SmallOrderNormalization.normalized 3 (smallOrder1 q)).vertex (j+(1 : Fin 5))))) =
    s(fastRow1 q (edgeMap1 q j),fastRow1 q (edgeMap1 q j+1)) := by decide +kernel
lemma row1_local (o : Orders) (j : Fin 5) :
    StableCanonicalCoarsening.word b hb o A hr c1 j = fastRow1 (o 1) j := by
  rw [stableWord_local]
  exact congrFun (row1_eq_fast (o 1)) j
#check endpoints1_valid

def markers2 : Fin 6 → Fin 98 := ![4,18,34,36,38,40]
lemma place2 : fastPlace b hb 2 = markers2 := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b hb 2 j = markers2 j) j
lemma retained2 : retained b A 2 = {4,18,34,36,38} := by decide +kernel

def smallMarkers2 : Fin 5 → Fin 72 := ![4,16,30,32,34]
lemma smallPlace2 : fastPlace b₀ hb₀ 2 = smallMarkers2 := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b₀ hb₀ 2 j = smallMarkers2 j) j

def row2 (q : Marked.Order 4) : Fin 5 → Fin 98 :=
  StableCanonicalCoarsening.word b hb (oneOrder b 2 q) A hr c2
def fastRow2 (q : Marked.Order 4) (j : Fin 5) : Fin 98 :=
  (FilteredWord.filtered (fun t : Fin 6 => markers2 ((SmallOrderNormalization.normalized 4 q).vertex t))
    {4,18,34,36,38}).getD j.val 0
lemma row2_eq_fast (q : Marked.Order 4) : row2 q = fastRow2 q := by
  funext j
  change StableCanonicalCoarsening.word b hb (oneOrder b 2 q) A hr c2 j = _
  rw [StableCanonicalCoarsening.word_eq_getD b hb (oneOrder b 2 q) A hr c2 j 0]
  have hw : fastWord b hb (oneOrder b 2 q) 2 =
      fun s => markers2 ((SmallOrderNormalization.normalized 4 q).vertex s) := by
    funext s
    unfold fastWord
    rw [oneOrder_self,place2]
    rfl
  change (FilteredWord.filtered (fastWord b hb (oneOrder b 2 q) 2) (retained b A 2)).getD j.val 0 = _
  rw [hw,retained2]
  rfl

def wordCode2 (q : Marked.Order 4) : ℕ :=
  6 * ((SmallOrderNormalization.normalized 4 q).vertex 1).val + 36 * ((SmallOrderNormalization.normalized 4 q).vertex 2).val + 216 * ((SmallOrderNormalization.normalized 4 q).vertex 3).val + 1296 * ((SmallOrderNormalization.normalized 4 q).vertex 4).val + 7776 * ((SmallOrderNormalization.normalized 4 q).vertex 5).val
def data2 : ℕ → Marked.Order 3 × (Fin 5 → Fin 5)
  | 44790 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 38310 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 43710 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 30750 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 36150 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 29670 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 44610 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 38130 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 42450 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 23010 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 34890 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 21930 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 43350 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 30390 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 42270 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 22830 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 27150 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 20670 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 35610 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 29130 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 34530 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 21570 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 26970 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 20490 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 44760 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 38280 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 43680 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 30720 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 36120 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 29640 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 44400 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 37920 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 41160 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 33600 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 43140 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 30180 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 40980 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![4,3,2,1,0])
  | 25860 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 35400 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 28920 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 33240 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 25680 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 44550 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 38070 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 42390 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 34830 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 44370 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 37890 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 41130 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 33570 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 41850 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 40770 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 34110 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 33030 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 43260 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 42180 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 43080 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 40920 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 41820 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![4,3,2,1,0])
  | 40740 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![4,3,2,1,0])
  | _ => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])

def smallOrder2 (q : Marked.Order 4) : Marked.Order 3 := (data2 (wordCode2 q)).1
def edgeMap2 (q : Marked.Order 4) : Fin 5 → Fin 5 := (data2 (wordCode2 q)).2
lemma edgeMap2_bijective : ∀ q, Function.Bijective (edgeMap2 q) := by decide +kernel
noncomputable def edgeEquiv2 (q : Marked.Order 4) : Equiv.Perm (Fin 5) :=
  Equiv.ofBijective (edgeMap2 q) (edgeMap2_bijective q)
lemma endpoints2_valid : ∀ q : Marked.Order 4, ∀ j : Fin 5,
    s(phi (smallMarkers2 ((SmallOrderNormalization.normalized 3 (smallOrder2 q)).vertex j)),
      phi (smallMarkers2 ((SmallOrderNormalization.normalized 3 (smallOrder2 q)).vertex (j+(1 : Fin 5))))) =
    s(fastRow2 q (edgeMap2 q j),fastRow2 q (edgeMap2 q j+1)) := by decide +kernel
lemma row2_local (o : Orders) (j : Fin 5) :
    StableCanonicalCoarsening.word b hb o A hr c2 j = fastRow2 (o 2) j := by
  rw [stableWord_local]
  exact congrFun (row2_eq_fast (o 2)) j
#check endpoints2_valid

def markers3 : Fin 6 → Fin 98 := ![6,20,34,50,52,54]
lemma place3 : fastPlace b hb 3 = markers3 := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b hb 3 j = markers3 j) j
lemma retained3 : retained b A 3 = {6,20,34,50,52} := by decide +kernel

def smallMarkers3 : Fin 5 → Fin 72 := ![6,18,30,44,46]
lemma smallPlace3 : fastPlace b₀ hb₀ 3 = smallMarkers3 := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b₀ hb₀ 3 j = smallMarkers3 j) j

def row3 (q : Marked.Order 4) : Fin 5 → Fin 98 :=
  StableCanonicalCoarsening.word b hb (oneOrder b 3 q) A hr c3
def fastRow3 (q : Marked.Order 4) (j : Fin 5) : Fin 98 :=
  (FilteredWord.filtered (fun t : Fin 6 => markers3 ((SmallOrderNormalization.normalized 4 q).vertex t))
    {6,20,34,50,52}).getD j.val 0
lemma row3_eq_fast (q : Marked.Order 4) : row3 q = fastRow3 q := by
  funext j
  change StableCanonicalCoarsening.word b hb (oneOrder b 3 q) A hr c3 j = _
  rw [StableCanonicalCoarsening.word_eq_getD b hb (oneOrder b 3 q) A hr c3 j 0]
  have hw : fastWord b hb (oneOrder b 3 q) 3 =
      fun s => markers3 ((SmallOrderNormalization.normalized 4 q).vertex s) := by
    funext s
    unfold fastWord
    rw [oneOrder_self,place3]
    rfl
  change (FilteredWord.filtered (fastWord b hb (oneOrder b 3 q) 3) (retained b A 3)).getD j.val 0 = _
  rw [hw,retained3]
  rfl

def wordCode3 (q : Marked.Order 4) : ℕ :=
  6 * ((SmallOrderNormalization.normalized 4 q).vertex 1).val + 36 * ((SmallOrderNormalization.normalized 4 q).vertex 2).val + 216 * ((SmallOrderNormalization.normalized 4 q).vertex 3).val + 1296 * ((SmallOrderNormalization.normalized 4 q).vertex 4).val + 7776 * ((SmallOrderNormalization.normalized 4 q).vertex 5).val
def data3 : ℕ → Marked.Order 3 × (Fin 5 → Fin 5)
  | 44790 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 38310 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 43710 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 30750 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 36150 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 29670 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 44610 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 38130 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 42450 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 23010 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 34890 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 21930 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 43350 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 30390 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 42270 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 22830 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 27150 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 20670 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 35610 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 29130 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 34530 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 21570 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 26970 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 20490 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 44760 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 38280 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 43680 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 30720 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 36120 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 29640 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 44400 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 37920 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 41160 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 33600 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 43140 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 30180 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 40980 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![4,3,2,1,0])
  | 25860 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 35400 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 28920 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 33240 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 25680 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 44550 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 38070 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 42390 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 34830 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 44370 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 37890 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 41130 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 33570 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 41850 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 40770 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 34110 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 33030 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 43260 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 42180 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 43080 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 40920 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 41820 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![4,3,2,1,0])
  | 40740 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![4,3,2,1,0])
  | _ => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])

def smallOrder3 (q : Marked.Order 4) : Marked.Order 3 := (data3 (wordCode3 q)).1
def edgeMap3 (q : Marked.Order 4) : Fin 5 → Fin 5 := (data3 (wordCode3 q)).2
lemma edgeMap3_bijective : ∀ q, Function.Bijective (edgeMap3 q) := by decide +kernel
noncomputable def edgeEquiv3 (q : Marked.Order 4) : Equiv.Perm (Fin 5) :=
  Equiv.ofBijective (edgeMap3 q) (edgeMap3_bijective q)
lemma endpoints3_valid : ∀ q : Marked.Order 4, ∀ j : Fin 5,
    s(phi (smallMarkers3 ((SmallOrderNormalization.normalized 3 (smallOrder3 q)).vertex j)),
      phi (smallMarkers3 ((SmallOrderNormalization.normalized 3 (smallOrder3 q)).vertex (j+(1 : Fin 5))))) =
    s(fastRow3 q (edgeMap3 q j),fastRow3 q (edgeMap3 q j+1)) := by decide +kernel
lemma row3_local (o : Orders) (j : Fin 5) :
    StableCanonicalCoarsening.word b hb o A hr c3 j = fastRow3 (o 3) j := by
  rw [stableWord_local]
  exact congrFun (row3_eq_fast (o 3)) j
#check endpoints3_valid

def markers4 : Fin 6 → Fin 98 := ![8,22,36,50,66,68]
lemma place4 : fastPlace b hb 4 = markers4 := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b hb 4 j = markers4 j) j
lemma retained4 : retained b A 4 = {8,22,36,50,66} := by decide +kernel

def smallMarkers4 : Fin 5 → Fin 72 := ![8,20,32,44,58]
lemma smallPlace4 : fastPlace b₀ hb₀ 4 = smallMarkers4 := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b₀ hb₀ 4 j = smallMarkers4 j) j

def row4 (q : Marked.Order 4) : Fin 5 → Fin 98 :=
  StableCanonicalCoarsening.word b hb (oneOrder b 4 q) A hr c4
def fastRow4 (q : Marked.Order 4) (j : Fin 5) : Fin 98 :=
  (FilteredWord.filtered (fun t : Fin 6 => markers4 ((SmallOrderNormalization.normalized 4 q).vertex t))
    {8,22,36,50,66}).getD j.val 0
lemma row4_eq_fast (q : Marked.Order 4) : row4 q = fastRow4 q := by
  funext j
  change StableCanonicalCoarsening.word b hb (oneOrder b 4 q) A hr c4 j = _
  rw [StableCanonicalCoarsening.word_eq_getD b hb (oneOrder b 4 q) A hr c4 j 0]
  have hw : fastWord b hb (oneOrder b 4 q) 4 =
      fun s => markers4 ((SmallOrderNormalization.normalized 4 q).vertex s) := by
    funext s
    unfold fastWord
    rw [oneOrder_self,place4]
    rfl
  change (FilteredWord.filtered (fastWord b hb (oneOrder b 4 q) 4) (retained b A 4)).getD j.val 0 = _
  rw [hw,retained4]
  rfl

def wordCode4 (q : Marked.Order 4) : ℕ :=
  6 * ((SmallOrderNormalization.normalized 4 q).vertex 1).val + 36 * ((SmallOrderNormalization.normalized 4 q).vertex 2).val + 216 * ((SmallOrderNormalization.normalized 4 q).vertex 3).val + 1296 * ((SmallOrderNormalization.normalized 4 q).vertex 4).val + 7776 * ((SmallOrderNormalization.normalized 4 q).vertex 5).val
def data4 : ℕ → Marked.Order 3 × (Fin 5 → Fin 5)
  | 44790 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 38310 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 43710 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 30750 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 36150 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 29670 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 44610 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 38130 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 42450 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 23010 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 34890 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 21930 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 43350 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 30390 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 42270 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 22830 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 27150 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 20670 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 35610 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 29130 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 34530 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 21570 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 26970 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 20490 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 44760 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 38280 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 43680 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 30720 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 36120 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 29640 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 44400 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 37920 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 41160 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 33600 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 43140 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 30180 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 40980 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![4,3,2,1,0])
  | 25860 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 35400 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 28920 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 33240 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 25680 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 44550 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 38070 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 42390 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 34830 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 44370 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 37890 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 41130 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 33570 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 41850 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 40770 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 34110 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 33030 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 43260 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 42180 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 43080 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 40920 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 41820 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![4,3,2,1,0])
  | 40740 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![4,3,2,1,0])
  | _ => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])

def smallOrder4 (q : Marked.Order 4) : Marked.Order 3 := (data4 (wordCode4 q)).1
def edgeMap4 (q : Marked.Order 4) : Fin 5 → Fin 5 := (data4 (wordCode4 q)).2
lemma edgeMap4_bijective : ∀ q, Function.Bijective (edgeMap4 q) := by decide +kernel
noncomputable def edgeEquiv4 (q : Marked.Order 4) : Equiv.Perm (Fin 5) :=
  Equiv.ofBijective (edgeMap4 q) (edgeMap4_bijective q)
lemma endpoints4_valid : ∀ q : Marked.Order 4, ∀ j : Fin 5,
    s(phi (smallMarkers4 ((SmallOrderNormalization.normalized 3 (smallOrder4 q)).vertex j)),
      phi (smallMarkers4 ((SmallOrderNormalization.normalized 3 (smallOrder4 q)).vertex (j+(1 : Fin 5))))) =
    s(fastRow4 q (edgeMap4 q j),fastRow4 q (edgeMap4 q j+1)) := by decide +kernel
lemma row4_local (o : Orders) (j : Fin 5) :
    StableCanonicalCoarsening.word b hb o A hr c4 j = fastRow4 (o 4) j := by
  rw [stableWord_local]
  exact congrFun (row4_eq_fast (o 4)) j
#check endpoints4_valid

def markers5 : Fin 6 → Fin 98 := ![10,24,38,52,66,82]
lemma place5 : fastPlace b hb 5 = markers5 := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b hb 5 j = markers5 j) j
lemma retained5 : retained b A 5 = {10,24,38,52,66} := by decide +kernel

def smallMarkers5 : Fin 5 → Fin 72 := ![10,22,34,46,58]
lemma smallPlace5 : fastPlace b₀ hb₀ 5 = smallMarkers5 := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b₀ hb₀ 5 j = smallMarkers5 j) j

def row5 (q : Marked.Order 4) : Fin 5 → Fin 98 :=
  StableCanonicalCoarsening.word b hb (oneOrder b 5 q) A hr c5
def fastRow5 (q : Marked.Order 4) (j : Fin 5) : Fin 98 :=
  (FilteredWord.filtered (fun t : Fin 6 => markers5 ((SmallOrderNormalization.normalized 4 q).vertex t))
    {10,24,38,52,66}).getD j.val 0
lemma row5_eq_fast (q : Marked.Order 4) : row5 q = fastRow5 q := by
  funext j
  change StableCanonicalCoarsening.word b hb (oneOrder b 5 q) A hr c5 j = _
  rw [StableCanonicalCoarsening.word_eq_getD b hb (oneOrder b 5 q) A hr c5 j 0]
  have hw : fastWord b hb (oneOrder b 5 q) 5 =
      fun s => markers5 ((SmallOrderNormalization.normalized 4 q).vertex s) := by
    funext s
    unfold fastWord
    rw [oneOrder_self,place5]
    rfl
  change (FilteredWord.filtered (fastWord b hb (oneOrder b 5 q) 5) (retained b A 5)).getD j.val 0 = _
  rw [hw,retained5]
  rfl

def wordCode5 (q : Marked.Order 4) : ℕ :=
  6 * ((SmallOrderNormalization.normalized 4 q).vertex 1).val + 36 * ((SmallOrderNormalization.normalized 4 q).vertex 2).val + 216 * ((SmallOrderNormalization.normalized 4 q).vertex 3).val + 1296 * ((SmallOrderNormalization.normalized 4 q).vertex 4).val + 7776 * ((SmallOrderNormalization.normalized 4 q).vertex 5).val
def data5 : ℕ → Marked.Order 3 × (Fin 5 → Fin 5)
  | 44790 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 38310 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 43710 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 30750 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 36150 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 29670 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 44610 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 38130 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 42450 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 23010 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 34890 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 21930 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 43350 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 30390 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 42270 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 22830 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 27150 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 20670 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 35610 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 29130 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 34530 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 21570 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 26970 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 20490 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 44760 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 38280 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 43680 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 30720 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 36120 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 29640 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 44400 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 37920 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 41160 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 33600 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 43140 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 30180 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 40980 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![4,3,2,1,0])
  | 25860 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 35400 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 28920 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 33240 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 25680 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 44550 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 38070 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 42390 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 34830 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 44370 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 37890 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 41130 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 33570 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 41850 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 40770 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 34110 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 33030 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 43260 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 42180 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 43080 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 40920 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 41820 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![4,3,2,1,0])
  | 40740 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![4,3,2,1,0])
  | _ => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])

def smallOrder5 (q : Marked.Order 4) : Marked.Order 3 := (data5 (wordCode5 q)).1
def edgeMap5 (q : Marked.Order 4) : Fin 5 → Fin 5 := (data5 (wordCode5 q)).2
lemma edgeMap5_bijective : ∀ q, Function.Bijective (edgeMap5 q) := by decide +kernel
noncomputable def edgeEquiv5 (q : Marked.Order 4) : Equiv.Perm (Fin 5) :=
  Equiv.ofBijective (edgeMap5 q) (edgeMap5_bijective q)
lemma endpoints5_valid : ∀ q : Marked.Order 4, ∀ j : Fin 5,
    s(phi (smallMarkers5 ((SmallOrderNormalization.normalized 3 (smallOrder5 q)).vertex j)),
      phi (smallMarkers5 ((SmallOrderNormalization.normalized 3 (smallOrder5 q)).vertex (j+(1 : Fin 5))))) =
    s(fastRow5 q (edgeMap5 q j),fastRow5 q (edgeMap5 q j+1)) := by decide +kernel
lemma row5_local (o : Orders) (j : Fin 5) :
    StableCanonicalCoarsening.word b hb o A hr c5 j = fastRow5 (o 5) j := by
  rw [stableWord_local]
  exact congrFun (row5_eq_fast (o 5)) j
#check endpoints5_valid

def smallOrders (o : Orders) : SmallOrders :=
  Fin.cases (smallOrder0 (o 0)) (Fin.cases (smallOrder1 (o 1)) (Fin.cases (smallOrder2 (o 2)) (Fin.cases (smallOrder3 (o 3)) (Fin.cases (smallOrder4 (o 4)) (Fin.cases (smallOrder5 (o 5)) ((fun i => Fin.elim0 i)))))))

noncomputable def rowEquiv (o : Orders) : ∀ i : Fin 6, Fin (arity b₀ i+2) ≃
    Fin (StableCanonicalCoarsening.arity b A (T i)+2) :=
  Fin.cases (edgeEquiv0 (o 0)) (Fin.cases (edgeEquiv1 (o 1)) (Fin.cases (edgeEquiv2 (o 2)) (Fin.cases (edgeEquiv3 (o 3)) (Fin.cases (edgeEquiv4 (o 4)) (Fin.cases (edgeEquiv5 (o 5)) ((fun i => Fin.elim0 i)))))))

noncomputable def edgeEquiv (o : Orders) : (Σ i : Fin 6, Fin (arity b₀ i+2)) ≃
    (Σ i : A, Fin (StableCanonicalCoarsening.arity b A i+2)) :=
  Equiv.sigmaCongr T (rowEquiv o)

lemma edge_apply_generic (o : Orders) (i : Fin 6) (j : Fin (arity b₀ i+2)) :
    edgeEquiv o ⟨i,j⟩ = ⟨T i,rowEquiv o i j⟩ := rfl

lemma row_apply0 (o : Orders) : rowEquiv o 0 = edgeEquiv0 (o 0) := by
  change rowEquiv o ((0 : Fin 6)) = edgeEquiv0 (o 0)
  simp only [rowEquiv,Fin.cases_zero,Fin.cases_succ]


#print axioms edgeEquiv
end Erdos184Work.SevenProjection6
