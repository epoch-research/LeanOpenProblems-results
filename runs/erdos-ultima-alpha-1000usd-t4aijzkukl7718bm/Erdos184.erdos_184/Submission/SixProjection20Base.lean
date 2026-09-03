import Submission.SixCanonicalCounts
import Submission.LargerColoredCoarsening
import Submission.FilteredCyclicWord
import Submission.FiveKernel1

/-! Five-color projection of six-color pattern 2, omitting color 0.
The result is a necessary word catalogue, not a global exclusion. -/
open scoped Classical
namespace Erdos184Work.SixProjection20
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open LabelKernel Erdos184Serial CanonicalSubsetCoarsening LocalCanonicalRows CanonicalThreeReduction
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.unusedSimpArgs false
noncomputable local instance projectionDecEq {I : Type*} {m : I → ℕ} :
    DecidableEq (Σ i, Fin (m i)) := Classical.decEq _
abbrev b := SixCanonicalCounts.counts 2
lemma hb : ∀ i, 2 ≤ (markers b i).card := SixCanonicalCounts.marker_bound 2
abbrev Orders := SixCanonicalCounts.Orders 2
abbrev b₀ := FiveCanonicalCounts.counts 1
lemma hb₀ : ∀ i, 2 ≤ (markers b₀ i).card := FiveCanonicalCounts.marker_bound 1
abbrev SmallOrders := FiveCanonicalCounts.Orders 1
def A : Finset (Fin 6) := {1,2,3,4,5}
lemma hr : ∀ i : A, 2 ≤ (retained b A i.val).card := by decide +kernel
def c0 : A := ⟨2,by decide⟩
def c1 : A := ⟨3,by decide⟩
def c2 : A := ⟨1,by decide⟩
def c3 : A := ⟨4,by decide⟩
def c4 : A := ⟨5,by decide⟩
def color : Fin 5 → A := ![c0,c1,c2,c3,c4]
lemma color_bijective : Function.Bijective color := by decide +kernel
noncomputable def T : Fin 5 ≃ A := Equiv.ofBijective color color_bijective
def phi : Fin 50 → Fin 72 := ![0,1,30,31,16,2,32,3,34,4,5,6,7,8,18,9,44,10,46,11,12,13,14,15,17,19,20,21,22,23,24,25,26,27,28,29,33,35,58,36,37,38,39,40,41,42,43,45,47,48]
lemma phi_injective : Function.Injective phi := by decide +kernel

def markers0 : Fin 6 → Fin 72 := ![4,16,30,31,32,34]
lemma place0 : fastPlace b hb 2 = markers0 := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b hb 2 j = markers0 j) j
lemma retained0 : retained b A 2 = {16,30,31,32,34} := by decide +kernel

def smallMarkers0 : Fin 5 → Fin 50 := ![2,3,4,6,8]
lemma smallPlace0 : fastPlace b₀ hb₀ 0 = smallMarkers0 := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b₀ hb₀ 0 j = smallMarkers0 j) j

def row0 (q : Marked.Order 4) : Fin 5 → Fin 72 :=
  StableCanonicalCoarsening.word b hb (oneOrder b 2 q) A hr c0
def fastRow0 (q : Marked.Order 4) (j : Fin 5) : Fin 72 :=
  (FilteredWord.filtered (fun t : Fin 6 => markers0 ((SmallOrderNormalization.normalized 4 q).vertex t))
    {16,30,31,32,34}).getD j.val 0
lemma row0_eq_fast (q : Marked.Order 4) : row0 q = fastRow0 q := by
  funext j
  change StableCanonicalCoarsening.word b hb (oneOrder b 2 q) A hr c0 j = _
  rw [StableCanonicalCoarsening.word_eq_getD b hb (oneOrder b 2 q) A hr c0 j 0]
  have hw : fastWord b hb (oneOrder b 2 q) 2 =
      fun s => markers0 ((SmallOrderNormalization.normalized 4 q).vertex s) := by
    funext s
    unfold fastWord
    rw [oneOrder_self,place0]
    rfl
  change (FilteredWord.filtered (fastWord b hb (oneOrder b 2 q) 2) (retained b A 2)).getD j.val 0 = _
  rw [hw,retained0]
  rfl

def wordCode0 (q : Marked.Order 4) : ℕ :=
  6 * ((SmallOrderNormalization.normalized 4 q).vertex 1).val + 36 * ((SmallOrderNormalization.normalized 4 q).vertex 2).val + 216 * ((SmallOrderNormalization.normalized 4 q).vertex 3).val + 1296 * ((SmallOrderNormalization.normalized 4 q).vertex 4).val + 7776 * ((SmallOrderNormalization.normalized 4 q).vertex 5).val
def data0 : ℕ → Marked.Order 3 × (Fin 5 → Fin 5)
  | 44790 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![1,2,3,4,0])
  | 38310 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![1,2,3,4,0])
  | 43710 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,4,3,2,1])
  | 30750 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,4,3,2,1])
  | 36150 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,4,3,2,1])
  | 29670 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,4,3,2,1])
  | 44610 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![1,0,4,3,2])
  | 38130 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![1,0,4,3,2])
  | 42450 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![2,1,0,4,3])
  | 23010 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![4,0,1,2,3])
  | 34890 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![3,4,0,1,2])
  | 21930 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,0,1,2,3])
  | 43350 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![2,3,4,0,1])
  | 30390 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![1,0,4,3,2])
  | 42270 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![2,1,0,4,3])
  | 22830 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,0,1,2,3])
  | 27150 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![3,4,0,1,2])
  | 20670 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![3,2,1,0,4])
  | 35610 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![2,3,4,0,1])
  | 29130 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![2,3,4,0,1])
  | 34530 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![2,1,0,4,3])
  | 21570 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![4,0,1,2,3])
  | 26970 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![3,4,0,1,2])
  | 20490 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![3,2,1,0,4])
  | 44760 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 38280 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 43680 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 30720 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 36120 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 29640 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![4,3,2,1,0])
  | 44400 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 37920 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 41160 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 33600 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 43140 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 30180 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 40980 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 25860 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 35400 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 28920 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 33240 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 25680 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![4,3,2,1,0])
  | 44550 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![1,0,4,3,2])
  | 38070 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![1,0,4,3,2])
  | 42390 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![2,1,0,4,3])
  | 34830 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![3,4,0,1,2])
  | 44370 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,4,3,2,1])
  | 37890 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,4,3,2,1])
  | 41130 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,4,3,2,1])
  | 33570 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,4,3,2,1])
  | 41850 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![2,1,0,4,3])
  | 40770 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![2,3,4,0,1])
  | 34110 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![2,1,0,4,3])
  | 33030 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![2,3,4,0,1])
  | 43260 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![2,3,4,0,1])
  | 42180 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![2,1,0,4,3])
  | 43080 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![1,2,3,4,0])
  | 40920 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![1,2,3,4,0])
  | 41820 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![2,1,0,4,3])
  | 40740 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![1,0,4,3,2])
  | _ => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![1,2,3,4,0])

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
    StableCanonicalCoarsening.word b hb o A hr c0 j = fastRow0 (o 2) j := by
  rw [stableWord_local]
  exact congrFun (row0_eq_fast (o 2)) j
#check endpoints0_valid

def markers1 : Fin 6 → Fin 72 := ![6,18,30,31,44,46]
lemma place1 : fastPlace b hb 3 = markers1 := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b hb 3 j = markers1 j) j
lemma retained1 : retained b A 3 = {18,30,31,44,46} := by decide +kernel

def smallMarkers1 : Fin 5 → Fin 50 := ![2,3,14,16,18]
lemma smallPlace1 : fastPlace b₀ hb₀ 1 = smallMarkers1 := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b₀ hb₀ 1 j = smallMarkers1 j) j

def row1 (q : Marked.Order 4) : Fin 5 → Fin 72 :=
  StableCanonicalCoarsening.word b hb (oneOrder b 3 q) A hr c1
def fastRow1 (q : Marked.Order 4) (j : Fin 5) : Fin 72 :=
  (FilteredWord.filtered (fun t : Fin 6 => markers1 ((SmallOrderNormalization.normalized 4 q).vertex t))
    {18,30,31,44,46}).getD j.val 0
lemma row1_eq_fast (q : Marked.Order 4) : row1 q = fastRow1 q := by
  funext j
  change StableCanonicalCoarsening.word b hb (oneOrder b 3 q) A hr c1 j = _
  rw [StableCanonicalCoarsening.word_eq_getD b hb (oneOrder b 3 q) A hr c1 j 0]
  have hw : fastWord b hb (oneOrder b 3 q) 3 =
      fun s => markers1 ((SmallOrderNormalization.normalized 4 q).vertex s) := by
    funext s
    unfold fastWord
    rw [oneOrder_self,place1]
    rfl
  change (FilteredWord.filtered (fastWord b hb (oneOrder b 3 q) 3) (retained b A 3)).getD j.val 0 = _
  rw [hw,retained1]
  rfl

def wordCode1 (q : Marked.Order 4) : ℕ :=
  6 * ((SmallOrderNormalization.normalized 4 q).vertex 1).val + 36 * ((SmallOrderNormalization.normalized 4 q).vertex 2).val + 216 * ((SmallOrderNormalization.normalized 4 q).vertex 3).val + 1296 * ((SmallOrderNormalization.normalized 4 q).vertex 4).val + 7776 * ((SmallOrderNormalization.normalized 4 q).vertex 5).val
def data1 : ℕ → Marked.Order 3 × (Fin 5 → Fin 5)
  | 44790 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![1,2,3,4,0])
  | 38310 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![1,2,3,4,0])
  | 43710 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,4,3,2,1])
  | 30750 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,4,3,2,1])
  | 36150 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,4,3,2,1])
  | 29670 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,4,3,2,1])
  | 44610 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![1,0,4,3,2])
  | 38130 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![1,0,4,3,2])
  | 42450 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![2,1,0,4,3])
  | 23010 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![4,0,1,2,3])
  | 34890 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![3,4,0,1,2])
  | 21930 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,0,1,2,3])
  | 43350 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![2,3,4,0,1])
  | 30390 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![1,0,4,3,2])
  | 42270 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![2,1,0,4,3])
  | 22830 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,0,1,2,3])
  | 27150 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![3,4,0,1,2])
  | 20670 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![3,2,1,0,4])
  | 35610 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![2,3,4,0,1])
  | 29130 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![2,3,4,0,1])
  | 34530 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![2,1,0,4,3])
  | 21570 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![4,0,1,2,3])
  | 26970 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![3,4,0,1,2])
  | 20490 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![3,2,1,0,4])
  | 44760 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 38280 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 43680 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 30720 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 36120 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 29640 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![4,3,2,1,0])
  | 44400 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 37920 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 41160 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 33600 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 43140 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 30180 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 40980 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 25860 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 35400 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 28920 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 33240 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 25680 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![4,3,2,1,0])
  | 44550 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![1,0,4,3,2])
  | 38070 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![1,0,4,3,2])
  | 42390 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![2,1,0,4,3])
  | 34830 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![3,4,0,1,2])
  | 44370 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,4,3,2,1])
  | 37890 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,4,3,2,1])
  | 41130 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,4,3,2,1])
  | 33570 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,4,3,2,1])
  | 41850 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![2,1,0,4,3])
  | 40770 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![2,3,4,0,1])
  | 34110 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![2,1,0,4,3])
  | 33030 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![2,3,4,0,1])
  | 43260 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![2,3,4,0,1])
  | 42180 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![2,1,0,4,3])
  | 43080 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![1,2,3,4,0])
  | 40920 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![1,2,3,4,0])
  | 41820 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![2,1,0,4,3])
  | 40740 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![1,0,4,3,2])
  | _ => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![1,2,3,4,0])

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
    StableCanonicalCoarsening.word b hb o A hr c1 j = fastRow1 (o 3) j := by
  rw [stableWord_local]
  exact congrFun (row1_eq_fast (o 3)) j
#check endpoints1_valid

def markers2 : Fin 6 → Fin 72 := ![2,3,16,18,20,22]
lemma place2 : fastPlace b hb 1 = markers2 := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b hb 1 j = markers2 j) j
lemma retained2 : retained b A 1 = {16,18,20,22} := by decide +kernel

def smallMarkers2 : Fin 4 → Fin 50 := ![4,14,26,28]
lemma smallPlace2 : fastPlace b₀ hb₀ 2 = smallMarkers2 := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b₀ hb₀ 2 j = smallMarkers2 j) j

def row2 (q : Marked.Order 4) : Fin 4 → Fin 72 :=
  StableCanonicalCoarsening.word b hb (oneOrder b 1 q) A hr c2
def fastRow2 (q : Marked.Order 4) (j : Fin 4) : Fin 72 :=
  (FilteredWord.filtered (fun t : Fin 6 => markers2 ((SmallOrderNormalization.normalized 4 q).vertex t))
    {16,18,20,22}).getD j.val 0
lemma row2_eq_fast (q : Marked.Order 4) : row2 q = fastRow2 q := by
  funext j
  change StableCanonicalCoarsening.word b hb (oneOrder b 1 q) A hr c2 j = _
  rw [StableCanonicalCoarsening.word_eq_getD b hb (oneOrder b 1 q) A hr c2 j 0]
  have hw : fastWord b hb (oneOrder b 1 q) 1 =
      fun s => markers2 ((SmallOrderNormalization.normalized 4 q).vertex s) := by
    funext s
    unfold fastWord
    rw [oneOrder_self,place2]
    rfl
  change (FilteredWord.filtered (fastWord b hb (oneOrder b 1 q) 1) (retained b A 1)).getD j.val 0 = _
  rw [hw,retained2]
  rfl

def wordCode2 (q : Marked.Order 4) : ℕ :=
  6 * ((SmallOrderNormalization.normalized 4 q).vertex 1).val + 36 * ((SmallOrderNormalization.normalized 4 q).vertex 2).val + 216 * ((SmallOrderNormalization.normalized 4 q).vertex 3).val + 1296 * ((SmallOrderNormalization.normalized 4 q).vertex 4).val + 7776 * ((SmallOrderNormalization.normalized 4 q).vertex 5).val
def data2 : ℕ → Marked.Order 2 × (Fin 4 → Fin 4)
  | 44790 => ((((),(1 : Fin 2)),(Sum.inr ())),![0,1,2,3])
  | 38310 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![0,1,2,3])
  | 43710 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![0,1,2,3])
  | 30750 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![3,2,1,0])
  | 36150 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![3,2,1,0])
  | 29670 => ((((),(1 : Fin 2)),(Sum.inr ())),![3,2,1,0])
  | 44610 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![0,3,2,1])
  | 38130 => ((((),(1 : Fin 2)),(Sum.inr ())),![0,3,2,1])
  | 42450 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![1,0,3,2])
  | 23010 => ((((),(1 : Fin 2)),(Sum.inr ())),![3,0,1,2])
  | 34890 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![2,3,0,1])
  | 21930 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![3,0,1,2])
  | 43350 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![1,2,3,0])
  | 30390 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![0,3,2,1])
  | 42270 => ((((),(1 : Fin 2)),(Sum.inr ())),![1,0,3,2])
  | 22830 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![3,0,1,2])
  | 27150 => ((((),(1 : Fin 2)),(Sum.inr ())),![2,3,0,1])
  | 20670 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![2,1,0,3])
  | 35610 => ((((),(1 : Fin 2)),(Sum.inr ())),![1,2,3,0])
  | 29130 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![1,2,3,0])
  | 34530 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![1,0,3,2])
  | 21570 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![2,1,0,3])
  | 26970 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![2,3,0,1])
  | 20490 => ((((),(1 : Fin 2)),(Sum.inr ())),![2,1,0,3])
  | 44760 => ((((),(1 : Fin 2)),(Sum.inr ())),![0,1,2,3])
  | 38280 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![0,1,2,3])
  | 43680 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![0,1,2,3])
  | 30720 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![3,2,1,0])
  | 36120 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![3,2,1,0])
  | 29640 => ((((),(1 : Fin 2)),(Sum.inr ())),![3,2,1,0])
  | 44400 => ((((),(1 : Fin 2)),(Sum.inr ())),![0,1,2,3])
  | 37920 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![0,1,2,3])
  | 41160 => ((((),(1 : Fin 2)),(Sum.inr ())),![0,1,2,3])
  | 33600 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![0,1,2,3])
  | 43140 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![0,1,2,3])
  | 30180 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![3,2,1,0])
  | 40980 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![0,1,2,3])
  | 25860 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![3,2,1,0])
  | 35400 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![3,2,1,0])
  | 28920 => ((((),(1 : Fin 2)),(Sum.inr ())),![3,2,1,0])
  | 33240 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![3,2,1,0])
  | 25680 => ((((),(1 : Fin 2)),(Sum.inr ())),![3,2,1,0])
  | 44550 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![0,3,2,1])
  | 38070 => ((((),(1 : Fin 2)),(Sum.inr ())),![0,3,2,1])
  | 42390 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![1,0,3,2])
  | 34830 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![2,3,0,1])
  | 44370 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![0,3,2,1])
  | 37890 => ((((),(1 : Fin 2)),(Sum.inr ())),![0,3,2,1])
  | 41130 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![0,3,2,1])
  | 33570 => ((((),(1 : Fin 2)),(Sum.inr ())),![0,3,2,1])
  | 41850 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![1,0,3,2])
  | 40770 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![1,0,3,2])
  | 34110 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![2,3,0,1])
  | 33030 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![2,3,0,1])
  | 43260 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![1,2,3,0])
  | 42180 => ((((),(1 : Fin 2)),(Sum.inr ())),![1,0,3,2])
  | 43080 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![1,2,3,0])
  | 40920 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![1,2,3,0])
  | 41820 => ((((),(1 : Fin 2)),(Sum.inr ())),![1,0,3,2])
  | 40740 => ((((),(1 : Fin 2)),(Sum.inr ())),![1,0,3,2])
  | _ => ((((),(1 : Fin 2)),(Sum.inr ())),![0,1,2,3])

def smallOrder2 (q : Marked.Order 4) : Marked.Order 2 := (data2 (wordCode2 q)).1
def edgeMap2 (q : Marked.Order 4) : Fin 4 → Fin 4 := (data2 (wordCode2 q)).2
lemma edgeMap2_bijective : ∀ q, Function.Bijective (edgeMap2 q) := by decide +kernel
noncomputable def edgeEquiv2 (q : Marked.Order 4) : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective (edgeMap2 q) (edgeMap2_bijective q)
lemma endpoints2_valid : ∀ q : Marked.Order 4, ∀ j : Fin 4,
    s(phi (smallMarkers2 ((SmallOrderNormalization.normalized 2 (smallOrder2 q)).vertex j)),
      phi (smallMarkers2 ((SmallOrderNormalization.normalized 2 (smallOrder2 q)).vertex (j+(1 : Fin 4))))) =
    s(fastRow2 q (edgeMap2 q j),fastRow2 q (edgeMap2 q j+1)) := by decide +kernel
lemma row2_local (o : Orders) (j : Fin 4) :
    StableCanonicalCoarsening.word b hb o A hr c2 j = fastRow2 (o 1) j := by
  rw [stableWord_local]
  exact congrFun (row2_eq_fast (o 1)) j
#check endpoints2_valid

def markers3 : Fin 5 → Fin 72 := ![8,20,32,44,58]
lemma place3 : fastPlace b hb 4 = markers3 := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b hb 4 j = markers3 j) j
lemma retained3 : retained b A 4 = {20,32,44,58} := by decide +kernel

def smallMarkers3 : Fin 4 → Fin 50 := ![6,16,26,38]
lemma smallPlace3 : fastPlace b₀ hb₀ 3 = smallMarkers3 := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b₀ hb₀ 3 j = smallMarkers3 j) j

def row3 (q : Marked.Order 3) : Fin 4 → Fin 72 :=
  StableCanonicalCoarsening.word b hb (oneOrder b 4 q) A hr c3
def fastRow3 (q : Marked.Order 3) (j : Fin 4) : Fin 72 :=
  (FilteredWord.filtered (fun t : Fin 5 => markers3 ((SmallOrderNormalization.normalized 3 q).vertex t))
    {20,32,44,58}).getD j.val 0
lemma row3_eq_fast (q : Marked.Order 3) : row3 q = fastRow3 q := by
  funext j
  change StableCanonicalCoarsening.word b hb (oneOrder b 4 q) A hr c3 j = _
  rw [StableCanonicalCoarsening.word_eq_getD b hb (oneOrder b 4 q) A hr c3 j 0]
  have hw : fastWord b hb (oneOrder b 4 q) 4 =
      fun s => markers3 ((SmallOrderNormalization.normalized 3 q).vertex s) := by
    funext s
    unfold fastWord
    rw [oneOrder_self,place3]
    rfl
  change (FilteredWord.filtered (fastWord b hb (oneOrder b 4 q) 4) (retained b A 4)).getD j.val 0 = _
  rw [hw,retained3]
  rfl

def wordCode3 (q : Marked.Order 3) : ℕ :=
  5 * ((SmallOrderNormalization.normalized 3 q).vertex 1).val + 25 * ((SmallOrderNormalization.normalized 3 q).vertex 2).val + 125 * ((SmallOrderNormalization.normalized 3 q).vertex 3).val + 625 * ((SmallOrderNormalization.normalized 3 q).vertex 4).val
def data3 : ℕ → Marked.Order 2 × (Fin 4 → Fin 4)
  | 2930 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![1,2,3,0])
  | 2430 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![0,3,2,1])
  | 2830 => ((((),(1 : Fin 2)),(Sum.inr ())),![1,0,3,2])
  | 1830 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![3,0,1,2])
  | 2230 => ((((),(1 : Fin 2)),(Sum.inr ())),![2,3,0,1])
  | 1730 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![2,1,0,3])
  | 2910 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![0,1,2,3])
  | 2410 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![3,2,1,0])
  | 2710 => ((((),(1 : Fin 2)),(Sum.inr ())),![0,1,2,3])
  | 2110 => ((((),(1 : Fin 2)),(Sum.inr ())),![3,2,1,0])
  | 2790 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![1,0,3,2])
  | 2690 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![0,3,2,1])
  | _ => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![1,2,3,0])

def smallOrder3 (q : Marked.Order 3) : Marked.Order 2 := (data3 (wordCode3 q)).1
def edgeMap3 (q : Marked.Order 3) : Fin 4 → Fin 4 := (data3 (wordCode3 q)).2
lemma edgeMap3_bijective : ∀ q, Function.Bijective (edgeMap3 q) := by decide +kernel
noncomputable def edgeEquiv3 (q : Marked.Order 3) : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective (edgeMap3 q) (edgeMap3_bijective q)
lemma endpoints3_valid : ∀ q : Marked.Order 3, ∀ j : Fin 4,
    s(phi (smallMarkers3 ((SmallOrderNormalization.normalized 2 (smallOrder3 q)).vertex j)),
      phi (smallMarkers3 ((SmallOrderNormalization.normalized 2 (smallOrder3 q)).vertex (j+(1 : Fin 4))))) =
    s(fastRow3 q (edgeMap3 q j),fastRow3 q (edgeMap3 q j+1)) := by decide +kernel
lemma row3_local (o : Orders) (j : Fin 4) :
    StableCanonicalCoarsening.word b hb o A hr c3 j = fastRow3 (o 4) j := by
  rw [stableWord_local]
  exact congrFun (row3_eq_fast (o 4)) j
#check endpoints3_valid

def markers4 : Fin 5 → Fin 72 := ![10,22,34,46,58]
lemma place4 : fastPlace b hb 5 = markers4 := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b hb 5 j = markers4 j) j
lemma retained4 : retained b A 5 = {22,34,46,58} := by decide +kernel

def smallMarkers4 : Fin 4 → Fin 50 := ![8,18,28,38]
lemma smallPlace4 : fastPlace b₀ hb₀ 4 = smallMarkers4 := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b₀ hb₀ 4 j = smallMarkers4 j) j

def row4 (q : Marked.Order 3) : Fin 4 → Fin 72 :=
  StableCanonicalCoarsening.word b hb (oneOrder b 5 q) A hr c4
def fastRow4 (q : Marked.Order 3) (j : Fin 4) : Fin 72 :=
  (FilteredWord.filtered (fun t : Fin 5 => markers4 ((SmallOrderNormalization.normalized 3 q).vertex t))
    {22,34,46,58}).getD j.val 0
lemma row4_eq_fast (q : Marked.Order 3) : row4 q = fastRow4 q := by
  funext j
  change StableCanonicalCoarsening.word b hb (oneOrder b 5 q) A hr c4 j = _
  rw [StableCanonicalCoarsening.word_eq_getD b hb (oneOrder b 5 q) A hr c4 j 0]
  have hw : fastWord b hb (oneOrder b 5 q) 5 =
      fun s => markers4 ((SmallOrderNormalization.normalized 3 q).vertex s) := by
    funext s
    unfold fastWord
    rw [oneOrder_self,place4]
    rfl
  change (FilteredWord.filtered (fastWord b hb (oneOrder b 5 q) 5) (retained b A 5)).getD j.val 0 = _
  rw [hw,retained4]
  rfl

def wordCode4 (q : Marked.Order 3) : ℕ :=
  5 * ((SmallOrderNormalization.normalized 3 q).vertex 1).val + 25 * ((SmallOrderNormalization.normalized 3 q).vertex 2).val + 125 * ((SmallOrderNormalization.normalized 3 q).vertex 3).val + 625 * ((SmallOrderNormalization.normalized 3 q).vertex 4).val
def data4 : ℕ → Marked.Order 2 × (Fin 4 → Fin 4)
  | 2930 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![1,2,3,0])
  | 2430 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![0,3,2,1])
  | 2830 => ((((),(1 : Fin 2)),(Sum.inr ())),![1,0,3,2])
  | 1830 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![3,0,1,2])
  | 2230 => ((((),(1 : Fin 2)),(Sum.inr ())),![2,3,0,1])
  | 1730 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![2,1,0,3])
  | 2910 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![0,1,2,3])
  | 2410 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![3,2,1,0])
  | 2710 => ((((),(1 : Fin 2)),(Sum.inr ())),![0,1,2,3])
  | 2110 => ((((),(1 : Fin 2)),(Sum.inr ())),![3,2,1,0])
  | 2790 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![1,0,3,2])
  | 2690 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![0,3,2,1])
  | _ => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![1,2,3,0])

def smallOrder4 (q : Marked.Order 3) : Marked.Order 2 := (data4 (wordCode4 q)).1
def edgeMap4 (q : Marked.Order 3) : Fin 4 → Fin 4 := (data4 (wordCode4 q)).2
lemma edgeMap4_bijective : ∀ q, Function.Bijective (edgeMap4 q) := by decide +kernel
noncomputable def edgeEquiv4 (q : Marked.Order 3) : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective (edgeMap4 q) (edgeMap4_bijective q)
lemma endpoints4_valid : ∀ q : Marked.Order 3, ∀ j : Fin 4,
    s(phi (smallMarkers4 ((SmallOrderNormalization.normalized 2 (smallOrder4 q)).vertex j)),
      phi (smallMarkers4 ((SmallOrderNormalization.normalized 2 (smallOrder4 q)).vertex (j+(1 : Fin 4))))) =
    s(fastRow4 q (edgeMap4 q j),fastRow4 q (edgeMap4 q j+1)) := by decide +kernel
lemma row4_local (o : Orders) (j : Fin 4) :
    StableCanonicalCoarsening.word b hb o A hr c4 j = fastRow4 (o 5) j := by
  rw [stableWord_local]
  exact congrFun (row4_eq_fast (o 5)) j
#check endpoints4_valid

def smallOrders (o : Orders) : SmallOrders :=
  Fin.cases (smallOrder0 (o 2)) (Fin.cases (smallOrder1 (o 3)) (Fin.cases (smallOrder2 (o 1)) (Fin.cases (smallOrder3 (o 4)) (Fin.cases (smallOrder4 (o 5)) ((fun i => Fin.elim0 i))))))

noncomputable def rowEquiv (o : Orders) : ∀ i : Fin 5, Fin (arity b₀ i+2) ≃
    Fin (StableCanonicalCoarsening.arity b A (T i)+2) :=
  Fin.cases (edgeEquiv0 (o 2)) (Fin.cases (edgeEquiv1 (o 3)) (Fin.cases (edgeEquiv2 (o 1)) (Fin.cases (edgeEquiv3 (o 4)) (Fin.cases (edgeEquiv4 (o 5)) ((fun i => Fin.elim0 i))))))

noncomputable def edgeEquiv (o : Orders) : (Σ i : Fin 5, Fin (arity b₀ i+2)) ≃
    (Σ i : A, Fin (StableCanonicalCoarsening.arity b A i+2)) :=
  Equiv.sigmaCongr T (rowEquiv o)

lemma edge_apply_generic (o : Orders) (i : Fin 5) (j : Fin (arity b₀ i+2)) :
    edgeEquiv o ⟨i,j⟩ = ⟨T i,rowEquiv o i j⟩ := rfl

lemma row_apply0 (o : Orders) : rowEquiv o 0 = edgeEquiv0 (o 2) := by
  change rowEquiv o ((0 : Fin 5)) = edgeEquiv0 (o 2)
  simp only [rowEquiv,Fin.cases_zero,Fin.cases_succ]


#print axioms edgeEquiv
end Erdos184Work.SixProjection20
