import Submission.FiveCanonicalCounts
import Submission.ColoredEmbeddingBounds
import Submission.FilteredCyclicWord
import Submission.FourKernel6

/-! Four-color projection of five-color pattern 4, omitting color 2.
The result is a necessary word catalogue, not a global exclusion. -/
open scoped Classical
namespace Erdos184Work.FiveProjection42
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open LabelKernel Erdos184Serial CanonicalSubsetCoarsening LocalCanonicalRows CanonicalThreeReduction
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.unusedSimpArgs false
noncomputable local instance projectionDecEq {I : Type*} {m : I → ℕ} :
    DecidableEq (Σ i, Fin (m i)) := Classical.decEq _
abbrev b := FiveCanonicalCounts.counts 4
lemma hb : ∀ i, 2 ≤ (markers b i).card := FiveCanonicalCounts.marker_bound 4
abbrev Orders := FiveCanonicalCounts.Orders 4
abbrev b₀ := FourCanonicalCounts.counts 6
lemma hb₀ : ∀ i, 2 ≤ (markers b₀ i).card := FourCanonicalCounts.marker_bound 6
abbrev SmallOrders := FourCanonicalCounts.Orders 6
def A : Finset (Fin 5) := {0,1,3,4}
lemma hr : ∀ i : A, 2 ≤ (retained b A i.val).card := by decide +kernel
def c0 : A := ⟨0,by decide⟩
def c1 : A := ⟨3,by decide⟩
def c2 : A := ⟨4,by decide⟩
def c3 : A := ⟨1,by decide⟩
def color : Fin 4 → A := ![c0,c1,c2,c3]
lemma color_bijective : Function.Bijective color := by decide +kernel
noncomputable def T : Fin 4 ≃ A := Equiv.ofBijective color color_bijective
def phi : Fin 32 → Fin 50 := ![0,1,6,4,8,5,2,3,7,9,10,11,38,39,16,12,13,14,15,17,19,20,18,21,22,23,24,25,26,27,28,29]
lemma phi_injective : Function.Injective phi := by decide +kernel

def markers0 : Fin 6 → Fin 50 := ![2,3,4,5,6,8]
lemma place0 : fastPlace b hb 0 = markers0 := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b hb 0 j = markers0 j) j
lemma retained0 : retained b A 0 = {2,3,6,8} := by decide +kernel

def smallMarkers0 : Fin 4 → Fin 32 := ![2,4,6,7]
lemma smallPlace0 : fastPlace b₀ hb₀ 0 = smallMarkers0 := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b₀ hb₀ 0 j = smallMarkers0 j) j

def row0 (q : Marked.Order 4) : Fin 4 → Fin 50 :=
  StableCanonicalCoarsening.word b hb (oneOrder b 0 q) A hr c0
def fastRow0 (q : Marked.Order 4) (j : Fin 4) : Fin 50 :=
  (FilteredWord.filtered (fun t : Fin 6 => markers0 ((SmallOrderNormalization.normalized 4 q).vertex t))
    {2,3,6,8}).getD j.val 0
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
def data0 : ℕ → Marked.Order 2 × (Fin 4 → Fin 4)
  | 44790 => ((((),(1 : Fin 2)),(Sum.inr ())),![2,3,0,1])
  | 38310 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![2,1,0,3])
  | 43710 => ((((),(1 : Fin 2)),(Sum.inr ())),![2,3,0,1])
  | 30750 => ((((),(1 : Fin 2)),(Sum.inr ())),![2,3,0,1])
  | 36150 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![2,1,0,3])
  | 29670 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![2,1,0,3])
  | 44610 => ((((),(1 : Fin 2)),(Sum.inr ())),![2,3,0,1])
  | 38130 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![2,1,0,3])
  | 42450 => ((((),(1 : Fin 2)),(Sum.inr ())),![2,3,0,1])
  | 23010 => ((((),(1 : Fin 2)),(Sum.inr ())),![2,3,0,1])
  | 34890 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![2,1,0,3])
  | 21930 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![2,1,0,3])
  | 43350 => ((((),(1 : Fin 2)),(Sum.inr ())),![2,3,0,1])
  | 30390 => ((((),(1 : Fin 2)),(Sum.inr ())),![2,3,0,1])
  | 42270 => ((((),(1 : Fin 2)),(Sum.inr ())),![2,3,0,1])
  | 22830 => ((((),(1 : Fin 2)),(Sum.inr ())),![2,3,0,1])
  | 27150 => ((((),(1 : Fin 2)),(Sum.inr ())),![2,3,0,1])
  | 20670 => ((((),(1 : Fin 2)),(Sum.inr ())),![2,3,0,1])
  | 35610 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![2,1,0,3])
  | 29130 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![2,1,0,3])
  | 34530 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![2,1,0,3])
  | 21570 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![2,1,0,3])
  | 26970 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![2,1,0,3])
  | 20490 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![2,1,0,3])
  | 44760 => ((((),(1 : Fin 2)),(Sum.inr ())),![2,3,0,1])
  | 38280 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![2,1,0,3])
  | 43680 => ((((),(1 : Fin 2)),(Sum.inr ())),![2,3,0,1])
  | 30720 => ((((),(1 : Fin 2)),(Sum.inr ())),![2,3,0,1])
  | 36120 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![2,1,0,3])
  | 29640 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![2,1,0,3])
  | 44400 => ((((),(1 : Fin 2)),(Sum.inr ())),![2,3,0,1])
  | 37920 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![2,1,0,3])
  | 41160 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![0,3,2,1])
  | 33600 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![3,0,1,2])
  | 43140 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![0,3,2,1])
  | 30180 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![0,3,2,1])
  | 40980 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![0,3,2,1])
  | 25860 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![1,2,3,0])
  | 35400 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![3,0,1,2])
  | 28920 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![3,0,1,2])
  | 33240 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![3,0,1,2])
  | 25680 => ((((),(1 : Fin 2)),(Sum.inr ())),![1,0,3,2])
  | 44550 => ((((),(1 : Fin 2)),(Sum.inr ())),![2,3,0,1])
  | 38070 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![2,1,0,3])
  | 42390 => ((((),(1 : Fin 2)),(Sum.inr ())),![2,3,0,1])
  | 34830 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![2,1,0,3])
  | 44370 => ((((),(1 : Fin 2)),(Sum.inr ())),![2,3,0,1])
  | 37890 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![2,1,0,3])
  | 41130 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![0,3,2,1])
  | 33570 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![3,0,1,2])
  | 41850 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![0,3,2,1])
  | 40770 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![0,3,2,1])
  | 34110 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![3,0,1,2])
  | 33030 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![3,0,1,2])
  | 43260 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![0,3,2,1])
  | 42180 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![0,3,2,1])
  | 43080 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![0,3,2,1])
  | 40920 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![0,3,2,1])
  | 41820 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![0,3,2,1])
  | 40740 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![0,3,2,1])
  | _ => ((((),(1 : Fin 2)),(Sum.inr ())),![2,3,0,1])

def smallOrder0 (q : Marked.Order 4) : Marked.Order 2 := (data0 (wordCode0 q)).1
def edgeMap0 (q : Marked.Order 4) : Fin 4 → Fin 4 := (data0 (wordCode0 q)).2
lemma edgeMap0_bijective : ∀ q, Function.Bijective (edgeMap0 q) := by decide +kernel
noncomputable def edgeEquiv0 (q : Marked.Order 4) : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective (edgeMap0 q) (edgeMap0_bijective q)
lemma endpoints0_valid : ∀ q : Marked.Order 4, ∀ j : Fin 4,
    s(phi (smallMarkers0 ((SmallOrderNormalization.normalized 2 (smallOrder0 q)).vertex j)),
      phi (smallMarkers0 ((SmallOrderNormalization.normalized 2 (smallOrder0 q)).vertex (j+(1 : Fin 4))))) =
    s(fastRow0 q (edgeMap0 q j),fastRow0 q (edgeMap0 q j+1)) := by decide +kernel
lemma row0_local (o : Orders) (j : Fin 4) :
    StableCanonicalCoarsening.word b hb o A hr c0 j = fastRow0 (o 0) j := by
  rw [stableWord_local]
  exact congrFun (row0_eq_fast (o 0)) j
#check endpoints0_valid

def markers1 : Fin 5 → Fin 50 := ![6,16,26,38,39]
lemma place1 : fastPlace b hb 3 = markers1 := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b hb 3 j = markers1 j) j
lemma retained1 : retained b A 3 = {6,16,38,39} := by decide +kernel

def smallMarkers1 : Fin 4 → Fin 32 := ![2,12,13,14]
lemma smallPlace1 : fastPlace b₀ hb₀ 1 = smallMarkers1 := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b₀ hb₀ 1 j = smallMarkers1 j) j

def row1 (q : Marked.Order 3) : Fin 4 → Fin 50 :=
  StableCanonicalCoarsening.word b hb (oneOrder b 3 q) A hr c1
def fastRow1 (q : Marked.Order 3) (j : Fin 4) : Fin 50 :=
  (FilteredWord.filtered (fun t : Fin 5 => markers1 ((SmallOrderNormalization.normalized 3 q).vertex t))
    {6,16,38,39}).getD j.val 0
lemma row1_eq_fast (q : Marked.Order 3) : row1 q = fastRow1 q := by
  funext j
  change StableCanonicalCoarsening.word b hb (oneOrder b 3 q) A hr c1 j = _
  rw [StableCanonicalCoarsening.word_eq_getD b hb (oneOrder b 3 q) A hr c1 j 0]
  have hw : fastWord b hb (oneOrder b 3 q) 3 =
      fun s => markers1 ((SmallOrderNormalization.normalized 3 q).vertex s) := by
    funext s
    unfold fastWord
    rw [oneOrder_self,place1]
    rfl
  change (FilteredWord.filtered (fastWord b hb (oneOrder b 3 q) 3) (retained b A 3)).getD j.val 0 = _
  rw [hw,retained1]
  rfl

def wordCode1 (q : Marked.Order 3) : ℕ :=
  5 * ((SmallOrderNormalization.normalized 3 q).vertex 1).val + 25 * ((SmallOrderNormalization.normalized 3 q).vertex 2).val + 125 * ((SmallOrderNormalization.normalized 3 q).vertex 3).val + 625 * ((SmallOrderNormalization.normalized 3 q).vertex 4).val
def data1 : ℕ → Marked.Order 2 × (Fin 4 → Fin 4)
  | 2930 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![3,2,1,0])
  | 2430 => ((((),(1 : Fin 2)),(Sum.inr ())),![3,2,1,0])
  | 2830 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![3,2,1,0])
  | 1830 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![3,2,1,0])
  | 2230 => ((((),(1 : Fin 2)),(Sum.inr ())),![3,2,1,0])
  | 1730 => ((((),(1 : Fin 2)),(Sum.inr ())),![3,2,1,0])
  | 2910 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![3,2,1,0])
  | 2410 => ((((),(1 : Fin 2)),(Sum.inr ())),![3,2,1,0])
  | 2710 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![0,1,2,3])
  | 2110 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![3,2,1,0])
  | 2790 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![0,1,2,3])
  | 2690 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![0,1,2,3])
  | _ => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![3,2,1,0])

def smallOrder1 (q : Marked.Order 3) : Marked.Order 2 := (data1 (wordCode1 q)).1
def edgeMap1 (q : Marked.Order 3) : Fin 4 → Fin 4 := (data1 (wordCode1 q)).2
lemma edgeMap1_bijective : ∀ q, Function.Bijective (edgeMap1 q) := by decide +kernel
noncomputable def edgeEquiv1 (q : Marked.Order 3) : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective (edgeMap1 q) (edgeMap1_bijective q)
lemma endpoints1_valid : ∀ q : Marked.Order 3, ∀ j : Fin 4,
    s(phi (smallMarkers1 ((SmallOrderNormalization.normalized 2 (smallOrder1 q)).vertex j)),
      phi (smallMarkers1 ((SmallOrderNormalization.normalized 2 (smallOrder1 q)).vertex (j+(1 : Fin 4))))) =
    s(fastRow1 q (edgeMap1 q j),fastRow1 q (edgeMap1 q j+1)) := by decide +kernel
lemma row1_local (o : Orders) (j : Fin 4) :
    StableCanonicalCoarsening.word b hb o A hr c1 j = fastRow1 (o 3) j := by
  rw [stableWord_local]
  exact congrFun (row1_eq_fast (o 3)) j
#check endpoints1_valid

def markers2 : Fin 5 → Fin 50 := ![8,18,28,38,39]
lemma place2 : fastPlace b hb 4 = markers2 := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b hb 4 j = markers2 j) j
lemma retained2 : retained b A 4 = {8,18,38,39} := by decide +kernel

def smallMarkers2 : Fin 4 → Fin 32 := ![4,12,13,22]
lemma smallPlace2 : fastPlace b₀ hb₀ 2 = smallMarkers2 := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b₀ hb₀ 2 j = smallMarkers2 j) j

def row2 (q : Marked.Order 3) : Fin 4 → Fin 50 :=
  StableCanonicalCoarsening.word b hb (oneOrder b 4 q) A hr c2
def fastRow2 (q : Marked.Order 3) (j : Fin 4) : Fin 50 :=
  (FilteredWord.filtered (fun t : Fin 5 => markers2 ((SmallOrderNormalization.normalized 3 q).vertex t))
    {8,18,38,39}).getD j.val 0
lemma row2_eq_fast (q : Marked.Order 3) : row2 q = fastRow2 q := by
  funext j
  change StableCanonicalCoarsening.word b hb (oneOrder b 4 q) A hr c2 j = _
  rw [StableCanonicalCoarsening.word_eq_getD b hb (oneOrder b 4 q) A hr c2 j 0]
  have hw : fastWord b hb (oneOrder b 4 q) 4 =
      fun s => markers2 ((SmallOrderNormalization.normalized 3 q).vertex s) := by
    funext s
    unfold fastWord
    rw [oneOrder_self,place2]
    rfl
  change (FilteredWord.filtered (fastWord b hb (oneOrder b 4 q) 4) (retained b A 4)).getD j.val 0 = _
  rw [hw,retained2]
  rfl

def wordCode2 (q : Marked.Order 3) : ℕ :=
  5 * ((SmallOrderNormalization.normalized 3 q).vertex 1).val + 25 * ((SmallOrderNormalization.normalized 3 q).vertex 2).val + 125 * ((SmallOrderNormalization.normalized 3 q).vertex 3).val + 625 * ((SmallOrderNormalization.normalized 3 q).vertex 4).val
def data2 : ℕ → Marked.Order 2 × (Fin 4 → Fin 4)
  | 2930 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![3,2,1,0])
  | 2430 => ((((),(1 : Fin 2)),(Sum.inr ())),![3,2,1,0])
  | 2830 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![3,2,1,0])
  | 1830 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![3,2,1,0])
  | 2230 => ((((),(1 : Fin 2)),(Sum.inr ())),![3,2,1,0])
  | 1730 => ((((),(1 : Fin 2)),(Sum.inr ())),![3,2,1,0])
  | 2910 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![3,2,1,0])
  | 2410 => ((((),(1 : Fin 2)),(Sum.inr ())),![3,2,1,0])
  | 2710 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![0,1,2,3])
  | 2110 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![3,2,1,0])
  | 2790 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![0,1,2,3])
  | 2690 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![0,1,2,3])
  | _ => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![3,2,1,0])

def smallOrder2 (q : Marked.Order 3) : Marked.Order 2 := (data2 (wordCode2 q)).1
def edgeMap2 (q : Marked.Order 3) : Fin 4 → Fin 4 := (data2 (wordCode2 q)).2
lemma edgeMap2_bijective : ∀ q, Function.Bijective (edgeMap2 q) := by decide +kernel
noncomputable def edgeEquiv2 (q : Marked.Order 3) : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective (edgeMap2 q) (edgeMap2_bijective q)
lemma endpoints2_valid : ∀ q : Marked.Order 3, ∀ j : Fin 4,
    s(phi (smallMarkers2 ((SmallOrderNormalization.normalized 2 (smallOrder2 q)).vertex j)),
      phi (smallMarkers2 ((SmallOrderNormalization.normalized 2 (smallOrder2 q)).vertex (j+(1 : Fin 4))))) =
    s(fastRow2 q (edgeMap2 q j),fastRow2 q (edgeMap2 q j+1)) := by decide +kernel
lemma row2_local (o : Orders) (j : Fin 4) :
    StableCanonicalCoarsening.word b hb o A hr c2 j = fastRow2 (o 4) j := by
  rw [stableWord_local]
  exact congrFun (row2_eq_fast (o 4)) j
#check endpoints2_valid

def markers3 : Fin 5 → Fin 50 := ![2,3,14,16,18]
lemma place3 : fastPlace b hb 1 = markers3 := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b hb 1 j = markers3 j) j
lemma retained3 : retained b A 1 = {2,3,16,18} := by decide +kernel

def smallMarkers3 : Fin 4 → Fin 32 := ![6,7,14,22]
lemma smallPlace3 : fastPlace b₀ hb₀ 3 = smallMarkers3 := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b₀ hb₀ 3 j = smallMarkers3 j) j

def row3 (q : Marked.Order 3) : Fin 4 → Fin 50 :=
  StableCanonicalCoarsening.word b hb (oneOrder b 1 q) A hr c3
def fastRow3 (q : Marked.Order 3) (j : Fin 4) : Fin 50 :=
  (FilteredWord.filtered (fun t : Fin 5 => markers3 ((SmallOrderNormalization.normalized 3 q).vertex t))
    {2,3,16,18}).getD j.val 0
lemma row3_eq_fast (q : Marked.Order 3) : row3 q = fastRow3 q := by
  funext j
  change StableCanonicalCoarsening.word b hb (oneOrder b 1 q) A hr c3 j = _
  rw [StableCanonicalCoarsening.word_eq_getD b hb (oneOrder b 1 q) A hr c3 j 0]
  have hw : fastWord b hb (oneOrder b 1 q) 1 =
      fun s => markers3 ((SmallOrderNormalization.normalized 3 q).vertex s) := by
    funext s
    unfold fastWord
    rw [oneOrder_self,place3]
    rfl
  change (FilteredWord.filtered (fastWord b hb (oneOrder b 1 q) 1) (retained b A 1)).getD j.val 0 = _
  rw [hw,retained3]
  rfl

def wordCode3 (q : Marked.Order 3) : ℕ :=
  5 * ((SmallOrderNormalization.normalized 3 q).vertex 1).val + 25 * ((SmallOrderNormalization.normalized 3 q).vertex 2).val + 125 * ((SmallOrderNormalization.normalized 3 q).vertex 3).val + 625 * ((SmallOrderNormalization.normalized 3 q).vertex 4).val
def data3 : ℕ → Marked.Order 2 × (Fin 4 → Fin 4)
  | 2930 => ((((),(1 : Fin 2)),(Sum.inr ())),![0,1,2,3])
  | 2430 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![0,1,2,3])
  | 2830 => ((((),(1 : Fin 2)),(Sum.inr ())),![0,1,2,3])
  | 1830 => ((((),(1 : Fin 2)),(Sum.inr ())),![0,1,2,3])
  | 2230 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![0,1,2,3])
  | 1730 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![0,1,2,3])
  | 2910 => ((((),(1 : Fin 2)),(Sum.inr ())),![0,1,2,3])
  | 2410 => ((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),![0,1,2,3])
  | 2710 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![0,1,2,3])
  | 2110 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![3,2,1,0])
  | 2790 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![0,1,2,3])
  | 2690 => ((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),![0,1,2,3])
  | _ => ((((),(1 : Fin 2)),(Sum.inr ())),![0,1,2,3])

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
    StableCanonicalCoarsening.word b hb o A hr c3 j = fastRow3 (o 1) j := by
  rw [stableWord_local]
  exact congrFun (row3_eq_fast (o 1)) j
#check endpoints3_valid

def smallOrders (o : Orders) : SmallOrders :=
  Fin.cases (smallOrder0 (o 0)) (Fin.cases (smallOrder1 (o 3)) (Fin.cases (smallOrder2 (o 4)) (Fin.cases (smallOrder3 (o 1)) ((fun i => Fin.elim0 i)))))

noncomputable def rowEquiv (o : Orders) : ∀ i : Fin 4, Fin (arity b₀ i+2) ≃
    Fin (StableCanonicalCoarsening.arity b A (T i)+2) :=
  Fin.cases (edgeEquiv0 (o 0)) (Fin.cases (edgeEquiv1 (o 3)) (Fin.cases (edgeEquiv2 (o 4)) (Fin.cases (edgeEquiv3 (o 1)) ((fun i => Fin.elim0 i)))))

noncomputable def edgeEquiv (o : Orders) : (Σ i : Fin 4, Fin (arity b₀ i+2)) ≃
    (Σ i : A, Fin (StableCanonicalCoarsening.arity b A i+2)) :=
  Equiv.sigmaCongr T (rowEquiv o)


#print axioms edgeEquiv
end Erdos184Work.FiveProjection42
