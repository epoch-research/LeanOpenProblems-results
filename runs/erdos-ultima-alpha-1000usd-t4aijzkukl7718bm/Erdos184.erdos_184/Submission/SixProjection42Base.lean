import Submission.SixCanonicalCounts
import Submission.LargerColoredCoarsening
import Submission.FilteredCyclicWord
import Submission.FiveKernel1

/-! Five-color projection of six-color pattern 4, omitting color 2.
The result is a necessary word catalogue, not a global exclusion. -/
open scoped Classical
namespace Erdos184Work.SixProjection42
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open LabelKernel Erdos184Serial CanonicalSubsetCoarsening LocalCanonicalRows CanonicalThreeReduction
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.unusedSimpArgs false
noncomputable local instance projectionDecEq {I : Type*} {m : I → ℕ} :
    DecidableEq (Σ i, Fin (m i)) := Classical.decEq _
abbrev b := SixCanonicalCounts.counts 4
lemma hb : ∀ i, 2 ≤ (markers b i).card := SixCanonicalCounts.marker_bound 4
abbrev Orders := SixCanonicalCounts.Orders 4
abbrev b₀ := FiveCanonicalCounts.counts 1
lemma hb₀ : ∀ i, 2 ≤ (markers b₀ i).card := FiveCanonicalCounts.marker_bound 1
abbrev SmallOrders := FiveCanonicalCounts.Orders 1
def A : Finset (Fin 6) := {0,1,3,4,5}
lemma hr : ∀ i : A, 2 ≤ (retained b A i.val).card := by decide +kernel
def c0 : A := ⟨0,by decide⟩
def c1 : A := ⟨1,by decide⟩
def c2 : A := ⟨3,by decide⟩
def c3 : A := ⟨4,by decide⟩
def c4 : A := ⟨5,by decide⟩
def color : Fin 5 → A := ![c0,c1,c2,c3,c4]
lemma color_bijective : Function.Bijective color := by decide +kernel
noncomputable def T : Fin 5 ≃ A := Equiv.ofBijective color color_bijective
def phi : Fin 50 → Fin 72 := ![0,1,2,3,6,4,8,5,10,7,9,11,12,13,18,14,20,15,22,16,17,19,21,23,24,25,44,26,46,27,28,29,30,31,32,33,34,35,58,36,37,38,39,40,41,42,43,45,47,48]
lemma phi_injective : Function.Injective phi := by decide +kernel

def markers0 : Fin 7 → Fin 72 := ![2,3,4,5,6,8,10]
lemma place0 : fastPlace b hb 0 = markers0 := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b hb 0 j = markers0 j) j
lemma retained0 : retained b A 0 = {2,3,6,8,10} := by decide +kernel

def smallMarkers0 : Fin 5 → Fin 50 := ![2,3,4,6,8]
lemma smallPlace0 : fastPlace b₀ hb₀ 0 = smallMarkers0 := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b₀ hb₀ 0 j = smallMarkers0 j) j

def row0 (q : Marked.Order 5) : Fin 5 → Fin 72 :=
  StableCanonicalCoarsening.word b hb (oneOrder b 0 q) A hr c0
def fastRow0 (q : Marked.Order 5) (j : Fin 5) : Fin 72 :=
  (FilteredWord.filtered (fun t : Fin 7 => markers0 ((SmallOrderNormalization.normalized 5 q).vertex t))
    {2,3,6,8,10}).getD j.val 0
lemma row0_eq_fast (q : Marked.Order 5) : row0 q = fastRow0 q := by
  funext j
  change StableCanonicalCoarsening.word b hb (oneOrder b 0 q) A hr c0 j = _
  rw [StableCanonicalCoarsening.word_eq_getD b hb (oneOrder b 0 q) A hr c0 j 0]
  have hw : fastWord b hb (oneOrder b 0 q) 0 =
      fun s => markers0 ((SmallOrderNormalization.normalized 5 q).vertex s) := by
    funext s
    unfold fastWord
    rw [oneOrder_self,place0]
    rfl
  change (FilteredWord.filtered (fastWord b hb (oneOrder b 0 q) 0) (retained b A 0)).getD j.val 0 = _
  rw [hw,retained0]
  rfl

def wordCode0 (q : Marked.Order 5) : ℕ :=
  7 * ((SmallOrderNormalization.normalized 5 q).vertex 1).val + 49 * ((SmallOrderNormalization.normalized 5 q).vertex 2).val + 343 * ((SmallOrderNormalization.normalized 5 q).vertex 3).val + 2401 * ((SmallOrderNormalization.normalized 5 q).vertex 4).val + 16807 * ((SmallOrderNormalization.normalized 5 q).vertex 5).val + 117649 * ((SmallOrderNormalization.normalized 5 q).vertex 6).val
def data0 : ℕ → Marked.Order 3 × (Fin 5 → Fin 5)
  | 800667 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 699825 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 786261 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 584577 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 671013 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 570171 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 798609 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 697767 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 769797 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 467271 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 654549 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 452865 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 782145 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 580461 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 767739 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 465213 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 537243 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 436401 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 664839 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 563997 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 650433 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 448749 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 535185 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 434343 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 800373 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 699531 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 785967 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 584283 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 670719 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 569877 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 796257 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 695415 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 753039 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 349671 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 637791 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 335265 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 779793 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 578109 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 750981 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 347613 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 520485 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 318801 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 662487 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 561645 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 633675 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 331149 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 518427 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 316743 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 798021 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 697179 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 769209 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 466683 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 653961 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 452277 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 795963 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 695121 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 752745 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 349377 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 637497 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 334971 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 763035 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 460509 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 748629 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 345261 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 402885 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 302043 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 645729 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 444045 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 631323 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 328797 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 400827 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 299985 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 781263 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 579579 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 766857 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 464331 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 536361 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 435519 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 779205 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 577521 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 750393 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 347025 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 519897 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 318213 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 762741 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 460215 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 748335 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 344967 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 402591 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 301749 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 528129 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 427287 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 513723 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 312039 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 398475 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 297633 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 663663 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 562821 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 649257 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 447573 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 534009 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 433167 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 661605 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 560763 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 632793 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 330267 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 517545 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 315861 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 645141 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 443457 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 630735 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 328209 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 400239 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 299397 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 527835 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 426993 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 513429 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 311745 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 398181 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 297339 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 800625 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 699783 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 786219 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 584535 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 670971 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 570129 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 798567 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 697725 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 769755 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 467229 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 654507 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 452823 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 782103 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 580419 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 767697 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 465171 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 537201 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 436359 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 664797 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 563955 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 650391 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 448707 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 535143 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 434301 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 800037 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 699195 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 785631 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 583947 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 670383 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 569541 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 793863 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 693021 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 736239 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 620991 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 777399 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 575715 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 734181 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 503685 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 660093 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 559251 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 616875 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 501627 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![4,3,2,1,0])
  | 797685 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 696843 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 768873 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 466347 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 653625 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 451941 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 793569 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 692727 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 735945 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 620697 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 760641 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 458115 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 731829 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 386085 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 643335 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 441651 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 614523 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 384027 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![4,3,2,1,0])
  | 780927 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 579243 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 766521 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 463995 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 536025 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 435183 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 776811 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 575127 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 733593 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 503097 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 760347 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 457821 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 731535 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 385791 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 525735 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 424893 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 496923 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 381675 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 663327 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 562485 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 648921 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 447237 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 533673 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 432831 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 659211 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 558369 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 615993 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 500745 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![4,3,2,1,0])
  | 642747 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 441063 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 613935 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 383439 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 525441 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![4,3,2,1,0])
  | 424599 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![4,3,2,1,0])
  | 496629 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![4,3,2,1,0])
  | 381381 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![4,3,2,1,0])
  | 800289 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 699447 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 785883 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 584199 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 670635 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 569793 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 796173 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 695331 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 752955 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 637707 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 779709 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 578025 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 750897 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 520401 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 662403 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 561561 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 633591 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 518343 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 799995 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 699153 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 785589 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 583905 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 670341 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 569499 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 793821 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 692979 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 736197 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 620949 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 777357 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 575673 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 734139 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 503643 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 660051 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 559209 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 616833 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 501585 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![4,3,2,1,0])
  | 795291 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 694449 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 752073 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 636825 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 793233 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 692391 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 735609 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 620361 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 743841 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 729435 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 626535 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 612129 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 778533 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 576849 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 749721 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 519225 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 776475 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 574791 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 733257 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 502761 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 743547 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 729141 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 508935 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 494529 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 660933 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 560091 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 632121 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 516873 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 658875 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 558033 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 615657 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 500409 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![4,3,2,1,0])
  | 625947 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 611541 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 508641 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![4,3,2,1,0])
  | 494235 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![4,3,2,1,0])
  | 797895 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 697053 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 769083 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 653835 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 795837 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 694995 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 752619 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 637371 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 762909 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 748503 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 645603 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 631197 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 797601 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 696759 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 768789 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 653541 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 793485 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 692643 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 735861 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 620613 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 760557 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 731745 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 643251 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 614439 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 795249 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 694407 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 752031 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 636783 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 793191 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 692349 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 735567 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 620319 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 743799 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 729393 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 626493 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 612087 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 761733 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 747327 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 759675 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 730863 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 743211 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 728805 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 644133 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 629727 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 642075 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 613263 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 625611 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 611205 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 781095 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 766689 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 779037 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 750225 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 762573 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 748167 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 780801 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 766395 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 776685 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 733467 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 760221 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 731409 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 778449 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 749637 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 776391 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 733173 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 743463 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 729057 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 761691 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 747285 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 759633 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 730821 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 743169 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 728763 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | _ => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])

def smallOrder0 (q : Marked.Order 5) : Marked.Order 3 := (data0 (wordCode0 q)).1
def edgeMap0 (q : Marked.Order 5) : Fin 5 → Fin 5 := (data0 (wordCode0 q)).2
lemma edgeMap0_bijective_0_0 : ∀ q : Marked.Order 3, Function.Bijective (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))) := by decide +kernel
lemma edgeMap0_bijective_0_1 : ∀ q : Marked.Order 3, Function.Bijective (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))) := by decide +kernel
lemma edgeMap0_bijective_0_2 : ∀ q : Marked.Order 3, Function.Bijective (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))) := by decide +kernel
lemma edgeMap0_bijective_0_3 : ∀ q : Marked.Order 3, Function.Bijective (edgeMap0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))) := by decide +kernel
lemma edgeMap0_bijective_0_4 : ∀ q : Marked.Order 3, Function.Bijective (edgeMap0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))) := by decide +kernel
lemma edgeMap0_bijective_0 : ∀ q : Marked.Order 4, Function.Bijective (edgeMap0 (q,(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))) := by
  rintro ⟨q,t⟩
  fin_cases t
  · exact edgeMap0_bijective_0_0 q
  · exact edgeMap0_bijective_0_1 q
  · exact edgeMap0_bijective_0_2 q
  · exact edgeMap0_bijective_0_3 q
  · exact edgeMap0_bijective_0_4 q
lemma edgeMap0_bijective_1_0 : ∀ q : Marked.Order 3, Function.Bijective (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))) := by decide +kernel
lemma edgeMap0_bijective_1_1 : ∀ q : Marked.Order 3, Function.Bijective (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))) := by decide +kernel
lemma edgeMap0_bijective_1_2 : ∀ q : Marked.Order 3, Function.Bijective (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))) := by decide +kernel
lemma edgeMap0_bijective_1_3 : ∀ q : Marked.Order 3, Function.Bijective (edgeMap0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))) := by decide +kernel
lemma edgeMap0_bijective_1_4 : ∀ q : Marked.Order 3, Function.Bijective (edgeMap0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))) := by decide +kernel
lemma edgeMap0_bijective_1 : ∀ q : Marked.Order 4, Function.Bijective (edgeMap0 (q,(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))) := by
  rintro ⟨q,t⟩
  fin_cases t
  · exact edgeMap0_bijective_1_0 q
  · exact edgeMap0_bijective_1_1 q
  · exact edgeMap0_bijective_1_2 q
  · exact edgeMap0_bijective_1_3 q
  · exact edgeMap0_bijective_1_4 q
lemma edgeMap0_bijective_2_0 : ∀ q : Marked.Order 3, Function.Bijective (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ())))))) := by decide +kernel
lemma edgeMap0_bijective_2_1 : ∀ q : Marked.Order 3, Function.Bijective (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ())))))) := by decide +kernel
lemma edgeMap0_bijective_2_2 : ∀ q : Marked.Order 3, Function.Bijective (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ())))))) := by decide +kernel
lemma edgeMap0_bijective_2_3 : ∀ q : Marked.Order 3, Function.Bijective (edgeMap0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ())))))) := by decide +kernel
lemma edgeMap0_bijective_2_4 : ∀ q : Marked.Order 3, Function.Bijective (edgeMap0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ())))))) := by decide +kernel
lemma edgeMap0_bijective_2 : ∀ q : Marked.Order 4, Function.Bijective (edgeMap0 (q,(Sum.inl (Sum.inl (Sum.inl (Sum.inr ())))))) := by
  rintro ⟨q,t⟩
  fin_cases t
  · exact edgeMap0_bijective_2_0 q
  · exact edgeMap0_bijective_2_1 q
  · exact edgeMap0_bijective_2_2 q
  · exact edgeMap0_bijective_2_3 q
  · exact edgeMap0_bijective_2_4 q
lemma edgeMap0_bijective_3_0 : ∀ q : Marked.Order 3, Function.Bijective (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inr ()))))) := by decide +kernel
lemma edgeMap0_bijective_3_1 : ∀ q : Marked.Order 3, Function.Bijective (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inr ()))))) := by decide +kernel
lemma edgeMap0_bijective_3_2 : ∀ q : Marked.Order 3, Function.Bijective (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inr ()))))) := by decide +kernel
lemma edgeMap0_bijective_3_3 : ∀ q : Marked.Order 3, Function.Bijective (edgeMap0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inr ()))))) := by decide +kernel
lemma edgeMap0_bijective_3_4 : ∀ q : Marked.Order 3, Function.Bijective (edgeMap0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inr ()))))) := by decide +kernel
lemma edgeMap0_bijective_3 : ∀ q : Marked.Order 4, Function.Bijective (edgeMap0 (q,(Sum.inl (Sum.inl (Sum.inr ()))))) := by
  rintro ⟨q,t⟩
  fin_cases t
  · exact edgeMap0_bijective_3_0 q
  · exact edgeMap0_bijective_3_1 q
  · exact edgeMap0_bijective_3_2 q
  · exact edgeMap0_bijective_3_3 q
  · exact edgeMap0_bijective_3_4 q
lemma edgeMap0_bijective_4_0 : ∀ q : Marked.Order 3, Function.Bijective (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inr ())))) := by decide +kernel
lemma edgeMap0_bijective_4_1 : ∀ q : Marked.Order 3, Function.Bijective (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inr ())))) := by decide +kernel
lemma edgeMap0_bijective_4_2 : ∀ q : Marked.Order 3, Function.Bijective (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inr ())))) := by decide +kernel
lemma edgeMap0_bijective_4_3 : ∀ q : Marked.Order 3, Function.Bijective (edgeMap0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inr ())))) := by decide +kernel
lemma edgeMap0_bijective_4_4 : ∀ q : Marked.Order 3, Function.Bijective (edgeMap0 ((q,(Sum.inr ())),(Sum.inl (Sum.inr ())))) := by decide +kernel
lemma edgeMap0_bijective_4 : ∀ q : Marked.Order 4, Function.Bijective (edgeMap0 (q,(Sum.inl (Sum.inr ())))) := by
  rintro ⟨q,t⟩
  fin_cases t
  · exact edgeMap0_bijective_4_0 q
  · exact edgeMap0_bijective_4_1 q
  · exact edgeMap0_bijective_4_2 q
  · exact edgeMap0_bijective_4_3 q
  · exact edgeMap0_bijective_4_4 q
lemma edgeMap0_bijective_5_0 : ∀ q : Marked.Order 3, Function.Bijective (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inr ()))) := by decide +kernel
lemma edgeMap0_bijective_5_1 : ∀ q : Marked.Order 3, Function.Bijective (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inr ()))) := by decide +kernel
lemma edgeMap0_bijective_5_2 : ∀ q : Marked.Order 3, Function.Bijective (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inr ()))) := by decide +kernel
lemma edgeMap0_bijective_5_3 : ∀ q : Marked.Order 3, Function.Bijective (edgeMap0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inr ()))) := by decide +kernel
lemma edgeMap0_bijective_5_4 : ∀ q : Marked.Order 3, Function.Bijective (edgeMap0 ((q,(Sum.inr ())),(Sum.inr ()))) := by decide +kernel
lemma edgeMap0_bijective_5 : ∀ q : Marked.Order 4, Function.Bijective (edgeMap0 (q,(Sum.inr ()))) := by
  rintro ⟨q,t⟩
  fin_cases t
  · exact edgeMap0_bijective_5_0 q
  · exact edgeMap0_bijective_5_1 q
  · exact edgeMap0_bijective_5_2 q
  · exact edgeMap0_bijective_5_3 q
  · exact edgeMap0_bijective_5_4 q
lemma edgeMap0_bijective : ∀ q : Marked.Order 5, Function.Bijective (edgeMap0 q) := by
  rintro ⟨q,t⟩
  fin_cases t
  · exact edgeMap0_bijective_0 q
  · exact edgeMap0_bijective_1 q
  · exact edgeMap0_bijective_2 q
  · exact edgeMap0_bijective_3 q
  · exact edgeMap0_bijective_4 q
  · exact edgeMap0_bijective_5 q
noncomputable def edgeEquiv0 (q : Marked.Order 5) : Equiv.Perm (Fin 5) :=
  Equiv.ofBijective (edgeMap0 q) (edgeMap0_bijective q)
lemma endpoints0_valid_0_0 : ∀ q : Marked.Order 3, ∀ j : Fin 5,
    s(phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))).vertex j)),
      phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))).vertex (j+(1 : Fin 5))))) =
    s(fastRow0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))) (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))) j),fastRow0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))) (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))) j+1)) := by decide +kernel
lemma endpoints0_valid_0_1 : ∀ q : Marked.Order 3, ∀ j : Fin 5,
    s(phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))).vertex j)),
      phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))).vertex (j+(1 : Fin 5))))) =
    s(fastRow0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))) (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))) j),fastRow0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))) (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))) j+1)) := by decide +kernel
lemma endpoints0_valid_0_2 : ∀ q : Marked.Order 3, ∀ j : Fin 5,
    s(phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))).vertex j)),
      phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))).vertex (j+(1 : Fin 5))))) =
    s(fastRow0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))) (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))) j),fastRow0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))) (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))) j+1)) := by decide +kernel
lemma endpoints0_valid_0_3 : ∀ q : Marked.Order 3, ∀ j : Fin 5,
    s(phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))).vertex j)),
      phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))).vertex (j+(1 : Fin 5))))) =
    s(fastRow0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))) (edgeMap0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))) j),fastRow0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))) (edgeMap0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))) j+1)) := by decide +kernel
lemma endpoints0_valid_0_4 : ∀ q : Marked.Order 3, ∀ j : Fin 5,
    s(phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))).vertex j)),
      phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))).vertex (j+(1 : Fin 5))))) =
    s(fastRow0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))) (edgeMap0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))) j),fastRow0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))) (edgeMap0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))) j+1)) := by decide +kernel
lemma endpoints0_valid_0 : ∀ q : Marked.Order 4, ∀ j : Fin 5,
    s(phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))).vertex j)),
      phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))).vertex (j+(1 : Fin 5))))) =
    s(fastRow0 (q,(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))) (edgeMap0 (q,(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))) j),fastRow0 (q,(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))) (edgeMap0 (q,(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))) j+1)) := by
  rintro ⟨q,t⟩
  fin_cases t
  · exact endpoints0_valid_0_0 q
  · exact endpoints0_valid_0_1 q
  · exact endpoints0_valid_0_2 q
  · exact endpoints0_valid_0_3 q
  · exact endpoints0_valid_0_4 q
lemma endpoints0_valid_1_0 : ∀ q : Marked.Order 3, ∀ j : Fin 5,
    s(phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))).vertex j)),
      phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))).vertex (j+(1 : Fin 5))))) =
    s(fastRow0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))) (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))) j),fastRow0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))) (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))) j+1)) := by decide +kernel
lemma endpoints0_valid_1_1 : ∀ q : Marked.Order 3, ∀ j : Fin 5,
    s(phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))).vertex j)),
      phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))).vertex (j+(1 : Fin 5))))) =
    s(fastRow0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))) (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))) j),fastRow0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))) (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))) j+1)) := by decide +kernel
lemma endpoints0_valid_1_2 : ∀ q : Marked.Order 3, ∀ j : Fin 5,
    s(phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))).vertex j)),
      phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))).vertex (j+(1 : Fin 5))))) =
    s(fastRow0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))) (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))) j),fastRow0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))) (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))) j+1)) := by decide +kernel
lemma endpoints0_valid_1_3 : ∀ q : Marked.Order 3, ∀ j : Fin 5,
    s(phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))).vertex j)),
      phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))).vertex (j+(1 : Fin 5))))) =
    s(fastRow0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))) (edgeMap0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))) j),fastRow0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))) (edgeMap0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))) j+1)) := by decide +kernel
lemma endpoints0_valid_1_4 : ∀ q : Marked.Order 3, ∀ j : Fin 5,
    s(phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))).vertex j)),
      phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))).vertex (j+(1 : Fin 5))))) =
    s(fastRow0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))) (edgeMap0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))) j),fastRow0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))) (edgeMap0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))) j+1)) := by decide +kernel
lemma endpoints0_valid_1 : ∀ q : Marked.Order 4, ∀ j : Fin 5,
    s(phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))).vertex j)),
      phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))).vertex (j+(1 : Fin 5))))) =
    s(fastRow0 (q,(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))) (edgeMap0 (q,(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))) j),fastRow0 (q,(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))) (edgeMap0 (q,(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))) j+1)) := by
  rintro ⟨q,t⟩
  fin_cases t
  · exact endpoints0_valid_1_0 q
  · exact endpoints0_valid_1_1 q
  · exact endpoints0_valid_1_2 q
  · exact endpoints0_valid_1_3 q
  · exact endpoints0_valid_1_4 q
lemma endpoints0_valid_2_0 : ∀ q : Marked.Order 3, ∀ j : Fin 5,
    s(phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))).vertex j)),
      phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))).vertex (j+(1 : Fin 5))))) =
    s(fastRow0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))) (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))) j),fastRow0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))) (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))) j+1)) := by decide +kernel
lemma endpoints0_valid_2_1 : ∀ q : Marked.Order 3, ∀ j : Fin 5,
    s(phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))).vertex j)),
      phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))).vertex (j+(1 : Fin 5))))) =
    s(fastRow0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))) (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))) j),fastRow0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))) (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))) j+1)) := by decide +kernel
lemma endpoints0_valid_2_2 : ∀ q : Marked.Order 3, ∀ j : Fin 5,
    s(phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))).vertex j)),
      phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))).vertex (j+(1 : Fin 5))))) =
    s(fastRow0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))) (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))) j),fastRow0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))) (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))) j+1)) := by decide +kernel
lemma endpoints0_valid_2_3 : ∀ q : Marked.Order 3, ∀ j : Fin 5,
    s(phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))).vertex j)),
      phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))).vertex (j+(1 : Fin 5))))) =
    s(fastRow0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))) (edgeMap0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))) j),fastRow0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))) (edgeMap0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))) j+1)) := by decide +kernel
lemma endpoints0_valid_2_4 : ∀ q : Marked.Order 3, ∀ j : Fin 5,
    s(phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))).vertex j)),
      phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))).vertex (j+(1 : Fin 5))))) =
    s(fastRow0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))) (edgeMap0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))) j),fastRow0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))) (edgeMap0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))) j+1)) := by decide +kernel
lemma endpoints0_valid_2 : ∀ q : Marked.Order 4, ∀ j : Fin 5,
    s(phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))).vertex j)),
      phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))).vertex (j+(1 : Fin 5))))) =
    s(fastRow0 (q,(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))) (edgeMap0 (q,(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))) j),fastRow0 (q,(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))) (edgeMap0 (q,(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))) j+1)) := by
  rintro ⟨q,t⟩
  fin_cases t
  · exact endpoints0_valid_2_0 q
  · exact endpoints0_valid_2_1 q
  · exact endpoints0_valid_2_2 q
  · exact endpoints0_valid_2_3 q
  · exact endpoints0_valid_2_4 q
lemma endpoints0_valid_3_0 : ∀ q : Marked.Order 3, ∀ j : Fin 5,
    s(phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inr ())))))).vertex j)),
      phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inr ())))))).vertex (j+(1 : Fin 5))))) =
    s(fastRow0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inr ())))) (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inr ())))) j),fastRow0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inr ())))) (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inr ())))) j+1)) := by decide +kernel
lemma endpoints0_valid_3_1 : ∀ q : Marked.Order 3, ∀ j : Fin 5,
    s(phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inr ())))))).vertex j)),
      phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inr ())))))).vertex (j+(1 : Fin 5))))) =
    s(fastRow0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inr ())))) (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inr ())))) j),fastRow0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inr ())))) (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inr ())))) j+1)) := by decide +kernel
lemma endpoints0_valid_3_2 : ∀ q : Marked.Order 3, ∀ j : Fin 5,
    s(phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inr ())))))).vertex j)),
      phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inr ())))))).vertex (j+(1 : Fin 5))))) =
    s(fastRow0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inr ())))) (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inr ())))) j),fastRow0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inr ())))) (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inr ())))) j+1)) := by decide +kernel
lemma endpoints0_valid_3_3 : ∀ q : Marked.Order 3, ∀ j : Fin 5,
    s(phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inr ())))))).vertex j)),
      phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inr ())))))).vertex (j+(1 : Fin 5))))) =
    s(fastRow0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inr ())))) (edgeMap0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inr ())))) j),fastRow0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inr ())))) (edgeMap0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inr ())))) j+1)) := by decide +kernel
lemma endpoints0_valid_3_4 : ∀ q : Marked.Order 3, ∀ j : Fin 5,
    s(phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inr ())))))).vertex j)),
      phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inr ())))))).vertex (j+(1 : Fin 5))))) =
    s(fastRow0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inr ())))) (edgeMap0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inr ())))) j),fastRow0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inr ())))) (edgeMap0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inr ())))) j+1)) := by decide +kernel
lemma endpoints0_valid_3 : ∀ q : Marked.Order 4, ∀ j : Fin 5,
    s(phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inr ())))))).vertex j)),
      phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inr ())))))).vertex (j+(1 : Fin 5))))) =
    s(fastRow0 (q,(Sum.inl (Sum.inl (Sum.inr ())))) (edgeMap0 (q,(Sum.inl (Sum.inl (Sum.inr ())))) j),fastRow0 (q,(Sum.inl (Sum.inl (Sum.inr ())))) (edgeMap0 (q,(Sum.inl (Sum.inl (Sum.inr ())))) j+1)) := by
  rintro ⟨q,t⟩
  fin_cases t
  · exact endpoints0_valid_3_0 q
  · exact endpoints0_valid_3_1 q
  · exact endpoints0_valid_3_2 q
  · exact endpoints0_valid_3_3 q
  · exact endpoints0_valid_3_4 q
lemma endpoints0_valid_4_0 : ∀ q : Marked.Order 3, ∀ j : Fin 5,
    s(phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inr ()))))).vertex j)),
      phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inr ()))))).vertex (j+(1 : Fin 5))))) =
    s(fastRow0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inr ()))) (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inr ()))) j),fastRow0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inr ()))) (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inr ()))) j+1)) := by decide +kernel
lemma endpoints0_valid_4_1 : ∀ q : Marked.Order 3, ∀ j : Fin 5,
    s(phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inr ()))))).vertex j)),
      phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inr ()))))).vertex (j+(1 : Fin 5))))) =
    s(fastRow0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inr ()))) (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inr ()))) j),fastRow0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inr ()))) (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inr ()))) j+1)) := by decide +kernel
lemma endpoints0_valid_4_2 : ∀ q : Marked.Order 3, ∀ j : Fin 5,
    s(phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inr ()))))).vertex j)),
      phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inr ()))))).vertex (j+(1 : Fin 5))))) =
    s(fastRow0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inr ()))) (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inr ()))) j),fastRow0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inr ()))) (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inr ()))) j+1)) := by decide +kernel
lemma endpoints0_valid_4_3 : ∀ q : Marked.Order 3, ∀ j : Fin 5,
    s(phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inr ()))))).vertex j)),
      phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inr ()))))).vertex (j+(1 : Fin 5))))) =
    s(fastRow0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inr ()))) (edgeMap0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inr ()))) j),fastRow0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inr ()))) (edgeMap0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inr ()))) j+1)) := by decide +kernel
lemma endpoints0_valid_4_4 : ∀ q : Marked.Order 3, ∀ j : Fin 5,
    s(phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inr ())),(Sum.inl (Sum.inr ()))))).vertex j)),
      phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inr ())),(Sum.inl (Sum.inr ()))))).vertex (j+(1 : Fin 5))))) =
    s(fastRow0 ((q,(Sum.inr ())),(Sum.inl (Sum.inr ()))) (edgeMap0 ((q,(Sum.inr ())),(Sum.inl (Sum.inr ()))) j),fastRow0 ((q,(Sum.inr ())),(Sum.inl (Sum.inr ()))) (edgeMap0 ((q,(Sum.inr ())),(Sum.inl (Sum.inr ()))) j+1)) := by decide +kernel
lemma endpoints0_valid_4 : ∀ q : Marked.Order 4, ∀ j : Fin 5,
    s(phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 (q,(Sum.inl (Sum.inr ()))))).vertex j)),
      phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 (q,(Sum.inl (Sum.inr ()))))).vertex (j+(1 : Fin 5))))) =
    s(fastRow0 (q,(Sum.inl (Sum.inr ()))) (edgeMap0 (q,(Sum.inl (Sum.inr ()))) j),fastRow0 (q,(Sum.inl (Sum.inr ()))) (edgeMap0 (q,(Sum.inl (Sum.inr ()))) j+1)) := by
  rintro ⟨q,t⟩
  fin_cases t
  · exact endpoints0_valid_4_0 q
  · exact endpoints0_valid_4_1 q
  · exact endpoints0_valid_4_2 q
  · exact endpoints0_valid_4_3 q
  · exact endpoints0_valid_4_4 q
lemma endpoints0_valid_5_0 : ∀ q : Marked.Order 3, ∀ j : Fin 5,
    s(phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inr ())))).vertex j)),
      phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inr ())))).vertex (j+(1 : Fin 5))))) =
    s(fastRow0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inr ())) (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inr ())) j),fastRow0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inr ())) (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inr ())) j+1)) := by decide +kernel
lemma endpoints0_valid_5_1 : ∀ q : Marked.Order 3, ∀ j : Fin 5,
    s(phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inr ())))).vertex j)),
      phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inr ())))).vertex (j+(1 : Fin 5))))) =
    s(fastRow0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inr ())) (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inr ())) j),fastRow0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inr ())) (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inr ())) j+1)) := by decide +kernel
lemma endpoints0_valid_5_2 : ∀ q : Marked.Order 3, ∀ j : Fin 5,
    s(phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inr ())))).vertex j)),
      phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inr ())))).vertex (j+(1 : Fin 5))))) =
    s(fastRow0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inr ())) (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inr ())) j),fastRow0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inr ())) (edgeMap0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inr ())) j+1)) := by decide +kernel
lemma endpoints0_valid_5_3 : ∀ q : Marked.Order 3, ∀ j : Fin 5,
    s(phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inr ())))).vertex j)),
      phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inr ())))).vertex (j+(1 : Fin 5))))) =
    s(fastRow0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inr ())) (edgeMap0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inr ())) j),fastRow0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inr ())) (edgeMap0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inr ())) j+1)) := by decide +kernel
lemma endpoints0_valid_5_4 : ∀ q : Marked.Order 3, ∀ j : Fin 5,
    s(phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inr ())),(Sum.inr ())))).vertex j)),
      phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inr ())),(Sum.inr ())))).vertex (j+(1 : Fin 5))))) =
    s(fastRow0 ((q,(Sum.inr ())),(Sum.inr ())) (edgeMap0 ((q,(Sum.inr ())),(Sum.inr ())) j),fastRow0 ((q,(Sum.inr ())),(Sum.inr ())) (edgeMap0 ((q,(Sum.inr ())),(Sum.inr ())) j+1)) := by decide +kernel
lemma endpoints0_valid_5 : ∀ q : Marked.Order 4, ∀ j : Fin 5,
    s(phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 (q,(Sum.inr ())))).vertex j)),
      phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 (q,(Sum.inr ())))).vertex (j+(1 : Fin 5))))) =
    s(fastRow0 (q,(Sum.inr ())) (edgeMap0 (q,(Sum.inr ())) j),fastRow0 (q,(Sum.inr ())) (edgeMap0 (q,(Sum.inr ())) j+1)) := by
  rintro ⟨q,t⟩
  fin_cases t
  · exact endpoints0_valid_5_0 q
  · exact endpoints0_valid_5_1 q
  · exact endpoints0_valid_5_2 q
  · exact endpoints0_valid_5_3 q
  · exact endpoints0_valid_5_4 q
lemma endpoints0_valid : ∀ q : Marked.Order 5, ∀ j : Fin 5,
    s(phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 q)).vertex j)),
      phi (smallMarkers0 ((SmallOrderNormalization.normalized 3 (smallOrder0 q)).vertex (j+(1 : Fin 5))))) =
    s(fastRow0 q (edgeMap0 q j),fastRow0 q (edgeMap0 q j+1)) := by
  rintro ⟨q,t⟩
  fin_cases t
  · exact endpoints0_valid_0 q
  · exact endpoints0_valid_1 q
  · exact endpoints0_valid_2 q
  · exact endpoints0_valid_3 q
  · exact endpoints0_valid_4 q
  · exact endpoints0_valid_5 q
lemma row0_local (o : Orders) (j : Fin 5) :
    StableCanonicalCoarsening.word b hb o A hr c0 j = fastRow0 (o 0) j := by
  rw [stableWord_local]
  exact congrFun (row0_eq_fast (o 0)) j
#check endpoints0_valid

def markers1 : Fin 6 → Fin 72 := ![2,3,16,18,20,22]
lemma place1 : fastPlace b hb 1 = markers1 := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b hb 1 j = markers1 j) j
lemma retained1 : retained b A 1 = {2,3,18,20,22} := by decide +kernel

def smallMarkers1 : Fin 5 → Fin 50 := ![2,3,14,16,18]
lemma smallPlace1 : fastPlace b₀ hb₀ 1 = smallMarkers1 := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b₀ hb₀ 1 j = smallMarkers1 j) j

def row1 (q : Marked.Order 4) : Fin 5 → Fin 72 :=
  StableCanonicalCoarsening.word b hb (oneOrder b 1 q) A hr c1
def fastRow1 (q : Marked.Order 4) (j : Fin 5) : Fin 72 :=
  (FilteredWord.filtered (fun t : Fin 6 => markers1 ((SmallOrderNormalization.normalized 4 q).vertex t))
    {2,3,18,20,22}).getD j.val 0
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
  | 38310 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 43710 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 30750 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 36150 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 29670 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 44610 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 38130 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 42450 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 23010 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 34890 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 21930 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 43350 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 30390 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 42270 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 22830 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 27150 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 20670 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 35610 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 29130 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 34530 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 21570 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 26970 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 20490 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 44760 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),![0,1,2,3,4])
  | 38280 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 43680 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 30720 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 36120 => (((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 29640 => (((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 44400 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 37920 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 41160 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 33600 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 43140 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 30180 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 40980 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 25860 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 35400 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 28920 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![4,3,2,1,0])
  | 33240 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![4,3,2,1,0])
  | 25680 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![4,3,2,1,0])
  | 44550 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 38070 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 42390 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 34830 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 44370 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),![0,1,2,3,4])
  | 37890 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 41130 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 33570 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 41850 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 40770 => (((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 34110 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 33030 => (((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 43260 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 42180 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 43080 => (((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),![0,1,2,3,4])
  | 40920 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 41820 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
  | 40740 => (((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),![0,1,2,3,4])
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

def markers2 : Fin 5 → Fin 72 := ![6,18,30,44,46]
lemma place2 : fastPlace b hb 3 = markers2 := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b hb 3 j = markers2 j) j
lemma retained2 : retained b A 3 = {6,18,44,46} := by decide +kernel

def smallMarkers2 : Fin 4 → Fin 50 := ![4,14,26,28]
lemma smallPlace2 : fastPlace b₀ hb₀ 2 = smallMarkers2 := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b₀ hb₀ 2 j = smallMarkers2 j) j

def row2 (q : Marked.Order 3) : Fin 4 → Fin 72 :=
  StableCanonicalCoarsening.word b hb (oneOrder b 3 q) A hr c2
def fastRow2 (q : Marked.Order 3) (j : Fin 4) : Fin 72 :=
  (FilteredWord.filtered (fun t : Fin 5 => markers2 ((SmallOrderNormalization.normalized 3 q).vertex t))
    {6,18,44,46}).getD j.val 0
lemma row2_eq_fast (q : Marked.Order 3) : row2 q = fastRow2 q := by
  funext j
  change StableCanonicalCoarsening.word b hb (oneOrder b 3 q) A hr c2 j = _
  rw [StableCanonicalCoarsening.word_eq_getD b hb (oneOrder b 3 q) A hr c2 j 0]
  have hw : fastWord b hb (oneOrder b 3 q) 3 =
      fun s => markers2 ((SmallOrderNormalization.normalized 3 q).vertex s) := by
    funext s
    unfold fastWord
    rw [oneOrder_self,place2]
    rfl
  change (FilteredWord.filtered (fastWord b hb (oneOrder b 3 q) 3) (retained b A 3)).getD j.val 0 = _
  rw [hw,retained2]
  rfl

def wordCode2 (q : Marked.Order 3) : ℕ :=
  5 * ((SmallOrderNormalization.normalized 3 q).vertex 1).val + 25 * ((SmallOrderNormalization.normalized 3 q).vertex 2).val + 125 * ((SmallOrderNormalization.normalized 3 q).vertex 3).val + 625 * ((SmallOrderNormalization.normalized 3 q).vertex 4).val
def data2 : ℕ → Marked.Order 2 × (Fin 4 → Fin 4)
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
    StableCanonicalCoarsening.word b hb o A hr c2 j = fastRow2 (o 3) j := by
  rw [stableWord_local]
  exact congrFun (row2_eq_fast (o 3)) j
#check endpoints2_valid

def markers3 : Fin 5 → Fin 72 := ![8,20,32,44,58]
lemma place3 : fastPlace b hb 4 = markers3 := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b hb 4 j = markers3 j) j
lemma retained3 : retained b A 4 = {8,20,44,58} := by decide +kernel

def smallMarkers3 : Fin 4 → Fin 50 := ![6,16,26,38]
lemma smallPlace3 : fastPlace b₀ hb₀ 3 = smallMarkers3 := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b₀ hb₀ 3 j = smallMarkers3 j) j

def row3 (q : Marked.Order 3) : Fin 4 → Fin 72 :=
  StableCanonicalCoarsening.word b hb (oneOrder b 4 q) A hr c3
def fastRow3 (q : Marked.Order 3) (j : Fin 4) : Fin 72 :=
  (FilteredWord.filtered (fun t : Fin 5 => markers3 ((SmallOrderNormalization.normalized 3 q).vertex t))
    {8,20,44,58}).getD j.val 0
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
    StableCanonicalCoarsening.word b hb o A hr c3 j = fastRow3 (o 4) j := by
  rw [stableWord_local]
  exact congrFun (row3_eq_fast (o 4)) j
#check endpoints3_valid

def markers4 : Fin 5 → Fin 72 := ![10,22,34,46,58]
lemma place4 : fastPlace b hb 5 = markers4 := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b hb 5 j = markers4 j) j
lemma retained4 : retained b A 5 = {10,22,46,58} := by decide +kernel

def smallMarkers4 : Fin 4 → Fin 50 := ![8,18,28,38]
lemma smallPlace4 : fastPlace b₀ hb₀ 4 = smallMarkers4 := by
  funext j
  exact (by decide +kernel : ∀ j, fastPlace b₀ hb₀ 4 j = smallMarkers4 j) j

def row4 (q : Marked.Order 3) : Fin 4 → Fin 72 :=
  StableCanonicalCoarsening.word b hb (oneOrder b 5 q) A hr c4
def fastRow4 (q : Marked.Order 3) (j : Fin 4) : Fin 72 :=
  (FilteredWord.filtered (fun t : Fin 5 => markers4 ((SmallOrderNormalization.normalized 3 q).vertex t))
    {10,22,46,58}).getD j.val 0
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
  Fin.cases (smallOrder0 (o 0)) (Fin.cases (smallOrder1 (o 1)) (Fin.cases (smallOrder2 (o 3)) (Fin.cases (smallOrder3 (o 4)) (Fin.cases (smallOrder4 (o 5)) ((fun i => Fin.elim0 i))))))

noncomputable def rowEquiv (o : Orders) : ∀ i : Fin 5, Fin (arity b₀ i+2) ≃
    Fin (StableCanonicalCoarsening.arity b A (T i)+2) :=
  Fin.cases (edgeEquiv0 (o 0)) (Fin.cases (edgeEquiv1 (o 1)) (Fin.cases (edgeEquiv2 (o 3)) (Fin.cases (edgeEquiv3 (o 4)) (Fin.cases (edgeEquiv4 (o 5)) ((fun i => Fin.elim0 i))))))

noncomputable def edgeEquiv (o : Orders) : (Σ i : Fin 5, Fin (arity b₀ i+2)) ≃
    (Σ i : A, Fin (StableCanonicalCoarsening.arity b A i+2)) :=
  Equiv.sigmaCongr T (rowEquiv o)

lemma edge_apply_generic (o : Orders) (i : Fin 5) (j : Fin (arity b₀ i+2)) :
    edgeEquiv o ⟨i,j⟩ = ⟨T i,rowEquiv o i j⟩ := rfl

lemma row_apply0 (o : Orders) : rowEquiv o 0 = edgeEquiv0 (o 0) := by
  change rowEquiv o ((0 : Fin 5)) = edgeEquiv0 (o 0)
  simp only [rowEquiv,Fin.cases_zero,Fin.cases_succ]


#print axioms edgeEquiv
end Erdos184Work.SixProjection42
