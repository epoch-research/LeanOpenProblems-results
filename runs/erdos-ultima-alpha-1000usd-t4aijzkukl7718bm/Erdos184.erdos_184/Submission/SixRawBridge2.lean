import Submission.SixRows2
import Submission.PureSixRowModel2

/-! Raw/canonical row identities factored through plain finite row variables. -/
namespace Erdos184Work.SixCaseCompatibility2
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open CanonicalThreeReduction SixRows2
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma key_rows (q0 : Fin 60) (q1 : Fin 60) (q2 : Fin 60) (q3 : Fin 60) (q4 : Fin 12) (q5 : Fin 12) :
    PureSixRowModel2.key (PureSixRowModel2.rows q0 q1 q2 q3 q4 q5) = 31104000 * q0.val + 518400 * q1.val + 8640 * q2.val + 144 * q3.val + 12 * q4.val + 1 * q5.val := rfl
lemma src_rows (q0 : Fin 60) (q1 : Fin 60) (q2 : Fin 60) (q3 : Fin 60) (q4 : Fin 12) (q5 : Fin 12) :
    PureSixRowModel2.src (PureSixRowModel2.rows q0 q1 q2 q3 q4 q5) = SixRows2.srcAt q0 q1 q2 q3 q4 q5 := by
  funext e
  fin_cases e <;> rfl
lemma dst_rows (q0 : Fin 60) (q1 : Fin 60) (q2 : Fin 60) (q3 : Fin 60) (q4 : Fin 12) (q5 : Fin 12) :
    PureSixRowModel2.dst (PureSixRowModel2.rows q0 q1 q2 q3 q4 q5) = SixRows2.dstAt q0 q1 q2 q3 q4 q5 := by
  funext e
  fin_cases e <;> rfl
def rawRows (o : Orders) : PureSixRowModel2.Rows := PureSixRowModel2.rows (SixRows2.key0 (o 0)) (SixRows2.key1 (o 1)) (SixRows2.key2 (o 2)) (SixRows2.key3 (o 3)) (SixRows2.key4 (o 4)) (SixRows2.key5 (o 5))
lemma key_rawRows (o : Orders) : PureSixRowModel2.key (rawRows o) = SixRows2.key o :=
  key_rows (SixRows2.key0 (o 0)) (SixRows2.key1 (o 1)) (SixRows2.key2 (o 2)) (SixRows2.key3 (o 3)) (SixRows2.key4 (o 4)) (SixRows2.key5 (o 5))
lemma unkey_rawRows (o : Orders) : PureSixRowModel2.unkey (SixRows2.key o) = rawRows o := by
  rw [← key_rawRows,PureSixRowModel2.unkey_key]
lemma src_rawRows (o : Orders) (h : LocalBounds b hb o) :
    PureSixRowModel2.src (rawRows o) = FlatCanonicalKernel.src b hb o :=
  (src_rows (SixRows2.key0 (o 0)) (SixRows2.key1 (o 1)) (SixRows2.key2 (o 2)) (SixRows2.key3 (o 3)) (SixRows2.key4 (o 4)) (SixRows2.key5 (o 5))).trans (funext (fun e => (SixRows2.flat_src o h e).symm))
lemma dst_rawRows (o : Orders) (h : LocalBounds b hb o) :
    PureSixRowModel2.dst (rawRows o) = FlatCanonicalKernel.dst b hb o :=
  (dst_rows (SixRows2.key0 (o 0)) (SixRows2.key1 (o 1)) (SixRows2.key2 (o 2)) (SixRows2.key3 (o 3)) (SixRows2.key4 (o 4)) (SixRows2.key5 (o 5))).trans (funext (fun e => (SixRows2.flat_dst o h e).symm))

#print axioms src_rawRows
#print axioms dst_rawRows
end Erdos184Work.SixCaseCompatibility2
