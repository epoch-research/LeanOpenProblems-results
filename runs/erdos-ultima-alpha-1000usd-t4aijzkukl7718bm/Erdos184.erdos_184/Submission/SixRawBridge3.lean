import Submission.SixRows3
import Submission.PureSixRowModel3

/-! Raw/canonical row identities factored through plain finite row variables. -/
namespace Erdos184Work.SixCaseCompatibility3
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open CanonicalThreeReduction SixRows3
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma key_rows (q0 : Fin 60) (q1 : Fin 60) (q2 : Fin 60) (q3 : Fin 60) (q4 : Fin 60) (q5 : Fin 60) :
    PureSixRowModel3.key (PureSixRowModel3.rows q0 q1 q2 q3 q4 q5) = 777600000 * q0.val + 12960000 * q1.val + 216000 * q2.val + 3600 * q3.val + 60 * q4.val + 1 * q5.val := rfl
lemma src_rows (q0 : Fin 60) (q1 : Fin 60) (q2 : Fin 60) (q3 : Fin 60) (q4 : Fin 60) (q5 : Fin 60) :
    PureSixRowModel3.src (PureSixRowModel3.rows q0 q1 q2 q3 q4 q5) = SixRows3.srcAt q0 q1 q2 q3 q4 q5 := by
  funext e
  fin_cases e <;> rfl
lemma dst_rows (q0 : Fin 60) (q1 : Fin 60) (q2 : Fin 60) (q3 : Fin 60) (q4 : Fin 60) (q5 : Fin 60) :
    PureSixRowModel3.dst (PureSixRowModel3.rows q0 q1 q2 q3 q4 q5) = SixRows3.dstAt q0 q1 q2 q3 q4 q5 := by
  funext e
  fin_cases e <;> rfl
def rawRows (o : Orders) : PureSixRowModel3.Rows := PureSixRowModel3.rows (SixRows3.key0 (o 0)) (SixRows3.key1 (o 1)) (SixRows3.key2 (o 2)) (SixRows3.key3 (o 3)) (SixRows3.key4 (o 4)) (SixRows3.key5 (o 5))
lemma key_rawRows (o : Orders) : PureSixRowModel3.key (rawRows o) = SixRows3.key o :=
  key_rows (SixRows3.key0 (o 0)) (SixRows3.key1 (o 1)) (SixRows3.key2 (o 2)) (SixRows3.key3 (o 3)) (SixRows3.key4 (o 4)) (SixRows3.key5 (o 5))
lemma unkey_rawRows (o : Orders) : PureSixRowModel3.unkey (SixRows3.key o) = rawRows o := by
  rw [← key_rawRows,PureSixRowModel3.unkey_key]
lemma src_rawRows (o : Orders) (h : LocalBounds b hb o) :
    PureSixRowModel3.src (rawRows o) = FlatCanonicalKernel.src b hb o :=
  (src_rows (SixRows3.key0 (o 0)) (SixRows3.key1 (o 1)) (SixRows3.key2 (o 2)) (SixRows3.key3 (o 3)) (SixRows3.key4 (o 4)) (SixRows3.key5 (o 5))).trans (funext (fun e => (SixRows3.flat_src o h e).symm))
lemma dst_rawRows (o : Orders) (h : LocalBounds b hb o) :
    PureSixRowModel3.dst (rawRows o) = FlatCanonicalKernel.dst b hb o :=
  (dst_rows (SixRows3.key0 (o 0)) (SixRows3.key1 (o 1)) (SixRows3.key2 (o 2)) (SixRows3.key3 (o 3)) (SixRows3.key4 (o 4)) (SixRows3.key5 (o 5))).trans (funext (fun e => (SixRows3.flat_dst o h e).symm))

#print axioms src_rawRows
#print axioms dst_rawRows
end Erdos184Work.SixCaseCompatibility3
