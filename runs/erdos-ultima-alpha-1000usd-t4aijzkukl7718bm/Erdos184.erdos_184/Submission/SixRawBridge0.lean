import Submission.SixRows0
import Submission.PureSixRowModel0

/-! Raw/canonical row identities factored through plain finite row variables. -/
namespace Erdos184Work.SixCaseCompatibility0
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open CanonicalThreeReduction SixRows0
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma key_rows (q0 : Fin 12) (q1 : Fin 12) (q2 : Fin 12) (q3 : Fin 12) (q4 : Fin 12) (q5 : Fin 12) :
    PureSixRowModel0.key (PureSixRowModel0.rows q0 q1 q2 q3 q4 q5) = 248832 * q0.val + 20736 * q1.val + 1728 * q2.val + 144 * q3.val + 12 * q4.val + 1 * q5.val := rfl
lemma src_rows (q0 : Fin 12) (q1 : Fin 12) (q2 : Fin 12) (q3 : Fin 12) (q4 : Fin 12) (q5 : Fin 12) :
    PureSixRowModel0.src (PureSixRowModel0.rows q0 q1 q2 q3 q4 q5) = SixRows0.srcAt q0 q1 q2 q3 q4 q5 := by
  funext e
  fin_cases e <;> rfl
lemma dst_rows (q0 : Fin 12) (q1 : Fin 12) (q2 : Fin 12) (q3 : Fin 12) (q4 : Fin 12) (q5 : Fin 12) :
    PureSixRowModel0.dst (PureSixRowModel0.rows q0 q1 q2 q3 q4 q5) = SixRows0.dstAt q0 q1 q2 q3 q4 q5 := by
  funext e
  fin_cases e <;> rfl
def rawRows (o : Orders) : PureSixRowModel0.Rows := PureSixRowModel0.rows (SixRows0.key0 (o 0)) (SixRows0.key1 (o 1)) (SixRows0.key2 (o 2)) (SixRows0.key3 (o 3)) (SixRows0.key4 (o 4)) (SixRows0.key5 (o 5))
lemma key_rawRows (o : Orders) : PureSixRowModel0.key (rawRows o) = SixRows0.key o :=
  key_rows (SixRows0.key0 (o 0)) (SixRows0.key1 (o 1)) (SixRows0.key2 (o 2)) (SixRows0.key3 (o 3)) (SixRows0.key4 (o 4)) (SixRows0.key5 (o 5))
lemma unkey_rawRows (o : Orders) : PureSixRowModel0.unkey (SixRows0.key o) = rawRows o := by
  rw [← key_rawRows,PureSixRowModel0.unkey_key]
lemma src_rawRows (o : Orders) (h : LocalBounds b hb o) :
    PureSixRowModel0.src (rawRows o) = FlatCanonicalKernel.src b hb o :=
  (src_rows (SixRows0.key0 (o 0)) (SixRows0.key1 (o 1)) (SixRows0.key2 (o 2)) (SixRows0.key3 (o 3)) (SixRows0.key4 (o 4)) (SixRows0.key5 (o 5))).trans (funext (fun e => (SixRows0.flat_src o h e).symm))
lemma dst_rawRows (o : Orders) (h : LocalBounds b hb o) :
    PureSixRowModel0.dst (rawRows o) = FlatCanonicalKernel.dst b hb o :=
  (dst_rows (SixRows0.key0 (o 0)) (SixRows0.key1 (o 1)) (SixRows0.key2 (o 2)) (SixRows0.key3 (o 3)) (SixRows0.key4 (o 4)) (SixRows0.key5 (o 5))).trans (funext (fun e => (SixRows0.flat_dst o h e).symm))

#print axioms src_rawRows
#print axioms dst_rawRows
end Erdos184Work.SixCaseCompatibility0
