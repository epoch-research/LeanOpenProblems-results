import Submission.SixRows4
import Submission.PureSixRowModel4

/-! Raw/canonical row identities factored through plain finite row variables. -/
namespace Erdos184Work.SixCaseCompatibility4
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open CanonicalThreeReduction SixRows4
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma key_rows (q0 : Fin 360) (q1 : Fin 60) (q2 : Fin 60) (q3 : Fin 12) (q4 : Fin 12) (q5 : Fin 12) :
    PureSixRowModel4.key (PureSixRowModel4.rows q0 q1 q2 q3 q4 q5) = 6220800 * q0.val + 103680 * q1.val + 1728 * q2.val + 144 * q3.val + 12 * q4.val + 1 * q5.val := rfl
lemma src_rows (q0 : Fin 360) (q1 : Fin 60) (q2 : Fin 60) (q3 : Fin 12) (q4 : Fin 12) (q5 : Fin 12) :
    PureSixRowModel4.src (PureSixRowModel4.rows q0 q1 q2 q3 q4 q5) = SixRows4.srcAt q0 q1 q2 q3 q4 q5 := by
  funext e
  fin_cases e <;> rfl
lemma dst_rows (q0 : Fin 360) (q1 : Fin 60) (q2 : Fin 60) (q3 : Fin 12) (q4 : Fin 12) (q5 : Fin 12) :
    PureSixRowModel4.dst (PureSixRowModel4.rows q0 q1 q2 q3 q4 q5) = SixRows4.dstAt q0 q1 q2 q3 q4 q5 := by
  funext e
  fin_cases e <;> rfl
def rawRows (o : Orders) : PureSixRowModel4.Rows := PureSixRowModel4.rows (SixRows4.key0 (o 0)) (SixRows4.key1 (o 1)) (SixRows4.key2 (o 2)) (SixRows4.key3 (o 3)) (SixRows4.key4 (o 4)) (SixRows4.key5 (o 5))
lemma key_rawRows (o : Orders) : PureSixRowModel4.key (rawRows o) = SixRows4.key o :=
  key_rows (SixRows4.key0 (o 0)) (SixRows4.key1 (o 1)) (SixRows4.key2 (o 2)) (SixRows4.key3 (o 3)) (SixRows4.key4 (o 4)) (SixRows4.key5 (o 5))
lemma unkey_rawRows (o : Orders) : PureSixRowModel4.unkey (SixRows4.key o) = rawRows o := by
  rw [← key_rawRows,PureSixRowModel4.unkey_key]
lemma src_rawRows (o : Orders) (h : LocalBounds b hb o) :
    PureSixRowModel4.src (rawRows o) = FlatCanonicalKernel.src b hb o :=
  (src_rows (SixRows4.key0 (o 0)) (SixRows4.key1 (o 1)) (SixRows4.key2 (o 2)) (SixRows4.key3 (o 3)) (SixRows4.key4 (o 4)) (SixRows4.key5 (o 5))).trans (funext (fun e => (SixRows4.flat_src o h e).symm))
lemma dst_rawRows (o : Orders) (h : LocalBounds b hb o) :
    PureSixRowModel4.dst (rawRows o) = FlatCanonicalKernel.dst b hb o :=
  (dst_rows (SixRows4.key0 (o 0)) (SixRows4.key1 (o 1)) (SixRows4.key2 (o 2)) (SixRows4.key3 (o 3)) (SixRows4.key4 (o 4)) (SixRows4.key5 (o 5))).trans (funext (fun e => (SixRows4.flat_dst o h e).symm))

#print axioms src_rawRows
#print axioms dst_rawRows
end Erdos184Work.SixCaseCompatibility4
