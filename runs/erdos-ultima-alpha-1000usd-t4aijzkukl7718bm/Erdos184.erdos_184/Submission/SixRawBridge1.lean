import Submission.SixRows1
import Submission.PureSixRowModel1

/-! Raw/canonical row identities factored through plain finite row variables. -/
namespace Erdos184Work.SixCaseCompatibility1
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open CanonicalThreeReduction SixRows1
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma key_rows (q0 : Fin 60) (q1 : Fin 60) (q2 : Fin 12) (q3 : Fin 12) (q4 : Fin 12) (q5 : Fin 12) :
    PureSixRowModel1.key (PureSixRowModel1.rows q0 q1 q2 q3 q4 q5) = 1244160 * q0.val + 20736 * q1.val + 1728 * q2.val + 144 * q3.val + 12 * q4.val + 1 * q5.val := rfl
lemma src_rows (q0 : Fin 60) (q1 : Fin 60) (q2 : Fin 12) (q3 : Fin 12) (q4 : Fin 12) (q5 : Fin 12) :
    PureSixRowModel1.src (PureSixRowModel1.rows q0 q1 q2 q3 q4 q5) = SixRows1.srcAt q0 q1 q2 q3 q4 q5 := by
  funext e
  fin_cases e <;> rfl
lemma dst_rows (q0 : Fin 60) (q1 : Fin 60) (q2 : Fin 12) (q3 : Fin 12) (q4 : Fin 12) (q5 : Fin 12) :
    PureSixRowModel1.dst (PureSixRowModel1.rows q0 q1 q2 q3 q4 q5) = SixRows1.dstAt q0 q1 q2 q3 q4 q5 := by
  funext e
  fin_cases e <;> rfl
def rawRows (o : Orders) : PureSixRowModel1.Rows := PureSixRowModel1.rows (SixRows1.key0 (o 0)) (SixRows1.key1 (o 1)) (SixRows1.key2 (o 2)) (SixRows1.key3 (o 3)) (SixRows1.key4 (o 4)) (SixRows1.key5 (o 5))
lemma key_rawRows (o : Orders) : PureSixRowModel1.key (rawRows o) = SixRows1.key o :=
  key_rows (SixRows1.key0 (o 0)) (SixRows1.key1 (o 1)) (SixRows1.key2 (o 2)) (SixRows1.key3 (o 3)) (SixRows1.key4 (o 4)) (SixRows1.key5 (o 5))
lemma unkey_rawRows (o : Orders) : PureSixRowModel1.unkey (SixRows1.key o) = rawRows o := by
  rw [← key_rawRows,PureSixRowModel1.unkey_key]
lemma src_rawRows (o : Orders) (h : LocalBounds b hb o) :
    PureSixRowModel1.src (rawRows o) = FlatCanonicalKernel.src b hb o :=
  (src_rows (SixRows1.key0 (o 0)) (SixRows1.key1 (o 1)) (SixRows1.key2 (o 2)) (SixRows1.key3 (o 3)) (SixRows1.key4 (o 4)) (SixRows1.key5 (o 5))).trans (funext (fun e => (SixRows1.flat_src o h e).symm))
lemma dst_rawRows (o : Orders) (h : LocalBounds b hb o) :
    PureSixRowModel1.dst (rawRows o) = FlatCanonicalKernel.dst b hb o :=
  (dst_rows (SixRows1.key0 (o 0)) (SixRows1.key1 (o 1)) (SixRows1.key2 (o 2)) (SixRows1.key3 (o 3)) (SixRows1.key4 (o 4)) (SixRows1.key5 (o 5))).trans (funext (fun e => (SixRows1.flat_dst o h e).symm))

#print axioms src_rawRows
#print axioms dst_rawRows
end Erdos184Work.SixCaseCompatibility1
