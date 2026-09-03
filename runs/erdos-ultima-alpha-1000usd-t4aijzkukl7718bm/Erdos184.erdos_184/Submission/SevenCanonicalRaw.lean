import Submission.SevenRows
import Submission.PureSevenRowModel
import Submission.PureSevenRowExt
import Submission.CanonicalColorLocalBounds

/-! Both directions between unrestricted seven-row words and canonical marked orders. -/
namespace Erdos184Work.SevenCanonicalRaw
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open LabelKernel Erdos184Serial CanonicalThreeReduction SevenRows
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option Elab.async false
noncomputable local instance {I : Type*} {m : I → ℕ} : DecidableEq (Σ i, Fin (m i)) := Classical.decEq _
def rawRows (o : Orders) : PureSevenRowModel.Rows := PureSevenRowModel.rows (SevenRows.key0 (o 0)) (SevenRows.key1 (o 1)) (SevenRows.key2 (o 2)) (SevenRows.key3 (o 3)) (SevenRows.key4 (o 4)) (SevenRows.key5 (o 5)) (SevenRows.key6 (o 6))
lemma key_rows (q0 q1 q2 q3 q4 q5 q6 : Fin 60) :
    PureSevenRowModel.key (PureSevenRowModel.rows q0 q1 q2 q3 q4 q5 q6) = 46656000000 * q0.val + 777600000 * q1.val + 12960000 * q2.val + 216000 * q3.val + 3600 * q4.val + 60 * q5.val + 1 * q6.val := rfl
#eval IO.eprintln "SevenCanonicalRaw: key_rows"
lemma key_rawRows (o : Orders) : PureSevenRowModel.key (rawRows o) = SevenRows.key o :=
  key_rows (SevenRows.key0 (o 0)) (SevenRows.key1 (o 1)) (SevenRows.key2 (o 2)) (SevenRows.key3 (o 3)) (SevenRows.key4 (o 4)) (SevenRows.key5 (o 5)) (SevenRows.key6 (o 6))
#eval IO.eprintln "SevenCanonicalRaw: key_rawRows"
lemma src_rows (q0 q1 q2 q3 q4 q5 q6 : Fin 60) :
    PureSevenRowModel.src (PureSevenRowModel.rows q0 q1 q2 q3 q4 q5 q6) =
      SevenRows.srcAt q0 q1 q2 q3 q4 q5 q6 := by
  funext e
  fin_cases e <;> rfl
#eval IO.eprintln "SevenCanonicalRaw: src_rows"
lemma src_rawRows (o : Orders) :
    PureSevenRowModel.src (rawRows o) = FlatCanonicalKernel.src b hb o := by
  funext e
  exact (congrFun (src_rows (SevenRows.key0 (o 0)) (SevenRows.key1 (o 1)) (SevenRows.key2 (o 2)) (SevenRows.key3 (o 3)) (SevenRows.key4 (o 4)) (SevenRows.key5 (o 5)) (SevenRows.key6 (o 6))) e).trans (SevenRows.flat_src o e).symm
#eval IO.eprintln "SevenCanonicalRaw: src_rawRows"
lemma dst_rows (q0 q1 q2 q3 q4 q5 q6 : Fin 60) :
    PureSevenRowModel.dst (PureSevenRowModel.rows q0 q1 q2 q3 q4 q5 q6) =
      SevenRows.dstAt q0 q1 q2 q3 q4 q5 q6 := by
  funext e
  fin_cases e <;> rfl
#eval IO.eprintln "SevenCanonicalRaw: dst_rows"
lemma dst_rawRows (o : Orders) :
    PureSevenRowModel.dst (rawRows o) = FlatCanonicalKernel.dst b hb o := by
  funext e
  exact (congrFun (dst_rows (SevenRows.key0 (o 0)) (SevenRows.key1 (o 1)) (SevenRows.key2 (o 2)) (SevenRows.key3 (o 3)) (SevenRows.key4 (o 4)) (SevenRows.key5 (o 5)) (SevenRows.key6 (o 6))) e).trans (SevenRows.flat_dst o e).symm
#eval IO.eprintln "SevenCanonicalRaw: dst_rawRows"
def rawColor (e : PureSevenRowModel.E) : Fin 7 := (PureSevenRowModel.edge e).1
lemma color_raw : rawColor = FlatCanonicalKernel.color b := by
  funext e
  fin_cases e <;> rfl
#eval IO.eprintln "SevenCanonicalRaw: color_raw"
def orderOfRow : Fin 60 → Marked.Order 4 := ![(((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),(Sum.inr ())),(((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),(Sum.inl (Sum.inr ()))),(((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inr ()))),(((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),(Sum.inr ())),(((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inr ())))),(((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inr ())))),(((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),(Sum.inr ())),(((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inr ())))),(((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inr ())))),(((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),(Sum.inr ())),(((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inr ()))),(((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),(Sum.inl (Sum.inr ()))),(((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),(Sum.inl (Sum.inr ()))),(((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),(Sum.inl (Sum.inl (Sum.inr ())))),(((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),(Sum.inl (Sum.inl (Sum.inr ())))),(((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),(Sum.inl (Sum.inr ()))),(((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),(Sum.inr ())),(((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),(Sum.inr ())),(((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),(Sum.inr ())),(((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),(Sum.inl (Sum.inr ()))),(((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),(Sum.inl (Sum.inr ()))),(((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),(Sum.inr ())),(((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),(Sum.inr ())),(((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),(Sum.inl (Sum.inr ()))),(((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inr ()))),(((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),(Sum.inr ())),(((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inr ())))),(((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),(Sum.inl (Sum.inl (Sum.inr ())))),(((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (1 : Fin 2)))),(Sum.inl (Sum.inl (Sum.inr ())))),(((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inr ())))),(((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),(Sum.inr ())),(((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inr ())))),(((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),(Sum.inl (Sum.inl (Sum.inr ())))),(((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),(Sum.inr ())),(((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),(Sum.inl (Sum.inl (Sum.inr ())))),(((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inr ())))),(((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inr ()))),(((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (1 : Fin 2)))),(Sum.inl (Sum.inr ()))),(((((),(1 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (0 : Fin 2)))),(Sum.inl (Sum.inr ()))),(((((),(1 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (0 : Fin 2)))),(Sum.inl (Sum.inl (Sum.inr ())))),(((((),(0 : Fin 2)),(Sum.inl (1 : Fin 2))),(Sum.inl (Sum.inl (0 : Fin 2)))),(Sum.inl (Sum.inr ()))),(((((),(0 : Fin 2)),(Sum.inr ())),(Sum.inl (Sum.inl (0 : Fin 2)))),(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(((((),(1 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (0 : Fin 2)))),(Sum.inl (Sum.inl (Sum.inr ())))),(((((),(0 : Fin 2)),(Sum.inl (0 : Fin 2))),(Sum.inl (Sum.inl (0 : Fin 2)))),(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))]
lemma key_orderOfRow : ∀ q : Fin 60, SevenRows.key0 (orderOfRow q) = q := by decide +kernel
#eval IO.eprintln "SevenCanonicalRaw: key_orderOfRow"
def canonical (q : PureSevenRowModel.Rows) : Orders :=
  Fin.cases (orderOfRow (q 0)) (Fin.cases (orderOfRow (q 1)) (Fin.cases (orderOfRow (q 2)) (Fin.cases (orderOfRow (q 3)) (Fin.cases (orderOfRow (q 4)) (Fin.cases (orderOfRow (q 5)) (Fin.cases (orderOfRow (q 6)) ((fun i => Fin.elim0 i))))))))
lemma key_eq1 : SevenRows.key1 = SevenRows.key0 := rfl
lemma key_eq2 : SevenRows.key2 = SevenRows.key0 := rfl
lemma key_eq3 : SevenRows.key3 = SevenRows.key0 := rfl
lemma key_eq4 : SevenRows.key4 = SevenRows.key0 := rfl
lemma key_eq5 : SevenRows.key5 = SevenRows.key0 := rfl
lemma key_eq6 : SevenRows.key6 = SevenRows.key0 := rfl
lemma canonical_at0 (q : PureSevenRowModel.Rows) : canonical q 0 = orderOfRow (q 0) := rfl
lemma canonical_at1 (q : PureSevenRowModel.Rows) : canonical q 1 = orderOfRow (q 1) := rfl
lemma canonical_at2 (q : PureSevenRowModel.Rows) : canonical q 2 = orderOfRow (q 2) := rfl
lemma canonical_at3 (q : PureSevenRowModel.Rows) : canonical q 3 = orderOfRow (q 3) := rfl
lemma canonical_at4 (q : PureSevenRowModel.Rows) : canonical q 4 = orderOfRow (q 4) := rfl
lemma canonical_at5 (q : PureSevenRowModel.Rows) : canonical q 5 = orderOfRow (q 5) := rfl
lemma canonical_at6 (q : PureSevenRowModel.Rows) : canonical q 6 = orderOfRow (q 6) := rfl
#eval IO.eprintln "SevenCanonicalRaw: coordinate identities"
lemma raw_rows_at6 (a0 a1 a2 a3 a4 a5 a6 : Fin 60) :
    PureSevenRowModel.rows a0 a1 a2 a3 a4 a5 a6 6 = a6 := rfl
lemma rawRows_canonical (q : PureSevenRowModel.Rows) : rawRows (canonical q) = q := by
  funext i
  fin_cases i
  · unfold rawRows
    exact (PureSevenRowModel.rows_at0 (SevenRows.key0 (canonical q 0)) (SevenRows.key1 (canonical q 1)) (SevenRows.key2 (canonical q 2)) (SevenRows.key3 (canonical q 3)) (SevenRows.key4 (canonical q 4)) (SevenRows.key5 (canonical q 5)) (SevenRows.key6 (canonical q 6))).trans
      ((congrArg SevenRows.key0 (canonical_at0 q)).trans (key_orderOfRow (q 0)))
  · unfold rawRows
    exact (PureSevenRowModel.rows_at1 (SevenRows.key0 (canonical q 0)) (SevenRows.key1 (canonical q 1)) (SevenRows.key2 (canonical q 2)) (SevenRows.key3 (canonical q 3)) (SevenRows.key4 (canonical q 4)) (SevenRows.key5 (canonical q 5)) (SevenRows.key6 (canonical q 6))).trans
      ((congrArg SevenRows.key1 (canonical_at1 q)).trans ((congrArg (fun f => f (orderOfRow (q 1))) key_eq1).trans (key_orderOfRow (q 1))))
  · unfold rawRows
    exact (PureSevenRowModel.rows_at2 (SevenRows.key0 (canonical q 0)) (SevenRows.key1 (canonical q 1)) (SevenRows.key2 (canonical q 2)) (SevenRows.key3 (canonical q 3)) (SevenRows.key4 (canonical q 4)) (SevenRows.key5 (canonical q 5)) (SevenRows.key6 (canonical q 6))).trans
      ((congrArg SevenRows.key2 (canonical_at2 q)).trans ((congrArg (fun f => f (orderOfRow (q 2))) key_eq2).trans (key_orderOfRow (q 2))))
  · unfold rawRows
    exact (PureSevenRowModel.rows_at3 (SevenRows.key0 (canonical q 0)) (SevenRows.key1 (canonical q 1)) (SevenRows.key2 (canonical q 2)) (SevenRows.key3 (canonical q 3)) (SevenRows.key4 (canonical q 4)) (SevenRows.key5 (canonical q 5)) (SevenRows.key6 (canonical q 6))).trans
      ((congrArg SevenRows.key3 (canonical_at3 q)).trans ((congrArg (fun f => f (orderOfRow (q 3))) key_eq3).trans (key_orderOfRow (q 3))))
  · unfold rawRows
    exact (PureSevenRowModel.rows_at4 (SevenRows.key0 (canonical q 0)) (SevenRows.key1 (canonical q 1)) (SevenRows.key2 (canonical q 2)) (SevenRows.key3 (canonical q 3)) (SevenRows.key4 (canonical q 4)) (SevenRows.key5 (canonical q 5)) (SevenRows.key6 (canonical q 6))).trans
      ((congrArg SevenRows.key4 (canonical_at4 q)).trans ((congrArg (fun f => f (orderOfRow (q 4))) key_eq4).trans (key_orderOfRow (q 4))))
  · unfold rawRows
    exact (PureSevenRowModel.rows_at5 (SevenRows.key0 (canonical q 0)) (SevenRows.key1 (canonical q 1)) (SevenRows.key2 (canonical q 2)) (SevenRows.key3 (canonical q 3)) (SevenRows.key4 (canonical q 4)) (SevenRows.key5 (canonical q 5)) (SevenRows.key6 (canonical q 6))).trans
      ((congrArg SevenRows.key5 (canonical_at5 q)).trans ((congrArg (fun f => f (orderOfRow (q 5))) key_eq5).trans (key_orderOfRow (q 5))))
  · unfold rawRows
    exact (raw_rows_at6 (SevenRows.key0 (canonical q 0)) (SevenRows.key1 (canonical q 1)) (SevenRows.key2 (canonical q 2)) (SevenRows.key3 (canonical q 3)) (SevenRows.key4 (canonical q 4)) (SevenRows.key5 (canonical q 5)) (SevenRows.key6 (canonical q 6))).trans
      ((congrArg SevenRows.key6 (canonical_at6 q)).trans ((congrArg (fun f => f (orderOfRow (q 6))) key_eq6).trans (key_orderOfRow (q 6))))
#eval IO.eprintln "SevenCanonicalRaw: rawRows_canonical"
lemma colored_of_local (o : Orders) (h : LocalBounds b hb o) :
    ColorLocalBounds (PureSevenRowModel.src (rawRows o)) (PureSevenRowModel.dst (rawRows o)) rawColor := by
  rw [src_rawRows,dst_rawRows,color_raw]
  exact LocalBounds.flat_colored b hb o h
lemma local_of_colored (q : PureSevenRowModel.Rows)
    (h : ColorLocalBounds (PureSevenRowModel.src q) (PureSevenRowModel.dst q) rawColor) :
    LocalBounds b hb (canonical q) := by
  apply localBounds_of_flat_colored b hb (canonical q)
  rw [← src_rawRows,← dst_rawRows,← color_raw,rawRows_canonical]
  exact h
#print axioms rawRows_canonical
#print axioms colored_of_local
#print axioms local_of_colored
end Erdos184Work.SevenCanonicalRaw
