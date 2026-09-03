import Submission.SevenProjection4
import Submission.SevenCanonicalRaw
import Submission.SixCaseCompatibility0
import Submission.SixOrbitKernel0
import Submission.PureSevenProjectionNumbers

/-! Necessary six-word catalogue conditions on each seven-color omission. -/
namespace Erdos184Work.SevenProjectionCode4
open CycleSegments CanonicalThreeReduction SevenProjection4
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option Elab.async false
lemma row0_0 : ∀ q : Marked.Order 3,
    PureSevenProjectionNumbers.enc4_0 (SevenRows.key0 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))) =
      SixRows0.key0 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))) := by decide +kernel
lemma row0_1 : ∀ q : Marked.Order 3,
    PureSevenProjectionNumbers.enc4_0 (SevenRows.key0 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))) =
      SixRows0.key0 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))) := by decide +kernel
lemma row0_2 : ∀ q : Marked.Order 3,
    PureSevenProjectionNumbers.enc4_0 (SevenRows.key0 (q,(Sum.inl (Sum.inl (Sum.inr ()))))) =
      SixRows0.key0 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inr ()))))) := by decide +kernel
lemma row0_3 : ∀ q : Marked.Order 3,
    PureSevenProjectionNumbers.enc4_0 (SevenRows.key0 (q,(Sum.inl (Sum.inr ())))) =
      SixRows0.key0 (smallOrder0 (q,(Sum.inl (Sum.inr ())))) := by decide +kernel
lemma row0_4 : ∀ q : Marked.Order 3,
    PureSevenProjectionNumbers.enc4_0 (SevenRows.key0 (q,(Sum.inr ()))) =
      SixRows0.key0 (smallOrder0 (q,(Sum.inr ()))) := by decide +kernel
lemma row0 : ∀ q : Marked.Order 4,
    PureSevenProjectionNumbers.enc4_0 (SevenRows.key0 q) =
      SixRows0.key0 (smallOrder0 q) := by
  rintro ⟨q,t⟩
  fin_cases t
  · exact row0_0 q
  · exact row0_1 q
  · exact row0_2 q
  · exact row0_3 q
  · exact row0_4 q
lemma row1_0 : ∀ q : Marked.Order 3,
    PureSevenProjectionNumbers.enc4_1 (SevenRows.key1 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))) =
      SixRows0.key1 (smallOrder1 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))) := by decide +kernel
lemma row1_1 : ∀ q : Marked.Order 3,
    PureSevenProjectionNumbers.enc4_1 (SevenRows.key1 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))) =
      SixRows0.key1 (smallOrder1 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))) := by decide +kernel
lemma row1_2 : ∀ q : Marked.Order 3,
    PureSevenProjectionNumbers.enc4_1 (SevenRows.key1 (q,(Sum.inl (Sum.inl (Sum.inr ()))))) =
      SixRows0.key1 (smallOrder1 (q,(Sum.inl (Sum.inl (Sum.inr ()))))) := by decide +kernel
lemma row1_3 : ∀ q : Marked.Order 3,
    PureSevenProjectionNumbers.enc4_1 (SevenRows.key1 (q,(Sum.inl (Sum.inr ())))) =
      SixRows0.key1 (smallOrder1 (q,(Sum.inl (Sum.inr ())))) := by decide +kernel
lemma row1_4 : ∀ q : Marked.Order 3,
    PureSevenProjectionNumbers.enc4_1 (SevenRows.key1 (q,(Sum.inr ()))) =
      SixRows0.key1 (smallOrder1 (q,(Sum.inr ()))) := by decide +kernel
lemma row1 : ∀ q : Marked.Order 4,
    PureSevenProjectionNumbers.enc4_1 (SevenRows.key1 q) =
      SixRows0.key1 (smallOrder1 q) := by
  rintro ⟨q,t⟩
  fin_cases t
  · exact row1_0 q
  · exact row1_1 q
  · exact row1_2 q
  · exact row1_3 q
  · exact row1_4 q
lemma row2_0 : ∀ q : Marked.Order 3,
    PureSevenProjectionNumbers.enc4_2 (SevenRows.key2 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))) =
      SixRows0.key2 (smallOrder2 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))) := by decide +kernel
lemma row2_1 : ∀ q : Marked.Order 3,
    PureSevenProjectionNumbers.enc4_2 (SevenRows.key2 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))) =
      SixRows0.key2 (smallOrder2 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))) := by decide +kernel
lemma row2_2 : ∀ q : Marked.Order 3,
    PureSevenProjectionNumbers.enc4_2 (SevenRows.key2 (q,(Sum.inl (Sum.inl (Sum.inr ()))))) =
      SixRows0.key2 (smallOrder2 (q,(Sum.inl (Sum.inl (Sum.inr ()))))) := by decide +kernel
lemma row2_3 : ∀ q : Marked.Order 3,
    PureSevenProjectionNumbers.enc4_2 (SevenRows.key2 (q,(Sum.inl (Sum.inr ())))) =
      SixRows0.key2 (smallOrder2 (q,(Sum.inl (Sum.inr ())))) := by decide +kernel
lemma row2_4 : ∀ q : Marked.Order 3,
    PureSevenProjectionNumbers.enc4_2 (SevenRows.key2 (q,(Sum.inr ()))) =
      SixRows0.key2 (smallOrder2 (q,(Sum.inr ()))) := by decide +kernel
lemma row2 : ∀ q : Marked.Order 4,
    PureSevenProjectionNumbers.enc4_2 (SevenRows.key2 q) =
      SixRows0.key2 (smallOrder2 q) := by
  rintro ⟨q,t⟩
  fin_cases t
  · exact row2_0 q
  · exact row2_1 q
  · exact row2_2 q
  · exact row2_3 q
  · exact row2_4 q
lemma row3_0 : ∀ q : Marked.Order 3,
    PureSevenProjectionNumbers.enc4_3 (SevenRows.key3 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))) =
      SixRows0.key3 (smallOrder3 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))) := by decide +kernel
lemma row3_1 : ∀ q : Marked.Order 3,
    PureSevenProjectionNumbers.enc4_3 (SevenRows.key3 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))) =
      SixRows0.key3 (smallOrder3 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))) := by decide +kernel
lemma row3_2 : ∀ q : Marked.Order 3,
    PureSevenProjectionNumbers.enc4_3 (SevenRows.key3 (q,(Sum.inl (Sum.inl (Sum.inr ()))))) =
      SixRows0.key3 (smallOrder3 (q,(Sum.inl (Sum.inl (Sum.inr ()))))) := by decide +kernel
lemma row3_3 : ∀ q : Marked.Order 3,
    PureSevenProjectionNumbers.enc4_3 (SevenRows.key3 (q,(Sum.inl (Sum.inr ())))) =
      SixRows0.key3 (smallOrder3 (q,(Sum.inl (Sum.inr ())))) := by decide +kernel
lemma row3_4 : ∀ q : Marked.Order 3,
    PureSevenProjectionNumbers.enc4_3 (SevenRows.key3 (q,(Sum.inr ()))) =
      SixRows0.key3 (smallOrder3 (q,(Sum.inr ()))) := by decide +kernel
lemma row3 : ∀ q : Marked.Order 4,
    PureSevenProjectionNumbers.enc4_3 (SevenRows.key3 q) =
      SixRows0.key3 (smallOrder3 q) := by
  rintro ⟨q,t⟩
  fin_cases t
  · exact row3_0 q
  · exact row3_1 q
  · exact row3_2 q
  · exact row3_3 q
  · exact row3_4 q
lemma row4_0 : ∀ q : Marked.Order 3,
    PureSevenProjectionNumbers.enc4_4 (SevenRows.key5 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))) =
      SixRows0.key4 (smallOrder4 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))) := by decide +kernel
lemma row4_1 : ∀ q : Marked.Order 3,
    PureSevenProjectionNumbers.enc4_4 (SevenRows.key5 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))) =
      SixRows0.key4 (smallOrder4 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))) := by decide +kernel
lemma row4_2 : ∀ q : Marked.Order 3,
    PureSevenProjectionNumbers.enc4_4 (SevenRows.key5 (q,(Sum.inl (Sum.inl (Sum.inr ()))))) =
      SixRows0.key4 (smallOrder4 (q,(Sum.inl (Sum.inl (Sum.inr ()))))) := by decide +kernel
lemma row4_3 : ∀ q : Marked.Order 3,
    PureSevenProjectionNumbers.enc4_4 (SevenRows.key5 (q,(Sum.inl (Sum.inr ())))) =
      SixRows0.key4 (smallOrder4 (q,(Sum.inl (Sum.inr ())))) := by decide +kernel
lemma row4_4 : ∀ q : Marked.Order 3,
    PureSevenProjectionNumbers.enc4_4 (SevenRows.key5 (q,(Sum.inr ()))) =
      SixRows0.key4 (smallOrder4 (q,(Sum.inr ()))) := by decide +kernel
lemma row4 : ∀ q : Marked.Order 4,
    PureSevenProjectionNumbers.enc4_4 (SevenRows.key5 q) =
      SixRows0.key4 (smallOrder4 q) := by
  rintro ⟨q,t⟩
  fin_cases t
  · exact row4_0 q
  · exact row4_1 q
  · exact row4_2 q
  · exact row4_3 q
  · exact row4_4 q
lemma row5_0 : ∀ q : Marked.Order 3,
    PureSevenProjectionNumbers.enc4_5 (SevenRows.key6 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))) =
      SixRows0.key5 (smallOrder5 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))) := by decide +kernel
lemma row5_1 : ∀ q : Marked.Order 3,
    PureSevenProjectionNumbers.enc4_5 (SevenRows.key6 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))) =
      SixRows0.key5 (smallOrder5 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))) := by decide +kernel
lemma row5_2 : ∀ q : Marked.Order 3,
    PureSevenProjectionNumbers.enc4_5 (SevenRows.key6 (q,(Sum.inl (Sum.inl (Sum.inr ()))))) =
      SixRows0.key5 (smallOrder5 (q,(Sum.inl (Sum.inl (Sum.inr ()))))) := by decide +kernel
lemma row5_3 : ∀ q : Marked.Order 3,
    PureSevenProjectionNumbers.enc4_5 (SevenRows.key6 (q,(Sum.inl (Sum.inr ())))) =
      SixRows0.key5 (smallOrder5 (q,(Sum.inl (Sum.inr ())))) := by decide +kernel
lemma row5_4 : ∀ q : Marked.Order 3,
    PureSevenProjectionNumbers.enc4_5 (SevenRows.key6 (q,(Sum.inr ()))) =
      SixRows0.key5 (smallOrder5 (q,(Sum.inr ()))) := by decide +kernel
lemma row5 : ∀ q : Marked.Order 4,
    PureSevenProjectionNumbers.enc4_5 (SevenRows.key6 q) =
      SixRows0.key5 (smallOrder5 q) := by
  rintro ⟨q,t⟩
  fin_cases t
  · exact row5_0 q
  · exact row5_1 q
  · exact row5_2 q
  · exact row5_3 q
  · exact row5_4 q
lemma project_at0 (q : PureSevenRowModel.Rows) :
    PureSevenProjectionNumbers.project4 q 0 = PureSevenProjectionNumbers.enc4_0 (q 0) := rfl
lemma seven_rows_at0 (a0 a1 a2 a3 a4 a5 a6 : Fin 60) :
    PureSevenRowModel.rows a0 a1 a2 a3 a4 a5 a6 0 = a0 := rfl
lemma raw_at0 (o : Orders) :
    SevenCanonicalRaw.rawRows o 0 = SevenRows.key0 (o 0) := by
  unfold SevenCanonicalRaw.rawRows
  exact seven_rows_at0 (SevenRows.key0 (o 0)) (SevenRows.key1 (o 1)) (SevenRows.key2 (o 2)) (SevenRows.key3 (o 3)) (SevenRows.key4 (o 4)) (SevenRows.key5 (o 5)) (SevenRows.key6 (o 6))
lemma projected_raw_at0 (o : Orders) :
    PureSevenProjectionNumbers.project4 (SevenCanonicalRaw.rawRows o) 0 =
      PureSevenProjectionNumbers.enc4_0 (SevenRows.key0 (o 0)) :=
  (project_at0 (SevenCanonicalRaw.rawRows o)).trans
    (congrArg PureSevenProjectionNumbers.enc4_0 (raw_at0 o))
lemma six_rows_at0 (a0 a1 a2 a3 a4 a5 : Fin 12) :
    PureSixRowModel0.rows a0 a1 a2 a3 a4 a5 0 = a0 := rfl
lemma smallOrders_at0 (o : Orders) : smallOrders o 0 = smallOrder0 (o 0) := rfl
lemma small_raw_at0 (o : Orders) :
    SixCaseCompatibility0.rawRows (smallOrders o) 0 = SixRows0.key0 (smallOrder0 (o 0)) := by
  unfold SixCaseCompatibility0.rawRows
  exact (six_rows_at0 (SixRows0.key0 (smallOrders o 0)) (SixRows0.key1 (smallOrders o 1)) (SixRows0.key2 (smallOrders o 2)) (SixRows0.key3 (smallOrders o 3)) (SixRows0.key4 (smallOrders o 4)) (SixRows0.key5 (smallOrders o 5))).trans (congrArg SixRows0.key0 (smallOrders_at0 o))
lemma project_at1 (q : PureSevenRowModel.Rows) :
    PureSevenProjectionNumbers.project4 q 1 = PureSevenProjectionNumbers.enc4_1 (q 1) := rfl
lemma seven_rows_at1 (a0 a1 a2 a3 a4 a5 a6 : Fin 60) :
    PureSevenRowModel.rows a0 a1 a2 a3 a4 a5 a6 1 = a1 := rfl
lemma raw_at1 (o : Orders) :
    SevenCanonicalRaw.rawRows o 1 = SevenRows.key1 (o 1) := by
  unfold SevenCanonicalRaw.rawRows
  exact seven_rows_at1 (SevenRows.key0 (o 0)) (SevenRows.key1 (o 1)) (SevenRows.key2 (o 2)) (SevenRows.key3 (o 3)) (SevenRows.key4 (o 4)) (SevenRows.key5 (o 5)) (SevenRows.key6 (o 6))
lemma projected_raw_at1 (o : Orders) :
    PureSevenProjectionNumbers.project4 (SevenCanonicalRaw.rawRows o) 1 =
      PureSevenProjectionNumbers.enc4_1 (SevenRows.key1 (o 1)) :=
  (project_at1 (SevenCanonicalRaw.rawRows o)).trans
    (congrArg PureSevenProjectionNumbers.enc4_1 (raw_at1 o))
lemma six_rows_at1 (a0 a1 a2 a3 a4 a5 : Fin 12) :
    PureSixRowModel0.rows a0 a1 a2 a3 a4 a5 1 = a1 := rfl
lemma smallOrders_at1 (o : Orders) : smallOrders o 1 = smallOrder1 (o 1) := rfl
lemma small_raw_at1 (o : Orders) :
    SixCaseCompatibility0.rawRows (smallOrders o) 1 = SixRows0.key1 (smallOrder1 (o 1)) := by
  unfold SixCaseCompatibility0.rawRows
  exact (six_rows_at1 (SixRows0.key0 (smallOrders o 0)) (SixRows0.key1 (smallOrders o 1)) (SixRows0.key2 (smallOrders o 2)) (SixRows0.key3 (smallOrders o 3)) (SixRows0.key4 (smallOrders o 4)) (SixRows0.key5 (smallOrders o 5))).trans (congrArg SixRows0.key1 (smallOrders_at1 o))
lemma project_at2 (q : PureSevenRowModel.Rows) :
    PureSevenProjectionNumbers.project4 q 2 = PureSevenProjectionNumbers.enc4_2 (q 2) := rfl
lemma seven_rows_at2 (a0 a1 a2 a3 a4 a5 a6 : Fin 60) :
    PureSevenRowModel.rows a0 a1 a2 a3 a4 a5 a6 2 = a2 := rfl
lemma raw_at2 (o : Orders) :
    SevenCanonicalRaw.rawRows o 2 = SevenRows.key2 (o 2) := by
  unfold SevenCanonicalRaw.rawRows
  exact seven_rows_at2 (SevenRows.key0 (o 0)) (SevenRows.key1 (o 1)) (SevenRows.key2 (o 2)) (SevenRows.key3 (o 3)) (SevenRows.key4 (o 4)) (SevenRows.key5 (o 5)) (SevenRows.key6 (o 6))
lemma projected_raw_at2 (o : Orders) :
    PureSevenProjectionNumbers.project4 (SevenCanonicalRaw.rawRows o) 2 =
      PureSevenProjectionNumbers.enc4_2 (SevenRows.key2 (o 2)) :=
  (project_at2 (SevenCanonicalRaw.rawRows o)).trans
    (congrArg PureSevenProjectionNumbers.enc4_2 (raw_at2 o))
lemma six_rows_at2 (a0 a1 a2 a3 a4 a5 : Fin 12) :
    PureSixRowModel0.rows a0 a1 a2 a3 a4 a5 2 = a2 := rfl
lemma smallOrders_at2 (o : Orders) : smallOrders o 2 = smallOrder2 (o 2) := rfl
lemma small_raw_at2 (o : Orders) :
    SixCaseCompatibility0.rawRows (smallOrders o) 2 = SixRows0.key2 (smallOrder2 (o 2)) := by
  unfold SixCaseCompatibility0.rawRows
  exact (six_rows_at2 (SixRows0.key0 (smallOrders o 0)) (SixRows0.key1 (smallOrders o 1)) (SixRows0.key2 (smallOrders o 2)) (SixRows0.key3 (smallOrders o 3)) (SixRows0.key4 (smallOrders o 4)) (SixRows0.key5 (smallOrders o 5))).trans (congrArg SixRows0.key2 (smallOrders_at2 o))
lemma project_at3 (q : PureSevenRowModel.Rows) :
    PureSevenProjectionNumbers.project4 q 3 = PureSevenProjectionNumbers.enc4_3 (q 3) := rfl
lemma seven_rows_at3 (a0 a1 a2 a3 a4 a5 a6 : Fin 60) :
    PureSevenRowModel.rows a0 a1 a2 a3 a4 a5 a6 3 = a3 := rfl
lemma raw_at3 (o : Orders) :
    SevenCanonicalRaw.rawRows o 3 = SevenRows.key3 (o 3) := by
  unfold SevenCanonicalRaw.rawRows
  exact seven_rows_at3 (SevenRows.key0 (o 0)) (SevenRows.key1 (o 1)) (SevenRows.key2 (o 2)) (SevenRows.key3 (o 3)) (SevenRows.key4 (o 4)) (SevenRows.key5 (o 5)) (SevenRows.key6 (o 6))
lemma projected_raw_at3 (o : Orders) :
    PureSevenProjectionNumbers.project4 (SevenCanonicalRaw.rawRows o) 3 =
      PureSevenProjectionNumbers.enc4_3 (SevenRows.key3 (o 3)) :=
  (project_at3 (SevenCanonicalRaw.rawRows o)).trans
    (congrArg PureSevenProjectionNumbers.enc4_3 (raw_at3 o))
lemma six_rows_at3 (a0 a1 a2 a3 a4 a5 : Fin 12) :
    PureSixRowModel0.rows a0 a1 a2 a3 a4 a5 3 = a3 := rfl
lemma smallOrders_at3 (o : Orders) : smallOrders o 3 = smallOrder3 (o 3) := rfl
lemma small_raw_at3 (o : Orders) :
    SixCaseCompatibility0.rawRows (smallOrders o) 3 = SixRows0.key3 (smallOrder3 (o 3)) := by
  unfold SixCaseCompatibility0.rawRows
  exact (six_rows_at3 (SixRows0.key0 (smallOrders o 0)) (SixRows0.key1 (smallOrders o 1)) (SixRows0.key2 (smallOrders o 2)) (SixRows0.key3 (smallOrders o 3)) (SixRows0.key4 (smallOrders o 4)) (SixRows0.key5 (smallOrders o 5))).trans (congrArg SixRows0.key3 (smallOrders_at3 o))
lemma project_at4 (q : PureSevenRowModel.Rows) :
    PureSevenProjectionNumbers.project4 q 4 = PureSevenProjectionNumbers.enc4_4 (q 5) := rfl
lemma seven_rows_at4 (a0 a1 a2 a3 a4 a5 a6 : Fin 60) :
    PureSevenRowModel.rows a0 a1 a2 a3 a4 a5 a6 5 = a5 := rfl
lemma raw_at4 (o : Orders) :
    SevenCanonicalRaw.rawRows o 5 = SevenRows.key5 (o 5) := by
  unfold SevenCanonicalRaw.rawRows
  exact seven_rows_at4 (SevenRows.key0 (o 0)) (SevenRows.key1 (o 1)) (SevenRows.key2 (o 2)) (SevenRows.key3 (o 3)) (SevenRows.key4 (o 4)) (SevenRows.key5 (o 5)) (SevenRows.key6 (o 6))
lemma projected_raw_at4 (o : Orders) :
    PureSevenProjectionNumbers.project4 (SevenCanonicalRaw.rawRows o) 4 =
      PureSevenProjectionNumbers.enc4_4 (SevenRows.key5 (o 5)) :=
  (project_at4 (SevenCanonicalRaw.rawRows o)).trans
    (congrArg PureSevenProjectionNumbers.enc4_4 (raw_at4 o))
lemma six_rows_at4 (a0 a1 a2 a3 a4 a5 : Fin 12) :
    PureSixRowModel0.rows a0 a1 a2 a3 a4 a5 4 = a4 := rfl
lemma smallOrders_at4 (o : Orders) : smallOrders o 4 = smallOrder4 (o 5) := rfl
lemma small_raw_at4 (o : Orders) :
    SixCaseCompatibility0.rawRows (smallOrders o) 4 = SixRows0.key4 (smallOrder4 (o 5)) := by
  unfold SixCaseCompatibility0.rawRows
  exact (six_rows_at4 (SixRows0.key0 (smallOrders o 0)) (SixRows0.key1 (smallOrders o 1)) (SixRows0.key2 (smallOrders o 2)) (SixRows0.key3 (smallOrders o 3)) (SixRows0.key4 (smallOrders o 4)) (SixRows0.key5 (smallOrders o 5))).trans (congrArg SixRows0.key4 (smallOrders_at4 o))
lemma project_at5 (q : PureSevenRowModel.Rows) :
    PureSevenProjectionNumbers.project4 q 5 = PureSevenProjectionNumbers.enc4_5 (q 6) := rfl
lemma seven_rows_at5 (a0 a1 a2 a3 a4 a5 a6 : Fin 60) :
    PureSevenRowModel.rows a0 a1 a2 a3 a4 a5 a6 6 = a6 := rfl
lemma raw_at5 (o : Orders) :
    SevenCanonicalRaw.rawRows o 6 = SevenRows.key6 (o 6) := by
  unfold SevenCanonicalRaw.rawRows
  exact seven_rows_at5 (SevenRows.key0 (o 0)) (SevenRows.key1 (o 1)) (SevenRows.key2 (o 2)) (SevenRows.key3 (o 3)) (SevenRows.key4 (o 4)) (SevenRows.key5 (o 5)) (SevenRows.key6 (o 6))
lemma projected_raw_at5 (o : Orders) :
    PureSevenProjectionNumbers.project4 (SevenCanonicalRaw.rawRows o) 5 =
      PureSevenProjectionNumbers.enc4_5 (SevenRows.key6 (o 6)) :=
  (project_at5 (SevenCanonicalRaw.rawRows o)).trans
    (congrArg PureSevenProjectionNumbers.enc4_5 (raw_at5 o))
lemma six_rows_at5 (a0 a1 a2 a3 a4 a5 : Fin 12) :
    PureSixRowModel0.rows a0 a1 a2 a3 a4 a5 5 = a5 := rfl
lemma smallOrders_at5 (o : Orders) : smallOrders o 5 = smallOrder5 (o 6) := rfl
lemma small_raw_at5 (o : Orders) :
    SixCaseCompatibility0.rawRows (smallOrders o) 5 = SixRows0.key5 (smallOrder5 (o 6)) := by
  unfold SixCaseCompatibility0.rawRows
  exact (six_rows_at5 (SixRows0.key0 (smallOrders o 0)) (SixRows0.key1 (smallOrders o 1)) (SixRows0.key2 (smallOrders o 2)) (SixRows0.key3 (smallOrders o 3)) (SixRows0.key4 (smallOrders o 4)) (SixRows0.key5 (smallOrders o 5))).trans (congrArg SixRows0.key5 (smallOrders_at5 o))
lemma rows_eq (o : Orders) :
    PureSevenProjectionNumbers.project4 (SevenCanonicalRaw.rawRows o) =
      SixCaseCompatibility0.rawRows (smallOrders o) := by
  funext i
  fin_cases i
  · exact (projected_raw_at0 o).trans ((row0 (o 0)).trans ((small_raw_at0 o).symm))
  · exact (projected_raw_at1 o).trans ((row1 (o 1)).trans ((small_raw_at1 o).symm))
  · exact (projected_raw_at2 o).trans ((row2 (o 2)).trans ((small_raw_at2 o).symm))
  · exact (projected_raw_at3 o).trans ((row3 (o 3)).trans ((small_raw_at3 o).symm))
  · exact (projected_raw_at4 o).trans ((row4 (o 5)).trans ((small_raw_at4 o).symm))
  · exact (projected_raw_at5 o).trans ((row5 (o 6)).trans ((small_raw_at5 o).symm))
lemma key_eq (o : Orders) :
    PureSevenProjectionNumbers.key4 (SevenCanonicalRaw.rawRows o) =
      SixRows0.key (smallOrders o) :=
  (congrArg PureSixRowModel0.key (rows_eq o)).trans (SixCaseCompatibility0.key_rawRows _)
lemma compatible (o : Orders) (h : LocalBounds b hb o) :
    PureSixGoodLookup.Good (PureSevenProjectionNumbers.key4 (SevenCanonicalRaw.rawRows o)) := by
  rw [key_eq]
  exact SixOrbitKernel0.catalogue (smallOrders o) (localBounds o h)
#print axioms compatible
#print axioms rows_eq
end Erdos184Work.SevenProjectionCode4
