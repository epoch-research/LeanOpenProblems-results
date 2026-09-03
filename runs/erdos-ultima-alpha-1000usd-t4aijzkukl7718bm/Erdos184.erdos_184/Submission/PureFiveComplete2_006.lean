import Submission.PureFiveFilter2
import Submission.FiniteIntervals

/-! Small-subinterval kernel checks, grouped into the original certificate intervals. -/
namespace Erdos184Work.PureFiveFilter2
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_sub60_0 : ∀ i : Fin 200, Compatible (60000 + i.val) →
    (table.lookup (60000 + i.val)).isSome = true := by decide +kernel
lemma interval_sub60_0 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 60000 60200 :=
  FiniteIntervals.of_fin 60000 200 complete_sub60_0

lemma complete_sub60_1 : ∀ i : Fin 200, Compatible (60200 + i.val) →
    (table.lookup (60200 + i.val)).isSome = true := by decide +kernel
lemma interval_sub60_1 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 60200 60400 :=
  FiniteIntervals.of_fin 60200 200 complete_sub60_1

lemma complete_sub60_2 : ∀ i : Fin 200, Compatible (60400 + i.val) →
    (table.lookup (60400 + i.val)).isSome = true := by decide +kernel
lemma interval_sub60_2 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 60400 60600 :=
  FiniteIntervals.of_fin 60400 200 complete_sub60_2

lemma complete_sub60_3 : ∀ i : Fin 200, Compatible (60600 + i.val) →
    (table.lookup (60600 + i.val)).isSome = true := by decide +kernel
lemma interval_sub60_3 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 60600 60800 :=
  FiniteIntervals.of_fin 60600 200 complete_sub60_3

lemma complete_sub60_4 : ∀ i : Fin 200, Compatible (60800 + i.val) →
    (table.lookup (60800 + i.val)).isSome = true := by decide +kernel
lemma interval_sub60_4 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 60800 61000 :=
  FiniteIntervals.of_fin 60800 200 complete_sub60_4

lemma interval_chunk60 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 60000 61000 := (FiniteIntervals.merge (FiniteIntervals.merge interval_sub60_0 interval_sub60_1) (FiniteIntervals.merge interval_sub60_2 (FiniteIntervals.merge interval_sub60_3 interval_sub60_4)))

lemma complete_sub61_0 : ∀ i : Fin 200, Compatible (61000 + i.val) →
    (table.lookup (61000 + i.val)).isSome = true := by decide +kernel
lemma interval_sub61_0 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 61000 61200 :=
  FiniteIntervals.of_fin 61000 200 complete_sub61_0

lemma complete_sub61_1 : ∀ i : Fin 200, Compatible (61200 + i.val) →
    (table.lookup (61200 + i.val)).isSome = true := by decide +kernel
lemma interval_sub61_1 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 61200 61400 :=
  FiniteIntervals.of_fin 61200 200 complete_sub61_1

lemma complete_sub61_2 : ∀ i : Fin 200, Compatible (61400 + i.val) →
    (table.lookup (61400 + i.val)).isSome = true := by decide +kernel
lemma interval_sub61_2 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 61400 61600 :=
  FiniteIntervals.of_fin 61400 200 complete_sub61_2

lemma complete_sub61_3 : ∀ i : Fin 200, Compatible (61600 + i.val) →
    (table.lookup (61600 + i.val)).isSome = true := by decide +kernel
lemma interval_sub61_3 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 61600 61800 :=
  FiniteIntervals.of_fin 61600 200 complete_sub61_3

lemma complete_sub61_4 : ∀ i : Fin 200, Compatible (61800 + i.val) →
    (table.lookup (61800 + i.val)).isSome = true := by decide +kernel
lemma interval_sub61_4 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 61800 62000 :=
  FiniteIntervals.of_fin 61800 200 complete_sub61_4

lemma interval_chunk61 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 61000 62000 := (FiniteIntervals.merge (FiniteIntervals.merge interval_sub61_0 interval_sub61_1) (FiniteIntervals.merge interval_sub61_2 (FiniteIntervals.merge interval_sub61_3 interval_sub61_4)))

lemma complete_sub62_0 : ∀ i : Fin 200, Compatible (62000 + i.val) →
    (table.lookup (62000 + i.val)).isSome = true := by decide +kernel
lemma interval_sub62_0 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 62000 62200 :=
  FiniteIntervals.of_fin 62000 200 complete_sub62_0

lemma complete_sub62_1 : ∀ i : Fin 200, Compatible (62200 + i.val) →
    (table.lookup (62200 + i.val)).isSome = true := by decide +kernel
lemma interval_sub62_1 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 62200 62400 :=
  FiniteIntervals.of_fin 62200 200 complete_sub62_1

lemma complete_sub62_2 : ∀ i : Fin 200, Compatible (62400 + i.val) →
    (table.lookup (62400 + i.val)).isSome = true := by decide +kernel
lemma interval_sub62_2 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 62400 62600 :=
  FiniteIntervals.of_fin 62400 200 complete_sub62_2

lemma complete_sub62_3 : ∀ i : Fin 200, Compatible (62600 + i.val) →
    (table.lookup (62600 + i.val)).isSome = true := by decide +kernel
lemma interval_sub62_3 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 62600 62800 :=
  FiniteIntervals.of_fin 62600 200 complete_sub62_3

lemma complete_sub62_4 : ∀ i : Fin 200, Compatible (62800 + i.val) →
    (table.lookup (62800 + i.val)).isSome = true := by decide +kernel
lemma interval_sub62_4 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 62800 63000 :=
  FiniteIntervals.of_fin 62800 200 complete_sub62_4

lemma interval_chunk62 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 62000 63000 := (FiniteIntervals.merge (FiniteIntervals.merge interval_sub62_0 interval_sub62_1) (FiniteIntervals.merge interval_sub62_2 (FiniteIntervals.merge interval_sub62_3 interval_sub62_4)))

lemma complete_sub63_0 : ∀ i : Fin 200, Compatible (63000 + i.val) →
    (table.lookup (63000 + i.val)).isSome = true := by decide +kernel
lemma interval_sub63_0 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 63000 63200 :=
  FiniteIntervals.of_fin 63000 200 complete_sub63_0

lemma complete_sub63_1 : ∀ i : Fin 200, Compatible (63200 + i.val) →
    (table.lookup (63200 + i.val)).isSome = true := by decide +kernel
lemma interval_sub63_1 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 63200 63400 :=
  FiniteIntervals.of_fin 63200 200 complete_sub63_1

lemma complete_sub63_2 : ∀ i : Fin 200, Compatible (63400 + i.val) →
    (table.lookup (63400 + i.val)).isSome = true := by decide +kernel
lemma interval_sub63_2 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 63400 63600 :=
  FiniteIntervals.of_fin 63400 200 complete_sub63_2

lemma complete_sub63_3 : ∀ i : Fin 200, Compatible (63600 + i.val) →
    (table.lookup (63600 + i.val)).isSome = true := by decide +kernel
lemma interval_sub63_3 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 63600 63800 :=
  FiniteIntervals.of_fin 63600 200 complete_sub63_3

lemma complete_sub63_4 : ∀ i : Fin 200, Compatible (63800 + i.val) →
    (table.lookup (63800 + i.val)).isSome = true := by decide +kernel
lemma interval_sub63_4 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 63800 64000 :=
  FiniteIntervals.of_fin 63800 200 complete_sub63_4

lemma interval_chunk63 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 63000 64000 := (FiniteIntervals.merge (FiniteIntervals.merge interval_sub63_0 interval_sub63_1) (FiniteIntervals.merge interval_sub63_2 (FiniteIntervals.merge interval_sub63_3 interval_sub63_4)))

lemma complete_sub64_0 : ∀ i : Fin 200, Compatible (64000 + i.val) →
    (table.lookup (64000 + i.val)).isSome = true := by decide +kernel
lemma interval_sub64_0 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 64000 64200 :=
  FiniteIntervals.of_fin 64000 200 complete_sub64_0

lemma complete_sub64_1 : ∀ i : Fin 200, Compatible (64200 + i.val) →
    (table.lookup (64200 + i.val)).isSome = true := by decide +kernel
lemma interval_sub64_1 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 64200 64400 :=
  FiniteIntervals.of_fin 64200 200 complete_sub64_1

lemma complete_sub64_2 : ∀ i : Fin 200, Compatible (64400 + i.val) →
    (table.lookup (64400 + i.val)).isSome = true := by decide +kernel
lemma interval_sub64_2 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 64400 64600 :=
  FiniteIntervals.of_fin 64400 200 complete_sub64_2

lemma complete_sub64_3 : ∀ i : Fin 200, Compatible (64600 + i.val) →
    (table.lookup (64600 + i.val)).isSome = true := by decide +kernel
lemma interval_sub64_3 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 64600 64800 :=
  FiniteIntervals.of_fin 64600 200 complete_sub64_3

lemma complete_sub64_4 : ∀ i : Fin 200, Compatible (64800 + i.val) →
    (table.lookup (64800 + i.val)).isSome = true := by decide +kernel
lemma interval_sub64_4 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 64800 65000 :=
  FiniteIntervals.of_fin 64800 200 complete_sub64_4

lemma interval_chunk64 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 64000 65000 := (FiniteIntervals.merge (FiniteIntervals.merge interval_sub64_0 interval_sub64_1) (FiniteIntervals.merge interval_sub64_2 (FiniteIntervals.merge interval_sub64_3 interval_sub64_4)))

lemma complete_sub65_0 : ∀ i : Fin 200, Compatible (65000 + i.val) →
    (table.lookup (65000 + i.val)).isSome = true := by decide +kernel
lemma interval_sub65_0 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 65000 65200 :=
  FiniteIntervals.of_fin 65000 200 complete_sub65_0

lemma complete_sub65_1 : ∀ i : Fin 200, Compatible (65200 + i.val) →
    (table.lookup (65200 + i.val)).isSome = true := by decide +kernel
lemma interval_sub65_1 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 65200 65400 :=
  FiniteIntervals.of_fin 65200 200 complete_sub65_1

lemma complete_sub65_2 : ∀ i : Fin 200, Compatible (65400 + i.val) →
    (table.lookup (65400 + i.val)).isSome = true := by decide +kernel
lemma interval_sub65_2 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 65400 65600 :=
  FiniteIntervals.of_fin 65400 200 complete_sub65_2

lemma complete_sub65_3 : ∀ i : Fin 200, Compatible (65600 + i.val) →
    (table.lookup (65600 + i.val)).isSome = true := by decide +kernel
lemma interval_sub65_3 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 65600 65800 :=
  FiniteIntervals.of_fin 65600 200 complete_sub65_3

lemma complete_sub65_4 : ∀ i : Fin 200, Compatible (65800 + i.val) →
    (table.lookup (65800 + i.val)).isSome = true := by decide +kernel
lemma interval_sub65_4 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 65800 66000 :=
  FiniteIntervals.of_fin 65800 200 complete_sub65_4

lemma interval_chunk65 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 65000 66000 := (FiniteIntervals.merge (FiniteIntervals.merge interval_sub65_0 interval_sub65_1) (FiniteIntervals.merge interval_sub65_2 (FiniteIntervals.merge interval_sub65_3 interval_sub65_4)))

lemma complete_sub66_0 : ∀ i : Fin 200, Compatible (66000 + i.val) →
    (table.lookup (66000 + i.val)).isSome = true := by decide +kernel
lemma interval_sub66_0 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 66000 66200 :=
  FiniteIntervals.of_fin 66000 200 complete_sub66_0

lemma complete_sub66_1 : ∀ i : Fin 200, Compatible (66200 + i.val) →
    (table.lookup (66200 + i.val)).isSome = true := by decide +kernel
lemma interval_sub66_1 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 66200 66400 :=
  FiniteIntervals.of_fin 66200 200 complete_sub66_1

lemma complete_sub66_2 : ∀ i : Fin 200, Compatible (66400 + i.val) →
    (table.lookup (66400 + i.val)).isSome = true := by decide +kernel
lemma interval_sub66_2 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 66400 66600 :=
  FiniteIntervals.of_fin 66400 200 complete_sub66_2

lemma complete_sub66_3 : ∀ i : Fin 200, Compatible (66600 + i.val) →
    (table.lookup (66600 + i.val)).isSome = true := by decide +kernel
lemma interval_sub66_3 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 66600 66800 :=
  FiniteIntervals.of_fin 66600 200 complete_sub66_3

lemma complete_sub66_4 : ∀ i : Fin 200, Compatible (66800 + i.val) →
    (table.lookup (66800 + i.val)).isSome = true := by decide +kernel
lemma interval_sub66_4 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 66800 67000 :=
  FiniteIntervals.of_fin 66800 200 complete_sub66_4

lemma interval_chunk66 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 66000 67000 := (FiniteIntervals.merge (FiniteIntervals.merge interval_sub66_0 interval_sub66_1) (FiniteIntervals.merge interval_sub66_2 (FiniteIntervals.merge interval_sub66_3 interval_sub66_4)))

lemma complete_sub67_0 : ∀ i : Fin 200, Compatible (67000 + i.val) →
    (table.lookup (67000 + i.val)).isSome = true := by decide +kernel
lemma interval_sub67_0 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 67000 67200 :=
  FiniteIntervals.of_fin 67000 200 complete_sub67_0

lemma complete_sub67_1 : ∀ i : Fin 200, Compatible (67200 + i.val) →
    (table.lookup (67200 + i.val)).isSome = true := by decide +kernel
lemma interval_sub67_1 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 67200 67400 :=
  FiniteIntervals.of_fin 67200 200 complete_sub67_1

lemma complete_sub67_2 : ∀ i : Fin 200, Compatible (67400 + i.val) →
    (table.lookup (67400 + i.val)).isSome = true := by decide +kernel
lemma interval_sub67_2 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 67400 67600 :=
  FiniteIntervals.of_fin 67400 200 complete_sub67_2

lemma complete_sub67_3 : ∀ i : Fin 200, Compatible (67600 + i.val) →
    (table.lookup (67600 + i.val)).isSome = true := by decide +kernel
lemma interval_sub67_3 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 67600 67800 :=
  FiniteIntervals.of_fin 67600 200 complete_sub67_3

lemma complete_sub67_4 : ∀ i : Fin 200, Compatible (67800 + i.val) →
    (table.lookup (67800 + i.val)).isSome = true := by decide +kernel
lemma interval_sub67_4 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 67800 68000 :=
  FiniteIntervals.of_fin 67800 200 complete_sub67_4

lemma interval_chunk67 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 67000 68000 := (FiniteIntervals.merge (FiniteIntervals.merge interval_sub67_0 interval_sub67_1) (FiniteIntervals.merge interval_sub67_2 (FiniteIntervals.merge interval_sub67_3 interval_sub67_4)))

lemma complete_sub68_0 : ∀ i : Fin 200, Compatible (68000 + i.val) →
    (table.lookup (68000 + i.val)).isSome = true := by decide +kernel
lemma interval_sub68_0 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 68000 68200 :=
  FiniteIntervals.of_fin 68000 200 complete_sub68_0

lemma complete_sub68_1 : ∀ i : Fin 200, Compatible (68200 + i.val) →
    (table.lookup (68200 + i.val)).isSome = true := by decide +kernel
lemma interval_sub68_1 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 68200 68400 :=
  FiniteIntervals.of_fin 68200 200 complete_sub68_1

lemma complete_sub68_2 : ∀ i : Fin 200, Compatible (68400 + i.val) →
    (table.lookup (68400 + i.val)).isSome = true := by decide +kernel
lemma interval_sub68_2 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 68400 68600 :=
  FiniteIntervals.of_fin 68400 200 complete_sub68_2

lemma complete_sub68_3 : ∀ i : Fin 200, Compatible (68600 + i.val) →
    (table.lookup (68600 + i.val)).isSome = true := by decide +kernel
lemma interval_sub68_3 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 68600 68800 :=
  FiniteIntervals.of_fin 68600 200 complete_sub68_3

lemma complete_sub68_4 : ∀ i : Fin 200, Compatible (68800 + i.val) →
    (table.lookup (68800 + i.val)).isSome = true := by decide +kernel
lemma interval_sub68_4 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 68800 69000 :=
  FiniteIntervals.of_fin 68800 200 complete_sub68_4

lemma interval_chunk68 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 68000 69000 := (FiniteIntervals.merge (FiniteIntervals.merge interval_sub68_0 interval_sub68_1) (FiniteIntervals.merge interval_sub68_2 (FiniteIntervals.merge interval_sub68_3 interval_sub68_4)))

lemma complete_sub69_0 : ∀ i : Fin 200, Compatible (69000 + i.val) →
    (table.lookup (69000 + i.val)).isSome = true := by decide +kernel
lemma interval_sub69_0 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 69000 69200 :=
  FiniteIntervals.of_fin 69000 200 complete_sub69_0

lemma complete_sub69_1 : ∀ i : Fin 200, Compatible (69200 + i.val) →
    (table.lookup (69200 + i.val)).isSome = true := by decide +kernel
lemma interval_sub69_1 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 69200 69400 :=
  FiniteIntervals.of_fin 69200 200 complete_sub69_1

lemma complete_sub69_2 : ∀ i : Fin 200, Compatible (69400 + i.val) →
    (table.lookup (69400 + i.val)).isSome = true := by decide +kernel
lemma interval_sub69_2 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 69400 69600 :=
  FiniteIntervals.of_fin 69400 200 complete_sub69_2

lemma complete_sub69_3 : ∀ i : Fin 200, Compatible (69600 + i.val) →
    (table.lookup (69600 + i.val)).isSome = true := by decide +kernel
lemma interval_sub69_3 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 69600 69800 :=
  FiniteIntervals.of_fin 69600 200 complete_sub69_3

lemma complete_sub69_4 : ∀ i : Fin 200, Compatible (69800 + i.val) →
    (table.lookup (69800 + i.val)).isSome = true := by decide +kernel
lemma interval_sub69_4 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 69800 70000 :=
  FiniteIntervals.of_fin 69800 200 complete_sub69_4

lemma interval_chunk69 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 69000 70000 := (FiniteIntervals.merge (FiniteIntervals.merge interval_sub69_0 interval_sub69_1) (FiniteIntervals.merge interval_sub69_2 (FiniteIntervals.merge interval_sub69_3 interval_sub69_4)))

#print axioms interval_chunk60
end Erdos184Work.PureFiveFilter2
