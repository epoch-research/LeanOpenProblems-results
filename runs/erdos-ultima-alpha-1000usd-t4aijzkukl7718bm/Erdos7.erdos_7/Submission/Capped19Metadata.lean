import Submission.Capped19Rows

/-! Exact rational metadata for the affine cells of the capped-19 row table. -/
namespace Erdos7Capped19Metadata
open Erdos7Capped19Rows
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def coeff (f : List ℚ) (j : ℕ) : ℚ := f[j]?.getD 0

def lastValue {α : Type*} (a : α) : List α → α
  | [] => a
  | b::l => lastValue b l

def Good (f : List ℚ) : Prop :=
  (∀ a ∈ f, 0 ≤ a) ∧
    slope f=coeff f 1+((List.range 8).map (fun j => coeff f (j+2))).sum

instance (f : List ℚ) : Decidable (Good f) := by unfold Good; infer_instance

def raw (s : Stage) (k : ℚ) : ℚ := s.cap*(1-k/(s.p-1))

def Cell (s : Stage) (ab : ℚ × ℚ) : Prop :=
  ab.1 ≤ ab.2 ∧ 0 ≤ raw s ab.1 ∧ 0 ≤ raw s ab.2 ∧
  ((raw s ab.1 ≤ 1 ∧ raw s ab.2 ≤ 1) ∨ (1 ≤ raw s ab.1 ∧ 1 ≤ raw s ab.2)) ∧
  (∀ j ∈ List.range 8, coeff s.U (j+2)=0 ∨
    ((j:ℚ)+2 ≤ ab.1 ∧ (j:ℚ)+2 ≤ ab.2) ∨ (ab.1 ≤ (j:ℚ)+2 ∧ ab.2 ≤ (j:ℚ)+2)) ∧
  ∀ j ∈ List.range 9,
    ((retention s.p s.cap ab.1 ≤ s.cap/s.p^(j+1)) ∧
      (retention s.p s.cap ab.2 ≤ s.cap/s.p^(j+1))) ∨
    ((s.cap/s.p^(j+1) ≤ retention s.p s.cap ab.1) ∧
      (s.cap/s.p^(j+1) ≤ retention s.p s.cap ab.2))

instance (s : Stage) (ab : ℚ × ℚ) : Decidable (Cell s ab) := by unfold Cell; infer_instance

def Metadata (s : Stage) (future : List ℚ) : Prop :=
  1<s.p ∧ 0 ≤ s.cap ∧ Good s.U ∧ Good s.V ∧ Good s.F ∧ Good future ∧
  s.rows=1::s.rows.tail ∧ lastValue (1:ℚ) s.rows.tail=s.cut ∧
  (∀ j ∈ List.range 10, coeff s.F j=coeff s.U j+coeff s.V j) ∧
  ∀ ab ∈ s.rows.zip s.rows.tail, Cell s ab

instance (s : Stage) (future : List ℚ) : Decidable (Metadata s future) := by
  unfold Metadata; infer_instance

theorem stage5_metadata : Metadata stage5 stage7.F := by decide +kernel
theorem stage7_metadata : Metadata stage7 stage11.F := by decide +kernel
theorem stage11_metadata : Metadata stage11 stage13.F := by decide +kernel
theorem stage13_metadata : Metadata stage13 stage17.F := by decide +kernel
theorem stage17_metadata : Metadata stage17 stage19.F := by decide +kernel
theorem stage19_metadata : Metadata stage19 terminal := by decide +kernel
#print axioms stage5_metadata
#print axioms stage19_metadata
end Erdos7Capped19Metadata
