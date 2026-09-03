import Submission.No9CertificateCore
import Submission.ArithmeticReduction

/-! Exact rational interpretation and geometry of the rounded no9 grid. -/
namespace Erdos7No9Certificate
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000

lemma scale_pos : (0:ℚ) < scale := by norm_num [scale]
lemma coefficientScale_pos : (0:ℚ) < coefficientScale := by norm_num [coefficientScale]
lemma nodes_pos : 0 < nodes := by decide +kernel

def realGrid (j : Fin nodes) : ℚ := grid j.val

def realValues (h : ℕ → ℕ) (j : Fin nodes) : ℚ := (h j.val:ℚ)/scale

lemma realValues_nonneg (h : ℕ → ℕ) (j : Fin nodes) : 0 ≤ realValues h j := by
  exact div_nonneg (Nat.cast_nonneg _) scale_pos.le

lemma ceilDiv_bound (a b : ℕ) (hb : 0 < b) : (a:ℚ)/b ≤ (ceilDiv a b:ℚ) :=
  Erdos7No23Sieve.nat_div_le_rounded a b hb

lemma rounded_mul_bound (x : ℚ) (u a b : ℕ) (hb : 0 < b) (hx : x ≤ (u:ℚ)/scale) :
    (a:ℚ)/b*x ≤ (ceilDiv (a*u) b:ℚ)/scale := by
  have hm := mul_le_mul_of_nonneg_left hx (by positivity : (0:ℚ) ≤ (a:ℚ)/b)
  apply hm.trans
  have hh := div_le_div_of_nonneg_right (ceilDiv_bound (a*u) b hb) scale_pos.le
  simp only [Nat.cast_mul] at hh
  convert hh using 1 <;> ring

lemma checkValues_iff (h v : ℕ → ℕ) (start count : ℕ) :
    checkValues h v start count=true ↔ ∀ j,start ≤ j → j < start+count → h j=v j := by
  simp only [checkValues,List.all_eq_true,List.mem_range',beq_iff_eq]
  constructor
  · intro h j hj0 hj1
    exact h j ⟨j-start,by omega,by omega⟩
  · rintro h j ⟨i,hi,rfl⟩
    exact h _ (by omega) (by omega)

lemma checkState_iff (s v : State) : checkState s v=true ↔
    s.mass=v.mass ∧ s.cubic=v.cubic ∧ ∀ j,j < nodes → s.values j=v.values j := by
  simp only [checkState,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,List.mem_range,and_assoc]

def CellValid (d j : ℕ) (v : Cell) : Prop :=
  v.lo+1 < nodes ∧ 0 < v.width ∧ grid v.lo+v.width=grid (v.lo+1) ∧
    grid j+v.left=d*grid (v.lo+1) ∧ d*grid v.lo+v.right=grid j

def cellCheck (d j : ℕ) : Bool :=
  let v := cells d j
  decide (v.lo+1 < nodes) && decide (0 < v.width) &&
    (grid v.lo+v.width==grid (v.lo+1)) && (grid j+v.left==d*grid (v.lo+1)) &&
    (d*grid v.lo+v.right==grid j)

def rowCheck (d : ℕ) : Bool := (List.range nodes).all (cellCheck d)

lemma cellCheck_iff (d j : ℕ) : cellCheck d j=true ↔ CellValid d j (cells d j) := by
  simp only [cellCheck,CellValid,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,and_assoc]

lemma rowCheck_iff (d : ℕ) : rowCheck d=true ↔ ∀ j,j < nodes → CellValid d j (cells d j) := by
  simp only [rowCheck,List.all_eq_true,List.mem_range,cellCheck_iff]

def gridCheck : Bool := grid 0==0 && (List.range (nodes-1)).all (fun j => decide (grid j < grid (j+1)))

lemma gridCheck_iff : gridCheck=true ↔ grid 0=0 ∧ ∀ j,j+1 < nodes → grid j < grid (j+1) := by
  simp only [gridCheck,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,List.mem_range,decide_eq_true_eq]
  have hnodes := nodes_pos
  constructor
  · rintro ⟨h0,h⟩; exact ⟨h0,fun j hj => h j (by omega)⟩
  · rintro ⟨h0,h⟩; exact ⟨h0,fun j hj => h j (by omega)⟩

theorem grid_certificate : gridCheck=true := by decide +kernel

theorem cell_row_2 : rowCheck 2=true := by decide +kernel

theorem cell_row_3 : rowCheck 3=true := by decide +kernel

theorem cell_row_4 : rowCheck 4=true := by decide +kernel

theorem cell_row_5 : rowCheck 5=true := by decide +kernel

theorem cell_row_6 : rowCheck 6=true := by decide +kernel

theorem cell_row_7 : rowCheck 7=true := by decide +kernel

theorem cell_row_8 : rowCheck 8=true := by decide +kernel

theorem cell_row_9 : rowCheck 9=true := by decide +kernel

theorem cell_row_10 : rowCheck 10=true := by decide +kernel

theorem cell_row_11 : rowCheck 11=true := by decide +kernel

theorem cell_row_12 : rowCheck 12=true := by decide +kernel

theorem cell_row_13 : rowCheck 13=true := by decide +kernel

theorem cell_row_14 : rowCheck 14=true := by decide +kernel

theorem cell_row_15 : rowCheck 15=true := by decide +kernel

theorem cell_row_16 : rowCheck 16=true := by decide +kernel

theorem cell_row_17 : rowCheck 17=true := by decide +kernel

theorem cell_row_18 : rowCheck 18=true := by decide +kernel

lemma cells_valid (d j : ℕ) (hd0 : 2 ≤ d) (hd1 : d ≤ 18) (hj : j < nodes) : CellValid d j (cells d j) := by
  apply (rowCheck_iff d).mp _ j hj
  interval_cases d
  · exact cell_row_2
  · exact cell_row_3
  · exact cell_row_4
  · exact cell_row_5
  · exact cell_row_6
  · exact cell_row_7
  · exact cell_row_8
  · exact cell_row_9
  · exact cell_row_10
  · exact cell_row_11
  · exact cell_row_12
  · exact cell_row_13
  · exact cell_row_14
  · exact cell_row_15
  · exact cell_row_16
  · exact cell_row_17
  · exact cell_row_18

lemma grid_zero : grid 0=0 := (gridCheck_iff.mp grid_certificate).1

lemma grid_succ (j : ℕ) (hj : j+1 < nodes) : grid j < grid (j+1) :=
  (gridCheck_iff.mp grid_certificate).2 j hj

lemma grid_mono {i j : ℕ} (hij : i ≤ j) (hj : j < nodes) : grid i ≤ grid j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    exact (ih (by omega)).trans (grid_succ j hj).le

lemma grid_strictMono : StrictMono (fun j : Fin nodes => grid j.val) := by
  intro i j hij
  have hle : i.val+1 ≤ j.val := hij
  exact (grid_succ i.val (hle.trans_lt j.isLt)).trans_le (grid_mono hle j.isLt)

#print axioms cells_valid
#print axioms grid_strictMono
end Erdos7No9Certificate
