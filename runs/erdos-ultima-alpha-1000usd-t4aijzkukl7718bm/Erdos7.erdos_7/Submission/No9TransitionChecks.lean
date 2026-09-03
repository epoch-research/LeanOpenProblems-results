import Submission.No9NumericalData
import Submission.No9ControlChecks

/-! Boolean checks for complete rounded transitions and their side conditions. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 100000000

def topCheck (h : ℕ → ℕ) : Bool :=
  (List.range nodes).all (fun j => decide (h j ≤ h 0))

lemma topCheck_iff (h : ℕ → ℕ) : topCheck h=true ↔ ∀ j,j < nodes → h j ≤ h 0 := by
  simp only [topCheck,List.all_eq_true,List.mem_range,decide_eq_true_eq]

def prefixStaticCheck (a : PrefixControl) : Bool :=
  decide (3 ≤ a.p) && decide (1 ≤ a.R) && decide (a.R ≤ 18) && decide (a.A ≤ a.B*a.p) &&
  decide (a.cut < nodes) && lossGeometryCheck a.A a.B (denominator a.p) a.lossIndex

def prefixTransitionCheck (i : ℕ) : Bool :=
  let a := prefixControl i
  let s := prefixState i
  prefixStaticCheck a && decide (loss a s.values < s.mass) && topCheck s.values &&
    checkState (step a s) (prefixState (i+1))

def blockStaticCheck (b : BlockControl) : Bool :=
  blockIntegerCheck b && decide (b.lo < b.hi) && decide (b.cut < nodes) &&
    lossGeometryCheck 5 4 (b.lo-1) b.lossIndex

def blockTransitionCheck (i : ℕ) : Bool :=
  let b := blockControl i
  let s := blockState i
  let y1 := blockY1 i
  let y2 := blockY2 i
  let y3 := blockY3 i
  blockStaticCheck b && decide (b.count*blockLoss b s.values y1 y2 y3 < s.mass) &&
    topCheck s.values &&
    checkValues (offdiag b.lo b.R 5 4 s.values) y1 0 nodes &&
    checkValues (offdiag b.lo b.R 5 4 y1) y2 0 nodes &&
    checkValues (offdiag b.lo b.R 5 4 y2) y3 0 nodes &&
    checkState (blockStep b s y1 y2 y3) (blockState (i+1))

end Erdos7No9Certificate
