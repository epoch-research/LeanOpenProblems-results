import Submission.SupportPrefixData

/-! Kernel checks of integer rows only. The interpretation as moment and
lower-law bounds is separate; these checks are not a full covering theorem. -/
namespace Erdos7SupportPrefixChecks
open Erdos7SupportPrefixData
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

def getNat (v : Array ℕ) (i : ℕ) : ℕ := v[i]?.getD 0

def lowerRow (i j : ℕ) : Prop :=
  let p := getNat primes i
  let c := getNat caps i
  let D := lower[i]?.getD #[]
  let D' := lower[i+1]?.getD #[]
  getNat D' j*(capDen*p^(depth+1)) ≤
    getNat D j*(capDen*p-c)*p^depth+
      ∑ a ∈ Finset.range depth,
        getNat D (getNat (predecessor[j]?.getD #[]) a)*c*(p-1)*p^(depth-1-a)

def momentRow (i j : ℕ) : Prop :=
  let p := getNat primes i
  let c := getNat caps i
  let M := moments[i]?.getD #[]
  let M' := moments[i+1]?.getD #[]
  let den := capDen*(p-1)^3
  let r := #[c*(p-1)^2,c*(p+1)*(p-1),c*(p^2+4*p+1)]
  den*getNat M j+(∑ k ∈ Finset.range 3,getNat r k*
    ∑ a ∈ Finset.range 10, getNat ((matrix[k]?.getD #[])[j]?.getD #[]) a*getNat M a) ≤ den*getNat M' j

def lossRow (i : ℕ) : Prop :=
  let p := getNat primes i
  let c := getNat caps i
  let M := moments[i]?.getD #[]
  let D := lower[i]?.getD #[]
  c*(getNat M 0+getNat M 1+getNat M 4)*lawScale*costScale ≤
    getNat costs i*(capDen*(p-1)*momentScale*lawScale)+momentScale*costScale*
      ∑ j ∈ Finset.range stateCount,getNat D j*
        min ((c-capDen)*(p-1)) (c*(1+(states[j]?.getD (0,0)).1+(states[j]?.getD (0,0)).2))

instance (i j : ℕ) : Decidable (lowerRow i j) := by unfold lowerRow; infer_instance
instance (i j : ℕ) : Decidable (momentRow i j) := by unfold momentRow; infer_instance
instance (i : ℕ) : Decidable (lossRow i) := by unfold lossRow; infer_instance

end Erdos7SupportPrefixChecks
