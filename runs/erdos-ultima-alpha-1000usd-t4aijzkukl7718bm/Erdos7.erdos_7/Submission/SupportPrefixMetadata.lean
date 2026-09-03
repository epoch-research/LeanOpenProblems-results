import Submission.SupportPrefixCheckDefs
import Submission.SupportMomentMatrix

/-! Finite metadata connecting the numerical prefix labels to support states.
The loss and moment row inequalities are checked in separate modules. -/
namespace Erdos7SupportPrefixMetadata
open scoped BigOperators
open Erdos7SupportPrefixData Erdos7SupportPrefixChecks
open Erdos7SupportCompression Erdos7SupportMomentMatrix
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

def repr (j : Fin 180) : TripleState := states[j.val]?.getD (0,0)
def p (i : ℕ) : ℕ := getNat primes i
def cn (i : ℕ) : ℕ := getNat caps i
def cap (i : ℕ) : ℚ := (cn i:ℚ)/capDen
def lowNat (i j : ℕ) : ℕ := getNat (lower[i]?.getD #[]) j
def momNat (i j : ℕ) : ℕ := getNat (moments[i]?.getD #[]) j
def low (i : ℕ) (j : Fin 180) : ℚ := (lowNat i j:ℚ)/lawScale
def mom (i : ℕ) (j : Fin 10) : ℚ := (momNat i j:ℚ)/momentScale
def cost (i : ℕ) : ℚ := (getNat costs i:ℚ)/costScale

def predIndex (j : Fin 180) (a : Fin 12) : ℕ := getNat (predecessor[j.val]?.getD #[]) a

def pred (j : Fin 180) (a : Fin 12) : Option (Fin 180) :=
  if h : predIndex j a < 180 then some ⟨predIndex j a,h⟩ else none

def stateCode (j : Fin 180) : ℕ := 67*(repr j).1+(repr j).2

theorem code_adjacent : ∀ j : Fin 179,stateCode j.castSucc < stateCode j.succ := by decide +kernel

theorem repr_injective : Function.Injective repr := by
  have h : StrictMono stateCode := Fin.strictMono_iff_lt_succ.mpr code_adjacent
  intro i j he
  apply h.injective
  unfold stateCode
  rw [he]

theorem pred_info : ∀ j a, predIndex j a ≤ 180 ∧
    (predIndex j a < 180 → tripleUpdate (a.val+1)
      (states[predIndex j a]?.getD (0,0))=repr j) := by decide +kernel

theorem sentinel_zero : ∀ i : Fin 168, lowNat i 180=0 := by decide +kernel

theorem cap_bounds : ∀ i : Fin 167, capDen ≤ cn i ∧ cn i ≤ capDen*p i ∧ 3 ≤ p i := by decide +kernel

theorem matrix_info : ∀ k : Fin 3, ∀ i j : Fin 10,
    (getNat ((matrix[k.val]?.getD #[])[i.val]?.getD #[]) j:ℚ)=coeff k i j := by decide +kernel

theorem initial_low : ∀ j : Fin 180,
    low 0 j ≤ (Finsupp.single (0,0) (1:ℚ) : TripleState →₀ ℚ) (repr j) := by
  have h : ∀ j : Fin 180,low 0 j ≤ if repr j=(0,0) then 1 else 0 := by decide +kernel
  intro j
  simpa only [Finsupp.single_apply,eq_comm] using h j

theorem initial_mom : ∀ j : Fin 10, mono j (0,0) ≤ mom 0 j := by decide +kernel

theorem initial_repr : repr 0=(0,0) := by decide +kernel

lemma pred_equation (j : Fin 180) (a : Fin 12) (k : Fin 180) (h : pred j a=some k) :
    tripleUpdate (a.val+1) (repr k)=repr j := by
  unfold pred at h
  split_ifs at h with hi
  · have hk := Option.some.inj h
    subst k
    exact (pred_info j a).2 hi

lemma pred_value (i : Fin 168) (j : Fin 180) (a : Fin 12) :
    (pred j a).elim 0 (low i)=(lowNat i (predIndex j a):ℚ)/lawScale := by
  unfold pred
  split_ifs with h
  · rfl
  · have he : predIndex j a=180 := by have := (pred_info j a).1; omega
    rw [he,sentinel_zero i]
    simp

lemma low_nonneg (i : ℕ) (j : Fin 180) : 0 ≤ low i j := by unfold low; positivity
lemma mom_nonneg (i : ℕ) (j : Fin 10) : 0 ≤ mom i j := by unfold mom; positivity

#print axioms repr_injective
#print axioms pred_info
#print axioms initial_low
#print axioms initial_mom
end Erdos7SupportPrefixMetadata
