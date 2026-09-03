import FormalConjecturesUtil
import Submission.C8MixedSuzukiMatrices

/-! A rational octagon word in opposite twisted central matrix families.
This is auxiliary to, and does not settle, Erdos 713. -/
namespace Erdos713C8CentralSuzukiMatrices
open Erdos713C8MixedSuzukiMatrices
variable {F : Type*} [Field F] [CharP F 2]
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

def Z (σ : F →+* F) (a : F) : Mat F := X a (σ a)
def O (σ : F →+* F) (a : F) : Mat F :=
  !![1,0,a,σ a; 0,1,0,a; 0,0,1,0; 0,0,0,1]

def J (σ : F →+* F) (c : F) : F := c^2+c+σ c
def A (σ : F →+* F) (c : F) : F := c^2+c*σ c+σ c

def d (σ : F →+* F) (c : F) : F :=
  (c+σ c)*(c^2+σ c)/(J σ c*σ (J σ c))
def e (σ : F →+* F) (c : F) : F :=
  (c+σ c)*(c^2+σ c)/(c*σ c)
def f (σ : F →+* F) (c : F) : F :=
  c^3*σ c/(A σ c*σ (A σ c))
def g (σ : F →+* F) (c : F) : F :=
  (A σ c)^2*σ (A σ c)/(c*σ c*J σ c*σ (J σ c))
def h (σ : F →+* F) (c : F) : F :=
  (J σ c)^2*σ (J σ c)/(A σ c*σ (A σ c))

lemma Z_sq (σ : F →+* F) (a : F) : Z σ a*Z σ a=1 := X_sq a (σ a)

lemma O_sq (σ : F →+* F) (a : F) : O σ a*O σ a=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [O,Matrix.mul_apply,Fin.sum_univ_succ,CharTwo.add_self_eq_zero]

end Erdos713C8CentralSuzukiMatrices
