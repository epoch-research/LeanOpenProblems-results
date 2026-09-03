import FormalConjecturesUtil

open scoped BigOperators

namespace E126

noncomputable section

variable {ι : Type*} [DecidableEq ι]

/-- A finite weighted laminar family. Repeated supports are combined in the weight. -/
structure LaminarFamily (ι : Type*) [DecidableEq ι] where
  nodes : Finset (Finset ι)
  weight : Finset ι → ℝ
  weight_nonneg : ∀ B ∈ nodes, 0 ≤ weight B
  laminar : ∀ B ∈ nodes, ∀ C ∈ nodes, B ⊆ C ∨ C ⊆ B ∨ Disjoint B C

/-- The real indicator of a finite subset. -/
def ind (B : Finset ι) (i : ι) : ℝ := if i ∈ B then 1 else 0

@[simp] theorem ind_of_mem {B : Finset ι} {i : ι} (h : i ∈ B) : ind B i = 1 := by
  simp [ind, h]

@[simp] theorem ind_of_not_mem {B : Finset ι} {i : ι} (h : i ∉ B) : ind B i = 0 := by
  simp [ind, h]

@[simp] theorem ind_sq (B : Finset ι) (i : ι) : ind B i ^ 2 = ind B i := by
  unfold ind
  split <;> norm_num

theorem ind_nonneg (B : Finset ι) (i : ι) : 0 ≤ ind B i := by
  unfold ind
  split <;> norm_num

namespace LaminarFamily

def kernel (W : LaminarFamily ι) (i j : ι) : ℝ :=
  ∑ B ∈ W.nodes, W.weight B * ind B i * ind B j

theorem kernel_symm (W : LaminarFamily ι) (i j : ι) : W.kernel i j = W.kernel j i := by
  unfold kernel
  apply Finset.sum_congr rfl
  intro B hB
  ring

theorem kernel_nonneg (W : LaminarFamily ι) (i j : ι) : 0 ≤ W.kernel i j := by
  apply Finset.sum_nonneg
  intro B hB
  exact mul_nonneg (mul_nonneg (W.weight_nonneg B hB) (ind_nonneg B i)) (ind_nonneg B j)

end LaminarFamily

/-- One prime's cancellation tree, with a consistent sign on each root. -/
structure OppositionFamily (ι : Type*) [DecidableEq ι] extends LaminarFamily ι where
  sign : ι → Bool
  bichromatic : ∀ B ∈ nodes, ∀ i ∈ B, ∃ j ∈ B, sign j ≠ sign i

namespace OppositionFamily

def unsigned (W : OppositionFamily ι) : ι → ι → ℝ := W.toLaminarFamily.kernel

def signVal (W : OppositionFamily ι) (i : ι) : ℝ := if W.sign i then 1 else -1

def signed (W : OppositionFamily ι) (i j : ι) : ℝ :=
  W.signVal i * W.signVal j * W.unsigned i j

def opposition (W : OppositionFamily ι) (i j : ι) : ℝ :=
  if W.sign i = W.sign j then 0 else W.unsigned i j

def agreement (W : OppositionFamily ι) (i j : ι) : ℝ :=
  if W.sign i = W.sign j then W.unsigned i j else 0

@[simp] theorem signVal_sq (W : OppositionFamily ι) (i : ι) : W.signVal i ^ 2 = 1 := by
  unfold signVal
  split <;> norm_num

theorem signVal_abs (W : OppositionFamily ι) (i : ι) : |W.signVal i| = 1 := by
  unfold signVal
  split <;> norm_num

theorem unsigned_nonneg (W : OppositionFamily ι) (i j : ι) : 0 ≤ W.unsigned i j :=
  W.toLaminarFamily.kernel_nonneg i j

theorem unsigned_symm (W : OppositionFamily ι) (i j : ι) : W.unsigned i j = W.unsigned j i :=
  W.toLaminarFamily.kernel_symm i j

theorem opposition_nonneg (W : OppositionFamily ι) (i j : ι) : 0 ≤ W.opposition i j := by
  unfold opposition
  split
  · exact le_rfl
  · exact W.unsigned_nonneg i j

@[simp] theorem opposition_diag (W : OppositionFamily ι) (i : ι) : W.opposition i i = 0 := by
  simp [opposition]

theorem opposition_symm (W : OppositionFamily ι) (i j : ι) :
    W.opposition i j = W.opposition j i := by
  simp only [opposition, eq_comm (a := W.sign i), W.unsigned_symm i j]

theorem signed_eq (W : OppositionFamily ι) (i j : ι) :
    W.signed i j = W.agreement i j - W.opposition i j := by
  cases hi : W.sign i <;> cases hj : W.sign j <;>
    simp [signed, signVal, agreement, opposition, hi, hj]

theorem unsigned_eq (W : OppositionFamily ι) (i j : ι) :
    W.unsigned i j = W.agreement i j + W.opposition i j := by
  unfold agreement opposition
  split <;> simp

theorem opposition_eq (W : OppositionFamily ι) (i j : ι) :
    W.opposition i j = (W.unsigned i j - W.signed i j) / 2 := by
  rw [W.signed_eq i j, W.unsigned_eq i j]
  ring

end OppositionFamily

variable [Fintype ι]

/-- Quadratic form, written as finite sums to avoid a matrix basis choice. -/
def quad (K : ι → ι → ℝ) (q : ι → ℝ) : ℝ := ∑ i, ∑ j, q i * q j * K i j

def CND (K : ι → ι → ℝ) : Prop := ∀ q : ι → ℝ, (∑ i, q i) = 0 → quad K q ≤ 0

variable {κ : Type*} [Fintype κ]

def totalOpposition (W : κ → OppositionFamily ι) (i j : ι) : ℝ :=
  ∑ p, (W p).opposition i j

def totalSigned (W : κ → OppositionFamily ι) (i j : ι) : ℝ :=
  ∑ p, (W p).signed i j

def totalUnsigned (W : κ → OppositionFamily ι) (i j : ι) : ℝ :=
  ∑ p, (W p).unsigned i j

end
end E126
