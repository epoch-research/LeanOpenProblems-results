import Submission.BinaryCriticalConeCertificates

/-! The exact joint binary orbit used by invariant-cone certificates. -/
namespace Erdos406BinaryCriticalCone
open Erdos406BinaryCriticalMatrix
open scoped Matrix BigOperators

variable {σ : Type*} [Fintype σ]

def parentBlock : Fin 2 → Fin 4 → Fin 4 :=
  ![![0,1,1,2], ![0,2,3,3]]

def outputDigit : Fin 2 → Fin 4 → Fin 2 :=
  ![![0,0,1,0], ![1,1,0,1]]

def jointValue (v : ℕ → σ → ℝ) (n : ℕ) : Fin 4 × σ → ℝ :=
  fun ⟨b,i⟩ => ![v n, v (3*n), v (3*n+1), v (3*n+2)] b i

def jointMatrix (A : Fin 2 → Matrix σ σ ℝ) (d : Fin 2) :
    Matrix (Fin 4 × σ) (Fin 4 × σ) ℝ :=
  fun ⟨b,i⟩ ⟨c,j⟩ => if c=parentBlock d b then A (outputDigit d b) i j else 0

lemma jointMatrix_mulVec (A : Fin 2 → Matrix σ σ ℝ) (d : Fin 2)
    (w : Fin 4 × σ → ℝ) (b : Fin 4) (i : σ) :
    (jointMatrix A d *ᵥ w) (b,i) =
      (A (outputDigit d b) *ᵥ (fun j => w (parentBlock d b,j))) i := by
  simp [Matrix.mulVec, dotProduct, jointMatrix, Fintype.sum_prod_type,
    Finset.sum_ite_irrel]

lemma joint_recurrence (v : ℕ → σ → ℝ) (A : Fin 2 → Matrix σ σ ℝ)
    (hstep : ∀ n : ℕ, 0<n → ∀ d : Fin 2, v (2*n+d.val)=A d *ᵥ v n)
    (n : ℕ) (hn : 0<n) (d : Fin 2) :
    jointValue v (2*n+d.val)=jointMatrix A d *ᵥ jointValue v n := by
  ext ⟨b,i⟩
  rw [jointMatrix_mulVec]
  fin_cases d <;> fin_cases b <;>
    simp [jointValue, parentBlock, outputDigit]

  · simpa using congrFun (hstep n hn 0) i
  · have he : 3*(2*n)=2*(3*n)+(0:Fin 2).val := by omega
    rw [he]
    exact congrFun (hstep (3*n) (by omega) 0) i
  · have he : 3*(2*n)+1=2*(3*n)+(1:Fin 2).val := by omega
    rw [he]
    exact congrFun (hstep (3*n) (by omega) 1) i
  · have he : 3*(2*n)+2=2*(3*n+1)+(0:Fin 2).val := by omega
    rw [he]
    exact congrFun (hstep (3*n+1) (by omega) 0) i
  · simpa using congrFun (hstep n hn 1) i
  · have he : 3*(2*n+1)=2*(3*n+1)+(1:Fin 2).val := by omega
    rw [he]
    exact congrFun (hstep (3*n+1) (by omega) 1) i
  · have he : 3*(2*n+1)+1=2*(3*n+2)+(0:Fin 2).val := by omega
    rw [he]
    exact congrFun (hstep (3*n+2) (by omega) 0) i
  · have he : 3*(2*n+1)+2=2*(3*n+2)+(1:Fin 2).val := by omega
    rw [he]
    exact congrFun (hstep (3*n+2) (by omega) 1) i

lemma evalNat_binary_step (A : ℕ → Matrix σ σ ℝ) (v0 : σ → ℝ)
    (n : ℕ) (hn : 0<n) (d : Fin 2) :
    evalNat A v0 (2*n+d.val)=A d.val *ᵥ evalNat A v0 n := by
  rw [evalNat_pos A v0 _ (by omega)]
  have hm : (2*n+d.val)%2=d.val := by omega
  have hq : (2*n+d.val)/2=n := by omega
  rw [hm,hq]

/-- The construction target is a signed row on the joint orbit. -/
def constructionRow (u : σ → ℝ) (d : Fin 2) : Fin 4 × σ → ℝ :=
  fun ⟨b,i⟩ => if b=0 then 3*u i else if b.val=d.val+1 then -u i else 0

lemma constructionRow_value (v : ℕ → σ → ℝ) (u : σ → ℝ)
    (n : ℕ) (d : Fin 2) :
    constructionRow u d ⬝ᵥ jointValue v n =
      3*(u ⬝ᵥ v n)-u ⬝ᵥ v (3*n+d.val) := by
  fin_cases d <;>
    simp [dotProduct, Fintype.sum_prod_type, Fin.sum_univ_succ,
      constructionRow, jointValue, Finset.mul_sum, Finset.sum_neg_distrib,
      sub_eq_add_neg, mul_assoc]

/-- A dedicated initial coordinate disappears after reading any positive input. -/
lemma evalNat_initial_coordinate_zero {N : ℕ}
    (A : ℕ → Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (v0 : Fin (N+1) → ℝ)
    (h0 : ∀ j, j≠0 → A 0 0 j=0) (h1 : ∀ j, A 1 0 j=0)
    (n : ℕ) (hn : 0<n) : evalNat A v0 n 0=0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [evalNat_pos A v0 n hn]
    by_cases hm : n%2=0
    · have hq : 0<n/2 := by omega
      have hi := ih (n/2) (Nat.div_lt_self hn (by decide)) hq
      simp [hm, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hi,
        h0 _ (Fin.succ_ne_zero _)]
    · have hm' : n%2=1 := by omega
      simp [hm', Matrix.mulVec, dotProduct, h1]

/-- The reduced orbit used by the exact search has the tail-to-tail matrices
once the dedicated initial coordinate has disappeared. -/
lemma reduced_binary_step {N : ℕ}
    (A : ℕ → Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (v0 : Fin (N+1) → ℝ)
    (h0 : ∀ j, j≠0 → A 0 0 j=0) (h1 : ∀ j, A 1 0 j=0)
    (n : ℕ) (hn : 0<n) (d : Fin 2) :
    (fun i : Fin N => evalNat A v0 (2*n+d.val) i.succ) =
      (fun i j : Fin N => A d.val i.succ j.succ) *ᵥ
        (fun i : Fin N => evalNat A v0 n i.succ) := by
  funext i
  rw [evalNat_binary_step A v0 n hn d]
  have hz := evalNat_initial_coordinate_zero A v0 h0 h1 n hn
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hz]

/-- Direct soundness theorem for the joint-orbit data format. No nonnegativity
restriction on the binary matrices or observable is needed here; the lower
bound on powers is a separate explicit obligation. -/
theorem joint_cone_finiteness {κ : Type*} [Fintype κ]
    (v : ℕ → σ → ℝ) (A : Fin 2 → Matrix σ σ ℝ) (u : σ → ℝ)
    (R : Matrix κ (Fin 4 × σ) ℝ) (C : Fin 2 → Matrix κ κ ℝ)
    (L : Fin 2 → κ → ℝ) (γ B : ℝ)
    (hC : ∀ d i j, 0≤C d i j) (hL : ∀ d i, 0≤L d i)
    (h1 : 0≤R *ᵥ jointValue v 1) (hS1 : 0≤u ⬝ᵥ v 1) (hγ : 0<γ)
    (hstep : ∀ n : ℕ, 0<n → ∀ d : Fin 2, v (2*n+d.val)=A d *ᵥ v n)
    (hclose : ∀ d, R*jointMatrix A d=C d*R)
    (htarget : ∀ d, Matrix.vecMul (L d) R=constructionRow u d)
    (hpower : ∀ k : ℕ, γ*k*(2:ℝ)^k≤u ⬝ᵥ v (2^k)+B*(2:ℝ)^k) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0,1]}.Finite := by
  apply finiteness (jointValue v) (jointMatrix A) R C (fun n => u ⬝ᵥ v n)
    L γ B hC hL h1 hS1 hγ (joint_recurrence v A hstep) hclose ?_ hpower
  intro n _ d
  rw [Matrix.dotProduct_mulVec, htarget, constructionRow_value]

end Erdos406BinaryCriticalCone
