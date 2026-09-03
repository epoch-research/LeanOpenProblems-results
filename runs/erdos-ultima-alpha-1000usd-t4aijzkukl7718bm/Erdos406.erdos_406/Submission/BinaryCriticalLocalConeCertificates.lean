import Submission.BinaryCriticalShiftedJordan

/-! State-dependent joint dynamics for residue-local critical potentials.
These are conditional soundness results, not a settlement of Erdős 406. -/
namespace Erdos406BinaryCriticalGuard
open Erdos406BinaryCriticalCone
open scoped Matrix BigOperators
variable {σ κ ρ : Type*} [Fintype σ] [Fintype κ]

theorem dependent_row_invariant (W : ℕ → σ → ℝ) (Q : ℕ → ρ)
    (next : ρ → Fin 2 → ρ) (T : ρ → Fin 2 → Matrix σ σ ℝ)
    (R : ρ → Matrix κ σ ℝ) (C : ρ → Fin 2 → Matrix κ κ ℝ)
    (hC : ∀ q d i j, 0≤C q d i j) (h1 : 0≤R (Q 1) *ᵥ W 1)
    (hQ : ∀ n : ℕ, 0<n → ∀ d : Fin 2, Q (2*n+d.val)=next (Q n) d)
    (hstep : ∀ n : ℕ, 0<n → ∀ d : Fin 2, W (2*n+d.val)=T (Q n) d *ᵥ W n)
    (hclose : ∀ q d, R (next q d)*T q d=C q d*R q) :
    ∀ n : ℕ, 0<n → 0≤R (Q n) *ᵥ W n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases he : n=1
    · simpa [he] using h1
    have hq : 0<n/2 := by omega
    have hi := ih (n/2) (Nat.div_lt_self hn (by decide)) hq
    let d : Fin 2 := ⟨n%2,Nat.mod_lt _ (by decide)⟩
    have hid : 2*(n/2)+d.val=n := by dsimp [d]; omega
    have hs := hstep (n/2) hq d
    have hqs := hQ (n/2) hq d
    rw [hid] at hs hqs
    rw [hs,hqs,Matrix.mulVec_mulVec,hclose,← Matrix.mulVec_mulVec]
    intro i
    exact dotProduct_nonneg_of_nonneg (hC _ d i) hi

def blockPhase (r : ℕ) (q : Fin (3^r)) : Fin 4 → Fin (3^r) :=
  ![q,residueState r (3*q.val),residueState r (3*q.val+1),residueState r (3*q.val+2)]

lemma blockPhase_residue (r n : ℕ) (b : Fin 4) :
    blockPhase r (residueState r n) b =
      ![residueState r n,residueState r (3*n),residueState r (3*n+1),residueState r (3*n+2)] b := by
  fin_cases b <;> simp [blockPhase,residueState,Nat.add_mod,Nat.mul_mod]

def localJointMatrix (r : ℕ) (A : Fin (3^r) → Fin 2 → Matrix σ σ ℝ)
    (q : Fin (3^r)) (d : Fin 2) : Matrix (Fin 4 × σ) (Fin 4 × σ) ℝ :=
  fun ⟨b,i⟩ ⟨c,j⟩ => if c=parentBlock d b then A (blockPhase r q c) (outputDigit d b) i j else 0

lemma localJointMatrix_mulVec (r : ℕ) (A : Fin (3^r) → Fin 2 → Matrix σ σ ℝ)
    (q : Fin (3^r)) (d : Fin 2) (w : Fin 4 × σ → ℝ) (b : Fin 4) (i : σ) :
    (localJointMatrix r A q d *ᵥ w) (b,i) =
      (A (blockPhase r q (parentBlock d b)) (outputDigit d b) *ᵥ
        (fun j => w (parentBlock d b,j))) i := by
  simp [Matrix.mulVec,dotProduct,localJointMatrix,Fintype.sum_prod_type,Finset.sum_ite_irrel]

lemma local_joint_recurrence (r : ℕ) (v : ℕ → σ → ℝ)
    (A : Fin (3^r) → Fin 2 → Matrix σ σ ℝ)
    (hstep : ∀ n : ℕ, 0<n → ∀ d : Fin 2,
      v (2*n+d.val)=A (residueState r n) d *ᵥ v n)
    (n : ℕ) (hn : 0<n) (d : Fin 2) :
    jointValue v (2*n+d.val)=localJointMatrix r A (residueState r n) d *ᵥ jointValue v n := by
  ext ⟨b,i⟩
  rw [localJointMatrix_mulVec,blockPhase_residue]
  fin_cases d <;> fin_cases b <;> simp [jointValue,parentBlock,outputDigit]
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

def localRow (r : ℕ) (u : Fin (3^r) → σ → ℝ) (q : Fin (3^r))
    (d : Fin 2) : Fin 4 × σ → ℝ :=
  fun ⟨b,i⟩ => if b=0 then 3*u q i else
    if b.val=d.val+1 then -u (residueState r (3*q.val+d.val)) i else 0

lemma localRow_value (r : ℕ) (v : ℕ → σ → ℝ) (u : Fin (3^r) → σ → ℝ)
    (n : ℕ) (d : Fin 2) :
    localRow r u (residueState r n) d ⬝ᵥ jointValue v n =
      3*(u (residueState r n) ⬝ᵥ v n)-u (residueState r (3*n+d.val)) ⬝ᵥ v (3*n+d.val) := by
  have he (c : ℕ) : residueState r (3*(residueState r n).val+c)=residueState r (3*n+c) := by
    apply Fin.ext
    simp [residueState,Nat.add_mod,Nat.mul_mod]
  have he0 : residueState r (3*(residueState r n).val)=residueState r (3*n) := by
    simpa using he 0
  fin_cases d <;>
    simp [dotProduct,Fintype.sum_prod_type,Fin.sum_univ_succ,localRow,jointValue,
      Finset.mul_sum,Finset.sum_neg_distrib,sub_eq_add_neg,mul_assoc,he,he0]

theorem local_construction (r : ℕ) (v : ℕ → σ → ℝ)
    (A : Fin (3^r) → Fin 2 → Matrix σ σ ℝ) (u : Fin (3^r) → σ → ℝ)
    (R : Fin (3^r) → Matrix κ (Fin 4 × σ) ℝ)
    (C : Fin (3^r) → Fin 2 → Matrix κ κ ℝ) (L : Fin (3^r) → Fin 2 → κ → ℝ)
    (hC : ∀ q d i j, 0≤C q d i j)
    (hL : ∀ q, Nat.digits 3 q.val ⊆ [0,1] → ∀ d i, 0≤L q d i)
    (h1 : 0≤R (residueState r 1) *ᵥ jointValue v 1)
    (hstep : ∀ n : ℕ, 0<n → ∀ d : Fin 2,
      v (2*n+d.val)=A (residueState r n) d *ᵥ v n)
    (hclose : ∀ q d, R (residueNext r q d)*localJointMatrix r A q d=C q d*R q)
    (htarget : ∀ q, Nat.digits 3 q.val ⊆ [0,1] → ∀ d,
      Matrix.vecMul (L q d) (R q)=localRow r u q d)
    (n : ℕ) (hn : 0<n) (hg : Nat.digits 3 (n%3^r) ⊆ [0,1]) (d : Fin 2) :
    u (residueState r (3*n+d.val)) ⬝ᵥ v (3*n+d.val)≤3*(u (residueState r n) ⬝ᵥ v n) := by
  have hi := dependent_row_invariant (jointValue v) (residueState r) (residueNext r)
    (localJointMatrix r A) R C hC h1 (fun n _ d => residue_step r n d)
    (local_joint_recurrence r v A hstep) hclose n hn
  have hp := dotProduct_nonneg_of_nonneg (hL (residueState r n) hg d) hi
  rw [Matrix.dotProduct_mulVec,htarget _ hg,localRow_value] at hp
  linarith

/-- Positive-input evaluator, initialized after the leading binary one. -/
def localEval (r : ℕ) (A : Fin (3^r) → Fin 2 → Matrix σ σ ℝ)
    (v1 : σ → ℝ) (n : ℕ) : σ → ℝ :=
  if h : n≤1 then v1 else
    A (residueState r (n/2)) ⟨n%2,Nat.mod_lt _ (by decide)⟩ *ᵥ localEval r A v1 (n/2)
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

@[simp] lemma localEval_one (r : ℕ) (A : Fin (3^r) → Fin 2 → Matrix σ σ ℝ)
    (v1 : σ → ℝ) : localEval r A v1 1=v1 := by rw [localEval]; simp

lemma localEval_step (r : ℕ) (A : Fin (3^r) → Fin 2 → Matrix σ σ ℝ)
    (v1 : σ → ℝ) (n : ℕ) (hn : 0<n) (d : Fin 2) :
    localEval r A v1 (2*n+d.val)=A (residueState r n) d *ᵥ localEval r A v1 n := by
  rw [localEval]
  have he : ¬ 2*n+d.val≤1 := by omega
  simp only [dif_neg he]
  have hq : (2*n+d.val)/2=n := by omega
  have hm : (2*n+d.val)%2=d.val := by omega
  simp only [hq,hm,Fin.eta]

lemma localEval_nonneg (r : ℕ) (A : Fin (3^r) → Fin 2 → Matrix σ σ ℝ)
    (v1 : σ → ℝ) (hv1 : 0≤v1) (hA : ∀ q d i j, 0≤A q d i j)
    (n : ℕ) (hn : 0<n) : 0≤localEval r A v1 n := by
  apply positive_orbit_nonneg (localEval r A v1) (fun n => A (residueState r n))
    (by simpa using hv1) (fun _ _ => hA _) (localEval_step r A v1) n hn

/-- Complete conditional soundness of the residue-local data format. The cone,
row ladder, initial inequalities, and strictly positive seed are all required. -/
theorem local_certificate_finiteness (r : ℕ)
    (A : Fin (3^r) → Fin 2 → Matrix σ σ ℝ) (v1 : σ → ℝ)
    (u : Fin (3^r) → σ → ℝ) (a b : σ → ℝ) (B : ℝ)
    (R : Fin (3^r) → Matrix κ (Fin 4 × σ) ℝ)
    (C : Fin (3^r) → Fin 2 → Matrix κ κ ℝ) (L : Fin (3^r) → Fin 2 → κ → ℝ)
    (hv1 : 0≤v1) (hA : ∀ q d i j, 0≤A q d i j) (ha : 0≤a)
    (hrowa : ∀ q j, 2*a j+2*b j≤Matrix.vecMul a (A q 0) j)
    (hrowb : ∀ q, Matrix.vecMul b (A q 0)=fun j => 2*b j)
    (hdom : ∀ q j, a j≤u q j+B*b j)
    (hS1 : 0≤u (residueState r 1) ⬝ᵥ v1) (hseed : 0<b ⬝ᵥ v1)
    (hC : ∀ q d i j, 0≤C q d i j)
    (hL : ∀ q, Nat.digits 3 q.val ⊆ [0,1] → ∀ d i, 0≤L q d i)
    (h1 : 0≤R (residueState r 1) *ᵥ jointValue (localEval r A v1) 1)
    (hclose : ∀ q d, R (residueNext r q d)*localJointMatrix r A q d=C q d*R q)
    (htarget : ∀ q, Nat.digits 3 q.val ⊆ [0,1] → ∀ d,
      Matrix.vecMul (L q d) (R q)=localRow r u q d) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0,1]}.Finite := by
  let v := localEval r A v1
  apply critical_criterion (fun n => u (residueState r n) ⬝ᵥ v n) r
    (b ⬝ᵥ v1) (B*(b ⬝ᵥ v1)) (by simpa [v] using hS1) hseed
  · exact local_construction r v A u R C L hC hL h1 (localEval_step r A v1) hclose htarget
  · intro k _
    have hh := shifted_matrix_power_lower v (fun n => u (residueState r n))
      (fun n => A (residueState r n) 0) a b B (localEval_nonneg r A v1 hv1 hA) ha
      (fun n hn => by simpa [v] using localEval_step r A v1 n hn 0)
      (fun n _ => hrowa _) (fun n _ => hrowb _) (fun n _ => hdom _) k
    simpa [v] using hh

end Erdos406BinaryCriticalGuard
