import Submission.BinaryCriticalMinObserver

/-! A finite common-cone certificate for minimum observers with a matching
child selected for every parent. No sufficient numerical instance is supplied. -/
namespace Erdos406BinaryCriticalMinObserver
open Erdos406BinaryCriticalGuard Erdos406BinaryCriticalCone
open scoped Matrix BigOperators
variable {ι σ κ : Type*} [Fintype ι] [Nonempty ι] [Fintype σ] [Fintype κ]

def familyRow (r : ℕ) (u : Fin (3^r) → ι → σ → ℝ)
    (q : Fin (3^r)) (d : Fin 2) (j i : ι) : Fin 4 × σ → ℝ :=
  fun ⟨b,k⟩ => if b=0 then 3*u q j k else
    if b.val=d.val+1 then -u (residueState r (3*q.val+d.val)) i k else 0

lemma familyRow_value (r : ℕ) (v : ℕ → σ → ℝ) (u : Fin (3^r) → ι → σ → ℝ)
    (n : ℕ) (d : Fin 2) (j i : ι) :
    familyRow r u (residueState r n) d j i ⬝ᵥ jointValue v n =
      3*(u (residueState r n) j ⬝ᵥ v n)-
        u (residueState r (3*n+d.val)) i ⬝ᵥ v (3*n+d.val) := by
  have he (c : ℕ) : residueState r (3*(residueState r n).val+c)=residueState r (3*n+c) := by
    apply Fin.ext
    simp [residueState,Nat.add_mod,Nat.mul_mod]
  have he0 : residueState r (3*(residueState r n).val)=residueState r (3*n) := by
    simpa using he 0
  fin_cases d <;>
    simp [dotProduct,Fintype.sum_prod_type,Fin.sum_univ_succ,familyRow,jointValue,
      Finset.mul_sum,Finset.sum_neg_distrib,sub_eq_add_neg,mul_assoc,he,he0]

lemma matched_construction (r : ℕ) (v : ℕ → σ → ℝ)
    (A : Fin (3^r) → Fin 2 → Matrix σ σ ℝ) (u : Fin (3^r) → ι → σ → ℝ)
    (choose : Fin (3^r) → Fin 2 → ι → ι)
    (R : Fin (3^r) → Matrix κ (Fin 4 × σ) ℝ)
    (C : Fin (3^r) → Fin 2 → Matrix κ κ ℝ)
    (L : Fin (3^r) → Fin 2 → ι → κ → ℝ)
    (hC : ∀ q d i j, 0≤C q d i j)
    (hL : ∀ q, Nat.digits 3 q.val ⊆ [0,1] → ∀ d j k, 0≤L q d j k)
    (h1 : 0≤R (residueState r 1) *ᵥ jointValue v 1)
    (hstep : ∀ n : ℕ, 0<n → ∀ d : Fin 2,
      v (2*n+d.val)=A (residueState r n) d *ᵥ v n)
    (hclose : ∀ q d, R (residueNext r q d)*localJointMatrix r A q d=C q d*R q)
    (htarget : ∀ q, Nat.digits 3 q.val ⊆ [0,1] → ∀ d j,
      Matrix.vecMul (L q d j) (R q)=familyRow r u q d j (choose q d j))
    (n : ℕ) (hn : 0<n) (hg : Nat.digits 3 (n%3^r) ⊆ [0,1]) (d : Fin 2) (j : ι) :
    ∃ i, u (residueState r (3*n+d.val)) i ⬝ᵥ v (3*n+d.val)≤
      3*(u (residueState r n) j ⬝ᵥ v n) := by
  have hi := dependent_row_invariant (jointValue v) (residueState r) (residueNext r)
    (localJointMatrix r A) R C hC h1 (fun n _ d => residue_step r n d)
    (local_joint_recurrence r v A hstep) hclose n hn
  have hp := dotProduct_nonneg_of_nonneg (hL (residueState r n) hg d j) hi
  rw [Matrix.dotProduct_mulVec,htarget _ hg,familyRow_value] at hp
  exact ⟨choose (residueState r n) d j, by linarith⟩

/-- Every premise is finite data except the evaluator, whose recurrence is
proved once. In particular, closure and all parent-to-child matches are needed. -/
theorem local_min_observer_cone_finiteness (r : ℕ)
    (A : Fin (3^r) → Fin 2 → Matrix σ σ ℝ)
    (a b c : σ → ℝ) (γ z η B : ℝ) (u : Fin (3^r) → ι → σ → ℝ)
    (choose : Fin (3^r) → Fin 2 → ι → ι)
    (R : Fin (3^r) → Matrix κ (Fin 4 × σ) ℝ)
    (C : Fin (3^r) → Fin 2 → Matrix κ κ ℝ)
    (L : Fin (3^r) → Fin 2 → ι → κ → ℝ)
    (hγ : 0<γ) (hz : 0≤z) (hη : 0≤η)
    (ha : ∀ q, A q 0 *ᵥ a=2 • a)
    (hb : ∀ q, A q 0 *ᵥ b=2 • a+2 • b)
    (hc : ∀ q, A q 0 *ᵥ c=η • c)
    (hu : ∀ q, Nat.digits 3 q.val ⊆ [0,1] → Nat.Coprime q.val (3^r) → ∀ i,
      1≤u q i ⬝ᵥ a ∧ -B≤u q i ⬝ᵥ b ∧ 0≤u q i ⬝ᵥ c)
    (hS1 : ∀ i, 0≤u (residueState r 1) i ⬝ᵥ (γ • b+z • c))
    (hC : ∀ q d i j, 0≤C q d i j)
    (hL : ∀ q, Nat.digits 3 q.val ⊆ [0,1] → ∀ d j k, 0≤L q d j k)
    (h1 : 0≤R (residueState r 1) *ᵥ jointValue (localEval r A (γ • b+z • c)) 1)
    (hclose : ∀ q d, R (residueNext r q d)*localJointMatrix r A q d=C q d*R q)
    (htarget : ∀ q, Nat.digits 3 q.val ⊆ [0,1] → ∀ d j,
      Matrix.vecMul (L q d j) (R q)=familyRow r u q d j (choose q d j)) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0,1]}.Finite := by
  apply local_min_observer_finiteness r A a b c γ z η B u hγ hz hη ha hb hc hu hS1
  exact matched_construction r (localEval r A (γ • b+z • c)) A u choose R C L hC hL h1
    (localEval_step r A _) hclose htarget

#print axioms familyRow_value
#print axioms matched_construction
#print axioms local_min_observer_cone_finiteness
end Erdos406BinaryCriticalMinObserver
