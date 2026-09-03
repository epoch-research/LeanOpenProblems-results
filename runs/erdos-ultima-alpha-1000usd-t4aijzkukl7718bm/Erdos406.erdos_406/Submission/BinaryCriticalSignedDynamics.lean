import Submission.BinaryCriticalLocalConeCertificates

/-! Signed binary dynamics with an exact zero-bit Jordan law. Positivity of
states and state-update matrices is not assumed. The cone and positive-seed
conditions below are explicit hypotheses, not an asserted certificate. -/
namespace Erdos406BinaryCriticalGuard
open Erdos406BinaryCriticalMatrix Erdos406BinaryCriticalCone
open scoped Matrix BigOperators

lemma zero_bit_eigenvalue (f : ℕ → ℝ) (a : ℝ)
    (hf : ∀ n : ℕ, 0<n → f (2*n)=a*f n) (k : ℕ) :
    f (2^k)=a^k*f 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ',hf _ (by positivity),ih,pow_succ']
    ring

/-- Only the three selected coordinates along powers must have controlled
signs. Odd-bit transitions may send arbitrary coordinates to negative values. -/
lemma signed_zero_ladder_lower (x y z S w η : ℕ → ℝ) (B : ℝ)
    (hx1 : 0≤x 1) (hy1 : 0≤y 1) (hz1 : 0≤z 1) (hη : ∀ n : ℕ, 0<n → 0≤η n)
    (hx : ∀ n : ℕ, 0<n → x (2*n)=2*x n+2*y n)
    (hy : ∀ n : ℕ, 0<n → y (2*n)=2*y n)
    (hz : ∀ n : ℕ, 0<n → z (2*n)=η n*z n)
    (hw : ∀ n : ℕ, -B≤w n)
    (hS : ∀ n : ℕ, S n=x n+w n*y n+z n) (k : ℕ) :
    (y 1)*k*(2:ℝ)^k≤S (2^k)+(B*y 1)*(2:ℝ)^k := by
  have hyp := zero_bit_eigenvalue y 2 hy k
  have hyl : 0≤y (2^k) := by rw [hyp]; positivity
  have hzall : ∀ j : ℕ, 0≤z (2^j) := by
    intro j
    induction j with
    | zero => simpa using hz1
    | succ j ih =>
      rw [pow_succ',hz _ (by positivity)]
      exact mul_nonneg (hη _ (by positivity)) ih
  have hzl := hzall k
  have hl := jordan_power_lower x y (fun n hn => (hx n hn).ge)
    (fun n hn => (hy n hn).ge) k
  have hm := mul_le_mul_of_nonneg_right (hw (2^k)) hyl
  have hp : (0:ℝ)≤2^k := by positivity
  have hxp := mul_nonneg hp hx1
  rw [hS,hyp]
  rw [hyp] at hm
  nlinarith

variable {σ κ : Type*} [Fintype σ] [Fintype κ]

lemma signed_matrix_power_lower (v : ℕ → σ → ℝ)
    (A : ℕ → Matrix σ σ ℝ) (u : ℕ → σ → ℝ)
    (a b c : σ → ℝ) (w η : ℕ → ℝ) (B : ℝ)
    (ha1 : 0≤a ⬝ᵥ v 1) (hb1 : 0≤b ⬝ᵥ v 1) (hc1 : 0≤c ⬝ᵥ v 1)
    (hη : ∀ n : ℕ, 0<n → 0≤η n)
    (hstep : ∀ n : ℕ, 0<n → v (2*n)=A n *ᵥ v n)
    (ha : ∀ n : ℕ, 0<n → Matrix.vecMul a (A n)=fun j => 2*a j+2*b j)
    (hb : ∀ n : ℕ, 0<n → Matrix.vecMul b (A n)=fun j => 2*b j)
    (hc : ∀ n : ℕ, 0<n → Matrix.vecMul c (A n)=fun j => η n*c j)
    (hu : ∀ n j, u n j=a j+w n*b j+c j) (hw : ∀ n, -B≤w n) (k : ℕ) :
    (b ⬝ᵥ v 1)*k*(2:ℝ)^k≤u (2^k) ⬝ᵥ v (2^k)+(B*(b ⬝ᵥ v 1))*(2:ℝ)^k := by
  apply signed_zero_ladder_lower (fun n => a ⬝ᵥ v n) (fun n => b ⬝ᵥ v n)
    (fun n => c ⬝ᵥ v n) (fun n => u n ⬝ᵥ v n) w η B ha1 hb1 hc1 hη
  · intro n hn
    rw [hstep n hn,Matrix.dotProduct_mulVec,ha n hn]
    simp [dotProduct,Finset.sum_add_distrib,Finset.mul_sum,add_mul,mul_assoc]
  · intro n hn
    rw [hstep n hn,Matrix.dotProduct_mulVec,hb n hn]
    simp [dotProduct,Finset.mul_sum,mul_assoc]
  · intro n hn
    rw [hstep n hn,Matrix.dotProduct_mulVec,hc n hn]
    simp [dotProduct,Finset.mul_sum,mul_assoc]
  · exact hw
  · intro n
    simp [dotProduct,hu,Finset.sum_add_distrib,Finset.mul_sum,add_mul,mul_assoc]

/-- Complete conditional soundness for signed residue-local updates. Only the
cone decomposition coefficients and the initial selected rows need signs. -/
theorem local_signed_certificate_finiteness (r : ℕ)
    (A : Fin (3^r) → Fin 2 → Matrix σ σ ℝ) (v1 : σ → ℝ)
    (u : Fin (3^r) → σ → ℝ) (a b c : σ → ℝ)
    (w η : Fin (3^r) → ℝ) (B : ℝ)
    (R : Fin (3^r) → Matrix κ (Fin 4 × σ) ℝ)
    (C : Fin (3^r) → Fin 2 → Matrix κ κ ℝ) (L : Fin (3^r) → Fin 2 → κ → ℝ)
    (ha1 : 0≤a ⬝ᵥ v1) (hb1 : 0<b ⬝ᵥ v1) (hc1 : 0≤c ⬝ᵥ v1) (hη : ∀ q, 0≤η q)
    (ha : ∀ q, Matrix.vecMul a (A q 0)=fun j => 2*a j+2*b j)
    (hb : ∀ q, Matrix.vecMul b (A q 0)=fun j => 2*b j)
    (hc : ∀ q, Matrix.vecMul c (A q 0)=fun j => η q*c j)
    (hu : ∀ q j, u q j=a j+w q*b j+c j) (hw : ∀ q, -B≤w q)
    (hS1 : 0≤u (residueState r 1) ⬝ᵥ v1)
    (hC : ∀ q d i j, 0≤C q d i j)
    (hL : ∀ q, Nat.digits 3 q.val ⊆ [0,1] → ∀ d i, 0≤L q d i)
    (h1 : 0≤R (residueState r 1) *ᵥ jointValue (localEval r A v1) 1)
    (hclose : ∀ q d, R (residueNext r q d)*localJointMatrix r A q d=C q d*R q)
    (htarget : ∀ q, Nat.digits 3 q.val ⊆ [0,1] → ∀ d,
      Matrix.vecMul (L q d) (R q)=localRow r u q d) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0,1]}.Finite := by
  let v := localEval r A v1
  apply critical_criterion (fun n => u (residueState r n) ⬝ᵥ v n) r
    (b ⬝ᵥ v1) (B*(b ⬝ᵥ v1)) (by simpa [v] using hS1) hb1
  · exact local_construction r v A u R C L hC hL h1 (localEval_step r A v1) hclose htarget
  · intro k _
    have hh := signed_matrix_power_lower v (fun n => A (residueState r n) 0)
      (fun n => u (residueState r n)) a b c (fun n => w (residueState r n)) (fun n => η (residueState r n)) B
      (by simpa [v] using ha1) (by simpa [v] using hb1.le) (by simpa [v] using hc1) (fun n _ => hη _)
      (fun n hn => by simpa [v] using localEval_step r A v1 n hn 0)
      (fun n _ => ha _) (fun n _ => hb _) (fun n _ => hc _)
      (fun n j => hu _ j) (fun n => hw _) k
    simpa [v] using hh

#print axioms signed_zero_ladder_lower
#print axioms signed_matrix_power_lower
#print axioms local_signed_certificate_finiteness
end Erdos406BinaryCriticalGuard
