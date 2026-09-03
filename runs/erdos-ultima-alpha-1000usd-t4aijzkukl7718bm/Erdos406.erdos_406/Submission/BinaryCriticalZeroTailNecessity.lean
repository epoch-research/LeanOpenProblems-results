import Submission.BinaryCriticalZeroTailSlope
import Submission.BinaryCriticalLocalConeCertificates

/-! A zero-tail obstruction for common-leading-eigenvector models.
The binary recurrence and the long-zero-block bridge are proved here.
This rejects potential models; it is not a proof of Erdős 406. -/
namespace Erdos406BinaryCriticalZeroTail
open Erdos406BinaryCriticalGuard Erdos406BinaryCriticalRecurrence
open scoped Matrix BigOperators

variable {N : ℕ}

def tailInput (k : ℕ) : ℕ := 3*2^(6*k+6)+1

lemma tail_residue (k : ℕ) : tailInput k % 9=4 := by
  norm_num [tailInput,pow_add,pow_mul,Nat.add_mod,Nat.mul_mod,Nat.pow_mod]

lemma zero_iterate (v : ℕ → Fin N → ℝ) (D : Matrix (Fin N) (Fin N) ℝ)
    (hz : ∀ n, 0 < n → v (2*n)=D *ᵥ v n) (m : ℕ) (hm : 0 < m) (k : ℕ) :
    v (2^k*m)=(D^k)*ᵥ v m := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ',mul_assoc,hz _ (by positivity),ih,Matrix.mulVec_mulVec,pow_succ']

lemma zero_block_factor (D R : Matrix (Fin N) (Fin N) ℝ)
    (hD : D^6=(64:ℝ) • R) (k j : ℕ) :
    D^(6*k+j)=(64:ℝ)^k • (D^j*R^k) := by
  rw [show 6*k+j=j+6*k by omega,pow_add,pow_mul,hD,smul_pow,Matrix.mul_smul]

lemma tail_values (v : ℕ → Fin N → ℝ)
    (D R : Matrix (Fin N) (Fin N) ℝ) (O : Fin 9 → Matrix (Fin N) (Fin N) ℝ)
    (hz : ∀ n, 0 < n → v (2*n)=D *ᵥ v n)
    (ho : ∀ n, 0 < n → v (2*n+1)=O (residueState 2 n) *ᵥ v n)
    (hD : D^6=(64:ℝ) • R) (k : ℕ) :
    v (tailInput k)=(64:ℝ)^k • ((O 6*D^5) *ᵥ ((R^k)*ᵥ v 3)) ∧
    v (3*tailInput k+1)=(64:ℝ)^k • ((D^2*O 0*D^3) *ᵥ ((R^k)*ᵥ v 9)) := by
  have qp : residueState 2 (2^(6*k+5)*3)=6 := by
    apply Fin.ext
    norm_num [residueState,pow_add,pow_mul,Nat.mul_mod,Nat.pow_mod]
  have qc : residueState 2 (2^(6*k+3)*9)=0 := by
    apply Fin.ext
    simp [residueState]
  have np : tailInput k=2*(2^(6*k+5)*3)+1 := by
    dsimp [tailInput]
    rw [show 6*k+6=(6*k+5)+1 by omega,pow_succ]
    ring
  have nc : 3*tailInput k+1=2^2*(2*(2^(6*k+3)*9)+1) := by
    dsimp [tailInput]
    rw [show 6*k+6=(6*k+3)+3 by omega,pow_add]
    norm_num
    ring
  constructor
  · rw [np,ho _ (by positivity),qp,zero_iterate v D hz 3 (by decide),
      zero_block_factor D R hD,Matrix.smul_mulVec,Matrix.mulVec_smul]
    congr 1
    simp only [Matrix.mulVec_mulVec,Matrix.mul_assoc]
  · rw [nc,zero_iterate v D hz _ (by positivity) 2,ho _ (by positivity),qc,
      zero_iterate v D hz 9 (by decide),zero_block_factor D R hD,
      Matrix.smul_mulVec,Matrix.mulVec_smul,Matrix.mulVec_smul]
    congr 1
    simp only [Matrix.mulVec_mulVec,Matrix.mul_assoc]

/-- A finite family of positive-leading observers on residue4 must obey
`Y9 <= 3*Y3`. All remaining hypotheses are finite matrix/vector identities
or the binary recurrence and a necessary subset of construction inequalities. -/
theorem zero_tail_tripling_necessary {ι : Type*} [Fintype ι] [Nonempty ι]
    (v : ℕ → Fin N → ℝ) (D R : Matrix (Fin N) (Fin N) ℝ)
    (O : Fin 9 → Matrix (Fin N) (Fin N) ℝ)
    (a b z3 z9 : Fin N → ℝ) (X3 Y3 X9 Y9 τ : ℝ) (u : ι → Fin N → ℝ)
    (hz : ∀ n, 0 < n → v (2*n)=D *ᵥ v n)
    (ho : ∀ n, 0 < n → v (2*n+1)=O (residueState 2 n) *ᵥ v n)
    (hD : D^6=(64:ℝ) • R)
    (ha : R *ᵥ a=a) (hb : R *ᵥ b=b+(6:ℝ) • a)
    (hz3 : R *ᵥ z3=τ • z3) (hz9 : R *ᵥ z9=τ • z9)
    (hv3 : v 3=X3 • a+Y3 • b+z3) (hv9 : v 9=X9 • a+Y9 • b+z9)
    (hBp : (O 6*D^5)*ᵥ a=(64:ℝ) • a)
    (hBc : (D^2*O 0*D^3)*ᵥ a=(64:ℝ) • a)
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (hY9 : 0 ≤ Y9)
    (hu : ∀ i, 0 < u i ⬝ᵥ a)
    (hconstruct : ∀ n : ℕ, 0 < n → n%9=4 → ∀ j, ∃ i,
      u i ⬝ᵥ v (3*n+1) ≤ 3*(u j ⬝ᵥ v n)) : Y9 ≤ 3*Y3 := by
  let BP := O 6*D^5
  let BC := D^2*O 0*D^3
  have hmatch (k : ℕ) (j : ι) : ∃ i,
      u i ⬝ᵥ (BC *ᵥ ((R^k)*ᵥ v 9)) ≤
        3*(u j ⬝ᵥ (BP *ᵥ ((R^k)*ᵥ v 3))) := by
    obtain ⟨i,hi⟩ := hconstruct (tailInput k) (by unfold tailInput; positivity)
      (tail_residue k) j
    obtain ⟨hp,hc⟩ := tail_values v D R O hz ho hD k
    rw [hp,hc,dotProduct_smul,dotProduct_smul,smul_eq_mul,smul_eq_mul] at hi
    refine ⟨i,?_⟩
    apply (mul_le_mul_iff_right₀ (show (0:ℝ)<64^k by positivity)).mp
    dsimp [BP,BC]
    nlinarith
  have hh := affine_transient_minimum_slope
    (fun i => u i ⬝ᵥ a)
    (fun i => 3*(64*X3*(u i ⬝ᵥ a)+Y3*(u i ⬝ᵥ (BP *ᵥ b))))
    (fun i => 3*(u i ⬝ᵥ (BP *ᵥ z3)))
    (fun i => 64*X9*(u i ⬝ᵥ a)+Y9*(u i ⬝ᵥ (BC *ᵥ b)))
    (fun i => u i ⬝ᵥ (BC *ᵥ z9)) hu (384*Y9) (1152*Y3) τ
    (by positivity) hτ hτ1 ?_
  · linarith
  · intro k j
    obtain ⟨i,hi⟩ := hmatch k j
    rw [hv3,hv9] at hi
    rw [suffix_jordan_scalar N R BC a b z9 (u i) X9 Y9 6 τ 64 ha hb hz9 hBc,
      suffix_jordan_scalar N R BP a b z3 (u j) X3 Y3 6 τ 64 ha hb hz3 hBp] at hi
    exact ⟨i,by nlinarith⟩

#print axioms tail_values
#print axioms zero_tail_tripling_necessary
end Erdos406BinaryCriticalZeroTail
