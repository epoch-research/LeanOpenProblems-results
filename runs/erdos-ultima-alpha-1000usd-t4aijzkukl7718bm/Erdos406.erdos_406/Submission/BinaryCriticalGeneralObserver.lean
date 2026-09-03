import Submission.BinaryCriticalSignedDynamics

/-! General signed observables for a prescribed zero-bit orbit.
All certificate hypotheses below remain explicit. No sufficient certificate
or settlement of the original conjecture is asserted here. -/
namespace Erdos406BinaryCriticalGuard
open Erdos406BinaryCriticalCone
open scoped Matrix BigOperators

variable {σ κ : Type*} [Fintype σ] [Fintype κ]

lemma zero_bit_vector_power (v : ℕ → σ → ℝ) (A : ℕ → Matrix σ σ ℝ)
    (a b c : σ → ℝ) (γ z η : ℝ)
    (h1 : v 1 = γ • b + z • c)
    (hstep : ∀ n : ℕ, 0<n → v (2*n)=A n *ᵥ v n)
    (ha : ∀ n : ℕ, 0<n → A n *ᵥ a=2 • a)
    (hb : ∀ n : ℕ, 0<n → A n *ᵥ b=2 • a+2 • b)
    (hc : ∀ n : ℕ, 0<n → A n *ᵥ c=η • c) (k : ℕ) :
    v (2^k)=(γ*k*(2:ℝ)^k) • a+(γ*(2:ℝ)^k) • b+(z*η^k) • c := by
  induction k with
  | zero => simpa using h1
  | succ k ih =>
    have hp : 0<(2:ℕ)^k := by positivity
    rw [pow_succ',hstep _ hp,ih]
    simp only [Matrix.mulVec_add,Matrix.mulVec_smul,ha _ hp,hb _ hp,hc _ hp]
    ext i
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Nat.cast_add,Nat.cast_one,pow_succ]
    ring

lemma general_observer_power_lower (v : ℕ → σ → ℝ) (A : ℕ → Matrix σ σ ℝ)
    (a b c : σ → ℝ) (γ z η B : ℝ) (u : σ → ℝ)
    (hγ : 0≤γ) (hz : 0≤z) (hη : 0≤η)
    (h1 : v 1 = γ • b + z • c)
    (hstep : ∀ n : ℕ, 0<n → v (2*n)=A n *ᵥ v n)
    (ha : ∀ n : ℕ, 0<n → A n *ᵥ a=2 • a)
    (hb : ∀ n : ℕ, 0<n → A n *ᵥ b=2 • a+2 • b)
    (hc : ∀ n : ℕ, 0<n → A n *ᵥ c=η • c)
    (hua : 1≤u ⬝ᵥ a) (hub : -B≤u ⬝ᵥ b) (huc : 0≤u ⬝ᵥ c) (k : ℕ) :
    γ*k*(2:ℝ)^k≤u ⬝ᵥ v (2^k)+(B*γ)*(2:ℝ)^k := by
  rw [zero_bit_vector_power v A a b c γ z η h1 hstep ha hb hc k]
  simp only [dotProduct_add,dotProduct_smul,smul_eq_mul]
  have hpa : 0≤γ*k*(2:ℝ)^k := by positivity
  have hpb : 0≤γ*(2:ℝ)^k := by positivity
  have hpc : 0≤z*η^k := by positivity
  have hma := mul_le_mul_of_nonneg_left hua hpa
  have hmb := mul_le_mul_of_nonneg_left hub hpb
  have hmc := mul_nonneg hpc huc
  nlinarith

lemma power_residue_coprime (r k : ℕ) : Nat.Coprime (2^k%3^r) (3^r) := by
  have hh : Nat.Coprime (2^k) (3^r) := ((show Nat.Coprime 2 3 by decide).pow_left k).pow_right r
  change Nat.gcd (2^k%3^r) (3^r)=1
  rw [← Nat.gcd_rec]
  exact hh.symm

/-- A general observable needs lower bounds only at good power-reachable
residues. Other coordinates may be signed and do not occur on the power orbit. -/
theorem local_general_observer_finiteness (r : ℕ)
    (A : Fin (3^r) → Fin 2 → Matrix σ σ ℝ)
    (a b c : σ → ℝ) (γ z η B : ℝ) (u : Fin (3^r) → σ → ℝ)
    (R : Fin (3^r) → Matrix κ (Fin 4 × σ) ℝ)
    (C : Fin (3^r) → Fin 2 → Matrix κ κ ℝ) (L : Fin (3^r) → Fin 2 → κ → ℝ)
    (hγ : 0<γ) (hz : 0≤z) (hη : 0≤η)
    (ha : ∀ q, A q 0 *ᵥ a=2 • a)
    (hb : ∀ q, A q 0 *ᵥ b=2 • a+2 • b)
    (hc : ∀ q, A q 0 *ᵥ c=η • c)
    (hu : ∀ q, Nat.digits 3 q.val ⊆ [0,1] → Nat.Coprime q.val (3^r) →
      1≤u q ⬝ᵥ a ∧ -B≤u q ⬝ᵥ b ∧ 0≤u q ⬝ᵥ c)
    (hS1 : 0≤u (residueState r 1) ⬝ᵥ (γ • b+z • c))
    (hC : ∀ q d i j, 0≤C q d i j)
    (hL : ∀ q, Nat.digits 3 q.val ⊆ [0,1] → ∀ d i, 0≤L q d i)
    (h1 : 0≤R (residueState r 1) *ᵥ jointValue (localEval r A (γ • b+z • c)) 1)
    (hclose : ∀ q d, R (residueNext r q d)*localJointMatrix r A q d=C q d*R q)
    (htarget : ∀ q, Nat.digits 3 q.val ⊆ [0,1] → ∀ d,
      Matrix.vecMul (L q d) (R q)=localRow r u q d) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0,1]}.Finite := by
  let v := localEval r A (γ • b+z • c)
  apply critical_criterion (fun n => u (residueState r n) ⬝ᵥ v n) r γ (B*γ)
    (by simpa [v] using hS1) hγ
  · exact local_construction r v A u R C L hC hL h1 (localEval_step r A _) hclose htarget
  · intro k hg
    obtain ⟨hua,hub,huc⟩ := hu (residueState r (2^k)) hg (power_residue_coprime r k)
    exact general_observer_power_lower v (fun n => A (residueState r n) 0)
      a b c γ z η B (u (residueState r (2^k))) hγ.le hz hη
      (by simp [v]) (fun n hn => by simpa [v] using localEval_step r A (γ • b+z • c) n hn 0)
      (fun n _ => ha _) (fun n _ => hb _) (fun n _ => hc _) hua hub huc k

#print axioms zero_bit_vector_power
#print axioms general_observer_power_lower
#print axioms power_residue_coprime
#print axioms local_general_observer_finiteness
end Erdos406BinaryCriticalGuard
