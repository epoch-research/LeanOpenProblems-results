import Submission.BinaryCriticalPeriodicNecessity

/-! Exact telescoping for phase-dependent conjugacies of the binary 01 update.
No sufficient cone or settlement of Erdős 406 is asserted. -/
namespace Erdos406BinaryCriticalConjugacy
open Erdos406BinaryCriticalGuard Erdos406BinaryCriticalPeriodic
open scoped Matrix BigOperators

lemma predFour_succ (h : ℕ) : predFour (h+1)=4*predFour h+1 := by
  have ha := predFour_identity h
  have hb := predFour_identity (h+1)
  rw [pow_succ] at hb
  omega

@[simp] lemma predFour_one : predFour 1=1 := by norm_num [predFour]

def pairPhase (r : ℕ) (q : Fin (3^r)) : Fin (3^r) :=
  residueNext r (residueNext r q 0) 1

lemma pair_phase_step (r n : ℕ) :
    residueState r (4*n+1)=pairPhase r (residueState r n) := by
  rw [show 4*n+1=2*(2*n+(0:Fin 2).val)+(1:Fin 2).val by omega,
    residue_step,residue_step]
  rfl

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def pairMatrix (r : ℕ) (A : Fin (3^r) → Fin 2 → Matrix σ σ ℝ)
    (q : Fin (3^r)) : Matrix σ σ ℝ := A (residueNext r q 0) 1*A q 0

lemma pair_recurrence (r : ℕ) (A : Fin (3^r) → Fin 2 → Matrix σ σ ℝ)
    (v : ℕ → σ → ℝ)
    (hstep : ∀ n : ℕ, 0<n → ∀ d : Fin 2,
      v (2*n+d.val)=A (residueState r n) d *ᵥ v n)
    (n : ℕ) (hn : 0<n) :
    v (4*n+1)=pairMatrix r A (residueState r n) *ᵥ v n := by
  have hz := hstep n hn 0
  simp only [Fin.val_zero,add_zero] at hz
  have hq := residue_step r n 0
  simp only [Fin.val_zero,add_zero] at hq
  rw [show 4*n+1=2*(2*n)+(1:Fin 2).val by omega,
    hstep (2*n) (by omega),hz,hq,Matrix.mulVec_mulVec]
  rfl

/-- Intertwining the 01 updates gives the entire periodic predecessor orbit,
not merely a finite test or a numerically estimated spectral radius. -/
theorem conjugate_predecessor_orbit (r : ℕ)
    (A : Fin (3^r) → Fin 2 → Matrix σ σ ℝ) (v : ℕ → σ → ℝ)
    (G : Fin (3^r) → Matrix σ σ ℝ) (H : Matrix σ σ ℝ)
    (hstep : ∀ n : ℕ, 0<n → ∀ d : Fin 2,
      v (2*n+d.val)=A (residueState r n) d *ᵥ v n)
    (hG : G (residueState r 1)=1)
    (hinter : ∀ q, pairMatrix r A q*G q=(4:ℝ) • (G (pairPhase r q)*H))
    (j : ℕ) :
    v (predFour (j+1))=(4:ℝ)^j •
      ((G (residueState r (predFour (j+1)))*H^j) *ᵥ v 1) := by
  induction j with
  | zero => simp [hG]
  | succ j ih =>
    have hn : 0<predFour (j+1) := predFour_pos (by omega)
    have hq : residueState r (predFour (j+1+1))=
        pairPhase r (residueState r (predFour (j+1))) := by
      rw [predFour_succ,pair_phase_step]
    calc
      v (predFour (j+1+1)) =
          pairMatrix r A (residueState r (predFour (j+1))) *ᵥ v (predFour (j+1)) := by
        rw [predFour_succ,pair_recurrence r A v hstep _ hn]
      _ = (4:ℝ)^j • ((pairMatrix r A (residueState r (predFour (j+1)))*
          (G (residueState r (predFour (j+1)))*H^j)) *ᵥ v 1) := by
        rw [ih,Matrix.mulVec_smul,Matrix.mulVec_mulVec]
      _ = (4:ℝ)^j • ((4:ℝ) •
          ((G (pairPhase r (residueState r (predFour (j+1))))*H^(j+1)) *ᵥ v 1)) := by
        rw [← Matrix.mul_assoc,hinter,Matrix.smul_mul,Matrix.smul_mulVec,
          Matrix.mul_assoc,← pow_succ']
      _ = (4:ℝ)^(j+1) •
          ((G (residueState r (predFour (j+1+1)))*H^(j+1)) *ᵥ v 1) := by
        rw [smul_smul,← pow_succ,hq]

#print axioms predFour_succ
#print axioms pair_recurrence
#print axioms conjugate_predecessor_orbit
end Erdos406BinaryCriticalConjugacy
