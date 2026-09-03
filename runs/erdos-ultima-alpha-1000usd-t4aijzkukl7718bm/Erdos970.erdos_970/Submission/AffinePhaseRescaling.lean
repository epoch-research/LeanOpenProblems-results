import Submission.GapVarianceSubadditive
import Submission.IntervalRescaling
import Submission.SurvivorResampling

/-! Exact transfer of the uniform-phase distribution along a progression whose
step is coprime to all sieve moduli. The same phase is retained across rows:
this is not an assertion that different rows are independent. -/
namespace Erdos970.GapAverages
open Finset

noncomputable def affineResidueEquiv (q a d : ℕ) (hq : 0 < q)
    (hdq : d.Coprime q) : Fin q ≃ Fin q := by
  let f : Fin q → Fin q := fun b => ⟨(a + d * b.val) % q, Nat.mod_lt _ hq⟩
  have hf : Function.Injective f := by
    intro b c hbc
    have hmod : a + d * b.val ≡ a + d * c.val [MOD q] := congrArg Fin.val hbc
    have h := Nat.ModEq.cancel_left_of_coprime hdq.symm
      (Nat.ModEq.add_left_cancel' a hmod)
    apply Fin.ext
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt b.isLt, Nat.mod_eq_of_lt c.isLt] using h
  exact Equiv.ofBijective f ⟨hf, Finite.surjective_of_injective hf⟩

lemma affineResidueEquiv_val (q a d : ℕ) (hq : 0 < q) (hdq : d.Coprime q)
    (b : Fin q) :
    (affineResidueEquiv q a d hq hdq b).val = (a + d * b.val) % q := rfl

noncomputable def affinePhaseEquiv (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime)
    (a d : ℕ) (hd : ∀ q ∈ P, d.Coprime q) : Phase P ≃ Phase P :=
  Equiv.piCongrRight (fun q : P =>
    affineResidueEquiv q.val a d (hP q.val q.property).pos (hd q.val q.property))

lemma affinePhaseEquiv_val (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime)
    (a d : ℕ) (hd : ∀ q ∈ P, d.Coprime q) (r : Phase P) (q : P) :
    ((affinePhaseEquiv P hP a d hd r) q).val = (a + d * (r q).val) % q.val := rfl

lemma point_affine (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime)
    (a d : ℕ) (hd : ∀ q ∈ P, d.Coprime q) (t : ℕ) (r : Phase P) :
    point P (a + d * t) (affinePhaseEquiv P hP a d hd r) = point P t r := by
  unfold point
  apply prod_congr rfl
  intro q hq
  rw [affinePhaseEquiv_val]
  have he : (a + d * t) % q.val = (a + d * (r q).val) % q.val ↔
      t % q.val = (r q).val := by
    constructor
    · intro h
      have hmod := Nat.ModEq.cancel_left_of_coprime (hd q.val q.property).symm
        (Nat.ModEq.add_left_cancel' a h)
      simpa only [Nat.ModEq, Nat.mod_eq_of_lt (r q).isLt] using hmod
    · intro h
      have hmod : t ≡ (r q).val [MOD q.val] := by
        simpa only [Nat.ModEq, Nat.mod_eq_of_lt (r q).isLt] using h
      exact (hmod.mul_left d).add_left a
  simp only [he]

lemma phaseMean_equiv (P : Finset ℕ) (e : Phase P ≃ Phase P) (f : Phase P → ℝ) :
    phaseMean P (fun r => f (e r)) = phaseMean P f := by
  unfold phaseMean
  rw [e.sum_comp]

noncomputable def progressionCount (P : Finset ℕ) (a d n : ℕ) (r : Phase P) : ℝ :=
  ∑ t ∈ range n, point P (a + d * t) r

lemma progressionCount_affine (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime)
    (a d n : ℕ) (hd : ∀ q ∈ P, d.Coprime q) (r : Phase P) :
    progressionCount P a d n (affinePhaseEquiv P hP a d hd r) = intervalCount P n r := by
  simp only [progressionCount, intervalCount, point_affine P hP a d hd]

/-- All scalar statistics of a single row transfer exactly to the smaller
interval. This statement does not factor joint statistics of several rows. -/
theorem progression_distribution (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime)
    (a d n : ℕ) (hd : ∀ q ∈ P, d.Coprime q) (F : ℝ → ℝ) :
    phaseMean P (fun r => F (progressionCount P a d n r)) =
      phaseMean P (fun r => F (intervalCount P n r)) := by
  rw [← phaseMean_equiv P (affinePhaseEquiv P hP a d hd)]
  simp only [progressionCount_affine P hP a d n hd]

lemma progression_variance_eq (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime)
    (a d n : ℕ) (hd : ∀ q ∈ P, d.Coprime q) :
    phaseMean P (fun r => (progressionCount P a d n r - (n : ℝ) * density P) ^ 2) =
      countVariance P n :=
  progression_distribution P hP a d n hd (fun x => (x - (n : ℝ) * density P) ^ 2)

noncomputable def rowCount (P : Finset ℕ) (m p : ℕ) (a : Fin p) (r : Phase P) : ℝ :=
  ∑ x ∈ (range m).filter (fun x => x % p = a.val), point P x r

/-- Residue rows are exact finite progressions, including their rounded lengths. -/
lemma rowCount_eq_progression (P : Finset ℕ) (m p : ℕ) (hp : 0 < p)
    (a : Fin p) (r : Phase P) :
    rowCount P m p a r = progressionCount P a.val p
      (IntervalRescaling.progressionLength m p a.val hp) r := by
  have he := IntervalRescaling.residueClass_eq_image m p a.val hp
  simp only [Nat.ModEq, Nat.mod_eq_of_lt a.isLt] at he
  unfold rowCount
  rw [he, sum_image]
  · rfl
  · intro x hx y hy hxy
    exact Nat.eq_of_mul_eq_mul_left hp (Nat.add_left_cancel hxy)

/-- Averaging over core phases gives the ordinary interval variance for a row. -/
theorem row_variance_eq (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime)
    (m p : ℕ) (hp : 0 < p) (hc : ∀ q ∈ P, p.Coprime q) (a : Fin p) :
    phaseMean P (fun r => (rowCount P m p a r -
      (IntervalRescaling.progressionLength m p a.val hp : ℝ) * density P) ^ 2) =
      countVariance P (IntervalRescaling.progressionLength m p a.val hp) := by
  simp only [rowCount_eq_progression P m p hp]
  exact progression_variance_eq P hP a.val p _ hc

lemma row_variance_le (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime)
    (m p : ℕ) (hp : 0 < p) (hc : ∀ q ∈ P, p.Coprime q) (a : Fin p) :
    phaseMean P (fun r => (rowCount P m p a r -
      (IntervalRescaling.progressionLength m p a.val hp : ℝ) * density P) ^ 2) ≤
      (IntervalRescaling.progressionLength m p a.val hp : ℝ) * density P * (1 - density P) := by
  rw [row_variance_eq P hP m p hp hc]
  exact phase_variance_le P hP _

#print axioms progression_distribution
#print axioms row_variance_eq
#print axioms row_variance_le
end Erdos970.GapAverages
