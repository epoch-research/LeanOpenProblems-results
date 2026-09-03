import Submission.ExceptionSieveBounds
import Submission.GaussianPrimeDecision

/-! A total, computable finite test for each exception-retaining cutoff.
The original negation is equivalent to finding a rejecting cutoff for every
jump bound. No termination theorem for that search is asserted. -/
namespace Erdos952Investigation
namespace ExceptionSieveDecision
open FiniteSieveReduction ExceptionSieveReduction ExceptionSieveBounds
set_option maxHeartbeats 0

instance allowedDecidable (N : ℕ) (z : GaussianInt) : Decidable (Allowed N z) :=
  decidable_of_iff
    (∀ p : Fin (N+1), p.val.Prime → ¬ (p.val : ℤ) ∣ z.norm) (by
      constructor
      · intro h p hpN hp
        exact h ⟨p,by omega⟩ hp
      · intro h p hp
        exact h p.val (by have := p.isLt; omega) hp)

instance candidateDecidable (N : ℕ) (z : GaussianInt) : Decidable (Candidate N z) :=
  inferInstanceAs (Decidable (_ ∨ _))

instance candidateAdjDecidable (C : ℤ) (N : ℕ) : DecidableRel (candidateGraph C N).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

def boxRadius (C : ℤ) (M : ℕ) : ℕ := M*(max C 1).toNat

lemma boxRadius_cast (C : ℤ) (M : ℕ) : (boxRadius C M : ℤ) = (M : ℤ)*max C 1 := by
  have hD : 0 ≤ max C 1 := (by norm_num : (0 : ℤ) ≤ 1).trans (le_max_right _ _)
  simp only [boxRadius,Nat.cast_mul,Int.toNat_of_nonneg hD]

abbrev Box (C : ℤ) (M : ℕ) := Fin (2*boxRadius C M+1) × Fin (2*boxRadius C M+1)

def point (C : ℤ) (M : ℕ) (z : GaussianInt) (r : Box C M) : GaussianInt :=
  ⟨z.re+(r.1.val : ℤ)-(boxRadius C M : ℤ),
    z.im+(r.2.val : ℤ)-(boxRadius C M : ℤ)⟩

def Fits (C : ℤ) (N : ℕ) (z : GaussianInt) (M : ℕ)
    (f : Fin (M+1) → Box C M) : Prop :=
  point C M z (f 0) = z ∧ Function.Injective (fun i => point C M z (f i)) ∧
    ∀ i : Fin M, (candidateGraph C N).Adj
      (point C M z (f i.castSucc)) (point C M z (f i.succ))

instance (C : ℤ) (N : ℕ) (z : GaussianInt) (M : ℕ) (f : Fin (M+1) → Box C M) :
    Decidable (Fits C N z M f) := by
  unfold Fits Function.Injective
  infer_instance

def FinitePrefixTest (C : ℤ) (N : ℕ) (z : GaussianInt) (M : ℕ) : Prop :=
  ∃ f : Fin (M+1) → Box C M, Fits C N z M f

instance (C : ℤ) (N : ℕ) (z : GaussianInt) (M : ℕ) :
    Decidable (FinitePrefixTest C N z M) :=
  inferInstanceAs (Decidable (∃ f : Fin (M+1) → Box C M, Fits C N z M f))

lemma prefix_projection_bound {C : ℤ} {N M : ℕ} {z : GaussianInt}
    (f : RayReduction.Prefix (candidateGraph C N) z M) (k : Fin 4) (i : Fin (M+1)) :
    coordinate k (f.val i)-coordinate k z ≤ (i.val : ℤ)*max C 1 := by
  induction i using Fin.induction with
  | zero => rw [f.property.1]; simp
  | succ i ih =>
    have hh := coordinate_step C k (f.val i.castSucc) (f.val i.succ)
      (f.property.2.2 i).2.2.2
    simp only [Fin.val_castSucc] at ih
    simp only [Fin.val_succ,Nat.cast_add,Nat.cast_one]
    nlinarith

lemma prefix_box_bound {C : ℤ} {N M : ℕ} {z : GaussianInt}
    (f : RayReduction.Prefix (candidateGraph C N) z M) (i : Fin (M+1)) :
    -(boxRadius C M : ℤ) ≤ (f.val i).re-z.re ∧
      (f.val i).re-z.re ≤ (boxRadius C M : ℤ) ∧
      -(boxRadius C M : ℤ) ≤ (f.val i).im-z.im ∧
      (f.val i).im-z.im ≤ (boxRadius C M : ℤ) := by
  have hD : 0 ≤ max C 1 := (by norm_num : (0 : ℤ) ≤ 1).trans (le_max_right _ _)
  have hi : (i.val : ℤ) ≤ M := by exact_mod_cast (show i.val ≤ M by omega)
  have hm := mul_le_mul_of_nonneg_right hi hD
  rw [← boxRadius_cast C M] at hm
  have h0 := (prefix_projection_bound f 0 i).trans hm
  have h1 := (prefix_projection_bound f 1 i).trans hm
  have h2 := (prefix_projection_bound f 2 i).trans hm
  have h3 := (prefix_projection_bound f 3 i).trans hm
  change (f.val i).re-z.re ≤ (boxRadius C M : ℤ) at h0
  change -(f.val i).re- -z.re ≤ (boxRadius C M : ℤ) at h1
  change (f.val i).im-z.im ≤ (boxRadius C M : ℤ) at h2
  change -(f.val i).im- -z.im ≤ (boxRadius C M : ℤ) at h3
  exact ⟨by omega,h0,by omega,h2⟩

theorem finite_prefix_test_iff (C : ℤ) (N : ℕ) (z : GaussianInt) (M : ℕ) :
    FinitePrefixTest C N z M ↔ Nonempty (RayReduction.Prefix (candidateGraph C N) z M) := by
  constructor
  · rintro ⟨f,hf⟩
    exact ⟨⟨fun i => point C M z (f i),hf⟩⟩
  · rintro ⟨f⟩
    let g : Fin (M+1) → Box C M := fun i =>
      (⟨((f.val i).re-z.re+(boxRadius C M : ℤ)).toNat,by
        have hh := prefix_box_bound f i; omega⟩,
       ⟨((f.val i).im-z.im+(boxRadius C M : ℤ)).toNat,by
        have hh := prefix_box_bound f i; omega⟩)
    have hg (i : Fin (M+1)) : point C M z (g i) = f.val i := by
      have hh := prefix_box_bound f i
      apply Zsqrtd.ext <;> dsimp [point,g] <;> omega
    refine ⟨g,?_,?_,?_⟩
    · rw [hg,f.property.1]
    · intro i j he
      dsimp only at he
      rw [hg,hg] at he
      exact f.property.2.1 he
    · intro i
      rw [hg,hg]
      exact f.property.2.2 i

/-- This Boolean function is computable by finite enumeration. The resulting
bounds are enormous; the definition is a decision procedure, not a practical
replacement for the compact moat certificates used elsewhere. -/
def cutoffTest (C : ℤ) (N : ℕ) : Bool :=
  decide (FinitePrefixTest C N (3 : GaussianInt) (prefixBound C N 3))

theorem cutoffTest_true_iff (C : ℤ) (N : ℕ) :
    cutoffTest C N = true ↔
      {w | (candidateGraph C N).Reachable (3 : GaussianInt) w}.Infinite := by
  rw [cutoffTest,decide_eq_true_eq,finite_prefix_test_iff]
  exact (infinite_component_iff_long_prefix C N 3).symm

theorem cutoffTest_false_iff (C : ℤ) (N : ℕ) :
    cutoffTest C N = false ↔
      {w | (candidateGraph C N).Reachable (3 : GaussianInt) w}.Finite := by
  have hh := not_congr (cutoffTest_true_iff C N)
  simpa only [Bool.not_eq_true,Set.not_infinite] using hh

/-- An exact arithmetic search formulation. The missing statement is that
this search succeeds for every C, or that some C has no rejecting cutoff. -/
theorem negation_iff_cutoffTest :
    (¬ ∃ (x : ℕ → GaussianInt) (C : ℤ), Function.Injective x ∧
      ∀ n, Prime (x n) ∧ (x (n+1)-x n).norm < C) ↔
    ∀ C : ℤ, ∃ N : ℕ, cutoffTest C N = false := by
  rw [negation_iff_seed_cutoffs]
  apply forall_congr'
  intro C
  exact exists_congr (fun N => (cutoffTest_false_iff C N).symm)

#print axioms finite_prefix_test_iff
#print axioms cutoffTest_false_iff
#print axioms negation_iff_cutoffTest

end ExceptionSieveDecision
end Erdos952Investigation
