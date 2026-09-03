import Submission.SurvivorResampling

/-! Exact coordinate resampling for genuine prime-class interval sieves.
The abstract finite populations are identified with survivors and private
positions; no independence of residue rows is asserted. -/
namespace Erdos970.Resampling
open Finset OptimalCoverCore

/-- The normalized old residue. -/
def oldResidue (p : ℕ) (hp : 0 < p) (r : ℕ → ℕ) : Fin p :=
  ⟨r p % p, Nat.mod_lt _ hp⟩

lemma avoidClass_erase (m : ℕ) (P : Finset ℕ) (r : ℕ → ℕ)
    (p : ℕ) (hp : 0 < p) (hpP : p ∈ P) :
    avoidClass (survivors m (P.erase p) r) p (oldResidue p hp r) =
      survivors m P r := by
  classical
  ext x
  simp only [avoidClass, mem_filter, mem_survivors, oldResidue]
  constructor
  · rintro ⟨⟨hxm, hxP⟩, hxp⟩
    refine ⟨hxm, fun q hq => ?_⟩
    by_cases hqp : q = p
    · subst q
      exact hxp
    · exact hxP q (mem_erase.mpr ⟨hqp, hq⟩)
  · rintro ⟨hxm, hxP⟩
    exact ⟨⟨hxm, fun q hq => hxP q (mem_of_mem_erase hq)⟩, hxP p hpP⟩

lemma classHits_erase (m : ℕ) (P : Finset ℕ) (r : ℕ → ℕ)
    (p : ℕ) (hp : 0 < p) :
    classHits (survivors m (P.erase p) r) p (oldResidue p hp r) =
      ((privatePositions m P r p).card : ℝ) := by
  rw [classHits_card]
  rfl

lemma avoidClass_update (m : ℕ) (P : Finset ℕ) (r : ℕ → ℕ)
    (p : ℕ) (hpP : p ∈ P) (a : Fin p) :
    avoidClass (survivors m (P.erase p) r) p a =
      survivors m P (Function.update r p a.val) := by
  have he := survivors_insert_update m (P.erase p) r p a.val (notMem_erase p P)
  rw [insert_erase hpP] at he
  rw [he]
  simp only [avoidClass, Nat.ModEq, Nat.mod_eq_of_lt a.isLt]

lemma remainingCount_update (m : ℕ) (P : Finset ℕ) (r : ℕ → ℕ)
    (p : ℕ) (hpP : p ∈ P) (a : Fin p) :
    remainingCount (survivors m (P.erase p) r) p a =
      ((survivors m P (Function.update r p a.val)).card : ℝ) := by
  rw [remainingCount, avoidClass_update m P r p hpP a]

lemma remainingCount_old (m : ℕ) (P : Finset ℕ) (r : ℕ → ℕ)
    (p : ℕ) (hp : 0 < p) (hpP : p ∈ P) :
    remainingCount (survivors m (P.erase p) r) p (oldResidue p hp r) =
      ((survivors m P r).card : ℝ) := by
  rw [remainingCount, avoidClass_erase m P r p hp hpP]

/-- Coordinate resampling trades exposed private positions for hits among
old survivors. The private population is not the old survivor population. -/
theorem prime_resampling_increment (m : ℕ) (P : Finset ℕ) (r : ℕ → ℕ)
    (p : ℕ) (hp : 0 < p) (hpP : p ∈ P) (a : Fin p) :
    ((survivors m P (Function.update r p a.val)).card : ℝ) -
      ((survivors m P r).card : ℝ) =
      (if a = oldResidue p hp r then 0 else ((privatePositions m P r p).card : ℝ)) -
        classHits (survivors m P r) p a := by
  have h := resampling_increment (survivors m (P.erase p) r) p a (oldResidue p hp r)
  rwa [remainingCount_update m P r p hpP, remainingCount_old m P r p hp hpP,
    classHits_erase, avoidClass_erase m P r p hp hpP] at h

/-- The full conditional second moment, including its negative mixed term. -/
theorem prime_increment_second_moment (m : ℕ) (P : Finset ℕ) (r : ℕ → ℕ)
    (p : ℕ) (hp : 0 < p) (hpP : p ∈ P) :
    residueMean p (fun a => (((survivors m P (Function.update r p a.val)).card : ℝ) -
      ((survivors m P r).card : ℝ)) ^ 2) =
      (1 - 1 / p) * ((privatePositions m P r p).card : ℝ) ^ 2 -
      2 * ((privatePositions m P r p).card : ℝ) * ((survivors m P r).card : ℝ) / p +
      residueMean p (fun a => (classHits (survivors m P r) p a) ^ 2) := by
  have h := increment_second_moment (survivors m (P.erase p) r) p hp (oldResidue p hp r)
  simp only [remainingCount_old m P r p hp hpP] at h
  simpa only [remainingCount_update m P r p hpP,
    classHits_erase, avoidClass_erase m P r p hp hpP] using h

/-- Covered phases can still have nonzero resampling second moment. -/
theorem prime_covered_second_moment (m : ℕ) (P : Finset ℕ) (r : ℕ → ℕ)
    (p : ℕ) (hp : 0 < p) (hpP : p ∈ P) (hzero : survivors m P r = ∅) :
    residueMean p (fun a => ((survivors m P (Function.update r p a.val)).card : ℝ) ^ 2) =
      (1 - 1 / p) * ((privatePositions m P r p).card : ℝ) ^ 2 := by
  have h := prime_increment_second_moment m P r p hp hpP
  simpa [hzero, classHits, residueMean] using h

/-- A genuine covered example: prime 2 covers 0 and 2, prime 3 covers 1. -/
def exampleResidues (p : ℕ) : ℕ := if p = 3 then 1 else 0

lemma example_covered : survivors 3 {2, 3} exampleResidues = ∅ := by
  decide +kernel

lemma example_private : (privatePositions 3 {2, 3} exampleResidues 2).card = 2 := by
  decide +kernel

/-- At this zero-survivor phase the raw resampling second moment is two. -/
theorem example_second_moment :
    residueMean 2 (fun a => ((survivors 3 {2, 3}
      (Function.update exampleResidues 2 a.val)).card : ℝ) ^ 2) = 2 := by
  rw [prime_covered_second_moment 3 {2, 3} exampleResidues 2 (by omega)
    (by simp) example_covered, example_private]
  norm_num

/-- Thus no uniform conditional second-moment bound can be proportional
solely to the current survivor count, even for genuine distinct-prime covers. -/
theorem no_survivor_only_conditional_second_moment :
    ¬ ∃ C : ℝ, ∀ (m : ℕ) (P : Finset ℕ) (r : ℕ → ℕ),
      (∀ q ∈ P, q.Prime) → ∀ p : ℕ, (hp : 0 < p) → p ∈ P →
      residueMean p (fun a => (((survivors m P (Function.update r p a.val)).card : ℝ) -
        ((survivors m P r).card : ℝ)) ^ 2) ≤ C * ((survivors m P r).card : ℝ) := by
  rintro ⟨C, hC⟩
  have h := hC 3 {2, 3} exampleResidues (by norm_num) 2 (by omega) (by simp)
  simp only [example_covered, card_empty, Nat.cast_zero, sub_zero, mul_zero] at h
  rw [example_second_moment] at h
  norm_num at h

#print axioms prime_resampling_increment
#print axioms prime_increment_second_moment
#print axioms prime_covered_second_moment
#print axioms example_second_moment
#print axioms no_survivor_only_conditional_second_moment
end Erdos970.Resampling
