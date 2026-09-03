import Submission.BackwardNFASimulation

/-! Finite-data interface for backward NFA simulations. These theorems
are conditional: no rejected-seed simulation is asserted to exist. -/
namespace Erdos406BackwardNFAFinite
open Erdos406MSDCertificate Erdos406ComplementNFA Erdos406BackwardNFASimulation

variable {σ : Type*} [DecidableEq σ]

structure Data (σ : Type*) [DecidableEq σ] where
  step : σ → ℕ → Finset σ
  start : Finset σ
  accept : Finset σ
  relation : σ → ℕ → Finset σ

namespace Data
variable (D : Data σ)

def toNFA : NFA ℕ σ where
  step q d := D.step q d
  start := D.start
  accept := D.accept

def stepStates (U : Finset σ) (d : ℕ) : Finset σ := U.biUnion (fun q => D.step q d)

def evalStates (n : ℕ) : Finset σ :=
  (Nat.digits 3 n).reverse.foldl D.stepStates D.start

lemma stepStates_coe (U : Finset σ) (d : ℕ) :
    (D.stepStates U d : Set σ) = D.toNFA.stepSet U d := by
  ext r
  simp [stepStates, NFA.mem_stepSet, toNFA]

lemma evalFrom_coe (w : List ℕ) (U : Finset σ) :
    ((w.foldl D.stepStates U : Finset σ) : Set σ) = D.toNFA.evalFrom U w := by
  induction w generalizing U with
  | nil => rfl
  | cons d w ih =>
    rw [List.foldl_cons, NFA.evalFrom_cons, ih, stepStates_coe]

lemma evalStates_coe (n : ℕ) :
    (D.evalStates n : Set σ) = evalNat D.toNFA.toDFA n := by
  exact D.evalFrom_coe (Nat.digits 3 n).reverse D.start

def toSimulation
    (hinit : ∀ c, c < 4 → ∀ p ∈ D.evalStates c,
      (D.start ∩ D.relation p c).Nonempty)
    (hstep : ∀ p c, c < 4 → ∀ q ∈ D.relation p c,
      ∀ d, d < 3 → ∀ e, e < 3 → ∀ c', c' < 4 →
      4 * d + c' = 3 * c + e → ∀ r ∈ D.step p e,
      (D.step q d ∩ D.relation r c').Nonempty)
    (hfinish : ∀ p ∈ D.accept, D.relation p 0 ⊆ D.accept) : Simulation σ where
  M := D.toNFA
  R p q c := q ∈ D.relation p c
  initial := by
    intro c hc p hp
    rw [← D.evalStates_coe] at hp
    obtain ⟨q, hq⟩ := hinit c hc p hp
    exact ⟨q, (Finset.mem_inter.mp hq).1, (Finset.mem_inter.mp hq).2⟩
  step := by
    intro p q c d e c' r hc hd he hc' hcarry hpq hr
    obtain ⟨s, hs⟩ := hstep p c hc q hpq d hd e he c' hc' hcarry r hr
    exact ⟨s, (Finset.mem_inter.mp hs).1, (Finset.mem_inter.mp hs).2⟩
  finish := by
    intro p q hpq hp
    exact hfinish p hp hpq

/-- A finite simulation, a good-digit state, and a rejected actual seed
would imply exactly the conjecture. All hypotheses remain explicit. -/
theorem finite_of_checks
    (hinit : ∀ c, c < 4 → ∀ p ∈ D.evalStates c,
      (D.start ∩ D.relation p c).Nonempty)
    (hstep : ∀ p c, c < 4 → ∀ q ∈ D.relation p c,
      ∀ d, d < 3 → ∀ e, e < 3 → ∀ c', c' < 4 →
      4 * d + c' = 3 * c + e → ∀ r ∈ D.step p e,
      (D.step q d ∩ D.relation r c').Nonempty)
    (hfinish : ∀ p ∈ D.accept, D.relation p 0 ⊆ D.accept)
    (g : σ) (hfirst : g ∈ D.stepStates D.start 1)
    (hloop : ∀ d, d < 2 → g ∈ D.step g d)
    (haccept : g ∈ D.accept) (E : ℕ)
    (hseed : Disjoint (D.evalStates (4 ^ E)) D.accept) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  let C := D.toSimulation hinit hstep hfinish
  refine C.finite_of_cover g ?_ hloop haccept E ?_
  · change g ∈ D.toNFA.stepSet (D.start : Set σ) 1
    rw [← D.stepStates_coe]
    exact hfirst
  · rintro ⟨p, hp, hpa⟩
    change p ∈ evalNat D.toNFA.toDFA (4 ^ E) at hp
    rw [← D.evalStates_coe] at hp
    exact Finset.disjoint_left.mp hseed hp hpa

/-- The carry equation determines the old carry and output digit. This form
avoids checking the numerous impossible carry tuples in concrete data. -/
def toSimulation_fast
    (hinit : ∀ c, c < 4 → ∀ p ∈ D.evalStates c,
      (D.start ∩ D.relation p c).Nonempty)
    (hstep : ∀ p d, d < 3 → ∀ c', c' < 4 →
      ∀ r ∈ D.step p ((4 * d + c') % 3),
      ∀ q ∈ D.relation p ((4 * d + c') / 3),
      (D.step q d ∩ D.relation r c').Nonempty)
    (hfinish : ∀ p ∈ D.accept, D.relation p 0 ⊆ D.accept) : Simulation σ :=
  D.toSimulation hinit (by
    intro p c hc q hpq d hd e he c' hc' hcarry r hr
    have hv : (4 * d + c') / 3 = c := by omega
    have hm : (4 * d + c') % 3 = e := by omega
    refine hstep p d hd c' hc' r ?_ q ?_
    · simpa only [hm] using hr
    · simpa only [hv] using hpq) hfinish

theorem finite_of_fast_checks
    (hinit : ∀ c, c < 4 → ∀ p ∈ D.evalStates c,
      (D.start ∩ D.relation p c).Nonempty)
    (hstep : ∀ p d, d < 3 → ∀ c', c' < 4 →
      ∀ r ∈ D.step p ((4 * d + c') % 3),
      ∀ q ∈ D.relation p ((4 * d + c') / 3),
      (D.step q d ∩ D.relation r c').Nonempty)
    (hfinish : ∀ p ∈ D.accept, D.relation p 0 ⊆ D.accept)
    (g : σ) (hfirst : g ∈ D.stepStates D.start 1)
    (hloop : ∀ d, d < 2 → g ∈ D.step g d)
    (haccept : g ∈ D.accept) (E : ℕ)
    (hseed : Disjoint (D.evalStates (4 ^ E)) D.accept) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  let C := D.toSimulation_fast hinit hstep hfinish
  refine C.finite_of_cover g ?_ hloop haccept E ?_
  · change g ∈ D.toNFA.stepSet (D.start : Set σ) 1
    rw [← D.stepStates_coe]
    exact hfirst
  · rintro ⟨p, hp, hpa⟩
    change p ∈ evalNat D.toNFA.toDFA (4 ^ E) at hp
    rw [← D.evalStates_coe] at hp
    exact Finset.disjoint_left.mp hseed hp hpa

end Data
#print axioms Data.toSimulation
#print axioms Data.finite_of_checks
#print axioms Data.finite_of_fast_checks
end Erdos406BackwardNFAFinite
