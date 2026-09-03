import Submission.Forest93Shapes
import Submission.ForestRestricted
import Submission.RootOverlapCompensation

/-! Concrete coordinate laws and residue boxes for the eight-prime profile. -/
namespace Erdos7Forest93Concrete
open scoped BigOperators
open Erdos7Forest93Certificate Erdos7Forest93Shapes Erdos7ForestRestricted
open Erdos7ForestUnion Erdos7RootOverlapCompensation
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedSectionVars false

abbrev Coord : Fin 8 → Type := Fin.cases (Fin 9) (fun j => Fin (primes j.succ))
instance coordFintype (j : Fin 8) : Fintype (Coord j) := by
  induction j using Fin.cases with
  | zero => change Fintype (Fin 9); infer_instance
  | succ j => change Fintype (Fin (primes j.succ)); infer_instance
instance coordDecidableEq (j : Fin 8) : DecidableEq (Coord j) := by
  induction j using Fin.cases with
  | zero => change DecidableEq (Fin 9); infer_instance
  | succ j => change DecidableEq (Fin (primes j.succ)); infer_instance

def zeroLeaf (j : Fin 7) : Coord j.succ := ⟨0,(prime_properties.2 j.succ).1.pos⟩
def root (b : Fin 9) : Finset (Fin 9) := survivors 0 b
def leaf (j : Fin 7) : Finset (Coord j.succ) := Finset.univ.erase (zeroLeaf j)
def allowed (b : Fin 9) : ∀ j,Finset (Coord j) := Fin.cases (root b) leaf
noncomputable def law (b : Fin 9) (j : Fin 8) : Coord j → ℚ := restricted (allowed b j)

def rootSection (i : Index) (r : Fin 9) : Finset (Fin 9) :=
  if exponent i 0 = 0 then Finset.univ else
  if exponent i 0 = 1 then Finset.univ.filter (fun x => x.val%3 = r.val%3) else {r}
def boxSection (i : Index) (r : ∀ j,Coord j) : ∀ j,Finset (Coord j) :=
  Fin.cases (rootSection i (r 0)) (fun j => if exponent i j.succ = 0 then Finset.univ else {r j.succ})

lemma root_card (b : Fin 9) (hb : b.val%3 ≠ 0) : (root b).card = 5 := survivors_card 0 b hb
lemma leaf_card (j : Fin 7) : (leaf j).card = primes j.succ-1 := by
  simp [leaf,Coord]
lemma allowed_nonempty (b : Fin 9) (hb : b.val%3 ≠ 0) (j : Fin 8) : (allowed b j).Nonempty := by
  induction j using Fin.cases with
  | zero => apply Finset.card_pos.mp; rw [show (allowed b 0).card = (root b).card from rfl,root_card b hb]; decide
  | succ j =>
    apply Finset.card_pos.mp
    change 0 < (leaf j).card
    rw [leaf_card]
    have hp := (prime_properties.2 j.succ).1.two_le
    omega
lemma law_nonneg (b : Fin 9) (j : Fin 8) (x : Coord j) : 0 ≤ law b j x := restricted_nonneg _ _
lemma law_sum (b : Fin 9) (hb : b.val%3 ≠ 0) (j : Fin 8) : (∑ x,law b j x) = 1 :=
  restricted_sum _ (allowed_nonempty b hb j)

lemma section_zero (i : Index) (r : ∀ j,Coord j) (j : Fin 8) (hj : exponent i j = 0) :
    boxSection i r j = Finset.univ := by
  induction j using Fin.cases with
  | zero => simp [boxSection,rootSection,hj]
  | succ j => simp [boxSection,hj]

lemma root_fiber (b r : Fin 9) :
    root b ∩ (Finset.univ.filter (fun x : Fin 9 => x.val%3 = r.val%3)) =
      branch 0 b ⟨r.val%3,Nat.mod_lt _ (by decide)⟩ := by
  ext x
  simp [root,branch]

lemma branch_card_le : ∀ (b : Fin 9) (r : Fin 3),b.val%3 ≠ 0 → (branch 0 b r).card ≤ 3 := by
  decide +kernel

lemma root_mass_le (b : Fin 9) (hb : b.val%3 ≠ 0) (i : Index) (r : Fin 9) :
    mass (law b 0) (fun x => x ∈ rootSection i r) ≤ sectionBound i 0 := by
  by_cases h0 : exponent i 0 = 0
  · simp only [rootSection,if_pos h0]
    have hh := restricted_full (root b) (allowed_nonempty b hb 0)
    simpa [law,allowed,sectionBound,sectionNum,sectionDen,h0] using hh.le
  · by_cases h1 : exponent i 0 = 1
    · have hh := branch_card_le b ⟨r.val%3,Nat.mod_lt _ (by decide)⟩ hb
      have hq : ((branch 0 b ⟨r.val%3,Nat.mod_lt _ (by decide)⟩).card:ℚ) ≤ 3 := by exact_mod_cast hh
      change mass (restricted (root b)) _ ≤ _
      rw [rootSection,if_neg h0,if_pos h1]
      have hm := restricted_mass (root b) (Finset.univ.filter (fun x : Fin 9 => x.val%3 = r.val%3))
      erw [hm]
      rw [root_fiber,root_card b hb]
      norm_num [sectionBound,sectionNum,sectionDen,h0,h1]
      linarith
    · have hh := restricted_singleton_le (root b) r
      rw [root_card b hb] at hh
      simpa [law,allowed,rootSection,h0,h1,sectionBound,sectionNum,sectionDen] using hh

lemma leaf_mass_le (b : Fin 9) (hb : b.val%3 ≠ 0) (i : Index) (r : ∀ j,Coord j) (j : Fin 7) :
    mass (law b j.succ) (fun x => x ∈ boxSection i r j.succ) ≤ sectionBound i j.succ := by
  by_cases h0 : exponent i j.succ = 0
  · have hh := restricted_full (leaf j) (allowed_nonempty b hb j.succ)
    simpa [law,allowed,boxSection,sectionBound,sectionNum,sectionDen,h0] using hh.le
  · have hh := restricted_singleton_le (leaf j) (r j.succ)
    rw [leaf_card] at hh
    simpa [law,allowed,boxSection,sectionBound,sectionNum,sectionDen,h0] using hh

lemma section_mass_le (b : Fin 9) (hb : b.val%3 ≠ 0) (i : Index) (r : ∀ j,Coord j) (j : Fin 8) :
    mass (law b j) (fun x => x ∈ boxSection i r j) ≤ sectionBound i j := by
  induction j using Fin.cases with
  | zero => exact root_mass_le b hb i (r 0)
  | succ j => exact leaf_mass_le b hb i r j

#print axioms section_mass_le
end Erdos7Forest93Concrete
