import Submission.BinaryRootOverlap
import Submission.ForestRestricted
import Submission.ArithmeticReduction

/-! Exponent-independent two-branch geometry after removing pure ternary
classes. Only the natural geometric class-size bounds are used. -/
namespace Erdos7BinaryRootGeometry
open scoped BigOperators
open Erdos7ForestUnion Erdos7ForestRestricted Erdos7BinaryRootOverlap
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]

def fiber (color : X → Fin 3) (r : Fin 3) : Finset X :=
  Finset.univ.filter (fun x => color x = r)

def branchColor (r : Bool) : Fin 3 := if r then 1 else 2

lemma two_fiber_partition (U : Finset X) (color : X → Fin 3)
    (hzero : ∀ x ∈ U,color x ≠ 0) : U = (U ∩ fiber color 1) ∪ (U ∩ fiber color 2) := by
  ext x
  simp only [Finset.mem_union,Finset.mem_inter,fiber,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro hx
    have hc : color x = 1 ∨ color x = 2 := by
      have hh := hzero x hx
      have hv : (color x).val ≠ 0 := by simpa only [ne_eq,Fin.ext_iff,Fin.val_zero] using hh
      have hl := (color x).isLt
      rcases (show (color x).val = 1 ∨ (color x).val = 2 by omega) with h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h)
    exact hc.elim (fun h => Or.inl ⟨hx,h⟩) (fun h => Or.inr ⟨hx,h⟩)
  · rintro (h | h) <;> exact h.1

lemma two_fiber_disjoint (U : Finset X) (color : X → Fin 3) :
    Disjoint (U ∩ fiber color 1) (U ∩ fiber color 2) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have h₁ := (Finset.mem_filter.mp (Finset.mem_inter.mp hx).2).2
  have h₂ := (Finset.mem_filter.mp (Finset.mem_inter.mp hy).2).2
  have : (1:Fin 3) = 2 := h₁.symm.trans h₂
  exact (by decide : (1:Fin 3) ≠ 2) this

lemma color_mass (U : Finset X) (color : X → Fin 3) (r : Fin 3) :
    mass (restricted U) (fun x => color x = r) = ((U ∩ fiber color r).card:ℚ)/U.card := by
  have he : (fun x => color x = r) = (fun x => x ∈ fiber color r) := by
    funext x
    simp [fiber]
  rw [he,restricted_mass]

/-- If at least half the root space survives, each of its two surviving
first-digit branches has conditional mass between1/3 and2/3. -/
theorem conditioned_two_branch_law (U : Finset X) (color : X → Fin 3)
    (hzero : ∀ x ∈ U,color x ≠ 0)
    (hU : (Fintype.card X:ℚ)/2 ≤ U.card)
    (hcolor : ∀ r,((fiber color r).card:ℚ) ≤ (Fintype.card X:ℚ)/3) :
    ∃ t : ℚ,(1/3 ≤ t ∧ t ≤ 2/3) ∧
      ∀ r : Bool,mass (restricted U) (fun x => color x = branchColor r) = branchMass t r := by
  have hN : (0:ℚ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hUc : (0:ℚ) < U.card := by linarith
  let t := mass (restricted U) (fun x => color x = (1:Fin 3))
  let u := mass (restricted U) (fun x => color x = (2:Fin 3))
  have hle (r : Fin 3) : mass (restricted U) (fun x => color x = r) ≤ 2/3 := by
    rw [color_mass]
    apply (div_le_iff₀ hUc).mpr
    have hsub : ((U ∩ fiber color r).card:ℚ) ≤ (fiber color r).card := by
      exact_mod_cast Finset.card_le_card (Finset.inter_subset_right (s₁ := U) (s₂ := fiber color r))
    have hc := hcolor r
    linarith
  have hsum : t+u = 1 := by
    have hc : U.card = (U ∩ fiber color 1).card + (U ∩ fiber color 2).card := by
      calc
        U.card = ((U ∩ fiber color 1) ∪ (U ∩ fiber color 2)).card :=
          congrArg Finset.card (two_fiber_partition U color hzero)
        _ = _ := Finset.card_union_of_disjoint (two_fiber_disjoint U color)
    have hq : (U.card:ℚ) = (U ∩ fiber color 1).card + (U ∩ fiber color 2).card := by exact_mod_cast hc
    dsimp only [t,u]
    rw [color_mass,color_mass,← add_div,← hq,div_self (ne_of_gt hUc)]
  refine ⟨t,⟨by have := hle 2; change u ≤ 2/3 at this; linarith,hle 1⟩,?_⟩
  intro r
  cases r
  · change u = 1-t
    linarith
  · rfl

/-- Geometric pure-class bounds imply the root half-space bound, uniformly
for every finite collection of positive exponents. -/
theorem pure_complement_two_branch (K : Finset ℕ) (hK : ∀ a ∈ K,0 < a)
    (h1 : 1 ∈ K) (B : ℕ → Finset X) (color : X → Fin 3)
    (hB : ∀ a ∈ K,((B a).card:ℚ) ≤ (Fintype.card X:ℚ)*((3:ℚ)⁻¹)^a)
    (hB1 : ∀ x,color x = 0 → x ∈ B 1)
    (hcolor : ∀ r,((fiber color r).card:ℚ) ≤ (Fintype.card X:ℚ)/3) :
    let U := Finset.univ \ K.biUnion B
    ∃ t : ℚ,(1/3 ≤ t ∧ t ≤ 2/3) ∧
      ∀ r : Bool,mass (restricted U) (fun x => color x = branchColor r) = branchMass t r := by
  dsimp only
  apply conditioned_two_branch_law
  · intro x hx hc
    have hn := (Finset.mem_sdiff.mp hx).2
    exact hn (Finset.mem_biUnion.mpr ⟨1,h1,hB1 x hc⟩)
  · have hh := Erdos7Reduction.relative_complement_bound K B (fun a => ((3:ℚ)⁻¹)^a) (1/2) hB
      (by
        have hg := Erdos7Reduction.positive_geometric_sum_le 3 (by decide) K hK
        norm_num only [Nat.cast_ofNat,show (3:ℚ)-1 = 2 by norm_num] at hg
        simpa only [one_div] using hg)
    convert hh using 1 <;> ring
  · exact hcolor

#print axioms conditioned_two_branch_law
#print axioms pure_complement_two_branch
end Erdos7BinaryRootGeometry
