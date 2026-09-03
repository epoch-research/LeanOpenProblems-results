import FormalConjecturesUtil

/-!
A finite-to-countable Ramsey transfer cannot be justified by increasing the
cardinality of a Hales--Jewett cube: at every dimension the three-letter
cube has a countable coloring with no monochromatic combinatorial line.
This auxiliary result does not settle Erdős Problem 595.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Erdos595CountableHalesJewett

noncomputable def sqNorm {I : Type*} (x : I →₀ ℚ) : ℚ :=
  ∑ i ∈ x.support, x i ^ 2

lemma sqNorm_on {I : Type*} (x : I →₀ ℚ) (s : Finset I)
    (hs : x.support ⊆ s) : sqNorm x = ∑ i ∈ s, x i ^ 2 := by
  classical
  apply Finset.sum_subset hs
  intro i _ hi
  have hx : x i = 0 := Finsupp.notMem_support_iff.mp hi
  simp [hx]

/-- Three rational vectors on a sphere cannot form a nonconstant
arithmetic progression. Only their finite supports are used. -/
theorem sqNorm_rigid {I : Type*} (x y z : I →₀ ℚ)
    (hrel : x + z = y + y) (hxy : sqNorm x = sqNorm y)
    (hxz : sqNorm x = sqNorm z) : x = z := by
  classical
  let s := x.support ∪ y.support ∪ z.support
  have hxs : x.support ⊆ s := fun i hi => Finset.mem_union_left _
    (Finset.mem_union_left _ hi)
  have hys : y.support ⊆ s := fun i hi => Finset.mem_union_left _
    (Finset.mem_union_right _ hi)
  have hzs : z.support ⊆ s := fun i hi => Finset.mem_union_right _ hi
  have hpoint : ∀ i, x i + z i = y i + y i := fun i => by
    simpa only [Finsupp.add_apply] using congrArg (fun v : I →₀ ℚ => v i) hrel
  have hidentity : ∀ i, (x i - z i) ^ 2 =
      2 * (x i ^ 2) + 2 * (z i ^ 2) - 4 * (y i ^ 2) := by
    intro i
    have hi : y i = (x i + z i) / 2 := by linarith [hpoint i]
    rw [hi]
    ring
  have hsum : (∑ i ∈ s, (x i - z i) ^ 2) = 0 := by
    simp_rw [hidentity]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [← sqNorm_on x s hxs, ← sqNorm_on z s hzs, ← sqNorm_on y s hys,
      ← hxy, ← hxz]
    ring
  have hzero : ∀ i ∈ s, (x i - z i) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (x i - z i))).mp hsum
  ext i
  by_cases hi : i ∈ s
  · exact sub_eq_zero.mp (sq_eq_zero_iff.mp (hzero i hi))
  · have hxi : x i = 0 := Finsupp.notMem_support_iff.mp (fun h => hi (hxs h))
    have hzi : z i = 0 := Finsupp.notMem_support_iff.mp (fun h => hi (hzs h))
    exact hxi.trans hzi.symm

/-- Every rational vector space, of any dimension, is a countable union
of sets containing no nonconstant three-term arithmetic progression. -/
theorem exists_progression_free_coloring (E : Type*) [AddCommGroup E] [Module ℚ E] :
    ∃ c : E → ℕ, ∀ x y z, x + z = y + y → c x = c y → c x = c z → x = z := by
  classical
  let b := Module.Free.chooseBasis ℚ E
  obtain ⟨enc, henc⟩ := exists_injective_nat ℚ
  refine ⟨fun x => enc (sqNorm (b.repr x)), ?_⟩
  intro x y z hrel hxy hxz
  apply b.repr.injective
  apply sqNorm_rigid (b.repr x) (b.repr y) (b.repr z)
  · simpa only [map_add] using congrArg b.repr hrel
  · exact henc hxy
  · exact henc hxz

/-- Countably many colors can avoid all combinatorial lines in a
three-letter cube, regardless of the cardinality of its index set. -/
theorem cube_countable_coloring (I : Type*) :
    ∃ c : (I → Fin 3) → ℕ, ∀ l : Combinatorics.Line (Fin 3) I, ¬l.IsMono c := by
  obtain ⟨f, hf⟩ := exists_progression_free_coloring (I → ℚ)
  let emb : (I → Fin 3) → I → ℚ := fun x i => (x i).val
  refine ⟨fun x => f (emb x), ?_⟩
  intro l hmono
  obtain ⟨k, hk⟩ := hmono
  have hrel : emb (l 0) + emb (l 2) = emb (l 1) + emb (l 1) := by
    funext i
    change ((l 0 i).val : ℚ) + (l 2 i).val = (l 1 i).val + (l 1 i).val
    cases hi : l.idxFun i with
    | none => norm_num [Combinatorics.Line.coe_apply, hi]
    | some a => simp only [Combinatorics.Line.coe_apply, hi, Option.getD_some]
  have he := hf (emb (l 0)) (emb (l 1)) (emb (l 2)) hrel
    ((hk 0).trans (hk 1).symm) ((hk 0).trans (hk 2).symm)
  obtain ⟨i, hi⟩ := l.proper
  have hcoord := congrFun he i
  change ((l 0 i).val : ℚ) = (l 2 i).val at hcoord
  norm_num [Combinatorics.Line.coe_apply, hi] at hcoord

/-- This contrasts with the existing finite-palette Hales--Jewett theorem. -/
theorem finite_palette_lines (C : Type*) [Finite C] :
    ∃ (I : Type) (_ : Fintype I), ∀ c : (I → Fin 3) → C,
      ∃ l : Combinatorics.Line (Fin 3) I, l.IsMono c :=
  Combinatorics.Line.exists_mono_in_high_dimension (Fin 3) C

#print axioms sqNorm_rigid
#print axioms exists_progression_free_coloring
#print axioms cube_countable_coloring
#print axioms finite_palette_lines

end Erdos595CountableHalesJewett
